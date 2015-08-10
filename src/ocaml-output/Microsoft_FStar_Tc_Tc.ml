
let syn' = (fun ( env ) ( k ) -> (let _109_11 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Syntax.syn _109_11 (Some (k)))))

let log = (fun ( env ) -> ((Support.ST.read Microsoft_FStar_Options.log_types) && (not ((let _109_14 = (Microsoft_FStar_Tc_Env.current_module env)
in (Microsoft_FStar_Absyn_Syntax.lid_equals Microsoft_FStar_Absyn_Const.prims_lid _109_14))))))

let rng = (fun ( env ) -> (Microsoft_FStar_Tc_Env.get_range env))

let instantiate_both = (fun ( env ) -> (let _38_24 = env
in {Microsoft_FStar_Tc_Env.solver = _38_24.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _38_24.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _38_24.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _38_24.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _38_24.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _38_24.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _38_24.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _38_24.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _38_24.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = true; Microsoft_FStar_Tc_Env.instantiate_vargs = true; Microsoft_FStar_Tc_Env.effects = _38_24.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _38_24.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _38_24.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _38_24.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _38_24.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = _38_24.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = _38_24.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _38_24.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _38_24.Microsoft_FStar_Tc_Env.default_effects}))

let no_inst = (fun ( env ) -> (let _38_27 = env
in {Microsoft_FStar_Tc_Env.solver = _38_27.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _38_27.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _38_27.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _38_27.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _38_27.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _38_27.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _38_27.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _38_27.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _38_27.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = false; Microsoft_FStar_Tc_Env.instantiate_vargs = false; Microsoft_FStar_Tc_Env.effects = _38_27.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _38_27.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _38_27.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _38_27.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _38_27.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = _38_27.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = _38_27.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _38_27.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _38_27.Microsoft_FStar_Tc_Env.default_effects}))

let mk_lex_list = (fun ( vs ) -> (Support.List.fold_right (fun ( v ) ( tl ) -> (let r = (match ((tl.Microsoft_FStar_Absyn_Syntax.pos = Microsoft_FStar_Absyn_Syntax.dummyRange)) with
| true -> begin
v.Microsoft_FStar_Absyn_Syntax.pos
end
| false -> begin
(Support.Microsoft.FStar.Range.union_ranges v.Microsoft_FStar_Absyn_Syntax.pos tl.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (let _109_34 = (let _109_33 = (let _109_32 = (let _109_27 = (let _109_26 = (Microsoft_FStar_Tc_Recheck.recompute_typ v)
in (Support.All.pipe_left (fun ( _109_25 ) -> Support.Microsoft.FStar.Util.Inl (_109_25)) _109_26))
in (_109_27, Some (Microsoft_FStar_Absyn_Syntax.Implicit)))
in (let _109_31 = (let _109_30 = (Microsoft_FStar_Absyn_Syntax.varg v)
in (let _109_29 = (let _109_28 = (Microsoft_FStar_Absyn_Syntax.varg tl)
in (_109_28)::[])
in (_109_30)::_109_29))
in (_109_32)::_109_31))
in (Microsoft_FStar_Absyn_Util.lex_pair, _109_33))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _109_34 (Some (Microsoft_FStar_Absyn_Util.lex_t)) r)))) vs Microsoft_FStar_Absyn_Util.lex_top))

let is_eq = (fun ( _38_1 ) -> (match (_38_1) with
| Some (Microsoft_FStar_Absyn_Syntax.Equality) -> begin
true
end
| _38_37 -> begin
false
end))

let steps = (fun ( env ) -> (match ((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
(Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.SNComp)::[]
end
| false -> begin
(Microsoft_FStar_Tc_Normalize.Beta)::[]
end))

let whnf = (fun ( env ) ( t ) -> (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.WHNF)::(Microsoft_FStar_Tc_Normalize.DeltaHard)::(Microsoft_FStar_Tc_Normalize.Beta)::[]) env t))

let norm_t = (fun ( env ) ( t ) -> (let _109_47 = (steps env)
in (Microsoft_FStar_Tc_Normalize.norm_typ _109_47 env t)))

let norm_k = (fun ( env ) ( k ) -> (let _109_52 = (steps env)
in (Microsoft_FStar_Tc_Normalize.norm_kind _109_52 env k)))

let norm_c = (fun ( env ) ( c ) -> (let _109_57 = (steps env)
in (Microsoft_FStar_Tc_Normalize.norm_comp _109_57 env c)))

let fxv_check = (fun ( head ) ( env ) ( kt ) ( fvs ) -> (let rec aux = (fun ( norm ) ( kt ) -> (match ((Support.Microsoft.FStar.Util.set_is_empty fvs)) with
| true -> begin
()
end
| false -> begin
(let fvs' = (match (kt) with
| Support.Microsoft.FStar.Util.Inl (k) -> begin
(let _109_76 = (match (norm) with
| true -> begin
(norm_k env k)
end
| false -> begin
k
end)
in (Microsoft_FStar_Absyn_Util.freevars_kind _109_76))
end
| Support.Microsoft.FStar.Util.Inr (t) -> begin
(let _109_77 = (match (norm) with
| true -> begin
(norm_t env t)
end
| false -> begin
t
end)
in (Microsoft_FStar_Absyn_Util.freevars_typ _109_77))
end)
in (let a = (Support.Microsoft.FStar.Util.set_intersect fvs fvs'.Microsoft_FStar_Absyn_Syntax.fxvs)
in (match ((Support.Microsoft.FStar.Util.set_is_empty a)) with
| true -> begin
()
end
| false -> begin
(match ((not (norm))) with
| true -> begin
(aux true kt)
end
| false -> begin
(let fail = (fun ( _38_61 ) -> (match (()) with
| () -> begin
(let escaping = (let _109_82 = (let _109_81 = (Support.Microsoft.FStar.Util.set_elements a)
in (Support.All.pipe_right _109_81 (Support.List.map (fun ( x ) -> (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)))))
in (Support.All.pipe_right _109_82 (Support.String.concat ", ")))
in (let msg = (match (((Support.Microsoft.FStar.Util.set_count a) > 1)) with
| true -> begin
(let _109_83 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env head)
in (Support.Microsoft.FStar.Util.format2 "Bound variables \'{%s}\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" escaping _109_83))
end
| false -> begin
(let _109_84 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env head)
in (Support.Microsoft.FStar.Util.format2 "Bound variable \'%s\' in the type of \'%s\' escapes because of impure applications; add explicit let-bindings" escaping _109_84))
end)
in (let _109_87 = (let _109_86 = (let _109_85 = (Microsoft_FStar_Tc_Env.get_range env)
in (msg, _109_85))
in Microsoft_FStar_Absyn_Syntax.Error (_109_86))
in (raise (_109_87)))))
end))
in (match (kt) with
| Support.Microsoft.FStar.Util.Inl (k) -> begin
(let s = (Microsoft_FStar_Tc_Util.new_kvar env)
in (match ((Microsoft_FStar_Tc_Rel.try_keq env k s)) with
| Some (g) -> begin
(Microsoft_FStar_Tc_Rel.try_discharge_guard env g)
end
| _38_71 -> begin
(fail ())
end))
end
| Support.Microsoft.FStar.Util.Inr (t) -> begin
(let s = (Microsoft_FStar_Tc_Util.new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (match ((Microsoft_FStar_Tc_Rel.try_teq env t s)) with
| Some (g) -> begin
(Microsoft_FStar_Tc_Rel.try_discharge_guard env g)
end
| _38_78 -> begin
(fail ())
end))
end))
end)
end)))
end))
in (aux false kt)))

let maybe_push_binding = (fun ( env ) ( b ) -> (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
env
end
| false -> begin
(match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let b = Microsoft_FStar_Tc_Env.Binding_typ ((a.Microsoft_FStar_Absyn_Syntax.v, a.Microsoft_FStar_Absyn_Syntax.sort))
in (Microsoft_FStar_Tc_Env.push_local_binding env b))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let b = Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))
in (Microsoft_FStar_Tc_Env.push_local_binding env b))
end)
end))

let maybe_make_subst = (fun ( _38_2 ) -> (match (_38_2) with
| Support.Microsoft.FStar.Util.Inl ((Some (a), t)) -> begin
(Support.Microsoft.FStar.Util.Inl ((a, t)))::[]
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), e)) -> begin
(Support.Microsoft.FStar.Util.Inr ((x, e)))::[]
end
| _38_99 -> begin
[]
end))

let maybe_alpha_subst = (fun ( s ) ( b1 ) ( b2 ) -> (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b1)) with
| true -> begin
s
end
| false -> begin
(match (((Support.Prims.fst b1), (Support.Prims.fst b2))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
(match ((Microsoft_FStar_Absyn_Util.bvar_eq a b)) with
| true -> begin
s
end
| false -> begin
(let _109_98 = (let _109_97 = (let _109_96 = (Microsoft_FStar_Absyn_Util.btvar_to_typ b)
in (a.Microsoft_FStar_Absyn_Syntax.v, _109_96))
in Support.Microsoft.FStar.Util.Inl (_109_97))
in (_109_98)::s)
end)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(match ((Microsoft_FStar_Absyn_Util.bvar_eq x y)) with
| true -> begin
s
end
| false -> begin
(let _109_101 = (let _109_100 = (let _109_99 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (x.Microsoft_FStar_Absyn_Syntax.v, _109_99))
in Support.Microsoft.FStar.Util.Inr (_109_100))
in (_109_101)::s)
end)
end
| _38_114 -> begin
(Support.All.failwith "impossible")
end)
end))

let maybe_extend_subst = (fun ( s ) ( b ) ( v ) -> (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
s
end
| false -> begin
(match (((Support.Prims.fst b), (Support.Prims.fst v))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (t)) -> begin
(Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::s
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (e)) -> begin
(Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, e)))::s
end
| _38_129 -> begin
(Support.All.failwith "Impossible")
end)
end))

let set_lcomp_result = (fun ( lc ) ( t ) -> (let _38_132 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _38_132.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = t; Microsoft_FStar_Absyn_Syntax.cflags = _38_132.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = (fun ( _38_134 ) -> (match (()) with
| () -> begin
(let _109_110 = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (Microsoft_FStar_Absyn_Util.set_result_typ _109_110 t))
end))}))

let value_check_expected_typ = (fun ( env ) ( e ) ( tlc ) -> (let lc = (match (tlc) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _109_117 = (match ((not ((Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t)))) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Total t)
end
| false -> begin
(Microsoft_FStar_Tc_Util.return_value env t e)
end)
in (Microsoft_FStar_Tc_Util.lcomp_of_comp _109_117))
end
| Support.Microsoft.FStar.Util.Inr (lc) -> begin
lc
end)
in (let t = lc.Microsoft_FStar_Absyn_Syntax.res_typ
in (let _38_158 = (match ((Microsoft_FStar_Tc_Env.expected_typ env)) with
| None -> begin
(e, lc, Microsoft_FStar_Tc_Rel.trivial_guard)
end
| Some (t') -> begin
(let _38_147 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _109_119 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (let _109_118 = (Microsoft_FStar_Absyn_Print.typ_to_string t')
in (Support.Microsoft.FStar.Util.fprint2 "Computed return type %s; expected type %s\n" _109_119 _109_118)))
end
| false -> begin
()
end)
in (let _38_151 = (Microsoft_FStar_Tc_Util.check_and_ascribe env e t t')
in (match (_38_151) with
| (e, g) -> begin
(let _38_154 = (let _109_125 = (Support.All.pipe_left (fun ( _109_124 ) -> Some (_109_124)) (Microsoft_FStar_Tc_Errors.subtyping_failed env t t'))
in (Microsoft_FStar_Tc_Util.strengthen_precondition _109_125 env e lc g))
in (match (_38_154) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))
end)))
end)
in (match (_38_158) with
| (e, lc, g) -> begin
(let _38_159 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _109_126 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string lc)
in (Support.Microsoft.FStar.Util.fprint1 "Return comp type is %s\n" _109_126))
end
| false -> begin
()
end)
in (e, lc, g))
end)))))

let comp_check_expected_typ = (fun ( env ) ( e ) ( lc ) -> (match ((Microsoft_FStar_Tc_Env.expected_typ env)) with
| None -> begin
(e, lc, Microsoft_FStar_Tc_Rel.trivial_guard)
end
| Some (t) -> begin
(Microsoft_FStar_Tc_Util.weaken_result_typ env e lc t)
end))

let check_expected_effect = (fun ( env ) ( copt ) ( _38_171 ) -> (match (_38_171) with
| (e, c) -> begin
(let expected_c_opt = (match (copt) with
| Some (_38_173) -> begin
copt
end
| None -> begin
(let c1 = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let md = (Microsoft_FStar_Tc_Env.get_effect_decl env c1.Microsoft_FStar_Absyn_Syntax.effect_name)
in (match ((Microsoft_FStar_Tc_Env.default_effect env md.Microsoft_FStar_Absyn_Syntax.mname)) with
| None -> begin
None
end
| Some (l) -> begin
(let flags = (match ((Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_Tot_lid)) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.TOTAL)::[]
end
| false -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals l Microsoft_FStar_Absyn_Const.effect_ML_lid)) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.MLEFFECT)::[]
end
| false -> begin
[]
end)
end)
in (let def = (Microsoft_FStar_Absyn_Syntax.mk_Comp {Microsoft_FStar_Absyn_Syntax.effect_name = l; Microsoft_FStar_Absyn_Syntax.result_typ = c1.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = []; Microsoft_FStar_Absyn_Syntax.flags = flags})
in Some (def)))
end)))
end)
in (match (expected_c_opt) with
| None -> begin
(let _109_139 = (norm_c env c)
in (e, _109_139, Microsoft_FStar_Tc_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(let _38_187 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _109_142 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _109_141 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (let _109_140 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string expected_c)
in (Support.Microsoft.FStar.Util.fprint3 "(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _109_142 _109_141 _109_140))))
end
| false -> begin
()
end)
in (let c = (norm_c env c)
in (let expected_c' = (let _109_143 = (Support.All.pipe_left Microsoft_FStar_Tc_Util.lcomp_of_comp expected_c)
in (Microsoft_FStar_Tc_Util.refresh_comp_label env true _109_143))
in (let _38_195 = (let _109_144 = (expected_c'.Microsoft_FStar_Absyn_Syntax.comp ())
in (Support.All.pipe_left (Microsoft_FStar_Tc_Util.check_comp env e c) _109_144))
in (match (_38_195) with
| (e, _38_193, g) -> begin
(let _38_196 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _109_146 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _109_145 = (Microsoft_FStar_Tc_Rel.guard_to_string env g)
in (Support.Microsoft.FStar.Util.fprint2 "(%s) DONE check_expected_effect; guard is: %s\n" _109_146 _109_145)))
end
| false -> begin
()
end)
in (e, expected_c, g))
end)))))
end))
end))

let no_logical_guard = (fun ( env ) ( _38_202 ) -> (match (_38_202) with
| (te, kt, f) -> begin
(match ((Microsoft_FStar_Tc_Rel.guard_f f)) with
| Microsoft_FStar_Tc_Rel.Trivial -> begin
(te, kt, f)
end
| Microsoft_FStar_Tc_Rel.NonTrivial (f) -> begin
(let _109_152 = (let _109_151 = (let _109_150 = (Microsoft_FStar_Tc_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _109_149 = (Microsoft_FStar_Tc_Env.get_range env)
in (_109_150, _109_149)))
in Microsoft_FStar_Absyn_Syntax.Error (_109_151))
in (raise (_109_152)))
end)
end))

let binding_of_lb = (fun ( x ) ( t ) -> (match (x) with
| Support.Microsoft.FStar.Util.Inl (bvd) -> begin
Microsoft_FStar_Tc_Env.Binding_var ((bvd, t))
end
| Support.Microsoft.FStar.Util.Inr (lid) -> begin
Microsoft_FStar_Tc_Env.Binding_lid ((lid, t))
end))

let print_expected_ty = (fun ( env ) -> (match ((Microsoft_FStar_Tc_Env.expected_typ env)) with
| None -> begin
(Support.Microsoft.FStar.Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _109_159 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint1 "Expected type is %s" _109_159))
end))

let with_implicits = (fun ( imps ) ( _38_220 ) -> (match (_38_220) with
| (e, l, g) -> begin
(e, l, (let _38_221 = g
in {Microsoft_FStar_Tc_Rel.guard_f = _38_221.Microsoft_FStar_Tc_Rel.guard_f; Microsoft_FStar_Tc_Rel.deferred = _38_221.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = (Support.List.append imps g.Microsoft_FStar_Tc_Rel.implicits)}))
end))

let add_implicit = (fun ( u ) ( g ) -> (let _38_225 = g
in {Microsoft_FStar_Tc_Rel.guard_f = _38_225.Microsoft_FStar_Tc_Rel.guard_f; Microsoft_FStar_Tc_Rel.deferred = _38_225.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = (u)::g.Microsoft_FStar_Tc_Rel.implicits}))

let rec tc_kind = (fun ( env ) ( k ) -> (let k = (Microsoft_FStar_Absyn_Util.compress_kind k)
in (let w = (fun ( f ) -> (f k.Microsoft_FStar_Absyn_Syntax.pos))
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Kind_lam (_)) | (Microsoft_FStar_Absyn_Syntax.Kind_delayed (_)) -> begin
(Support.All.failwith "impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) -> begin
(k, Microsoft_FStar_Tc_Rel.trivial_guard)
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((u, args)) -> begin
(let _38_244 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _109_210 = (Support.Microsoft.FStar.Range.string_of_range k.Microsoft_FStar_Absyn_Syntax.pos)
in (let _109_209 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (Support.Microsoft.FStar.Util.fprint2 "(%s) - Checking kind %s" _109_210 _109_209)))
end
| false -> begin
()
end)
in (let _38_249 = (Microsoft_FStar_Tc_Env.clear_expected_typ env)
in (match (_38_249) with
| (env, _38_248) -> begin
(let _38_252 = (tc_args env args)
in (match (_38_252) with
| (args, g) -> begin
(let _109_212 = (Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Kind_uvar (u, args)))
in (_109_212, g))
end))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev (((l, args), {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_unknown; Microsoft_FStar_Absyn_Syntax.tk = _38_263; Microsoft_FStar_Absyn_Syntax.pos = _38_261; Microsoft_FStar_Absyn_Syntax.fvs = _38_259; Microsoft_FStar_Absyn_Syntax.uvs = _38_257})) -> begin
(let _38_272 = (Microsoft_FStar_Tc_Env.lookup_kind_abbrev env l)
in (match (_38_272) with
| (_38_269, binders, body) -> begin
(let _38_275 = (tc_args env args)
in (match (_38_275) with
| (args, g) -> begin
(match (((Support.List.length binders) <> (Support.List.length args))) with
| true -> begin
(let _109_216 = (let _109_215 = (let _109_214 = (let _109_213 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.String.strcat "Unexpected number of arguments to kind abbreviation " _109_213))
in (_109_214, k.Microsoft_FStar_Absyn_Syntax.pos))
in Microsoft_FStar_Absyn_Syntax.Error (_109_215))
in (raise (_109_216)))
end
| false -> begin
(let _38_308 = (Support.List.fold_left2 (fun ( _38_279 ) ( b ) ( a ) -> (match (_38_279) with
| (subst, args, guards) -> begin
(match (((Support.Prims.fst b), (Support.Prims.fst a))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (t)) -> begin
(let _38_289 = (let _109_220 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (tc_typ_check env t _109_220))
in (match (_38_289) with
| (t, g) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::subst
in (let _109_222 = (let _109_221 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (_109_221)::args)
in (subst, _109_222, (g)::guards)))
end))
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (e)) -> begin
(let env = (let _109_223 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Tc_Env.set_expected_typ env _109_223))
in (let _38_301 = (tc_ghost_exp env e)
in (match (_38_301) with
| (e, _38_299, g) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, e)))::subst
in (let _109_225 = (let _109_224 = (Microsoft_FStar_Absyn_Syntax.varg e)
in (_109_224)::args)
in (subst, _109_225, (g)::guards)))
end)))
end
| _38_304 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Ill-typed argument to kind abbreviation", (Microsoft_FStar_Absyn_Util.range_of_arg a)))))
end)
end)) ([], [], []) binders args)
in (match (_38_308) with
| (subst, args, guards) -> begin
(let args = (Support.List.rev args)
in (let k = (Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown)))
in (let k' = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.DeltaHard)::[]) env k)
in (let k = (Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), k')))
in (let _109_228 = (Support.List.fold_left Microsoft_FStar_Tc_Rel.conj_guard g guards)
in (k', _109_228))))))
end))
end)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((kabr, k)) -> begin
(let _38_319 = (tc_kind env k)
in (match (_38_319) with
| (k, f) -> begin
(let _38_322 = (Support.All.pipe_left (tc_args env) (Support.Prims.snd kabr))
in (match (_38_322) with
| (args, g) -> begin
(let kabr = ((Support.Prims.fst kabr), args)
in (let kk = (Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Kind_abbrev (kabr, k)))
in (let _109_230 = (Microsoft_FStar_Tc_Rel.conj_guard f g)
in (kk, _109_230))))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _38_332 = (tc_binders env bs)
in (match (_38_332) with
| (bs, env, g) -> begin
(let _38_335 = (tc_kind env k)
in (match (_38_335) with
| (k, f) -> begin
(let f = (Microsoft_FStar_Tc_Rel.close_guard bs f)
in (let _109_233 = (Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, k)))
in (let _109_232 = (Microsoft_FStar_Tc_Rel.conj_guard g f)
in (_109_233, _109_232))))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(let _109_234 = (Microsoft_FStar_Tc_Util.new_kvar env)
in (_109_234, Microsoft_FStar_Tc_Rel.trivial_guard))
end))))
and tc_vbinder = (fun ( env ) ( x ) -> (let _38_342 = (tc_typ_check env x.Microsoft_FStar_Absyn_Syntax.sort Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_38_342) with
| (t, g) -> begin
(let x = (let _38_343 = x
in {Microsoft_FStar_Absyn_Syntax.v = _38_343.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _38_343.Microsoft_FStar_Absyn_Syntax.p})
in (let env' = (let _109_237 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (maybe_push_binding env _109_237))
in (x, env', g)))
end)))
and tc_binders = (fun ( env ) ( bs ) -> (let rec aux = (fun ( env ) ( bs ) -> (match (bs) with
| [] -> begin
([], env, Microsoft_FStar_Tc_Rel.trivial_guard)
end
| (b, imp)::bs -> begin
(match (b) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _38_362 = (tc_kind env a.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_38_362) with
| (k, g) -> begin
(let b = (Support.Microsoft.FStar.Util.Inl ((let _38_363 = a
in {Microsoft_FStar_Absyn_Syntax.v = _38_363.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _38_363.Microsoft_FStar_Absyn_Syntax.p})), imp)
in (let env' = (maybe_push_binding env b)
in (let _38_370 = (aux env' bs)
in (match (_38_370) with
| (bs, env', g') -> begin
(let _109_245 = (let _109_244 = (Microsoft_FStar_Tc_Rel.close_guard ((b)::[]) g')
in (Microsoft_FStar_Tc_Rel.conj_guard g _109_244))
in ((b)::bs, env', _109_245))
end))))
end))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _38_376 = (tc_vbinder env x)
in (match (_38_376) with
| (x, env', g) -> begin
(let b = (Support.Microsoft.FStar.Util.Inr (x), imp)
in (let _38_381 = (aux env' bs)
in (match (_38_381) with
| (bs, env', g') -> begin
(let _109_247 = (let _109_246 = (Microsoft_FStar_Tc_Rel.close_guard ((b)::[]) g')
in (Microsoft_FStar_Tc_Rel.conj_guard g _109_246))
in ((b)::bs, env', _109_247))
end)))
end))
end)
end))
in (aux env bs)))
and tc_args = (fun ( env ) ( args ) -> (Support.List.fold_right (fun ( _38_386 ) ( _38_389 ) -> (match ((_38_386, _38_389)) with
| ((arg, imp), (args, g)) -> begin
(match (arg) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _38_396 = (tc_typ env t)
in (match (_38_396) with
| (t, _38_394, g') -> begin
(let _109_252 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (((Support.Microsoft.FStar.Util.Inl (t), imp))::args, _109_252))
end))
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(let _38_403 = (tc_ghost_exp env e)
in (match (_38_403) with
| (e, _38_401, g') -> begin
(let _109_253 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (((Support.Microsoft.FStar.Util.Inr (e), imp))::args, _109_253))
end))
end)
end)) args ([], Microsoft_FStar_Tc_Rel.trivial_guard)))
and tc_comp = (fun ( env ) ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(let _38_410 = (tc_typ_check env t Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_38_410) with
| (t, g) -> begin
(let _109_256 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (_109_256, g))
end))
end
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
(let kc = (Microsoft_FStar_Tc_Env.lookup_effect_lid env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let head = (Microsoft_FStar_Absyn_Util.ftv c.Microsoft_FStar_Absyn_Syntax.effect_name kc)
in (let tc = (let _109_259 = (let _109_258 = (let _109_257 = (Microsoft_FStar_Absyn_Syntax.targ c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (_109_257)::c.Microsoft_FStar_Absyn_Syntax.effect_args)
in (head, _109_258))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _109_259 None c.Microsoft_FStar_Absyn_Syntax.result_typ.Microsoft_FStar_Absyn_Syntax.pos))
in (let _38_418 = (tc_typ_check env tc Microsoft_FStar_Absyn_Syntax.keffect)
in (match (_38_418) with
| (tc, f) -> begin
(let _38_422 = (Microsoft_FStar_Absyn_Util.head_and_args tc)
in (match (_38_422) with
| (_38_420, args) -> begin
(let _38_434 = (match (args) with
| (Support.Microsoft.FStar.Util.Inl (res), _38_427)::args -> begin
(res, args)
end
| _38_431 -> begin
(Support.All.failwith "Impossible")
end)
in (match (_38_434) with
| (res, args) -> begin
(let _38_450 = (let _109_261 = (Support.All.pipe_right c.Microsoft_FStar_Absyn_Syntax.flags (Support.List.map (fun ( _38_3 ) -> (match (_38_3) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _38_441 = (Microsoft_FStar_Tc_Env.clear_expected_typ env)
in (match (_38_441) with
| (env, _38_440) -> begin
(let _38_446 = (tc_ghost_exp env e)
in (match (_38_446) with
| (e, _38_444, g) -> begin
(Microsoft_FStar_Absyn_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, Microsoft_FStar_Tc_Rel.trivial_guard)
end))))
in (Support.All.pipe_right _109_261 Support.List.unzip))
in (match (_38_450) with
| (flags, guards) -> begin
(let _109_263 = (Microsoft_FStar_Absyn_Syntax.mk_Comp (let _38_451 = c
in {Microsoft_FStar_Absyn_Syntax.effect_name = _38_451.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = res; Microsoft_FStar_Absyn_Syntax.effect_args = args; Microsoft_FStar_Absyn_Syntax.flags = _38_451.Microsoft_FStar_Absyn_Syntax.flags}))
in (let _109_262 = (Support.List.fold_left Microsoft_FStar_Tc_Rel.conj_guard f guards)
in (_109_263, _109_262)))
end))
end))
end))
end)))))
end))
and tc_typ = (fun ( env ) ( t ) -> (let env = (Microsoft_FStar_Tc_Env.set_range env t.Microsoft_FStar_Absyn_Syntax.pos)
in (let w = (fun ( k ) -> (Microsoft_FStar_Absyn_Syntax.syn t.Microsoft_FStar_Absyn_Syntax.pos (Some (k))))
in (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (let top = t
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let k = (Microsoft_FStar_Tc_Env.lookup_btvar env a)
in (let a = (let _38_463 = a
in {Microsoft_FStar_Absyn_Syntax.v = _38_463.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _38_463.Microsoft_FStar_Absyn_Syntax.p})
in (let t = (Support.All.pipe_left (w k) (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a))
in (let _38_470 = (Microsoft_FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_38_470) with
| (t, k, implicits) -> begin
(Support.All.pipe_left (with_implicits implicits) (t, k, Microsoft_FStar_Tc_Rel.trivial_guard))
end)))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (i) when (Microsoft_FStar_Absyn_Syntax.lid_equals i.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.eqT_lid) -> begin
(let k = (Microsoft_FStar_Tc_Util.new_kvar env)
in (let qk = (Microsoft_FStar_Absyn_Util.eqT_k k)
in (let i = (let _38_475 = i
in {Microsoft_FStar_Absyn_Syntax.v = _38_475.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = qk; Microsoft_FStar_Absyn_Syntax.p = _38_475.Microsoft_FStar_Absyn_Syntax.p})
in (let _109_286 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.Microsoft_FStar_Absyn_Syntax.pos)
in (_109_286, qk, Microsoft_FStar_Tc_Rel.trivial_guard)))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (i) when ((Microsoft_FStar_Absyn_Syntax.lid_equals i.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.allTyp_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals i.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.exTyp_lid)) -> begin
(let k = (Microsoft_FStar_Tc_Util.new_kvar env)
in (let qk = (Microsoft_FStar_Absyn_Util.allT_k k)
in (let i = (let _38_482 = i
in {Microsoft_FStar_Absyn_Syntax.v = _38_482.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = qk; Microsoft_FStar_Absyn_Syntax.p = _38_482.Microsoft_FStar_Absyn_Syntax.p})
in (let _109_287 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.Microsoft_FStar_Absyn_Syntax.pos)
in (_109_287, qk, Microsoft_FStar_Tc_Rel.trivial_guard)))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (i) -> begin
(let k = (match ((Microsoft_FStar_Tc_Env.try_lookup_effect_lid env i.Microsoft_FStar_Absyn_Syntax.v)) with
| Some (k) -> begin
k
end
| _38_490 -> begin
(Microsoft_FStar_Tc_Env.lookup_typ_lid env i.Microsoft_FStar_Absyn_Syntax.v)
end)
in (let i = (let _38_492 = i
in {Microsoft_FStar_Absyn_Syntax.v = _38_492.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _38_492.Microsoft_FStar_Absyn_Syntax.p})
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_const i (Some (k)) t.Microsoft_FStar_Absyn_Syntax.pos)
in (let _38_499 = (Microsoft_FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_38_499) with
| (t, k, imps) -> begin
(Support.All.pipe_left (with_implicits imps) (t, k, Microsoft_FStar_Tc_Rel.trivial_guard))
end)))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, cod)) -> begin
(let _38_507 = (tc_binders env bs)
in (match (_38_507) with
| (bs, env, g) -> begin
(let _38_510 = (tc_comp env cod)
in (match (_38_510) with
| (cod, f) -> begin
(let t = (Support.All.pipe_left (w Microsoft_FStar_Absyn_Syntax.ktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, cod)))
in (let _38_550 = (match ((Microsoft_FStar_Absyn_Util.is_smt_lemma t)) with
| true -> begin
(match (cod.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp ({Microsoft_FStar_Absyn_Syntax.effect_name = _38_533; Microsoft_FStar_Absyn_Syntax.result_typ = _38_531; Microsoft_FStar_Absyn_Syntax.effect_args = (Support.Microsoft.FStar.Util.Inl (pre), _38_527)::(Support.Microsoft.FStar.Util.Inl (post), _38_522)::(Support.Microsoft.FStar.Util.Inr (pats), _38_517)::[]; Microsoft_FStar_Absyn_Syntax.flags = _38_513}) -> begin
(let fvs = (Microsoft_FStar_Absyn_Util.freevars_exp pats)
in (match ((Support.All.pipe_right bs (Support.Microsoft.FStar.Util.find_opt (fun ( _38_540 ) -> (match (_38_540) with
| (b, _38_539) -> begin
(match (b) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(not ((Support.Microsoft.FStar.Util.set_mem a fvs.Microsoft_FStar_Absyn_Syntax.ftvs)))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(not ((Support.Microsoft.FStar.Util.set_mem x fvs.Microsoft_FStar_Absyn_Syntax.fxvs)))
end)
end))))) with
| None -> begin
()
end
| Some (b) -> begin
(let _109_292 = (let _109_291 = (Microsoft_FStar_Absyn_Print.binder_to_string b)
in (Support.Microsoft.FStar.Util.format1 "Pattern misses at least one bound variables: %s" _109_291))
in (Microsoft_FStar_Tc_Errors.warn t.Microsoft_FStar_Absyn_Syntax.pos _109_292))
end))
end
| _38_549 -> begin
()
end)
end
| false -> begin
()
end)
in (let _109_294 = (let _109_293 = (Microsoft_FStar_Tc_Rel.close_guard bs f)
in (Microsoft_FStar_Tc_Rel.conj_guard g _109_293))
in (t, Microsoft_FStar_Absyn_Syntax.ktype, _109_294))))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, t)) -> begin
(let _38_559 = (tc_binders env bs)
in (match (_38_559) with
| (bs, env, g) -> begin
(let _38_563 = (tc_typ env t)
in (match (_38_563) with
| (t, k, f) -> begin
(let k = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, k) top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _109_299 = (Support.All.pipe_left (w k) (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, t)))
in (let _109_298 = (let _109_297 = (Microsoft_FStar_Tc_Rel.close_guard bs f)
in (Support.All.pipe_left (Microsoft_FStar_Tc_Rel.conj_guard g) _109_297))
in (_109_299, k, _109_298))))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, phi)) -> begin
(let _38_572 = (tc_vbinder env x)
in (match (_38_572) with
| (x, env, f1) -> begin
(let _38_576 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _109_302 = (Support.Microsoft.FStar.Range.string_of_range top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _109_301 = (Microsoft_FStar_Absyn_Print.typ_to_string phi)
in (let _109_300 = (match ((Microsoft_FStar_Tc_Env.expected_typ env)) with
| None -> begin
"None"
end
| Some (t) -> begin
(Microsoft_FStar_Absyn_Print.typ_to_string t)
end)
in (Support.Microsoft.FStar.Util.fprint3 "(%s) Checking refinement formula %s; env expects type %s\n" _109_302 _109_301 _109_300))))
end
| false -> begin
()
end)
in (let _38_580 = (tc_typ_check env phi Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_38_580) with
| (phi, f2) -> begin
(let _109_309 = (Support.All.pipe_left (w Microsoft_FStar_Absyn_Syntax.ktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (x, phi)))
in (let _109_308 = (let _109_307 = (let _109_306 = (let _109_305 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_109_305)::[])
in (Microsoft_FStar_Tc_Rel.close_guard _109_306 f2))
in (Microsoft_FStar_Tc_Rel.conj_guard f1 _109_307))
in (_109_309, Microsoft_FStar_Absyn_Syntax.ktype, _109_308)))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(let _38_585 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _109_312 = (Support.Microsoft.FStar.Range.string_of_range top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _109_311 = (Support.All.pipe_left Support.Microsoft.FStar.Util.string_of_int (Support.List.length args))
in (let _109_310 = (Microsoft_FStar_Absyn_Print.typ_to_string top)
in (Support.Microsoft.FStar.Util.fprint3 "(%s) Checking type application (%s): %s\n" _109_312 _109_311 _109_310))))
end
| false -> begin
()
end)
in (let _38_590 = (tc_typ (no_inst env) head)
in (match (_38_590) with
| (head, k1', f1) -> begin
(let args0 = args
in (let k1 = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.WHNF)::(Microsoft_FStar_Tc_Normalize.Beta)::[]) env k1')
in (let _38_593 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _109_316 = (Support.Microsoft.FStar.Range.string_of_range head.Microsoft_FStar_Absyn_Syntax.pos)
in (let _109_315 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (let _109_314 = (Microsoft_FStar_Absyn_Print.kind_to_string k1')
in (let _109_313 = (Microsoft_FStar_Absyn_Print.kind_to_string k1)
in (Support.Microsoft.FStar.Util.fprint4 "(%s) head %s has kind %s ... after norm %s\n" _109_316 _109_315 _109_314 _109_313)))))
end
| false -> begin
()
end)
in (let check_app = (fun ( _38_596 ) -> (match (()) with
| () -> begin
(match (k1.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_uvar (_38_598) -> begin
(let _38_602 = (tc_args env args)
in (match (_38_602) with
| (args, g) -> begin
(let fvs = (Microsoft_FStar_Absyn_Util.freevars_kind k1)
in (let binders = (Microsoft_FStar_Absyn_Util.binders_of_freevars fvs)
in (let kres = (let _109_319 = (Microsoft_FStar_Tc_Rel.new_kvar k1.Microsoft_FStar_Absyn_Syntax.pos binders)
in (Support.All.pipe_right _109_319 Support.Prims.fst))
in (let bs = (let _109_320 = (Microsoft_FStar_Tc_Util.tks_of_args args)
in (Microsoft_FStar_Absyn_Util.null_binders_of_tks _109_320))
in (let kar = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) k1.Microsoft_FStar_Absyn_Syntax.pos)
in (let _38_608 = (let _109_321 = (Microsoft_FStar_Tc_Rel.keq env None k1 kar)
in (Support.All.pipe_left (Microsoft_FStar_Tc_Util.force_trivial env) _109_321))
in (kres, args, g)))))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((formals, kres)) -> begin
(let rec check_args = (fun ( outargs ) ( subst ) ( g ) ( formals ) ( args ) -> (match ((formals, args)) with
| ([], []) -> begin
(let _109_332 = (Microsoft_FStar_Absyn_Util.subst_kind subst kres)
in (_109_332, (Support.List.rev outargs), g))
end
| (((_, None)::_, (_, Some (Microsoft_FStar_Absyn_Syntax.Implicit))::_)) | (((_, Some (Microsoft_FStar_Absyn_Syntax.Equality))::_, (_, Some (Microsoft_FStar_Absyn_Syntax.Implicit))::_)) -> begin
(let _109_336 = (let _109_335 = (let _109_334 = (let _109_333 = (Support.List.hd args)
in (Microsoft_FStar_Absyn_Util.range_of_arg _109_333))
in ("Argument is marked as instantiating an implicit parameter; although the expected parameter is explicit", _109_334))
in Microsoft_FStar_Absyn_Syntax.Error (_109_335))
in (raise (_109_336)))
end
| (((Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest, (_, None)::_)) | (((Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest, [])) -> begin
(let formal = (Support.List.hd formals)
in (let _38_681 = (let _109_337 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Tc_Util.new_implicit_tvar env _109_337))
in (match (_38_681) with
| (t, u) -> begin
(let targ = (Support.Microsoft.FStar.Util.Inl (t), Some (Microsoft_FStar_Absyn_Syntax.Implicit))
in (let g = (add_implicit (Support.Microsoft.FStar.Util.Inl (u)) g)
in (let subst = (maybe_extend_subst subst formal targ)
in (check_args ((targ)::outargs) subst g rest args))))
end)))
end
| (((Support.Microsoft.FStar.Util.Inr (x), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest, (_, None)::_)) | (((Support.Microsoft.FStar.Util.Inr (x), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest, [])) -> begin
(let formal = (Support.List.hd formals)
in (let _38_710 = (let _109_338 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Tc_Util.new_implicit_evar env _109_338))
in (match (_38_710) with
| (e, u) -> begin
(let varg = (Support.Microsoft.FStar.Util.Inr (e), Some (Microsoft_FStar_Absyn_Syntax.Implicit))
in (let g = (add_implicit (Support.Microsoft.FStar.Util.Inr (u)) g)
in (let subst = (maybe_extend_subst subst formal varg)
in (check_args ((varg)::outargs) subst g rest args))))
end)))
end
| (formal::formals, actual::actuals) -> begin
(match ((formal, actual)) with
| ((Support.Microsoft.FStar.Util.Inl (a), aqual), (Support.Microsoft.FStar.Util.Inl (t), imp)) -> begin
(let formal_k = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _38_731 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _109_340 = (Microsoft_FStar_Absyn_Print.arg_to_string actual)
in (let _109_339 = (Microsoft_FStar_Absyn_Print.kind_to_string formal_k)
in (Support.Microsoft.FStar.Util.fprint2 "Checking argument %s against expected kind %s\n" _109_340 _109_339)))
end
| false -> begin
()
end)
in (let _38_737 = (tc_typ_check (let _38_733 = env
in {Microsoft_FStar_Tc_Env.solver = _38_733.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _38_733.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _38_733.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _38_733.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _38_733.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _38_733.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _38_733.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _38_733.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _38_733.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _38_733.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _38_733.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _38_733.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _38_733.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _38_733.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _38_733.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _38_733.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = (is_eq aqual); Microsoft_FStar_Tc_Env.is_iface = _38_733.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _38_733.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _38_733.Microsoft_FStar_Tc_Env.default_effects}) t formal_k)
in (match (_38_737) with
| (t, g') -> begin
(let _38_738 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _109_341 = (Microsoft_FStar_Tc_Rel.guard_to_string env g')
in (Support.Microsoft.FStar.Util.fprint1 ">>>Got guard %s\n" _109_341))
end
| false -> begin
()
end)
in (let actual = (Support.Microsoft.FStar.Util.Inl (t), imp)
in (let g' = (let _109_343 = (let _109_342 = (Microsoft_FStar_Tc_Util.short_circuit_typ (Support.Microsoft.FStar.Util.Inl (head)) outargs)
in (Support.All.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula _109_342))
in (Microsoft_FStar_Tc_Rel.imp_guard _109_343 g'))
in (let subst = (maybe_extend_subst subst formal actual)
in (let _109_344 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _109_344 formals actuals))))))
end))))
end
| ((Support.Microsoft.FStar.Util.Inr (x), aqual), (Support.Microsoft.FStar.Util.Inr (v), imp)) -> begin
(let tx = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let env' = (Microsoft_FStar_Tc_Env.set_expected_typ env tx)
in (let env' = (let _38_754 = env'
in {Microsoft_FStar_Tc_Env.solver = _38_754.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _38_754.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _38_754.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _38_754.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _38_754.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _38_754.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _38_754.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _38_754.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _38_754.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _38_754.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _38_754.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _38_754.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _38_754.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _38_754.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _38_754.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _38_754.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = (is_eq aqual); Microsoft_FStar_Tc_Env.is_iface = _38_754.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _38_754.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _38_754.Microsoft_FStar_Tc_Env.default_effects})
in (let _38_757 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _109_346 = (Microsoft_FStar_Absyn_Print.arg_to_string actual)
in (let _109_345 = (Microsoft_FStar_Absyn_Print.typ_to_string tx)
in (Support.Microsoft.FStar.Util.fprint2 "Checking argument %s against expected type %s\n" _109_346 _109_345)))
end
| false -> begin
()
end)
in (let _38_763 = (tc_ghost_exp env' v)
in (match (_38_763) with
| (v, _38_761, g') -> begin
(let actual = (Support.Microsoft.FStar.Util.Inr (v), imp)
in (let g' = (let _109_348 = (let _109_347 = (Microsoft_FStar_Tc_Util.short_circuit_typ (Support.Microsoft.FStar.Util.Inl (head)) outargs)
in (Support.All.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula _109_347))
in (Microsoft_FStar_Tc_Rel.imp_guard _109_348 g'))
in (let subst = (maybe_extend_subst subst formal actual)
in (let _109_349 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _109_349 formals actuals)))))
end))))))
end
| ((Support.Microsoft.FStar.Util.Inl (a), _38_770), (Support.Microsoft.FStar.Util.Inr (v), imp)) -> begin
(match (a.Microsoft_FStar_Absyn_Syntax.sort.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
(let tv = (Microsoft_FStar_Absyn_Util.b2t v)
in (let _109_351 = (let _109_350 = (Microsoft_FStar_Absyn_Syntax.targ tv)
in (_109_350)::actuals)
in (check_args outargs subst g ((formal)::formals) _109_351)))
end
| _38_780 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Expected a type; got an expression", v.Microsoft_FStar_Absyn_Syntax.pos))))
end)
end
| ((Support.Microsoft.FStar.Util.Inr (_38_782), _38_785), (Support.Microsoft.FStar.Util.Inl (_38_788), _38_791)) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Expected an expression; got a type", (Microsoft_FStar_Absyn_Util.range_of_arg actual)))))
end)
end
| (_38_795, []) -> begin
(let _109_353 = (let _109_352 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (formals, kres) kres.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Util.subst_kind subst _109_352))
in (_109_353, (Support.List.rev outargs), g))
end
| ([], _38_800) -> begin
(let _109_361 = (let _109_360 = (let _109_359 = (let _109_358 = (let _109_356 = (let _109_355 = (Support.All.pipe_right outargs (Support.List.filter (fun ( _38_4 ) -> (match (_38_4) with
| (_38_804, Some (Microsoft_FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _38_809 -> begin
true
end))))
in (Support.List.length _109_355))
in (Support.All.pipe_right _109_356 Support.Microsoft.FStar.Util.string_of_int))
in (let _109_357 = (Support.All.pipe_right (Support.List.length args0) Support.Microsoft.FStar.Util.string_of_int)
in (Support.Microsoft.FStar.Util.format2 "Too many arguments to type; expected %s arguments but got %s" _109_358 _109_357)))
in (_109_359, top.Microsoft_FStar_Absyn_Syntax.pos))
in Microsoft_FStar_Absyn_Syntax.Error (_109_360))
in (raise (_109_361)))
end))
in (check_args [] [] f1 formals args))
end
| _38_811 -> begin
(let _109_364 = (let _109_363 = (let _109_362 = (Microsoft_FStar_Tc_Errors.expected_tcon_kind env top k1)
in (_109_362, top.Microsoft_FStar_Absyn_Syntax.pos))
in Microsoft_FStar_Absyn_Syntax.Error (_109_363))
in (raise (_109_364)))
end)
end))
in (match ((let _109_368 = (let _109_365 = (Microsoft_FStar_Absyn_Util.compress_typ head)
in _109_365.Microsoft_FStar_Absyn_Syntax.n)
in (let _109_367 = (let _109_366 = (Microsoft_FStar_Absyn_Util.compress_kind k1)
in _109_366.Microsoft_FStar_Absyn_Syntax.n)
in (_109_368, _109_367)))) with
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_38_813), Microsoft_FStar_Absyn_Syntax.Kind_arrow ((formals, k))) when ((Support.List.length args) = (Support.List.length formals)) -> begin
(let result_k = (let s = (Support.List.map2 Microsoft_FStar_Absyn_Util.subst_formal formals args)
in (Microsoft_FStar_Absyn_Util.subst_kind s k))
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (head, args) (Some (result_k)) top.Microsoft_FStar_Absyn_Syntax.pos)
in (t, result_k, Microsoft_FStar_Tc_Rel.trivial_guard)))
end
| _38_824 -> begin
(let _38_828 = (check_app ())
in (match (_38_828) with
| (k, args, g) -> begin
(let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (head, args) (Some (k)) top.Microsoft_FStar_Absyn_Syntax.pos)
in (t, k, g))
end))
end)))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t1, k1)) -> begin
(let _38_836 = (tc_kind env k1)
in (match (_38_836) with
| (k1, f1) -> begin
(let _38_839 = (tc_typ_check env t1 k1)
in (match (_38_839) with
| (t1, f2) -> begin
(let _109_372 = (Support.All.pipe_left (w k1) (Microsoft_FStar_Absyn_Syntax.mk_Typ_ascribed' (t1, k1)))
in (let _109_371 = (Microsoft_FStar_Tc_Rel.conj_guard f1 f2)
in (_109_372, k1, _109_371)))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((u, k1)) when env.Microsoft_FStar_Tc_Env.check_uvars -> begin
(let s = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (s.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((u, k1)) -> begin
(let _38_851 = (tc_kind env k1)
in (match (_38_851) with
| (k1, g) -> begin
(let _38_855 = (Microsoft_FStar_Tc_Rel.new_tvar s.Microsoft_FStar_Absyn_Syntax.pos [] k1)
in (match (_38_855) with
| (_38_853, u') -> begin
(let _38_856 = (Microsoft_FStar_Absyn_Util.unchecked_unify u u')
in (u', k1, g))
end))
end))
end
| _38_859 -> begin
(tc_typ env s)
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((_38_861, k1)) -> begin
(let s = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (s.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((u, k1)) -> begin
(let _38_870 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) Microsoft_FStar_Options.High)) with
| true -> begin
(let _109_374 = (Microsoft_FStar_Absyn_Print.typ_to_string s)
in (let _109_373 = (Microsoft_FStar_Absyn_Print.kind_to_string k1)
in (Support.Microsoft.FStar.Util.fprint2 "Admitting un-instantiated uvar %s at kind %s\n" _109_374 _109_373)))
end
| false -> begin
()
end)
in (let _109_377 = (Support.All.pipe_left (w k1) (Microsoft_FStar_Absyn_Syntax.mk_Typ_uvar' (u, k1)))
in (_109_377, k1, Microsoft_FStar_Tc_Rel.trivial_guard)))
end
| _38_873 -> begin
(let _38_874 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) Microsoft_FStar_Options.High)) with
| true -> begin
(let _109_379 = (Microsoft_FStar_Absyn_Print.typ_to_string s)
in (let _109_378 = (Microsoft_FStar_Absyn_Print.kind_to_string k1)
in (Support.Microsoft.FStar.Util.fprint2 "Admitting instantiated uvar %s at kind %s\n" _109_379 _109_378)))
end
| false -> begin
()
end)
in (s, k1, Microsoft_FStar_Tc_Rel.trivial_guard))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r))) -> begin
(let _38_885 = (tc_typ env t)
in (match (_38_885) with
| (t, k, f) -> begin
(let _109_380 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r))))
in (_109_380, k, f))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, r, p))) -> begin
(let _38_896 = (tc_typ env t)
in (match (_38_896) with
| (t, k, f) -> begin
(let _109_381 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, r, p))))
in (_109_381, k, f))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, l))) -> begin
(let _38_905 = (tc_typ env t)
in (match (_38_905) with
| (t, k, f) -> begin
(let _109_382 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, l))))
in (_109_382, k, f))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((qbody, pats))) -> begin
(let _38_913 = (tc_typ_check env qbody Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_38_913) with
| (quant, f) -> begin
(let _38_916 = (tc_args env pats)
in (match (_38_916) with
| (pats, g) -> begin
(let _109_385 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((quant, pats))))
in (let _109_384 = (Microsoft_FStar_Tc_Util.force_tk quant)
in (let _109_383 = (Microsoft_FStar_Tc_Rel.conj_guard f g)
in (_109_385, _109_384, _109_383))))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(let k = (Microsoft_FStar_Tc_Util.new_kvar env)
in (let t = (Microsoft_FStar_Tc_Util.new_tvar env k)
in (t, k, Microsoft_FStar_Tc_Rel.trivial_guard)))
end
| _38_921 -> begin
(let _109_387 = (let _109_386 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format1 "Unexpected type : %s\n" _109_386))
in (Support.All.failwith _109_387))
end))))))
and tc_typ_check = (fun ( env ) ( t ) ( k ) -> (let _38_928 = (tc_typ env t)
in (match (_38_928) with
| (t, k', f) -> begin
(let env = (Microsoft_FStar_Tc_Env.set_range env t.Microsoft_FStar_Absyn_Syntax.pos)
in (let f' = (match (env.Microsoft_FStar_Tc_Env.use_eq) with
| true -> begin
(Microsoft_FStar_Tc_Rel.keq env (Some (t)) k' k)
end
| false -> begin
(Microsoft_FStar_Tc_Rel.subkind env k' k)
end)
in (let f = (Microsoft_FStar_Tc_Rel.conj_guard f f')
in (t, f))))
end)))
and tc_value = (fun ( env ) ( e ) -> (let env = (Microsoft_FStar_Tc_Env.set_range env e.Microsoft_FStar_Absyn_Syntax.pos)
in (let top = e
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((_38_937, t1)) -> begin
(value_check_expected_typ env e (Support.Microsoft.FStar.Util.Inl (t1)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (Microsoft_FStar_Tc_Env.lookup_bvar env x)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar (let _38_944 = x
in {Microsoft_FStar_Absyn_Syntax.v = _38_944.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _38_944.Microsoft_FStar_Absyn_Syntax.p}) (Some (t)) e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _38_950 = (Microsoft_FStar_Tc_Util.maybe_instantiate env e t)
in (match (_38_950) with
| (e, t, implicits) -> begin
(let tc = (match ((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
Support.Microsoft.FStar.Util.Inl (t)
end
| false -> begin
(let _109_394 = (let _109_393 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (Support.All.pipe_left Microsoft_FStar_Tc_Util.lcomp_of_comp _109_393))
in Support.Microsoft.FStar.Util.Inr (_109_394))
end)
in (let _109_395 = (value_check_expected_typ env e tc)
in (Support.All.pipe_left (with_implicits implicits) _109_395)))
end))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((v, dc)) -> begin
(let t = (Microsoft_FStar_Tc_Env.lookup_lid env v.Microsoft_FStar_Absyn_Syntax.v)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar ((let _38_957 = v
in {Microsoft_FStar_Absyn_Syntax.v = _38_957.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _38_957.Microsoft_FStar_Absyn_Syntax.p}), dc) (Some (t)) e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _38_963 = (Microsoft_FStar_Tc_Util.maybe_instantiate env e t)
in (match (_38_963) with
| (e, t, implicits) -> begin
(let tc = (match ((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
Support.Microsoft.FStar.Util.Inl (t)
end
| false -> begin
(let _109_397 = (let _109_396 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (Support.All.pipe_left Microsoft_FStar_Tc_Util.lcomp_of_comp _109_396))
in Support.Microsoft.FStar.Util.Inr (_109_397))
end)
in (let is_data_ctor = (fun ( _38_5 ) -> (match (_38_5) with
| (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) | (Some (Microsoft_FStar_Absyn_Syntax.Record_ctor (_))) -> begin
true
end
| _38_973 -> begin
false
end))
in (match (((is_data_ctor dc) && (not ((Microsoft_FStar_Tc_Env.is_datacon env v.Microsoft_FStar_Absyn_Syntax.v))))) with
| true -> begin
(let _109_403 = (let _109_402 = (let _109_401 = (Support.Microsoft.FStar.Util.format1 "Expected a data constructor; got %s" v.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
in (let _109_400 = (Microsoft_FStar_Tc_Env.get_range env)
in (_109_401, _109_400)))
in Microsoft_FStar_Absyn_Syntax.Error (_109_402))
in (raise (_109_403)))
end
| false -> begin
(let _109_404 = (value_check_expected_typ env e tc)
in (Support.All.pipe_left (with_implicits implicits) _109_404))
end)))
end))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let t = (Microsoft_FStar_Tc_Recheck.typing_const e.Microsoft_FStar_Absyn_Syntax.pos c)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c (Some (t)) e.Microsoft_FStar_Absyn_Syntax.pos)
in (value_check_expected_typ env e (Support.Microsoft.FStar.Util.Inl (t)))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let fail = (fun ( msg ) ( t ) -> (let _109_409 = (let _109_408 = (let _109_407 = (Microsoft_FStar_Tc_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_109_407, top.Microsoft_FStar_Absyn_Syntax.pos))
in Microsoft_FStar_Absyn_Syntax.Error (_109_408))
in (raise (_109_409))))
in (let rec expected_function_typ = (fun ( env ) ( t0 ) -> (match (t0) with
| None -> begin
(let _38_994 = (match (env.Microsoft_FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _38_993 -> begin
(Support.All.failwith "Impossible")
end)
in (let _38_999 = (tc_binders env bs)
in (match (_38_999) with
| (bs, envbody, g) -> begin
(None, bs, [], None, envbody, g)
end)))
end
| Some (t) -> begin
(let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (let rec as_function_typ = (fun ( norm ) ( t ) -> (match ((let _109_418 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _109_418.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let _38_1028 = (match (env.Microsoft_FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _38_1027 -> begin
(Support.All.failwith "Impossible")
end)
in (let _38_1033 = (tc_binders env bs)
in (match (_38_1033) with
| (bs, envbody, g) -> begin
(let _38_1037 = (Microsoft_FStar_Tc_Env.clear_expected_typ envbody)
in (match (_38_1037) with
| (envbody, _38_1036) -> begin
(Some ((t, true)), bs, [], None, envbody, g)
end))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs', c)) -> begin
(let rec tc_binders = (fun ( _38_1047 ) ( bs_annot ) ( c ) ( bs ) -> (match (_38_1047) with
| (out, env, g, subst) -> begin
(match ((bs_annot, bs)) with
| ([], []) -> begin
(let _109_427 = (Microsoft_FStar_Absyn_Util.subst_comp subst c)
in ((Support.List.rev out), env, g, _109_427))
end
| (hdannot::tl_annot, hd::tl) -> begin
(match ((hdannot, hd)) with
| ((Support.Microsoft.FStar.Util.Inl (_38_1062), _38_1065), (Support.Microsoft.FStar.Util.Inr (_38_1068), _38_1071)) -> begin
(let env = (maybe_push_binding env hdannot)
in (tc_binders ((hdannot)::out, env, g, subst) tl_annot c bs))
end
| ((Support.Microsoft.FStar.Util.Inl (a), _38_1078), (Support.Microsoft.FStar.Util.Inl (b), imp)) -> begin
(let ka = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _38_1096 = (match (b.Microsoft_FStar_Absyn_Syntax.sort.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(ka, Microsoft_FStar_Tc_Rel.trivial_guard)
end
| _38_1088 -> begin
(let _38_1091 = (tc_kind env b.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_38_1091) with
| (k, g1) -> begin
(let g2 = (Microsoft_FStar_Tc_Rel.keq env None ka k)
in (let g = (let _109_428 = (Microsoft_FStar_Tc_Rel.conj_guard g1 g2)
in (Microsoft_FStar_Tc_Rel.conj_guard g _109_428))
in (k, g)))
end))
end)
in (match (_38_1096) with
| (k, g) -> begin
(let b = (Support.Microsoft.FStar.Util.Inl ((let _38_1097 = b
in {Microsoft_FStar_Absyn_Syntax.v = _38_1097.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _38_1097.Microsoft_FStar_Absyn_Syntax.p})), imp)
in (let env = (maybe_push_binding env b)
in (let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders ((b)::out, env, g, subst) tl_annot c tl))))
end)))
end
| ((Support.Microsoft.FStar.Util.Inr (x), _38_1105), (Support.Microsoft.FStar.Util.Inr (y), imp)) -> begin
(let tx = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _38_1127 = (match ((let _109_429 = (Microsoft_FStar_Absyn_Util.unmeta_typ y.Microsoft_FStar_Absyn_Syntax.sort)
in _109_429.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(tx, g)
end
| _38_1115 -> begin
(let _38_1116 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _109_430 = (Microsoft_FStar_Absyn_Print.binder_to_string hd)
in (Support.Microsoft.FStar.Util.fprint1 "Checking binder %s\n" _109_430))
end
| false -> begin
()
end)
in (let _38_1122 = (tc_typ env y.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_38_1122) with
| (t, _38_1120, g1) -> begin
(let g2 = (Microsoft_FStar_Tc_Rel.teq env tx t)
in (let g = (let _109_431 = (Microsoft_FStar_Tc_Rel.conj_guard g1 g2)
in (Microsoft_FStar_Tc_Rel.conj_guard g _109_431))
in (t, g)))
end)))
end)
in (match (_38_1127) with
| (t, g) -> begin
(let b = (Support.Microsoft.FStar.Util.Inr ((let _38_1128 = y
in {Microsoft_FStar_Absyn_Syntax.v = _38_1128.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _38_1128.Microsoft_FStar_Absyn_Syntax.p})), imp)
in (let env = (maybe_push_binding env b)
in (let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders ((b)::out, env, g, subst) tl_annot c tl))))
end)))
end
| _38_1134 -> begin
(let _109_434 = (let _109_433 = (Microsoft_FStar_Absyn_Print.binder_to_string hdannot)
in (let _109_432 = (Microsoft_FStar_Absyn_Print.binder_to_string hd)
in (Support.Microsoft.FStar.Util.format2 "Annotated %s; given %s" _109_433 _109_432)))
in (fail _109_434 t))
end)
end
| ([], _38_1137) -> begin
(match ((Microsoft_FStar_Absyn_Util.is_total_comp c)) with
| true -> begin
(match ((Support.All.pipe_right (Microsoft_FStar_Absyn_Util.comp_result c) (whnf env))) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs_annot, c')); Microsoft_FStar_Absyn_Syntax.tk = _38_1146; Microsoft_FStar_Absyn_Syntax.pos = _38_1144; Microsoft_FStar_Absyn_Syntax.fvs = _38_1142; Microsoft_FStar_Absyn_Syntax.uvs = _38_1140} -> begin
(tc_binders (out, env, g, subst) bs_annot c' bs)
end
| t -> begin
(let _109_436 = (let _109_435 = (Microsoft_FStar_Absyn_Print.tag_of_typ t)
in (Support.Microsoft.FStar.Util.format1 "More arguments than annotated type (%s)" _109_435))
in (fail _109_436 t))
end)
end
| false -> begin
(fail "Curried function, but not total" t)
end)
end
| (_38_1154, []) -> begin
(let c = (let _109_437 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs_annot, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) c.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Util.total_comp _109_437 c.Microsoft_FStar_Absyn_Syntax.pos))
in (let _109_438 = (Microsoft_FStar_Absyn_Util.subst_comp subst c)
in ((Support.List.rev out), env, g, _109_438)))
end)
end))
in (let mk_letrec_environment = (fun ( actuals ) ( env ) -> (match (env.Microsoft_FStar_Tc_Env.letrecs) with
| [] -> begin
(env, [])
end
| letrecs -> begin
(let _38_1163 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _109_443 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint1 "Building let-rec environment... type of this abstraction is %s\n" _109_443))
end
| false -> begin
()
end)
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let env = (let _38_1166 = env
in {Microsoft_FStar_Tc_Env.solver = _38_1166.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _38_1166.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _38_1166.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _38_1166.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _38_1166.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _38_1166.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _38_1166.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _38_1166.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _38_1166.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _38_1166.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _38_1166.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _38_1166.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _38_1166.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = []; Microsoft_FStar_Tc_Env.top_level = _38_1166.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _38_1166.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = _38_1166.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = _38_1166.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _38_1166.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _38_1166.Microsoft_FStar_Tc_Env.default_effects})
in (let filter_types_and_functions = (fun ( bs ) -> (Support.All.pipe_right bs (Support.List.collect (fun ( b ) -> (match (b) with
| (Support.Microsoft.FStar.Util.Inl (_38_1173), _38_1176) -> begin
[]
end
| (Support.Microsoft.FStar.Util.Inr (x), _38_1181) -> begin
(match ((let _109_449 = (let _109_448 = (let _109_447 = (Microsoft_FStar_Absyn_Util.unrefine x.Microsoft_FStar_Absyn_Syntax.sort)
in (whnf env _109_447))
in (Microsoft_FStar_Absyn_Util.unrefine _109_448))
in _109_449.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_38_1184) -> begin
[]
end
| _38_1187 -> begin
(let _109_450 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (_109_450)::[])
end)
end)))))
in (let precedes = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.precedes_lid Microsoft_FStar_Absyn_Syntax.kun)
in (let as_lex_list = (fun ( dec ) -> (let _38_1194 = (Microsoft_FStar_Absyn_Util.head_and_args_e dec)
in (match (_38_1194) with
| (head, _38_1193) -> begin
(match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _38_1197)) when (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.lexcons_lid) -> begin
dec
end
| _38_1201 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (let prev_dec = (let ct = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c)
in (match ((Support.All.pipe_right ct.Microsoft_FStar_Absyn_Syntax.flags (Support.List.tryFind (fun ( _38_6 ) -> (match (_38_6) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (_38_1205) -> begin
true
end
| _38_1208 -> begin
false
end))))) with
| Some (Microsoft_FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(let _38_1212 = (match (((Support.List.length bs') <> (Support.List.length actuals))) with
| true -> begin
(let _109_459 = (let _109_458 = (let _109_457 = (let _109_455 = (Support.Microsoft.FStar.Util.string_of_int (Support.List.length bs'))
in (let _109_454 = (Support.Microsoft.FStar.Util.string_of_int (Support.List.length actuals))
in (Support.Microsoft.FStar.Util.format2 "Decreases clause on a function with an unexpected number of arguments (expected %s; got %s)" _109_455 _109_454)))
in (let _109_456 = (Microsoft_FStar_Tc_Env.get_range env)
in (_109_457, _109_456)))
in Microsoft_FStar_Absyn_Syntax.Error (_109_458))
in (raise (_109_459)))
end
| false -> begin
()
end)
in (let dec = (as_lex_list dec)
in (let subst = (Support.List.map2 (fun ( b ) ( a ) -> (match ((b, a)) with
| ((Support.Microsoft.FStar.Util.Inl (formal), _38_1220), (Support.Microsoft.FStar.Util.Inl (actual), _38_1225)) -> begin
(let _109_463 = (let _109_462 = (Microsoft_FStar_Absyn_Util.btvar_to_typ actual)
in (formal.Microsoft_FStar_Absyn_Syntax.v, _109_462))
in Support.Microsoft.FStar.Util.Inl (_109_463))
end
| ((Support.Microsoft.FStar.Util.Inr (formal), _38_1231), (Support.Microsoft.FStar.Util.Inr (actual), _38_1236)) -> begin
(let _109_465 = (let _109_464 = (Microsoft_FStar_Absyn_Util.bvar_to_exp actual)
in (formal.Microsoft_FStar_Absyn_Syntax.v, _109_464))
in Support.Microsoft.FStar.Util.Inr (_109_465))
end
| _38_1240 -> begin
(Support.All.failwith "impossible")
end)) bs' actuals)
in (Microsoft_FStar_Absyn_Util.subst_exp subst dec))))
end
| _38_1243 -> begin
(let actual_args = (Support.All.pipe_right actuals filter_types_and_functions)
in (match (actual_args) with
| i::[] -> begin
i
end
| _38_1248 -> begin
(mk_lex_list actual_args)
end))
end))
in (let letrecs = (Support.All.pipe_right letrecs (Support.List.map (fun ( _38_1252 ) -> (match (_38_1252) with
| (l, t0) -> begin
(let t = (Microsoft_FStar_Absyn_Util.alpha_typ t0)
in (match ((let _109_467 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _109_467.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((formals, c)) -> begin
(match ((Support.Microsoft.FStar.Util.prefix formals)) with
| (bs, (Support.Microsoft.FStar.Util.Inr (x), imp)) -> begin
(let y = (Microsoft_FStar_Absyn_Util.gen_bvar_p x.Microsoft_FStar_Absyn_Syntax.p x.Microsoft_FStar_Absyn_Syntax.sort)
in (let ct = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c)
in (let precedes = (match ((Support.All.pipe_right ct.Microsoft_FStar_Absyn_Syntax.flags (Support.List.tryFind (fun ( _38_7 ) -> (match (_38_7) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (_38_1268) -> begin
true
end
| _38_1271 -> begin
false
end))))) with
| Some (Microsoft_FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(let dec = (as_lex_list dec)
in (let dec = (let subst = (let _109_471 = (let _109_470 = (let _109_469 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (x.Microsoft_FStar_Absyn_Syntax.v, _109_469))
in Support.Microsoft.FStar.Util.Inr (_109_470))
in (_109_471)::[])
in (Microsoft_FStar_Absyn_Util.subst_exp subst dec))
in (let _109_476 = (let _109_475 = (let _109_474 = (Microsoft_FStar_Absyn_Syntax.varg dec)
in (let _109_473 = (let _109_472 = (Microsoft_FStar_Absyn_Syntax.varg prev_dec)
in (_109_472)::[])
in (_109_474)::_109_473))
in (precedes, _109_475))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _109_476 None r))))
end
| _38_1279 -> begin
(let formal_args = (let _109_479 = (let _109_478 = (let _109_477 = (Microsoft_FStar_Absyn_Syntax.v_binder y)
in (_109_477)::[])
in (Support.List.append bs _109_478))
in (Support.All.pipe_right _109_479 filter_types_and_functions))
in (let lhs = (match (formal_args) with
| i::[] -> begin
i
end
| _38_1284 -> begin
(mk_lex_list formal_args)
end)
in (let _109_484 = (let _109_483 = (let _109_482 = (Microsoft_FStar_Absyn_Syntax.varg lhs)
in (let _109_481 = (let _109_480 = (Microsoft_FStar_Absyn_Syntax.varg prev_dec)
in (_109_480)::[])
in (_109_482)::_109_481))
in (precedes, _109_483))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _109_484 None r))))
end)
in (let refined_domain = (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (y, precedes) None r)
in (let bs = (Support.List.append bs (((Support.Microsoft.FStar.Util.Inr ((let _38_1288 = x
in {Microsoft_FStar_Absyn_Syntax.v = _38_1288.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = refined_domain; Microsoft_FStar_Absyn_Syntax.p = _38_1288.Microsoft_FStar_Absyn_Syntax.p})), imp))::[]))
in (let t' = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None r)
in (let _38_1292 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _109_487 = (Microsoft_FStar_Absyn_Print.lbname_to_string l)
in (let _109_486 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (let _109_485 = (Microsoft_FStar_Absyn_Print.typ_to_string t')
in (Support.Microsoft.FStar.Util.fprint3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _109_487 _109_486 _109_485))))
end
| false -> begin
()
end)
in (let _38_1299 = (let _109_489 = (let _109_488 = (Microsoft_FStar_Tc_Env.clear_expected_typ env)
in (Support.All.pipe_right _109_488 Support.Prims.fst))
in (tc_typ _109_489 t'))
in (match (_38_1299) with
| (t', _38_1296, _38_1298) -> begin
(l, t')
end)))))))))
end
| _38_1301 -> begin
(Support.All.failwith "Impossible")
end)
end
| _38_1303 -> begin
(Support.All.failwith "Impossible")
end))
end))))
in (let _109_495 = (Support.All.pipe_right letrecs (Support.List.fold_left (fun ( env ) ( _38_1308 ) -> (match (_38_1308) with
| (x, t) -> begin
(Microsoft_FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end)) env))
in (let _109_494 = (Support.All.pipe_right letrecs (Support.List.collect (fun ( _38_8 ) -> (match (_38_8) with
| (Support.Microsoft.FStar.Util.Inl (x), t) -> begin
(let _109_493 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_109_493)::[])
end
| _38_1315 -> begin
[]
end))))
in (_109_495, _109_494)))))))))))
end))
in (let _38_1320 = (tc_binders ([], env, Microsoft_FStar_Tc_Rel.trivial_guard, []) bs' c bs)
in (match (_38_1320) with
| (bs, envbody, g, c) -> begin
(let _38_1323 = (match ((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
(mk_letrec_environment bs envbody)
end
| false -> begin
(envbody, [])
end)
in (match (_38_1323) with
| (envbody, letrecs) -> begin
(let envbody = (Microsoft_FStar_Tc_Env.set_expected_typ envbody (Microsoft_FStar_Absyn_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, g))
end))
end))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((b, _38_1327)) -> begin
(let _38_1337 = (as_function_typ norm b.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_38_1337) with
| (_38_1331, bs, bs', copt, env, g) -> begin
(Some ((t, false)), bs, bs', copt, env, g)
end))
end
| _38_1339 -> begin
(match ((not (norm))) with
| true -> begin
(let _109_496 = (whnf env t)
in (as_function_typ true _109_496))
end
| false -> begin
(let _38_1348 = (expected_function_typ env None)
in (match (_38_1348) with
| (_38_1341, bs, _38_1344, c_opt, envbody, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, g)
end))
end)
end))
in (as_function_typ false t)))
end))
in (let use_eq = env.Microsoft_FStar_Tc_Env.use_eq
in (let _38_1352 = (Microsoft_FStar_Tc_Env.clear_expected_typ env)
in (match (_38_1352) with
| (env, topt) -> begin
(let _38_1359 = (expected_function_typ env topt)
in (match (_38_1359) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, g) -> begin
(let _38_1365 = (tc_exp (let _38_1360 = envbody
in {Microsoft_FStar_Tc_Env.solver = _38_1360.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _38_1360.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _38_1360.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _38_1360.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _38_1360.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _38_1360.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _38_1360.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _38_1360.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _38_1360.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _38_1360.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _38_1360.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _38_1360.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _38_1360.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _38_1360.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = false; Microsoft_FStar_Tc_Env.check_uvars = _38_1360.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = use_eq; Microsoft_FStar_Tc_Env.is_iface = _38_1360.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _38_1360.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _38_1360.Microsoft_FStar_Tc_Env.default_effects}) body)
in (match (_38_1365) with
| (body, cbody, guard_body) -> begin
(let _38_1366 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _109_499 = (Microsoft_FStar_Absyn_Print.exp_to_string body)
in (let _109_498 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string cbody)
in (let _109_497 = (Microsoft_FStar_Tc_Rel.guard_to_string env guard_body)
in (Support.Microsoft.FStar.Util.fprint3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _109_499 _109_498 _109_497))))
end
| false -> begin
()
end)
in (let guard_body = (Microsoft_FStar_Tc_Rel.solve_deferred_constraints envbody guard_body)
in (let _38_1369 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Implicits")))) with
| true -> begin
(let _109_500 = (Support.All.pipe_left Support.Microsoft.FStar.Util.string_of_int (Support.List.length guard_body.Microsoft_FStar_Tc_Rel.implicits))
in (Support.Microsoft.FStar.Util.fprint1 "Introduced %s implicits in body of abstraction\n" _109_500))
end
| false -> begin
()
end)
in (let _38_1376 = (let _109_502 = (let _109_501 = (cbody.Microsoft_FStar_Absyn_Syntax.comp ())
in (body, _109_501))
in (check_expected_effect (let _38_1371 = envbody
in {Microsoft_FStar_Tc_Env.solver = _38_1371.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _38_1371.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _38_1371.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _38_1371.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _38_1371.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _38_1371.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _38_1371.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _38_1371.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _38_1371.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _38_1371.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _38_1371.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _38_1371.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _38_1371.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _38_1371.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _38_1371.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _38_1371.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = use_eq; Microsoft_FStar_Tc_Env.is_iface = _38_1371.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _38_1371.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _38_1371.Microsoft_FStar_Tc_Env.default_effects}) c_opt _109_502))
in (match (_38_1376) with
| (body, cbody, guard) -> begin
(let guard = (Microsoft_FStar_Tc_Rel.conj_guard guard_body guard)
in (let guard = (match ((env.Microsoft_FStar_Tc_Env.top_level || (not ((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str))))) with
| true -> begin
(let _38_1378 = (let _109_503 = (Microsoft_FStar_Tc_Rel.conj_guard g guard)
in (Microsoft_FStar_Tc_Util.discharge_guard envbody _109_503))
in (let _38_1380 = Microsoft_FStar_Tc_Rel.trivial_guard
in {Microsoft_FStar_Tc_Rel.guard_f = _38_1380.Microsoft_FStar_Tc_Rel.guard_f; Microsoft_FStar_Tc_Rel.deferred = _38_1380.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = guard.Microsoft_FStar_Tc_Rel.implicits}))
end
| false -> begin
(let guard = (Microsoft_FStar_Tc_Rel.close_guard (Support.List.append bs letrec_binders) guard)
in (Microsoft_FStar_Tc_Rel.conj_guard g guard))
end)
in (let tfun_computed = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, cbody) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) top.Microsoft_FStar_Absyn_Syntax.pos)
in (let e = (let _109_505 = (let _109_504 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (bs, body) (Some (tfun_computed)) top.Microsoft_FStar_Absyn_Syntax.pos)
in (_109_504, tfun_computed, Some (Microsoft_FStar_Absyn_Const.effect_Tot_lid)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed _109_505 None top.Microsoft_FStar_Absyn_Syntax.pos))
in (let _38_1403 = (match (tfun_opt) with
| Some ((t, use_teq)) -> begin
(let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_38_1392) -> begin
(let _109_508 = (let _109_507 = (let _109_506 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (bs, body) (Some (t)) e.Microsoft_FStar_Absyn_Syntax.pos)
in (_109_506, t, Some (Microsoft_FStar_Absyn_Const.effect_Tot_lid)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed _109_507 None top.Microsoft_FStar_Absyn_Syntax.pos))
in (_109_508, t, guard))
end
| _38_1395 -> begin
(let _38_1398 = (match (use_teq) with
| true -> begin
(let _109_509 = (Microsoft_FStar_Tc_Rel.teq env t tfun_computed)
in (e, _109_509))
end
| false -> begin
(Microsoft_FStar_Tc_Util.check_and_ascribe env e tfun_computed t)
end)
in (match (_38_1398) with
| (e, guard') -> begin
(let _109_511 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed (e, t, Some (Microsoft_FStar_Absyn_Const.effect_Tot_lid)) None top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _109_510 = (Microsoft_FStar_Tc_Rel.conj_guard guard guard')
in (_109_511, t, _109_510)))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_38_1403) with
| (e, tfun, guard) -> begin
(let _38_1404 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _109_514 = (Microsoft_FStar_Absyn_Print.typ_to_string tfun)
in (let _109_513 = (Microsoft_FStar_Absyn_Print.tag_of_typ tfun)
in (let _109_512 = (Microsoft_FStar_Tc_Rel.guard_to_string env guard)
in (Support.Microsoft.FStar.Util.fprint3 "!!!!!!!!!!!!!!!Annotating lambda with type %s (%s)\nGuard is %s\n" _109_514 _109_513 _109_512))))
end
| false -> begin
()
end)
in (let c = (match (env.Microsoft_FStar_Tc_Env.top_level) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Total tfun)
end
| false -> begin
(Microsoft_FStar_Tc_Util.return_value env tfun e)
end)
in (let _38_1409 = (let _109_516 = (Microsoft_FStar_Tc_Util.lcomp_of_comp c)
in (Microsoft_FStar_Tc_Util.strengthen_precondition None env e _109_516 guard))
in (match (_38_1409) with
| (c, g) -> begin
(e, c, g)
end))))
end))))))
end)))))
end))
end))
end)))))
end
| _38_1411 -> begin
(let _109_518 = (let _109_517 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format1 "Unexpected value: %s" _109_517))
in (Support.All.failwith _109_518))
end))))
and tc_exp = (fun ( env ) ( e ) -> (let env = (match ((e.Microsoft_FStar_Absyn_Syntax.pos = Microsoft_FStar_Absyn_Syntax.dummyRange)) with
| true -> begin
env
end
| false -> begin
(Microsoft_FStar_Tc_Env.set_range env e.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (let _38_1415 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _109_523 = (let _109_521 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range _109_521))
in (let _109_522 = (Microsoft_FStar_Absyn_Print.tag_of_exp e)
in (Support.Microsoft.FStar.Util.fprint2 "%s (%s)\n" _109_523 _109_522)))
end
| false -> begin
()
end)
in (let w = (fun ( lc ) -> (Support.All.pipe_left (Microsoft_FStar_Absyn_Syntax.syn e.Microsoft_FStar_Absyn_Syntax.pos) (Some (lc.Microsoft_FStar_Absyn_Syntax.res_typ))))
in (let top = e
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_38_1421) -> begin
(let _109_547 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (tc_exp env _109_547))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_abs (_)) -> begin
(tc_value env e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e1, t1, _38_1441)) -> begin
(let _38_1446 = (tc_typ_check env t1 Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_38_1446) with
| (t1, f) -> begin
(let _38_1450 = (let _109_548 = (Microsoft_FStar_Tc_Env.set_expected_typ env t1)
in (tc_exp _109_548 e1))
in (match (_38_1450) with
| (e1, c, g) -> begin
(let _38_1454 = (let _109_552 = (Microsoft_FStar_Tc_Env.set_range env t1.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Tc_Util.strengthen_precondition (Some ((fun ( _38_1451 ) -> (match (()) with
| () -> begin
Microsoft_FStar_Tc_Errors.ill_kinded_type
end)))) _109_552 e1 c f))
in (match (_38_1454) with
| (c, f) -> begin
(let _38_1458 = (let _109_556 = (let _109_555 = (w c)
in (Support.All.pipe_left _109_555 (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed (e1, t1, Some (c.Microsoft_FStar_Absyn_Syntax.eff_name)))))
in (comp_check_expected_typ env _109_556 c))
in (match (_38_1458) with
| (e, c, f2) -> begin
(let _109_558 = (let _109_557 = (Microsoft_FStar_Tc_Rel.conj_guard g f2)
in (Microsoft_FStar_Tc_Rel.conj_guard f _109_557))
in (e, c, _109_558))
end))
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.Sequence))) -> begin
(match ((let _109_559 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _109_559.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_let (((_38_1465, {Microsoft_FStar_Absyn_Syntax.lbname = x; Microsoft_FStar_Absyn_Syntax.lbtyp = _38_1470; Microsoft_FStar_Absyn_Syntax.lbeff = _38_1468; Microsoft_FStar_Absyn_Syntax.lbdef = e1}::[]), e2)) -> begin
(let _38_1481 = (let _109_560 = (Microsoft_FStar_Tc_Env.set_expected_typ env Microsoft_FStar_Tc_Recheck.t_unit)
in (tc_exp _109_560 e1))
in (match (_38_1481) with
| (e1, c1, g1) -> begin
(let _38_1485 = (tc_exp env e2)
in (match (_38_1485) with
| (e2, c2, g2) -> begin
(let c = (Microsoft_FStar_Tc_Util.bind env (Some (e1)) c1 (None, c2))
in (let _109_573 = (let _109_571 = (let _109_570 = (let _109_569 = (let _109_568 = (w c)
in (let _109_567 = (let _109_566 = (let _109_565 = (let _109_564 = (let _109_563 = (Microsoft_FStar_Absyn_Syntax.mk_lb (x, c1.Microsoft_FStar_Absyn_Syntax.eff_name, Microsoft_FStar_Tc_Recheck.t_unit, e1))
in (_109_563)::[])
in (false, _109_564))
in (_109_565, e2))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_let _109_566))
in (Support.All.pipe_left _109_568 _109_567)))
in (_109_569, Microsoft_FStar_Absyn_Syntax.Sequence))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_109_570))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _109_571))
in (let _109_572 = (Microsoft_FStar_Tc_Rel.conj_guard g1 g2)
in (_109_573, c, _109_572))))
end))
end))
end
| _38_1488 -> begin
(let _38_1492 = (tc_exp env e)
in (match (_38_1492) with
| (e, c, g) -> begin
(let _109_574 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.Sequence))))
in (_109_574, c, g))
end))
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, i))) -> begin
(let _38_1501 = (tc_exp env e)
in (match (_38_1501) with
| (e, c, g) -> begin
(let _109_575 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, i))))
in (_109_575, c, g))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args)) -> begin
(let env0 = env
in (let env = (let _109_577 = (let _109_576 = (Microsoft_FStar_Tc_Env.clear_expected_typ env)
in (Support.All.pipe_right _109_576 Support.Prims.fst))
in (Support.All.pipe_right _109_577 instantiate_both))
in (let _38_1508 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _109_579 = (Support.Microsoft.FStar.Range.string_of_range top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _109_578 = (Microsoft_FStar_Absyn_Print.exp_to_string top)
in (Support.Microsoft.FStar.Util.fprint2 "(%s) Checking app %s\n" _109_579 _109_578)))
end
| false -> begin
()
end)
in (let _38_1513 = (tc_exp (no_inst env) head)
in (match (_38_1513) with
| (head, chead, g_head) -> begin
(let aux = (fun ( _38_1515 ) -> (match (()) with
| () -> begin
(let n_args = (Support.List.length args)
in (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _38_1519)) when (((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.op_And) || (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.op_Or)) && (n_args = 2)) -> begin
(let env = (Microsoft_FStar_Tc_Env.set_expected_typ env Microsoft_FStar_Absyn_Util.t_bool)
in (match (args) with
| (Support.Microsoft.FStar.Util.Inr (e1), _38_1531)::(Support.Microsoft.FStar.Util.Inr (e2), _38_1526)::[] -> begin
(let _38_1537 = (tc_exp env e1)
in (match (_38_1537) with
| (e1, c1, g1) -> begin
(let _38_1541 = (tc_exp env e2)
in (match (_38_1541) with
| (e2, c2, g2) -> begin
(let x = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Absyn_Util.t_bool)
in (let xexp = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (let c2 = (match ((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.op_And)) with
| true -> begin
(let _109_585 = (let _109_582 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Util.b2t _109_582))
in (let _109_584 = (let _109_583 = (Microsoft_FStar_Tc_Util.return_value env Microsoft_FStar_Absyn_Util.t_bool xexp)
in (Support.All.pipe_right _109_583 Microsoft_FStar_Tc_Util.lcomp_of_comp))
in (Microsoft_FStar_Tc_Util.ite env _109_585 c2 _109_584)))
end
| false -> begin
(let _109_589 = (let _109_586 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Util.b2t _109_586))
in (let _109_588 = (let _109_587 = (Microsoft_FStar_Tc_Util.return_value env Microsoft_FStar_Absyn_Util.t_bool xexp)
in (Support.All.pipe_right _109_587 Microsoft_FStar_Tc_Util.lcomp_of_comp))
in (Microsoft_FStar_Tc_Util.ite env _109_589 _109_588 c2)))
end)
in (let c = (let _109_592 = (let _109_591 = (Support.All.pipe_left (fun ( _109_590 ) -> Some (_109_590)) (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, Microsoft_FStar_Absyn_Util.t_bool))))
in (_109_591, c2))
in (Microsoft_FStar_Tc_Util.bind env None c1 _109_592))
in (let e = (let _109_597 = (let _109_596 = (let _109_595 = (Microsoft_FStar_Absyn_Syntax.varg e1)
in (let _109_594 = (let _109_593 = (Microsoft_FStar_Absyn_Syntax.varg e2)
in (_109_593)::[])
in (_109_595)::_109_594))
in (head, _109_596))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _109_597 (Some (Microsoft_FStar_Absyn_Util.t_bool)) top.Microsoft_FStar_Absyn_Syntax.pos))
in (let _109_599 = (let _109_598 = (Microsoft_FStar_Tc_Rel.conj_guard g1 g2)
in (Microsoft_FStar_Tc_Rel.conj_guard g_head _109_598))
in (e, c, _109_599)))))))
end))
end))
end
| _38_1548 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Expected two boolean arguments", head.Microsoft_FStar_Absyn_Syntax.pos))))
end))
end
| _38_1550 -> begin
(let thead = chead.Microsoft_FStar_Absyn_Syntax.res_typ
in (let _38_1552 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _109_601 = (Support.Microsoft.FStar.Range.string_of_range head.Microsoft_FStar_Absyn_Syntax.pos)
in (let _109_600 = (Microsoft_FStar_Absyn_Print.typ_to_string thead)
in (Support.Microsoft.FStar.Util.fprint2 "(%s) Type of head is %s\n" _109_601 _109_600)))
end
| false -> begin
()
end)
in (let rec check_function_app = (fun ( norm ) ( tf ) -> (match ((let _109_606 = (Microsoft_FStar_Absyn_Util.unrefine tf)
in _109_606.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let rec tc_args = (fun ( env ) ( args ) -> (match (args) with
| [] -> begin
([], [], Microsoft_FStar_Tc_Rel.trivial_guard)
end
| (Support.Microsoft.FStar.Util.Inl (t), _38_1585)::_38_1581 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Explicit type applications on a term with unknown type; add an annotation?", t.Microsoft_FStar_Absyn_Syntax.pos))))
end
| (Support.Microsoft.FStar.Util.Inr (e), imp)::tl -> begin
(let _38_1597 = (tc_exp env e)
in (match (_38_1597) with
| (e, c, g_e) -> begin
(let _38_1601 = (tc_args env tl)
in (match (_38_1601) with
| (args, comps, g_rest) -> begin
(let _109_611 = (Microsoft_FStar_Tc_Rel.conj_guard g_e g_rest)
in (((Support.Microsoft.FStar.Util.Inr (e), imp))::args, (c)::comps, _109_611))
end))
end))
end))
in (let _38_1605 = (tc_args env args)
in (match (_38_1605) with
| (args, comps, g_args) -> begin
(let bs = (let _109_612 = (Microsoft_FStar_Tc_Util.tks_of_args args)
in (Microsoft_FStar_Absyn_Util.null_binders_of_tks _109_612))
in (let cres = (let _109_613 = (Microsoft_FStar_Tc_Util.new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Util.ml_comp _109_613 top.Microsoft_FStar_Absyn_Syntax.pos))
in (let _38_1608 = (let _109_615 = (let _109_614 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, cres) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) tf.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Tc_Rel.teq env tf _109_614))
in (Support.All.pipe_left (Microsoft_FStar_Tc_Util.force_trivial env) _109_615))
in (let comp = (let _109_618 = (Support.All.pipe_left Microsoft_FStar_Tc_Util.lcomp_of_comp cres)
in (Support.List.fold_right (fun ( c ) ( out ) -> (Microsoft_FStar_Tc_Util.bind env None c (None, out))) ((chead)::comps) _109_618))
in (let _109_620 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (head, args) (Some (comp.Microsoft_FStar_Absyn_Syntax.res_typ)) top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _109_619 = (Microsoft_FStar_Tc_Rel.conj_guard g_head g_args)
in (_109_620, comp, _109_619)))))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let vars = (Microsoft_FStar_Tc_Env.binders env)
in (let rec tc_args = (fun ( _38_1625 ) ( bs ) ( cres ) ( args ) -> (match (_38_1625) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest, (_38_1639, None)::_38_1637) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _38_1645 = (fxv_check head env (Support.Microsoft.FStar.Util.Inl (k)) fvs)
in (let _38_1649 = (let _109_656 = (let _109_655 = (Support.List.hd args)
in (Microsoft_FStar_Absyn_Util.range_of_arg _109_655))
in (Microsoft_FStar_Tc_Rel.new_tvar _109_656 vars k))
in (match (_38_1649) with
| (targ, u) -> begin
(let _38_1650 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _109_658 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (let _109_657 = (Microsoft_FStar_Absyn_Print.typ_to_string targ)
in (Support.Microsoft.FStar.Util.fprint2 "Instantiating %s to %s" _109_658 _109_657)))
end
| false -> begin
()
end)
in (let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, targ)))::subst
in (let arg = (let _109_659 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inl (targ), _109_659))
in (let _109_668 = (let _109_667 = (let _109_666 = (let _109_665 = (let _109_664 = (Microsoft_FStar_Tc_Util.as_uvar_t u)
in (_109_664, u.Microsoft_FStar_Absyn_Syntax.pos))
in Support.Microsoft.FStar.Util.Inl (_109_665))
in (add_implicit _109_666 g))
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _109_667, fvs))
in (tc_args _109_668 rest cres args)))))
end))))
end
| ((Support.Microsoft.FStar.Util.Inr (x), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest, (_38_1664, None)::_38_1662) -> begin
(let t = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _38_1670 = (fxv_check head env (Support.Microsoft.FStar.Util.Inr (t)) fvs)
in (let _38_1674 = (Microsoft_FStar_Tc_Util.new_implicit_evar env t)
in (match (_38_1674) with
| (varg, u) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, varg)))::subst
in (let arg = (let _109_669 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inr (varg), _109_669))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, (add_implicit (Support.Microsoft.FStar.Util.Inr (u)) g), fvs) rest cres args)))
end))))
end
| ((Support.Microsoft.FStar.Util.Inl (a), aqual)::rest, (Support.Microsoft.FStar.Util.Inl (t), aq)::rest') -> begin
(let _38_1690 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _109_675 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (let _109_674 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint2 "\tGot a type arg for %s = %s\n" _109_675 _109_674)))
end
| false -> begin
()
end)
in (let k = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _38_1693 = (fxv_check head env (Support.Microsoft.FStar.Util.Inl (k)) fvs)
in (let _38_1699 = (tc_typ_check (let _38_1695 = env
in {Microsoft_FStar_Tc_Env.solver = _38_1695.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _38_1695.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _38_1695.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _38_1695.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _38_1695.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _38_1695.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _38_1695.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _38_1695.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _38_1695.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _38_1695.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _38_1695.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _38_1695.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _38_1695.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _38_1695.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _38_1695.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _38_1695.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = (is_eq aqual); Microsoft_FStar_Tc_Env.is_iface = _38_1695.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _38_1695.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _38_1695.Microsoft_FStar_Tc_Env.default_effects}) t k)
in (match (_38_1699) with
| (t, g') -> begin
(let f = (let _109_676 = (Microsoft_FStar_Tc_Rel.guard_f g')
in (Microsoft_FStar_Tc_Util.label_guard Microsoft_FStar_Tc_Errors.ill_kinded_type t.Microsoft_FStar_Absyn_Syntax.pos _109_676))
in (let g' = (let _38_1701 = g'
in {Microsoft_FStar_Tc_Rel.guard_f = f; Microsoft_FStar_Tc_Rel.deferred = _38_1701.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = _38_1701.Microsoft_FStar_Tc_Rel.implicits})
in (let arg = (Support.Microsoft.FStar.Util.Inl (t), aq)
in (let subst = (let _109_677 = (Support.List.hd bs)
in (maybe_extend_subst subst _109_677 arg))
in (let _109_683 = (let _109_682 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _109_682, fvs))
in (tc_args _109_683 rest cres rest'))))))
end)))))
end
| ((Support.Microsoft.FStar.Util.Inr (x), aqual)::rest, (Support.Microsoft.FStar.Util.Inr (e), aq)::rest') -> begin
(let _38_1719 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _109_685 = (Microsoft_FStar_Absyn_Print.subst_to_string subst)
in (let _109_684 = (Microsoft_FStar_Absyn_Print.typ_to_string x.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.Microsoft.FStar.Util.fprint2 "\tType of arg (before subst (%s)) = %s\n" _109_685 _109_684)))
end
| false -> begin
()
end)
in (let targ = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _38_1722 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _109_686 = (Microsoft_FStar_Absyn_Print.typ_to_string targ)
in (Support.Microsoft.FStar.Util.fprint1 "\tType of arg (after subst) = %s\n" _109_686))
end
| false -> begin
()
end)
in (let _38_1724 = (fxv_check head env (Support.Microsoft.FStar.Util.Inr (targ)) fvs)
in (let env = (Microsoft_FStar_Tc_Env.set_expected_typ env targ)
in (let env = (let _38_1727 = env
in {Microsoft_FStar_Tc_Env.solver = _38_1727.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _38_1727.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _38_1727.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _38_1727.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _38_1727.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _38_1727.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _38_1727.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _38_1727.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _38_1727.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _38_1727.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _38_1727.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _38_1727.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _38_1727.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _38_1727.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _38_1727.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _38_1727.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = (is_eq aqual); Microsoft_FStar_Tc_Env.is_iface = _38_1727.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _38_1727.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _38_1727.Microsoft_FStar_Tc_Env.default_effects})
in (let _38_1730 = (match (((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("EQ"))) && env.Microsoft_FStar_Tc_Env.use_eq)) with
| true -> begin
(let _109_688 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _109_687 = (Microsoft_FStar_Absyn_Print.typ_to_string targ)
in (Support.Microsoft.FStar.Util.fprint2 "Checking arg %s at type %s with an equality constraint!\n" _109_688 _109_687)))
end
| false -> begin
()
end)
in (let _38_1732 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _109_691 = (Microsoft_FStar_Absyn_Print.tag_of_exp e)
in (let _109_690 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _109_689 = (Microsoft_FStar_Absyn_Print.typ_to_string targ)
in (Support.Microsoft.FStar.Util.fprint3 "Checking arg (%s) %s at type %s\n" _109_691 _109_690 _109_689))))
end
| false -> begin
()
end)
in (let _38_1737 = (tc_exp env e)
in (match (_38_1737) with
| (e, c, g_e) -> begin
(let g = (Microsoft_FStar_Tc_Rel.conj_guard g g_e)
in (let _38_1739 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _109_693 = (Microsoft_FStar_Tc_Rel.guard_to_string env g_e)
in (let _109_692 = (Microsoft_FStar_Tc_Rel.guard_to_string env g)
in (Support.Microsoft.FStar.Util.fprint2 "Guard on this arg is %s;\naccumulated guard is %s\n" _109_693 _109_692)))
end
| false -> begin
()
end)
in (let arg = (Support.Microsoft.FStar.Util.Inr (e), aq)
in (match ((Microsoft_FStar_Absyn_Util.is_tot_or_gtot_lcomp c)) with
| true -> begin
(let subst = (let _109_694 = (Support.List.hd bs)
in (maybe_extend_subst subst _109_694 arg))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end
| false -> begin
(match ((Microsoft_FStar_Tc_Util.is_pure_or_ghost_effect env c.Microsoft_FStar_Absyn_Syntax.eff_name)) with
| true -> begin
(let subst = (let _109_699 = (Support.List.hd bs)
in (maybe_extend_subst subst _109_699 arg))
in (let _38_1746 = (((Some (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, targ))), c))::comps, g)
in (match (_38_1746) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end
| false -> begin
(match ((let _109_704 = (Support.List.hd bs)
in (Microsoft_FStar_Absyn_Syntax.is_null_binder _109_704))) with
| true -> begin
(let newx = (Microsoft_FStar_Absyn_Util.gen_bvar_p e.Microsoft_FStar_Absyn_Syntax.pos c.Microsoft_FStar_Absyn_Syntax.res_typ)
in (let arg' = (let _109_705 = (Microsoft_FStar_Absyn_Util.bvar_to_exp newx)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.varg _109_705))
in (let binding = Microsoft_FStar_Tc_Env.Binding_var ((newx.Microsoft_FStar_Absyn_Syntax.v, newx.Microsoft_FStar_Absyn_Syntax.sort))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (binding), c))::comps, g, fvs) rest cres rest'))))
end
| false -> begin
(let _109_718 = (let _109_717 = (let _109_711 = (let _109_710 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.varg _109_710))
in (_109_711)::arg_rets)
in (let _109_716 = (let _109_714 = (let _109_713 = (Support.All.pipe_left (fun ( _109_712 ) -> Some (_109_712)) (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, targ))))
in (_109_713, c))
in (_109_714)::comps)
in (let _109_715 = (Support.Microsoft.FStar.Util.set_add x fvs)
in (subst, (arg)::outargs, _109_717, _109_716, g, _109_715))))
in (tc_args _109_718 rest cres rest'))
end)
end)
end))))
end))))))))))
end
| ((Support.Microsoft.FStar.Util.Inr (_38_1753), _38_1756)::_38_1751, (Support.Microsoft.FStar.Util.Inl (_38_1762), _38_1765)::_38_1760) -> begin
(let _109_722 = (let _109_721 = (let _109_720 = (let _109_719 = (Support.List.hd args)
in (Microsoft_FStar_Absyn_Util.range_of_arg _109_719))
in ("Expected an expression; got a type", _109_720))
in Microsoft_FStar_Absyn_Syntax.Error (_109_721))
in (raise (_109_722)))
end
| ((Support.Microsoft.FStar.Util.Inl (_38_1772), _38_1775)::_38_1770, (Support.Microsoft.FStar.Util.Inr (_38_1781), _38_1784)::_38_1779) -> begin
(let _109_726 = (let _109_725 = (let _109_724 = (let _109_723 = (Support.List.hd args)
in (Microsoft_FStar_Absyn_Util.range_of_arg _109_723))
in ("Expected a type; got an expression", _109_724))
in Microsoft_FStar_Absyn_Syntax.Error (_109_725))
in (raise (_109_726)))
end
| (_38_1789, []) -> begin
(let _38_1792 = (fxv_check head env (Support.Microsoft.FStar.Util.Inr (cres.Microsoft_FStar_Absyn_Syntax.res_typ)) fvs)
in (let _38_1810 = (match (bs) with
| [] -> begin
(let cres = (Microsoft_FStar_Tc_Util.subst_lcomp subst cres)
in (let g = (Microsoft_FStar_Tc_Rel.conj_guard g_head g)
in (let refine_with_equality = ((Microsoft_FStar_Absyn_Util.is_pure_or_ghost_lcomp cres) && (Support.All.pipe_right comps (Support.Microsoft.FStar.Util.for_some (fun ( _38_1800 ) -> (match (_38_1800) with
| (_38_1798, c) -> begin
(not ((Microsoft_FStar_Absyn_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (let cres = (match (refine_with_equality) with
| true -> begin
(let _109_728 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app_flat (head, (Support.List.rev arg_rets)) (Some (cres.Microsoft_FStar_Absyn_Syntax.res_typ)) top.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Tc_Util.maybe_assume_result_eq_pure_term env _109_728 cres))
end
| false -> begin
(let _38_1802 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _109_731 = (Microsoft_FStar_Absyn_Print.exp_to_string head)
in (let _109_730 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string cres)
in (let _109_729 = (Microsoft_FStar_Tc_Rel.guard_to_string env g)
in (Support.Microsoft.FStar.Util.fprint3 "Not refining result: f=%s; cres=%s; guard=%s\n" _109_731 _109_730 _109_729))))
end
| false -> begin
()
end)
in cres)
end)
in (let _109_732 = (Microsoft_FStar_Tc_Util.refresh_comp_label env false cres)
in (_109_732, g))))))
end
| _38_1806 -> begin
(let g = (let _109_733 = (Microsoft_FStar_Tc_Rel.conj_guard g_head g)
in (Support.All.pipe_right _109_733 (Microsoft_FStar_Tc_Rel.solve_deferred_constraints env)))
in (let _109_739 = (let _109_738 = (let _109_737 = (let _109_736 = (let _109_735 = (let _109_734 = (cres.Microsoft_FStar_Absyn_Syntax.comp ())
in (bs, _109_734))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _109_735 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) top.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.All.pipe_left (Microsoft_FStar_Absyn_Util.subst_typ subst) _109_736))
in (Microsoft_FStar_Absyn_Syntax.mk_Total _109_737))
in (Support.All.pipe_left Microsoft_FStar_Tc_Util.lcomp_of_comp _109_738))
in (_109_739, g)))
end)
in (match (_38_1810) with
| (cres, g) -> begin
(let _38_1811 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _109_740 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string cres)
in (Support.Microsoft.FStar.Util.fprint1 "\t Type of result cres is %s\n" _109_740))
end
| false -> begin
()
end)
in (let comp = (Support.List.fold_left (fun ( out ) ( c ) -> (Microsoft_FStar_Tc_Util.bind env None (Support.Prims.snd c) ((Support.Prims.fst c), out))) cres comps)
in (let comp = (Microsoft_FStar_Tc_Util.bind env None chead (None, comp))
in (let app = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app_flat (head, (Support.List.rev outargs)) (Some (comp.Microsoft_FStar_Absyn_Syntax.res_typ)) top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _38_1820 = (Microsoft_FStar_Tc_Util.strengthen_precondition None env app comp g)
in (match (_38_1820) with
| (comp, g) -> begin
(let _38_1821 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _109_746 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env app)
in (let _109_745 = (let _109_744 = (comp.Microsoft_FStar_Absyn_Syntax.comp ())
in (Microsoft_FStar_Absyn_Print.comp_typ_to_string _109_744))
in (Support.Microsoft.FStar.Util.fprint2 "\t Type of app term %s is %s\n" _109_746 _109_745)))
end
| false -> begin
()
end)
in (app, comp, g))
end))))))
end)))
end
| ([], arg::_38_1825) -> begin
(let rec aux = (fun ( norm ) ( tres ) -> (let tres = (let _109_751 = (Microsoft_FStar_Absyn_Util.compress_typ tres)
in (Support.All.pipe_right _109_751 Microsoft_FStar_Absyn_Util.unrefine))
in (match (tres.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, cres')) -> begin
(let _38_1837 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _109_752 = (Support.Microsoft.FStar.Range.string_of_range tres.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Microsoft.FStar.Util.fprint1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _109_752))
end
| false -> begin
()
end)
in (let _109_757 = (Microsoft_FStar_Tc_Util.lcomp_of_comp cres')
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs _109_757 args)))
end
| _38_1840 when (not (norm)) -> begin
(let _109_758 = (whnf env tres)
in (aux true _109_758))
end
| _38_1842 -> begin
(let _109_764 = (let _109_763 = (let _109_762 = (let _109_760 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env tf)
in (let _109_759 = (Microsoft_FStar_Absyn_Print.exp_to_string top)
in (Support.Microsoft.FStar.Util.format2 "Too many arguments to function of type %s; got %s" _109_760 _109_759)))
in (let _109_761 = (Microsoft_FStar_Absyn_Syntax.argpos arg)
in (_109_762, _109_761)))
in Microsoft_FStar_Absyn_Syntax.Error (_109_763))
in (raise (_109_764)))
end)))
in (aux false cres.Microsoft_FStar_Absyn_Syntax.res_typ))
end)
end))
in (let _109_765 = (Microsoft_FStar_Tc_Util.lcomp_of_comp c)
in (tc_args ([], [], [], [], Microsoft_FStar_Tc_Rel.trivial_guard, Microsoft_FStar_Absyn_Syntax.no_fvs.Microsoft_FStar_Absyn_Syntax.fxvs) bs _109_765 args))))
end
| _38_1844 -> begin
(match ((not (norm))) with
| true -> begin
(let _109_766 = (whnf env tf)
in (check_function_app true _109_766))
end
| false -> begin
(let _109_769 = (let _109_768 = (let _109_767 = (Microsoft_FStar_Tc_Errors.expected_function_typ env tf)
in (_109_767, head.Microsoft_FStar_Absyn_Syntax.pos))
in Microsoft_FStar_Absyn_Syntax.Error (_109_768))
in (raise (_109_769)))
end)
end))
in (let _109_770 = (Microsoft_FStar_Absyn_Util.unrefine thead)
in (check_function_app false _109_770)))))
end))
end))
in (let _38_1848 = (aux ())
in (match (_38_1848) with
| (e, c, g) -> begin
(let _38_1849 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Implicits")))) with
| true -> begin
(let _109_771 = (Support.All.pipe_left Support.Microsoft.FStar.Util.string_of_int (Support.List.length g.Microsoft_FStar_Tc_Rel.implicits))
in (Support.Microsoft.FStar.Util.fprint1 "Introduced %s implicits in application\n" _109_771))
end
| false -> begin
()
end)
in (let c = (match ((((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str) && (not ((Microsoft_FStar_Absyn_Util.is_lcomp_partial_return c)))) && (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_lcomp c))) with
| true -> begin
(Microsoft_FStar_Tc_Util.maybe_assume_result_eq_pure_term env e c)
end
| false -> begin
c
end)
in (let _38_1856 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _109_776 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _109_775 = (Microsoft_FStar_Absyn_Print.typ_to_string c.Microsoft_FStar_Absyn_Syntax.res_typ)
in (let _109_774 = (let _109_773 = (Microsoft_FStar_Tc_Env.expected_typ env0)
in (Support.All.pipe_right _109_773 (fun ( x ) -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(Microsoft_FStar_Absyn_Print.typ_to_string t)
end))))
in (Support.Microsoft.FStar.Util.fprint3 "(%s) About to check %s against expected typ %s\n" _109_776 _109_775 _109_774))))
end
| false -> begin
()
end)
in (let _38_1861 = (comp_check_expected_typ env0 e c)
in (match (_38_1861) with
| (e, c, g') -> begin
(let _109_777 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (e, c, _109_777))
end)))))
end)))
end)))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e1, eqns)) -> begin
(let _38_1868 = (Microsoft_FStar_Tc_Env.clear_expected_typ env)
in (match (_38_1868) with
| (env1, topt) -> begin
(let env1 = (instantiate_both env1)
in (let _38_1873 = (tc_exp env1 e1)
in (match (_38_1873) with
| (e1, c1, g1) -> begin
(let _38_1880 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(let res_t = (Microsoft_FStar_Tc_Util.new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (let _109_778 = (Microsoft_FStar_Tc_Env.set_expected_typ env res_t)
in (_109_778, res_t)))
end)
in (match (_38_1880) with
| (env_branches, res_t) -> begin
(let guard_x = (let _109_780 = (Support.All.pipe_left (fun ( _109_779 ) -> Some (_109_779)) e1.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Util.new_bvd _109_780))
in (let t_eqns = (Support.All.pipe_right eqns (Support.List.map (tc_eqn guard_x c1.Microsoft_FStar_Absyn_Syntax.res_typ env_branches)))
in (let _38_1897 = (let _38_1894 = (Support.List.fold_right (fun ( _38_1888 ) ( _38_1891 ) -> (match ((_38_1888, _38_1891)) with
| ((_38_1884, f, c, g), (caccum, gaccum)) -> begin
(let _109_783 = (Microsoft_FStar_Tc_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _109_783))
end)) t_eqns ([], Microsoft_FStar_Tc_Rel.trivial_guard))
in (match (_38_1894) with
| (cases, g) -> begin
(let _109_784 = (Microsoft_FStar_Tc_Util.bind_cases env res_t cases)
in (_109_784, g))
end))
in (match (_38_1897) with
| (c_branches, g_branches) -> begin
(let _38_1898 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _109_788 = (Support.Microsoft.FStar.Range.string_of_range top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _109_787 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string c1)
in (let _109_786 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string c_branches)
in (let _109_785 = (Microsoft_FStar_Tc_Rel.guard_to_string env g_branches)
in (Support.Microsoft.FStar.Util.fprint4 "(%s) comp\n\tscrutinee: %s\n\tbranches: %s\nguard = %s\n" _109_788 _109_787 _109_786 _109_785)))))
end
| false -> begin
()
end)
in (let cres = (let _109_791 = (let _109_790 = (Support.All.pipe_left (fun ( _109_789 ) -> Some (_109_789)) (Microsoft_FStar_Tc_Env.Binding_var ((guard_x, c1.Microsoft_FStar_Absyn_Syntax.res_typ))))
in (_109_790, c_branches))
in (Microsoft_FStar_Tc_Util.bind env (Some (e1)) c1 _109_791))
in (let e = (let _109_798 = (w cres)
in (let _109_797 = (let _109_796 = (let _109_795 = (Support.List.map (fun ( _38_1908 ) -> (match (_38_1908) with
| (f, _38_1903, _38_1905, _38_1907) -> begin
f
end)) t_eqns)
in (e1, _109_795))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_match _109_796))
in (Support.All.pipe_left _109_798 _109_797)))
in (let _109_800 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed (e, cres.Microsoft_FStar_Absyn_Syntax.res_typ, Some (cres.Microsoft_FStar_Absyn_Syntax.eff_name)) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _109_799 = (Microsoft_FStar_Tc_Rel.conj_guard g1 g_branches)
in (_109_800, cres, _109_799))))))
end))))
end))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((false, {Microsoft_FStar_Absyn_Syntax.lbname = x; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _38_1913; Microsoft_FStar_Absyn_Syntax.lbdef = e1}::[]), e2)) -> begin
(let env = (instantiate_both env)
in (let env0 = env
in (let topt = (Microsoft_FStar_Tc_Env.expected_typ env)
in (let top_level = (match (x) with
| Support.Microsoft.FStar.Util.Inr (_38_1926) -> begin
true
end
| _38_1929 -> begin
false
end)
in (let _38_1934 = (Microsoft_FStar_Tc_Env.clear_expected_typ env)
in (match (_38_1934) with
| (env1, _38_1933) -> begin
(let _38_1947 = (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(Microsoft_FStar_Tc_Rel.trivial_guard, env1)
end
| _38_1937 -> begin
(match ((top_level && (not (env.Microsoft_FStar_Tc_Env.generalize)))) with
| true -> begin
(let _109_801 = (Microsoft_FStar_Tc_Env.set_expected_typ env1 t)
in (Microsoft_FStar_Tc_Rel.trivial_guard, _109_801))
end
| false -> begin
(let _38_1940 = (tc_typ_check env1 t Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_38_1940) with
| (t, f) -> begin
(let _38_1941 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _109_803 = (Support.Microsoft.FStar.Range.string_of_range top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _109_802 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint2 "(%s) Checked type annotation %s\n" _109_803 _109_802)))
end
| false -> begin
()
end)
in (let t = (norm_t env1 t)
in (let env1 = (Microsoft_FStar_Tc_Env.set_expected_typ env1 t)
in (f, env1))))
end))
end)
end)
in (match (_38_1947) with
| (f, env1) -> begin
(let _38_1953 = (tc_exp (let _38_1948 = env1
in {Microsoft_FStar_Tc_Env.solver = _38_1948.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _38_1948.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _38_1948.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _38_1948.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _38_1948.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _38_1948.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _38_1948.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _38_1948.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _38_1948.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _38_1948.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _38_1948.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _38_1948.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _38_1948.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _38_1948.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = top_level; Microsoft_FStar_Tc_Env.check_uvars = _38_1948.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = _38_1948.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = _38_1948.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _38_1948.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _38_1948.Microsoft_FStar_Tc_Env.default_effects}) e1)
in (match (_38_1953) with
| (e1, c1, g1) -> begin
(let _38_1957 = (let _109_807 = (Microsoft_FStar_Tc_Env.set_range env t.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Tc_Util.strengthen_precondition (Some ((fun ( _38_1954 ) -> (match (()) with
| () -> begin
Microsoft_FStar_Tc_Errors.ill_kinded_type
end)))) _109_807 e1 c1 f))
in (match (_38_1957) with
| (c1, guard_f) -> begin
(match (x) with
| Support.Microsoft.FStar.Util.Inr (_38_1959) -> begin
(let _38_1970 = (match ((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
(let _38_1963 = (let _109_808 = (Microsoft_FStar_Tc_Rel.conj_guard g1 guard_f)
in (Microsoft_FStar_Tc_Util.check_top_level env _109_808 c1))
in (match (_38_1963) with
| (ok, c1) -> begin
(match (ok) with
| true -> begin
(e2, c1)
end
| false -> begin
(let _38_1964 = (match ((Support.ST.read Microsoft_FStar_Options.warn_top_level_effects)) with
| true -> begin
(let _109_809 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Tc_Errors.warn _109_809 Microsoft_FStar_Tc_Errors.top_level_effect))
end
| false -> begin
()
end)
in (let _109_810 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e2, Microsoft_FStar_Absyn_Syntax.MaskedEffect))))
in (_109_810, c1)))
end)
end))
end
| false -> begin
(let _38_1966 = (let _109_811 = (Microsoft_FStar_Tc_Rel.conj_guard g1 guard_f)
in (Microsoft_FStar_Tc_Util.discharge_guard env _109_811))
in (let _109_812 = (c1.Microsoft_FStar_Absyn_Syntax.comp ())
in (e2, _109_812)))
end)
in (match (_38_1970) with
| (e2, c1) -> begin
(let _38_1975 = (match (env.Microsoft_FStar_Tc_Env.generalize) with
| true -> begin
(let _109_813 = (Microsoft_FStar_Tc_Util.generalize false env1 (((x, e1, c1))::[]))
in (Support.All.pipe_left Support.List.hd _109_813))
end
| false -> begin
(x, e1, c1)
end)
in (match (_38_1975) with
| (_38_1972, e1, c1) -> begin
(let cres = (let _109_814 = (Microsoft_FStar_Absyn_Util.ml_comp Microsoft_FStar_Tc_Recheck.t_unit top.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.All.pipe_left Microsoft_FStar_Tc_Util.lcomp_of_comp _109_814))
in (let cres = (match ((Microsoft_FStar_Absyn_Util.is_total_comp c1)) with
| true -> begin
cres
end
| false -> begin
(let _109_815 = (Microsoft_FStar_Tc_Util.lcomp_of_comp c1)
in (Microsoft_FStar_Tc_Util.bind env None _109_815 (None, cres)))
end)
in (let _38_1978 = (Support.ST.op_Colon_Equals e2.Microsoft_FStar_Absyn_Syntax.tk (Some (Microsoft_FStar_Tc_Recheck.t_unit)))
in (let _109_824 = (let _109_823 = (w cres)
in (let _109_822 = (let _109_821 = (let _109_820 = (let _109_819 = (let _109_818 = (Microsoft_FStar_Absyn_Syntax.mk_lb (x, (Microsoft_FStar_Absyn_Util.comp_effect_name c1), (Microsoft_FStar_Absyn_Util.comp_result c1), e1))
in (_109_818)::[])
in (false, _109_819))
in (_109_820, e2))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_let _109_821))
in (Support.All.pipe_left _109_823 _109_822)))
in (_109_824, cres, Microsoft_FStar_Tc_Rel.trivial_guard)))))
end))
end))
end
| Support.Microsoft.FStar.Util.Inl (bvd) -> begin
(let b = (binding_of_lb x c1.Microsoft_FStar_Absyn_Syntax.res_typ)
in (let _38_1986 = (let _109_825 = (Microsoft_FStar_Tc_Env.push_local_binding env b)
in (tc_exp _109_825 e2))
in (match (_38_1986) with
| (e2, c2, g2) -> begin
(let cres = (Microsoft_FStar_Tc_Util.bind env (Some (e1)) c1 (Some (b), c2))
in (let e = (let _109_833 = (w cres)
in (let _109_832 = (let _109_831 = (let _109_830 = (let _109_829 = (let _109_828 = (Microsoft_FStar_Absyn_Syntax.mk_lb (x, c1.Microsoft_FStar_Absyn_Syntax.eff_name, c1.Microsoft_FStar_Absyn_Syntax.res_typ, e1))
in (_109_828)::[])
in (false, _109_829))
in (_109_830, e2))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_let _109_831))
in (Support.All.pipe_left _109_833 _109_832)))
in (let g2 = (let _109_842 = (let _109_835 = (let _109_834 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s bvd c1.Microsoft_FStar_Absyn_Syntax.res_typ))
in (_109_834)::[])
in (Microsoft_FStar_Tc_Rel.close_guard _109_835))
in (let _109_841 = (let _109_840 = (let _109_839 = (let _109_838 = (let _109_837 = (Microsoft_FStar_Absyn_Util.bvd_to_exp bvd c1.Microsoft_FStar_Absyn_Syntax.res_typ)
in (Microsoft_FStar_Absyn_Util.mk_eq c1.Microsoft_FStar_Absyn_Syntax.res_typ c1.Microsoft_FStar_Absyn_Syntax.res_typ _109_837 e1))
in (Support.All.pipe_left (fun ( _109_836 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_109_836)) _109_838))
in (Microsoft_FStar_Tc_Rel.guard_of_guard_formula _109_839))
in (Microsoft_FStar_Tc_Rel.imp_guard _109_840 g2))
in (Support.All.pipe_left _109_842 _109_841)))
in (let guard = (let _109_843 = (Microsoft_FStar_Tc_Rel.conj_guard g1 g2)
in (Microsoft_FStar_Tc_Rel.conj_guard guard_f _109_843))
in (match (topt) with
| None -> begin
(let tres = cres.Microsoft_FStar_Absyn_Syntax.res_typ
in (let fvs = (Microsoft_FStar_Absyn_Util.freevars_typ tres)
in (match ((Support.Microsoft.FStar.Util.set_mem (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s bvd t) fvs.Microsoft_FStar_Absyn_Syntax.fxvs)) with
| true -> begin
(let t = (Microsoft_FStar_Tc_Util.new_tvar env0 Microsoft_FStar_Absyn_Syntax.ktype)
in (let _38_1995 = (let _109_844 = (Microsoft_FStar_Tc_Rel.teq env tres t)
in (Support.All.pipe_left (Microsoft_FStar_Tc_Rel.try_discharge_guard env) _109_844))
in (e, cres, guard)))
end
| false -> begin
(e, cres, guard)
end)))
end
| _38_1998 -> begin
(e, cres, guard)
end)))))
end)))
end)
end))
end))
end))
end))))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((false, _38_2001), _38_2004)) -> begin
(Support.All.failwith "impossible")
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((true, lbs), e1)) -> begin
(let env = (instantiate_both env)
in (let _38_2016 = (Microsoft_FStar_Tc_Env.clear_expected_typ env)
in (match (_38_2016) with
| (env0, topt) -> begin
(let is_inner_let = (Support.All.pipe_right lbs (Support.Microsoft.FStar.Util.for_some (fun ( _38_9 ) -> (match (_38_9) with
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inl (_38_2025); Microsoft_FStar_Absyn_Syntax.lbtyp = _38_2023; Microsoft_FStar_Absyn_Syntax.lbeff = _38_2021; Microsoft_FStar_Absyn_Syntax.lbdef = _38_2019} -> begin
true
end
| _38_2029 -> begin
false
end))))
in (let _38_2056 = (Support.All.pipe_right lbs (Support.List.fold_left (fun ( _38_2033 ) ( _38_2039 ) -> (match ((_38_2033, _38_2039)) with
| ((xts, env), {Microsoft_FStar_Absyn_Syntax.lbname = x; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _38_2036; Microsoft_FStar_Absyn_Syntax.lbdef = e}) -> begin
(let _38_2044 = (Microsoft_FStar_Tc_Util.extract_lb_annotation env t e)
in (match (_38_2044) with
| (_38_2041, t, check_t) -> begin
(let e = (Microsoft_FStar_Absyn_Util.unascribe e)
in (let t = (match ((not (check_t))) with
| true -> begin
t
end
| false -> begin
(match (((not (is_inner_let)) && (not (env.Microsoft_FStar_Tc_Env.generalize)))) with
| true -> begin
(let _38_2046 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) Microsoft_FStar_Options.High)) with
| true -> begin
(let _109_848 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint1 "Type %s is marked as no-generalize\n" _109_848))
end
| false -> begin
()
end)
in t)
end
| false -> begin
(let _109_849 = (tc_typ_check_trivial (let _38_2048 = env0
in {Microsoft_FStar_Tc_Env.solver = _38_2048.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _38_2048.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _38_2048.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _38_2048.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _38_2048.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _38_2048.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _38_2048.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _38_2048.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _38_2048.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _38_2048.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _38_2048.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _38_2048.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _38_2048.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _38_2048.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _38_2048.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = true; Microsoft_FStar_Tc_Env.use_eq = _38_2048.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = _38_2048.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _38_2048.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _38_2048.Microsoft_FStar_Tc_Env.default_effects}) t Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.All.pipe_right _109_849 (norm_t env)))
end)
end)
in (let env = (match (((Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t) && (Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str))) with
| true -> begin
(let _38_2051 = env
in {Microsoft_FStar_Tc_Env.solver = _38_2051.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _38_2051.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _38_2051.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _38_2051.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _38_2051.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _38_2051.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _38_2051.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _38_2051.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _38_2051.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _38_2051.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _38_2051.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _38_2051.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _38_2051.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = ((x, t))::env.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _38_2051.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _38_2051.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = _38_2051.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = _38_2051.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _38_2051.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _38_2051.Microsoft_FStar_Tc_Env.default_effects})
end
| false -> begin
(Microsoft_FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end)
in (((x, t, e))::xts, env))))
end))
end)) ([], env)))
in (match (_38_2056) with
| (lbs, env') -> begin
(let _38_2071 = (let _109_855 = (let _109_854 = (Support.All.pipe_right lbs Support.List.rev)
in (Support.All.pipe_right _109_854 (Support.List.map (fun ( _38_2060 ) -> (match (_38_2060) with
| (x, t, e) -> begin
(let t = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env t)
in (let _38_2062 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _109_853 = (Microsoft_FStar_Absyn_Print.lbname_to_string x)
in (let _109_852 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _109_851 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint3 "Checking %s = %s against type %s\n" _109_853 _109_852 _109_851))))
end
| false -> begin
()
end)
in (let env' = (Microsoft_FStar_Tc_Env.set_expected_typ env' t)
in (let _38_2068 = (tc_total_exp env' e)
in (match (_38_2068) with
| (e, t, g) -> begin
((x, t, e), g)
end)))))
end)))))
in (Support.All.pipe_right _109_855 Support.List.unzip))
in (match (_38_2071) with
| (lbs, gs) -> begin
(let g_lbs = (Support.List.fold_right Microsoft_FStar_Tc_Rel.conj_guard gs Microsoft_FStar_Tc_Rel.trivial_guard)
in (let _38_2090 = (match (((not (env.Microsoft_FStar_Tc_Env.generalize)) || is_inner_let)) with
| true -> begin
(let _109_857 = (Support.List.map (fun ( _38_2076 ) -> (match (_38_2076) with
| (x, t, e) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_lb (x, Microsoft_FStar_Absyn_Const.effect_Tot_lid, t, e))
end)) lbs)
in (_109_857, g_lbs))
end
| false -> begin
(let _38_2077 = (Microsoft_FStar_Tc_Util.discharge_guard env g_lbs)
in (let ecs = (let _109_861 = (Support.All.pipe_right lbs (Support.List.map (fun ( _38_2082 ) -> (match (_38_2082) with
| (x, t, e) -> begin
(let _109_860 = (let _109_859 = (Microsoft_FStar_Absyn_Util.range_of_lb (x, t, e))
in (Support.All.pipe_left (Microsoft_FStar_Absyn_Util.total_comp t) _109_859))
in (x, e, _109_860))
end))))
in (Microsoft_FStar_Tc_Util.generalize true env _109_861))
in (let _109_863 = (Support.List.map (fun ( _38_2087 ) -> (match (_38_2087) with
| (x, e, c) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_lb (x, Microsoft_FStar_Absyn_Const.effect_Tot_lid, (Microsoft_FStar_Absyn_Util.comp_result c), e))
end)) ecs)
in (_109_863, Microsoft_FStar_Tc_Rel.trivial_guard))))
end)
in (match (_38_2090) with
| (lbs, g_lbs) -> begin
(match ((not (is_inner_let))) with
| true -> begin
(let cres = (let _109_864 = (Microsoft_FStar_Absyn_Util.total_comp Microsoft_FStar_Tc_Recheck.t_unit top.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.All.pipe_left Microsoft_FStar_Tc_Util.lcomp_of_comp _109_864))
in (let _38_2092 = (Microsoft_FStar_Tc_Util.discharge_guard env g_lbs)
in (let _38_2094 = (Support.ST.op_Colon_Equals e1.Microsoft_FStar_Absyn_Syntax.tk (Some (Microsoft_FStar_Tc_Recheck.t_unit)))
in (let _109_868 = (let _109_867 = (w cres)
in (Support.All.pipe_left _109_867 (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((true, lbs), e1))))
in (_109_868, cres, Microsoft_FStar_Tc_Rel.trivial_guard)))))
end
| false -> begin
(let _38_2110 = (Support.All.pipe_right lbs (Support.List.fold_left (fun ( _38_2098 ) ( _38_2105 ) -> (match ((_38_2098, _38_2105)) with
| ((bindings, env), {Microsoft_FStar_Absyn_Syntax.lbname = x; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _38_2102; Microsoft_FStar_Absyn_Syntax.lbdef = _38_2100}) -> begin
(let b = (binding_of_lb x t)
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env b)
in ((b)::bindings, env)))
end)) ([], env)))
in (match (_38_2110) with
| (bindings, env) -> begin
(let _38_2114 = (tc_exp env e1)
in (match (_38_2114) with
| (e1, cres, g1) -> begin
(let guard = (Microsoft_FStar_Tc_Rel.conj_guard g_lbs g1)
in (let cres = (Microsoft_FStar_Tc_Util.close_comp env bindings cres)
in (let tres = (norm_t env cres.Microsoft_FStar_Absyn_Syntax.res_typ)
in (let cres = (let _38_2118 = cres
in {Microsoft_FStar_Absyn_Syntax.eff_name = _38_2118.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = tres; Microsoft_FStar_Absyn_Syntax.cflags = _38_2118.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = _38_2118.Microsoft_FStar_Absyn_Syntax.comp})
in (let e = (let _109_873 = (w cres)
in (Support.All.pipe_left _109_873 (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((true, lbs), e1))))
in (match (topt) with
| Some (_38_2123) -> begin
(e, cres, guard)
end
| None -> begin
(let fvs = (Support.All.pipe_left Microsoft_FStar_Absyn_Util.freevars_typ tres)
in (match ((Support.All.pipe_right lbs (Support.List.tryFind (fun ( _38_10 ) -> (match (_38_10) with
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (_38_2135); Microsoft_FStar_Absyn_Syntax.lbtyp = _38_2133; Microsoft_FStar_Absyn_Syntax.lbeff = _38_2131; Microsoft_FStar_Absyn_Syntax.lbdef = _38_2129} -> begin
false
end
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inl (x); Microsoft_FStar_Absyn_Syntax.lbtyp = _38_2143; Microsoft_FStar_Absyn_Syntax.lbeff = _38_2141; Microsoft_FStar_Absyn_Syntax.lbdef = _38_2139} -> begin
(Support.Microsoft.FStar.Util.set_mem (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x Microsoft_FStar_Absyn_Syntax.tun) fvs.Microsoft_FStar_Absyn_Syntax.fxvs)
end))))) with
| Some ({Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inl (y); Microsoft_FStar_Absyn_Syntax.lbtyp = _38_2152; Microsoft_FStar_Absyn_Syntax.lbeff = _38_2150; Microsoft_FStar_Absyn_Syntax.lbdef = _38_2148}) -> begin
(let t' = (Microsoft_FStar_Tc_Util.new_tvar env0 Microsoft_FStar_Absyn_Syntax.ktype)
in (let _38_2158 = (let _109_875 = (Microsoft_FStar_Tc_Rel.teq env tres t')
in (Support.All.pipe_left (Microsoft_FStar_Tc_Rel.try_discharge_guard env) _109_875))
in (e, cres, guard)))
end
| _38_2161 -> begin
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
and tc_eqn = (fun ( scrutinee_x ) ( pat_t ) ( env ) ( _38_2168 ) -> (match (_38_2168) with
| (pattern, when_clause, branch) -> begin
(let tc_pat = (fun ( allow_implicits ) ( pat_t ) ( p0 ) -> (let _38_2176 = (Microsoft_FStar_Tc_Util.pat_as_exps allow_implicits env p0)
in (match (_38_2176) with
| (bindings, exps, p) -> begin
(let pat_env = (Support.List.fold_left Microsoft_FStar_Tc_Env.push_local_binding env bindings)
in (let _38_2185 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Pat")))) with
| true -> begin
(Support.All.pipe_right bindings (Support.List.iter (fun ( _38_11 ) -> (match (_38_11) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, t)) -> begin
(let _109_888 = (Microsoft_FStar_Absyn_Print.strBvd x)
in (let _109_887 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (Support.Microsoft.FStar.Util.fprint2 "Before tc ... pattern var %s  : %s\n" _109_888 _109_887)))
end
| _38_2184 -> begin
()
end))))
end
| false -> begin
()
end)
in (let _38_2190 = (Microsoft_FStar_Tc_Env.clear_expected_typ pat_env)
in (match (_38_2190) with
| (env1, _38_2189) -> begin
(let env1 = (let _38_2191 = env1
in {Microsoft_FStar_Tc_Env.solver = _38_2191.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _38_2191.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _38_2191.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _38_2191.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _38_2191.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _38_2191.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _38_2191.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _38_2191.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = true; Microsoft_FStar_Tc_Env.instantiate_targs = _38_2191.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _38_2191.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _38_2191.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _38_2191.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _38_2191.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _38_2191.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _38_2191.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = _38_2191.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = _38_2191.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _38_2191.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _38_2191.Microsoft_FStar_Tc_Env.default_effects})
in (let expected_pat_t = (Microsoft_FStar_Tc_Rel.unrefine env pat_t)
in (let exps = (Support.All.pipe_right exps (Support.List.map (fun ( e ) -> (let _38_2196 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _109_891 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _109_890 = (Microsoft_FStar_Absyn_Print.typ_to_string pat_t)
in (Support.Microsoft.FStar.Util.fprint2 "Checking pattern expression %s against expected type %s\n" _109_891 _109_890)))
end
| false -> begin
()
end)
in (let _38_2201 = (tc_exp env1 e)
in (match (_38_2201) with
| (e, lc, g) -> begin
(let _38_2202 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _109_893 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env e)
in (let _109_892 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env lc.Microsoft_FStar_Absyn_Syntax.res_typ)
in (Support.Microsoft.FStar.Util.fprint2 "Pre-checked pattern expression %s at type %s\n" _109_893 _109_892)))
end
| false -> begin
()
end)
in (let g' = (Microsoft_FStar_Tc_Rel.teq env lc.Microsoft_FStar_Absyn_Syntax.res_typ expected_pat_t)
in (let g = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (let _38_2206 = (let _109_894 = (Microsoft_FStar_Tc_Rel.solve_deferred_constraints env g)
in (Support.All.pipe_left Support.Prims.ignore _109_894))
in (let e' = (Microsoft_FStar_Tc_Normalize.norm_exp ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env e)
in (let _38_2209 = (match ((let _109_897 = (let _109_896 = (Microsoft_FStar_Absyn_Util.uvars_in_exp e')
in (let _109_895 = (Microsoft_FStar_Absyn_Util.uvars_in_typ expected_pat_t)
in (Microsoft_FStar_Absyn_Util.uvars_included_in _109_896 _109_895)))
in (Support.All.pipe_left Support.Prims.op_Negation _109_897))) with
| true -> begin
(let _109_902 = (let _109_901 = (let _109_900 = (let _109_899 = (Microsoft_FStar_Absyn_Print.exp_to_string e')
in (let _109_898 = (Microsoft_FStar_Absyn_Print.typ_to_string expected_pat_t)
in (Support.Microsoft.FStar.Util.format2 "Implicit pattern variables in %s could not be resolved against expected type %s; please bind them explicitly" _109_899 _109_898)))
in (_109_900, p.Microsoft_FStar_Absyn_Syntax.p))
in Microsoft_FStar_Absyn_Syntax.Error (_109_901))
in (raise (_109_902)))
end
| false -> begin
()
end)
in (let _38_2211 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _109_903 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env e)
in (Support.Microsoft.FStar.Util.fprint1 "Done checking pattern expression %s\n" _109_903))
end
| false -> begin
()
end)
in e)))))))
end))))))
in (let p = (Microsoft_FStar_Tc_Util.decorate_pattern env p exps)
in (let _38_2222 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Pat")))) with
| true -> begin
(Support.All.pipe_right bindings (Support.List.iter (fun ( _38_12 ) -> (match (_38_12) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, t)) -> begin
(let _109_906 = (Microsoft_FStar_Absyn_Print.strBvd x)
in (let _109_905 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint2 "Pattern var %s  : %s\n" _109_906 _109_905)))
end
| _38_2221 -> begin
()
end))))
end
| false -> begin
()
end)
in (p, bindings, pat_env, exps, Microsoft_FStar_Tc_Rel.trivial_guard))))))
end))))
end)))
in (let _38_2229 = (tc_pat true pat_t pattern)
in (match (_38_2229) with
| (pattern, bindings, pat_env, disj_exps, g_pat) -> begin
(let _38_2239 = (match (when_clause) with
| None -> begin
(None, Microsoft_FStar_Tc_Rel.trivial_guard)
end
| Some (e) -> begin
(match ((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("When clauses are not yet supported in --verify mode; they soon will be", e.Microsoft_FStar_Absyn_Syntax.pos))))
end
| false -> begin
(let _38_2236 = (let _109_907 = (Microsoft_FStar_Tc_Env.set_expected_typ pat_env Microsoft_FStar_Tc_Recheck.t_bool)
in (tc_exp _109_907 e))
in (match (_38_2236) with
| (e, c, g) -> begin
(Some (e), g)
end))
end)
end)
in (match (_38_2239) with
| (when_clause, g_when) -> begin
(let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _109_909 = (Microsoft_FStar_Absyn_Util.mk_eq Microsoft_FStar_Absyn_Util.t_bool Microsoft_FStar_Absyn_Util.t_bool w Microsoft_FStar_Absyn_Const.exp_true_bool)
in (Support.All.pipe_left (fun ( _109_908 ) -> Some (_109_908)) _109_909))
end)
in (let _38_2247 = (tc_exp pat_env branch)
in (match (_38_2247) with
| (branch, c, g_branch) -> begin
(let scrutinee = (Microsoft_FStar_Absyn_Util.bvd_to_exp scrutinee_x pat_t)
in (let _38_2252 = (let _109_910 = (Microsoft_FStar_Tc_Env.push_local_binding env (Microsoft_FStar_Tc_Env.Binding_var ((scrutinee_x, pat_t))))
in (Support.All.pipe_right _109_910 Microsoft_FStar_Tc_Env.clear_expected_typ))
in (match (_38_2252) with
| (scrutinee_env, _38_2251) -> begin
(let c = (let eqs = (Support.All.pipe_right disj_exps (Support.List.fold_left (fun ( fopt ) ( e ) -> (let e = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
fopt
end
| _38_2266 -> begin
(let clause = (let _109_914 = (Microsoft_FStar_Tc_Recheck.recompute_typ scrutinee)
in (let _109_913 = (Microsoft_FStar_Tc_Recheck.recompute_typ e)
in (Microsoft_FStar_Absyn_Util.mk_eq _109_914 _109_913 scrutinee e)))
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _109_916 = (Microsoft_FStar_Absyn_Util.mk_disj clause f)
in (Support.All.pipe_left (fun ( _109_915 ) -> Some (_109_915)) _109_916))
end))
end))) None))
in (let c = (match ((eqs, when_condition)) with
| (None, None) -> begin
c
end
| (Some (f), None) -> begin
(Microsoft_FStar_Tc_Util.weaken_precondition env c (Microsoft_FStar_Tc_Rel.NonTrivial (f)))
end
| (Some (f), Some (w)) -> begin
(let _109_919 = (let _109_918 = (Microsoft_FStar_Absyn_Util.mk_conj f w)
in (Support.All.pipe_left (fun ( _109_917 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_109_917)) _109_918))
in (Microsoft_FStar_Tc_Util.weaken_precondition env c _109_919))
end
| (None, Some (w)) -> begin
(Microsoft_FStar_Tc_Util.weaken_precondition env c (Microsoft_FStar_Tc_Rel.NonTrivial (w)))
end)
in (Microsoft_FStar_Tc_Util.close_comp env bindings c)))
in (let discriminate = (fun ( scrutinee ) ( f ) -> (let disc = (let _109_926 = (let _109_924 = (Microsoft_FStar_Absyn_Util.mk_discriminator f.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Util.fvar None _109_924))
in (let _109_925 = (Microsoft_FStar_Absyn_Syntax.range_of_lid f.Microsoft_FStar_Absyn_Syntax.v)
in (Support.All.pipe_left _109_926 _109_925)))
in (let disc = (let _109_929 = (let _109_928 = (let _109_927 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.varg scrutinee)
in (_109_927)::[])
in (disc, _109_928))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _109_929 None scrutinee.Microsoft_FStar_Absyn_Syntax.pos))
in (Microsoft_FStar_Absyn_Util.mk_eq Microsoft_FStar_Absyn_Util.t_bool Microsoft_FStar_Absyn_Util.t_bool disc Microsoft_FStar_Absyn_Const.exp_true_bool))))
in (let rec mk_guard = (fun ( scrutinee ) ( pat_exp ) -> (let pat_exp = (Microsoft_FStar_Absyn_Util.compress_exp pat_exp)
in (match (pat_exp.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) | (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_constant (Microsoft_FStar_Absyn_Syntax.Const_unit)) -> begin
(Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (_38_2324) -> begin
(let _109_938 = (let _109_937 = (let _109_936 = (Microsoft_FStar_Absyn_Syntax.varg scrutinee)
in (let _109_935 = (let _109_934 = (Microsoft_FStar_Absyn_Syntax.varg pat_exp)
in (_109_934)::[])
in (_109_936)::_109_935))
in (Microsoft_FStar_Absyn_Util.teq, _109_937))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _109_938 None scrutinee.Microsoft_FStar_Absyn_Syntax.pos))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((f, _38_2328)) -> begin
(discriminate scrutinee f)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((f, _38_2341)); Microsoft_FStar_Absyn_Syntax.tk = _38_2338; Microsoft_FStar_Absyn_Syntax.pos = _38_2336; Microsoft_FStar_Absyn_Syntax.fvs = _38_2334; Microsoft_FStar_Absyn_Syntax.uvs = _38_2332}, args)) -> begin
(let head = (discriminate scrutinee f)
in (let sub_term_guards = (let _109_946 = (Support.All.pipe_right args (Support.List.mapi (fun ( i ) ( arg ) -> (match ((Support.Prims.fst arg)) with
| Support.Microsoft.FStar.Util.Inl (_38_2352) -> begin
[]
end
| Support.Microsoft.FStar.Util.Inr (ei) -> begin
(let projector = (Microsoft_FStar_Tc_Env.lookup_projector env f.Microsoft_FStar_Absyn_Syntax.v i)
in (let sub_term = (let _109_944 = (let _109_943 = (Microsoft_FStar_Absyn_Util.fvar None projector f.Microsoft_FStar_Absyn_Syntax.p)
in (let _109_942 = (let _109_941 = (Microsoft_FStar_Absyn_Syntax.varg scrutinee)
in (_109_941)::[])
in (_109_943, _109_942)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _109_944 None f.Microsoft_FStar_Absyn_Syntax.p))
in (let _109_945 = (mk_guard sub_term ei)
in (_109_945)::[])))
end))))
in (Support.All.pipe_right _109_946 Support.List.flatten))
in (Microsoft_FStar_Absyn_Util.mk_conj_l ((head)::sub_term_guards))))
end
| _38_2360 -> begin
(let _109_949 = (let _109_948 = (Support.Microsoft.FStar.Range.string_of_range pat_exp.Microsoft_FStar_Absyn_Syntax.pos)
in (let _109_947 = (Microsoft_FStar_Absyn_Print.exp_to_string pat_exp)
in (Support.Microsoft.FStar.Util.format2 "tc_eqn: Impossible (%s) %s" _109_948 _109_947)))
in (Support.All.failwith _109_949))
end)))
in (let mk_guard = (fun ( s ) ( tsc ) ( pat ) -> (match ((not ((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)))) with
| true -> begin
(Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
end
| false -> begin
(let t = (mk_guard s pat)
in (let _38_2369 = (tc_typ_check scrutinee_env t Microsoft_FStar_Absyn_Syntax.mk_Kind_type)
in (match (_38_2369) with
| (t, _38_2368) -> begin
t
end)))
end))
in (let path_guard = (let _109_958 = (Support.All.pipe_right disj_exps (Support.List.map (fun ( e ) -> (let _109_957 = (Microsoft_FStar_Tc_Normalize.norm_exp ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env e)
in (mk_guard scrutinee pat_t _109_957)))))
in (Support.All.pipe_right _109_958 Microsoft_FStar_Absyn_Util.mk_disj_l))
in (let path_guard = (match (when_condition) with
| None -> begin
path_guard
end
| Some (w) -> begin
(Microsoft_FStar_Absyn_Util.mk_conj path_guard w)
end)
in (let guard = (let _109_959 = (Microsoft_FStar_Tc_Rel.conj_guard g_when g_branch)
in (Microsoft_FStar_Tc_Rel.conj_guard g_pat _109_959))
in (let _38_2377 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _109_960 = (Microsoft_FStar_Tc_Rel.guard_to_string env guard)
in (Support.All.pipe_left (Support.Microsoft.FStar.Util.fprint1 "Carrying guard from match: %s\n") _109_960))
end
| false -> begin
()
end)
in (let _109_962 = (let _109_961 = (Microsoft_FStar_Tc_Rel.conj_guard g_when g_branch)
in (Microsoft_FStar_Tc_Rel.conj_guard g_pat _109_961))
in ((pattern, when_clause, branch), path_guard, c, _109_962))))))))))
end)))
end)))
end))
end)))
end))
and tc_kind_trivial = (fun ( env ) ( k ) -> (let _38_2383 = (tc_kind env k)
in (match (_38_2383) with
| (k, g) -> begin
(let _38_2384 = (Microsoft_FStar_Tc_Util.discharge_guard env g)
in k)
end)))
and tc_typ_trivial = (fun ( env ) ( t ) -> (let _38_2391 = (tc_typ env t)
in (match (_38_2391) with
| (t, k, g) -> begin
(let _38_2392 = (Microsoft_FStar_Tc_Util.discharge_guard env g)
in (t, k))
end)))
and tc_typ_check_trivial = (fun ( env ) ( t ) ( k ) -> (let _38_2399 = (tc_typ_check env t k)
in (match (_38_2399) with
| (t, f) -> begin
(let _38_2400 = (Microsoft_FStar_Tc_Util.discharge_guard env f)
in t)
end)))
and tc_total_exp = (fun ( env ) ( e ) -> (let _38_2407 = (tc_exp env e)
in (match (_38_2407) with
| (e, c, g) -> begin
(match ((Microsoft_FStar_Absyn_Util.is_total_lcomp c)) with
| true -> begin
(e, c.Microsoft_FStar_Absyn_Syntax.res_typ, g)
end
| false -> begin
(let g = (Microsoft_FStar_Tc_Rel.solve_deferred_constraints env g)
in (let c = (let _109_972 = (c.Microsoft_FStar_Absyn_Syntax.comp ())
in (Support.All.pipe_right _109_972 (norm_c env)))
in (match ((let _109_974 = (let _109_973 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Util.total_comp (Microsoft_FStar_Absyn_Util.comp_result c) _109_973))
in (Microsoft_FStar_Tc_Rel.sub_comp env c _109_974))) with
| Some (g') -> begin
(let _109_975 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (e, (Microsoft_FStar_Absyn_Util.comp_result c), _109_975))
end
| _38_2413 -> begin
(let _109_978 = (let _109_977 = (let _109_976 = (Microsoft_FStar_Tc_Errors.expected_pure_expression e c)
in (_109_976, e.Microsoft_FStar_Absyn_Syntax.pos))
in Microsoft_FStar_Absyn_Syntax.Error (_109_977))
in (raise (_109_978)))
end)))
end)
end)))
and tc_ghost_exp = (fun ( env ) ( e ) -> (let _38_2419 = (tc_exp env e)
in (match (_38_2419) with
| (e, c, g) -> begin
(match ((Microsoft_FStar_Absyn_Util.is_total_lcomp c)) with
| true -> begin
(e, c.Microsoft_FStar_Absyn_Syntax.res_typ, g)
end
| false -> begin
(let c = (let _109_981 = (c.Microsoft_FStar_Absyn_Syntax.comp ())
in (Support.All.pipe_right _109_981 (norm_c env)))
in (let expected_c = (Microsoft_FStar_Absyn_Util.gtotal_comp (Microsoft_FStar_Absyn_Util.comp_result c))
in (let g = (Microsoft_FStar_Tc_Rel.solve_deferred_constraints env g)
in (match ((Microsoft_FStar_Tc_Rel.sub_comp (let _38_2423 = env
in {Microsoft_FStar_Tc_Env.solver = _38_2423.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _38_2423.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _38_2423.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _38_2423.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _38_2423.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _38_2423.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _38_2423.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _38_2423.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _38_2423.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _38_2423.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _38_2423.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _38_2423.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _38_2423.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _38_2423.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _38_2423.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _38_2423.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = false; Microsoft_FStar_Tc_Env.is_iface = _38_2423.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _38_2423.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _38_2423.Microsoft_FStar_Tc_Env.default_effects}) c expected_c)) with
| Some (g') -> begin
(let _109_982 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (e, (Microsoft_FStar_Absyn_Util.comp_result c), _109_982))
end
| _38_2428 -> begin
(let _109_985 = (let _109_984 = (let _109_983 = (Microsoft_FStar_Tc_Errors.expected_ghost_expression e c)
in (_109_983, e.Microsoft_FStar_Absyn_Syntax.pos))
in Microsoft_FStar_Absyn_Syntax.Error (_109_984))
in (raise (_109_985)))
end))))
end)
end)))

let tc_tparams = (fun ( env ) ( tps ) -> (let _38_2434 = (tc_binders env tps)
in (match (_38_2434) with
| (tps, env, g) -> begin
(let _38_2435 = (Microsoft_FStar_Tc_Util.force_trivial env g)
in (tps, env))
end)))

let a_kwp_a = (fun ( env ) ( m ) ( s ) -> (match (s.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow (((Support.Microsoft.FStar.Util.Inl (a), _38_2454)::(Support.Microsoft.FStar.Util.Inl (wp), _38_2449)::(Support.Microsoft.FStar.Util.Inl (_38_2441), _38_2444)::[], _38_2458)) -> begin
(a, wp.Microsoft_FStar_Absyn_Syntax.sort)
end
| _38_2462 -> begin
(let _109_999 = (let _109_998 = (let _109_997 = (Microsoft_FStar_Tc_Errors.unexpected_signature_for_monad env m s)
in (let _109_996 = (Microsoft_FStar_Absyn_Syntax.range_of_lid m)
in (_109_997, _109_996)))
in Microsoft_FStar_Absyn_Syntax.Error (_109_998))
in (raise (_109_999)))
end))

let rec tc_eff_decl = (fun ( env ) ( m ) -> (let _38_2468 = (tc_binders env m.Microsoft_FStar_Absyn_Syntax.binders)
in (match (_38_2468) with
| (binders, env, g) -> begin
(let _38_2469 = (Microsoft_FStar_Tc_Util.discharge_guard env g)
in (let mk = (tc_kind_trivial env m.Microsoft_FStar_Absyn_Syntax.signature)
in (let _38_2474 = (a_kwp_a env m.Microsoft_FStar_Absyn_Syntax.mname mk)
in (match (_38_2474) with
| (a, kwp_a) -> begin
(let a_typ = (Microsoft_FStar_Absyn_Util.btvar_to_typ a)
in (let b = (let _109_1013 = (Microsoft_FStar_Absyn_Syntax.range_of_lid m.Microsoft_FStar_Absyn_Syntax.mname)
in (Microsoft_FStar_Absyn_Util.gen_bvar_p _109_1013 Microsoft_FStar_Absyn_Syntax.ktype))
in (let b_typ = (Microsoft_FStar_Absyn_Util.btvar_to_typ b)
in (let kwp_b = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, b_typ)))::[]) kwp_a)
in (let kwlp_a = kwp_a
in (let kwlp_b = kwp_b
in (let a_kwp_b = (let _109_1016 = (let _109_1015 = (let _109_1014 = (Microsoft_FStar_Absyn_Syntax.null_v_binder a_typ)
in (_109_1014)::[])
in (_109_1015, kwp_b))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _109_1016 a_typ.Microsoft_FStar_Absyn_Syntax.pos))
in (let a_kwlp_b = a_kwp_b
in (let w = (fun ( k ) -> (let _109_1024 = (Microsoft_FStar_Absyn_Syntax.range_of_lid m.Microsoft_FStar_Absyn_Syntax.mname)
in (k _109_1024)))
in (let ret = (let expected_k = (let _109_1031 = (let _109_1030 = (let _109_1029 = (let _109_1028 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _109_1027 = (let _109_1026 = (Microsoft_FStar_Absyn_Syntax.null_v_binder a_typ)
in (_109_1026)::[])
in (_109_1028)::_109_1027))
in (_109_1029, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _109_1030))
in (Support.All.pipe_left w _109_1031))
in (let _109_1032 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.ret expected_k)
in (Support.All.pipe_right _109_1032 (norm_t env))))
in (let bind_wp = (let expected_k = (let _109_1047 = (let _109_1046 = (let _109_1045 = (let _109_1044 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _109_1043 = (let _109_1042 = (Microsoft_FStar_Absyn_Syntax.t_binder b)
in (let _109_1041 = (let _109_1040 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _109_1039 = (let _109_1038 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _109_1037 = (let _109_1036 = (Microsoft_FStar_Absyn_Syntax.null_t_binder a_kwp_b)
in (let _109_1035 = (let _109_1034 = (Microsoft_FStar_Absyn_Syntax.null_t_binder a_kwlp_b)
in (_109_1034)::[])
in (_109_1036)::_109_1035))
in (_109_1038)::_109_1037))
in (_109_1040)::_109_1039))
in (_109_1042)::_109_1041))
in (_109_1044)::_109_1043))
in (_109_1045, kwp_b))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _109_1046))
in (Support.All.pipe_left w _109_1047))
in (let _109_1048 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.bind_wp expected_k)
in (Support.All.pipe_right _109_1048 (norm_t env))))
in (let bind_wlp = (let expected_k = (let _109_1059 = (let _109_1058 = (let _109_1057 = (let _109_1056 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _109_1055 = (let _109_1054 = (Microsoft_FStar_Absyn_Syntax.t_binder b)
in (let _109_1053 = (let _109_1052 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _109_1051 = (let _109_1050 = (Microsoft_FStar_Absyn_Syntax.null_t_binder a_kwlp_b)
in (_109_1050)::[])
in (_109_1052)::_109_1051))
in (_109_1054)::_109_1053))
in (_109_1056)::_109_1055))
in (_109_1057, kwlp_b))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _109_1058))
in (Support.All.pipe_left w _109_1059))
in (let _109_1060 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.bind_wlp expected_k)
in (Support.All.pipe_right _109_1060 (norm_t env))))
in (let if_then_else = (let expected_k = (let _109_1071 = (let _109_1070 = (let _109_1069 = (let _109_1068 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _109_1067 = (let _109_1066 = (Microsoft_FStar_Absyn_Syntax.t_binder b)
in (let _109_1065 = (let _109_1064 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _109_1063 = (let _109_1062 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_109_1062)::[])
in (_109_1064)::_109_1063))
in (_109_1066)::_109_1065))
in (_109_1068)::_109_1067))
in (_109_1069, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _109_1070))
in (Support.All.pipe_left w _109_1071))
in (let _109_1072 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.if_then_else expected_k)
in (Support.All.pipe_right _109_1072 (norm_t env))))
in (let ite_wp = (let expected_k = (let _109_1081 = (let _109_1080 = (let _109_1079 = (let _109_1078 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _109_1077 = (let _109_1076 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _109_1075 = (let _109_1074 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_109_1074)::[])
in (_109_1076)::_109_1075))
in (_109_1078)::_109_1077))
in (_109_1079, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _109_1080))
in (Support.All.pipe_left w _109_1081))
in (let _109_1082 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.ite_wp expected_k)
in (Support.All.pipe_right _109_1082 (norm_t env))))
in (let ite_wlp = (let expected_k = (let _109_1089 = (let _109_1088 = (let _109_1087 = (let _109_1086 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _109_1085 = (let _109_1084 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (_109_1084)::[])
in (_109_1086)::_109_1085))
in (_109_1087, kwlp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _109_1088))
in (Support.All.pipe_left w _109_1089))
in (let _109_1090 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.ite_wlp expected_k)
in (Support.All.pipe_right _109_1090 (norm_t env))))
in (let wp_binop = (let expected_k = (let _109_1102 = (let _109_1101 = (let _109_1100 = (let _109_1099 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _109_1098 = (let _109_1097 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _109_1096 = (let _109_1095 = (let _109_1092 = (Microsoft_FStar_Absyn_Const.kbin Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Syntax.null_t_binder _109_1092))
in (let _109_1094 = (let _109_1093 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_109_1093)::[])
in (_109_1095)::_109_1094))
in (_109_1097)::_109_1096))
in (_109_1099)::_109_1098))
in (_109_1100, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _109_1101))
in (Support.All.pipe_left w _109_1102))
in (let _109_1103 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.wp_binop expected_k)
in (Support.All.pipe_right _109_1103 (norm_t env))))
in (let wp_as_type = (let expected_k = (let _109_1110 = (let _109_1109 = (let _109_1108 = (let _109_1107 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _109_1106 = (let _109_1105 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_109_1105)::[])
in (_109_1107)::_109_1106))
in (_109_1108, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _109_1109))
in (Support.All.pipe_left w _109_1110))
in (let _109_1111 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.wp_as_type expected_k)
in (Support.All.pipe_right _109_1111 (norm_t env))))
in (let close_wp = (let expected_k = (let _109_1120 = (let _109_1119 = (let _109_1118 = (let _109_1117 = (Microsoft_FStar_Absyn_Syntax.t_binder b)
in (let _109_1116 = (let _109_1115 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _109_1114 = (let _109_1113 = (Microsoft_FStar_Absyn_Syntax.null_t_binder a_kwp_b)
in (_109_1113)::[])
in (_109_1115)::_109_1114))
in (_109_1117)::_109_1116))
in (_109_1118, kwp_b))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _109_1119))
in (Support.All.pipe_left w _109_1120))
in (let _109_1121 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.close_wp expected_k)
in (Support.All.pipe_right _109_1121 (norm_t env))))
in (let close_wp_t = (let expected_k = (let _109_1134 = (let _109_1133 = (let _109_1132 = (let _109_1131 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _109_1130 = (let _109_1129 = (let _109_1128 = (let _109_1127 = (let _109_1126 = (let _109_1125 = (let _109_1124 = (Microsoft_FStar_Absyn_Syntax.null_t_binder Microsoft_FStar_Absyn_Syntax.ktype)
in (_109_1124)::[])
in (_109_1125, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _109_1126))
in (Support.All.pipe_left w _109_1127))
in (Microsoft_FStar_Absyn_Syntax.null_t_binder _109_1128))
in (_109_1129)::[])
in (_109_1131)::_109_1130))
in (_109_1132, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _109_1133))
in (Support.All.pipe_left w _109_1134))
in (let _109_1135 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.close_wp_t expected_k)
in (Support.All.pipe_right _109_1135 (norm_t env))))
in (let _38_2508 = (let expected_k = (let _109_1144 = (let _109_1143 = (let _109_1142 = (let _109_1141 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _109_1140 = (let _109_1139 = (Microsoft_FStar_Absyn_Syntax.null_t_binder Microsoft_FStar_Absyn_Syntax.ktype)
in (let _109_1138 = (let _109_1137 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_109_1137)::[])
in (_109_1139)::_109_1138))
in (_109_1141)::_109_1140))
in (_109_1142, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _109_1143))
in (Support.All.pipe_left w _109_1144))
in (let _109_1148 = (let _109_1145 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.assert_p expected_k)
in (Support.All.pipe_right _109_1145 (norm_t env)))
in (let _109_1147 = (let _109_1146 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.assume_p expected_k)
in (Support.All.pipe_right _109_1146 (norm_t env)))
in (_109_1148, _109_1147))))
in (match (_38_2508) with
| (assert_p, assume_p) -> begin
(let null_wp = (let expected_k = (let _109_1153 = (let _109_1152 = (let _109_1151 = (let _109_1150 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (_109_1150)::[])
in (_109_1151, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _109_1152))
in (Support.All.pipe_left w _109_1153))
in (let _109_1154 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.null_wp expected_k)
in (Support.All.pipe_right _109_1154 (norm_t env))))
in (let trivial_wp = (let expected_k = (let _109_1161 = (let _109_1160 = (let _109_1159 = (let _109_1158 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _109_1157 = (let _109_1156 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_109_1156)::[])
in (_109_1158)::_109_1157))
in (_109_1159, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _109_1160))
in (Support.All.pipe_left w _109_1161))
in (let _109_1162 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.trivial expected_k)
in (Support.All.pipe_right _109_1162 (norm_t env))))
in {Microsoft_FStar_Absyn_Syntax.mname = m.Microsoft_FStar_Absyn_Syntax.mname; Microsoft_FStar_Absyn_Syntax.binders = binders; Microsoft_FStar_Absyn_Syntax.qualifiers = m.Microsoft_FStar_Absyn_Syntax.qualifiers; Microsoft_FStar_Absyn_Syntax.signature = mk; Microsoft_FStar_Absyn_Syntax.ret = ret; Microsoft_FStar_Absyn_Syntax.bind_wp = bind_wp; Microsoft_FStar_Absyn_Syntax.bind_wlp = bind_wlp; Microsoft_FStar_Absyn_Syntax.if_then_else = if_then_else; Microsoft_FStar_Absyn_Syntax.ite_wp = ite_wp; Microsoft_FStar_Absyn_Syntax.ite_wlp = ite_wlp; Microsoft_FStar_Absyn_Syntax.wp_binop = wp_binop; Microsoft_FStar_Absyn_Syntax.wp_as_type = wp_as_type; Microsoft_FStar_Absyn_Syntax.close_wp = close_wp; Microsoft_FStar_Absyn_Syntax.close_wp_t = close_wp_t; Microsoft_FStar_Absyn_Syntax.assert_p = assert_p; Microsoft_FStar_Absyn_Syntax.assume_p = assume_p; Microsoft_FStar_Absyn_Syntax.null_wp = null_wp; Microsoft_FStar_Absyn_Syntax.trivial = trivial_wp}))
end)))))))))))))))))))))
end))))
end)))
and tc_decl = (fun ( env ) ( se ) ( deserialized ) -> (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_pragma ((p, r)) -> begin
(match (p) with
| Microsoft_FStar_Absyn_Syntax.SetOptions (o) -> begin
(match ((Microsoft_FStar_Options.set_options o)) with
| Support.Microsoft.FStar.Getopt.GoOn -> begin
(se, env)
end
| Support.Microsoft.FStar.Getopt.Help -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Failed to process pragma: use \'fstar --help\' to see which options are available", r))))
end
| Support.Microsoft.FStar.Getopt.Die (s) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat "Failed to process pragma: " s), r))))
end)
end
| Microsoft_FStar_Absyn_Syntax.ResetOptions -> begin
(let _38_2527 = (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.refresh ())
in (let _38_2529 = (let _109_1166 = (Microsoft_FStar_Options.reset_options ())
in (Support.All.pipe_right _109_1166 Support.Prims.ignore))
in (se, env)))
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ne, r)) -> begin
(let ne = (tc_eff_decl env ne)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ne, r))
in (let env = (Microsoft_FStar_Tc_Env.push_sigelt env se)
in (se, env))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_sub_effect ((sub, r)) -> begin
(let _38_2544 = (let _109_1167 = (Microsoft_FStar_Tc_Env.lookup_effect_lid env sub.Microsoft_FStar_Absyn_Syntax.source)
in (a_kwp_a env sub.Microsoft_FStar_Absyn_Syntax.source _109_1167))
in (match (_38_2544) with
| (a, kwp_a_src) -> begin
(let _38_2547 = (let _109_1168 = (Microsoft_FStar_Tc_Env.lookup_effect_lid env sub.Microsoft_FStar_Absyn_Syntax.target)
in (a_kwp_a env sub.Microsoft_FStar_Absyn_Syntax.target _109_1168))
in (match (_38_2547) with
| (b, kwp_b_tgt) -> begin
(let kwp_a_tgt = (let _109_1172 = (let _109_1171 = (let _109_1170 = (let _109_1169 = (Microsoft_FStar_Absyn_Util.btvar_to_typ a)
in (b.Microsoft_FStar_Absyn_Syntax.v, _109_1169))
in Support.Microsoft.FStar.Util.Inl (_109_1170))
in (_109_1171)::[])
in (Microsoft_FStar_Absyn_Util.subst_kind _109_1172 kwp_b_tgt))
in (let expected_k = (let _109_1178 = (let _109_1177 = (let _109_1176 = (let _109_1175 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _109_1174 = (let _109_1173 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a_src)
in (_109_1173)::[])
in (_109_1175)::_109_1174))
in (_109_1176, kwp_a_tgt))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _109_1177))
in (Support.All.pipe_right r _109_1178))
in (let lift = (tc_typ_check_trivial env sub.Microsoft_FStar_Absyn_Syntax.lift expected_k)
in (let sub = (let _38_2551 = sub
in {Microsoft_FStar_Absyn_Syntax.source = _38_2551.Microsoft_FStar_Absyn_Syntax.source; Microsoft_FStar_Absyn_Syntax.target = _38_2551.Microsoft_FStar_Absyn_Syntax.target; Microsoft_FStar_Absyn_Syntax.lift = lift})
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_sub_effect ((sub, r))
in (let env = (Microsoft_FStar_Tc_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, _mutuals, _data, tags, r)) -> begin
(let env = (Microsoft_FStar_Tc_Env.set_range env r)
in (let _38_2568 = (tc_tparams env tps)
in (match (_38_2568) with
| (tps, env) -> begin
(let k = (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
Microsoft_FStar_Absyn_Syntax.ktype
end
| _38_2571 -> begin
(tc_kind_trivial env k)
end)
in (let _38_2573 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _109_1181 = (Microsoft_FStar_Absyn_Print.sli lid)
in (let _109_1180 = (let _109_1179 = (Microsoft_FStar_Absyn_Util.close_kind tps k)
in (Microsoft_FStar_Absyn_Print.kind_to_string _109_1179))
in (Support.Microsoft.FStar.Util.fprint2 "Checked %s at kind %s\n" _109_1181 _109_1180)))
end
| false -> begin
()
end)
in (let k = (norm_k env k)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, _mutuals, _data, tags, r))
in (let _38_2591 = (match ((Microsoft_FStar_Absyn_Util.compress_kind k)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_uvar (_38_2586); Microsoft_FStar_Absyn_Syntax.tk = _38_2584; Microsoft_FStar_Absyn_Syntax.pos = _38_2582; Microsoft_FStar_Absyn_Syntax.fvs = _38_2580; Microsoft_FStar_Absyn_Syntax.uvs = _38_2578} -> begin
(let _109_1182 = (Microsoft_FStar_Tc_Rel.keq env None k Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.All.pipe_left (Microsoft_FStar_Tc_Util.force_trivial env) _109_1182))
end
| _38_2590 -> begin
()
end)
in (let env = (Microsoft_FStar_Tc_Env.push_sigelt env se)
in (se, env)))))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev ((lid, tps, k, r)) -> begin
(let env0 = env
in (let env = (Microsoft_FStar_Tc_Env.set_range env r)
in (let _38_2604 = (tc_tparams env tps)
in (match (_38_2604) with
| (tps, env) -> begin
(let k = (tc_kind_trivial env k)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev ((lid, tps, k, r))
in (let env = (Microsoft_FStar_Tc_Env.push_sigelt env0 se)
in (se, env))))
end))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((lid, tps, c, tags, r)) -> begin
(let env0 = env
in (let env = (Microsoft_FStar_Tc_Env.set_range env r)
in (let _38_2619 = (tc_tparams env tps)
in (match (_38_2619) with
| (tps, env) -> begin
(let _38_2622 = (tc_comp env c)
in (match (_38_2622) with
| (c, g) -> begin
(let tags = (Support.All.pipe_right tags (Support.List.map (fun ( _38_13 ) -> (match (_38_13) with
| Microsoft_FStar_Absyn_Syntax.DefaultEffect (None) -> begin
(let c' = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _109_1185 = (Support.All.pipe_right c'.Microsoft_FStar_Absyn_Syntax.effect_name (fun ( _109_1184 ) -> Some (_109_1184)))
in Microsoft_FStar_Absyn_Syntax.DefaultEffect (_109_1185)))
end
| t -> begin
t
end))))
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((lid, tps, c, tags, r))
in (let env = (Microsoft_FStar_Tc_Env.push_sigelt env0 se)
in (se, env))))
end))
end))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, k, t, tags, r)) -> begin
(let env = (Microsoft_FStar_Tc_Env.set_range env r)
in (let _38_2642 = (tc_tparams env tps)
in (match (_38_2642) with
| (tps, env') -> begin
(let _38_2648 = (let _109_1189 = (tc_typ_trivial env' t)
in (Support.All.pipe_right _109_1189 (fun ( _38_2645 ) -> (match (_38_2645) with
| (t, k) -> begin
(let _109_1188 = (norm_t env' t)
in (let _109_1187 = (norm_k env' k)
in (_109_1188, _109_1187)))
end))))
in (match (_38_2648) with
| (t, k1) -> begin
(let k2 = (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
k1
end
| _38_2651 -> begin
(let k2 = (let _109_1190 = (tc_kind_trivial env' k)
in (Support.All.pipe_right _109_1190 (norm_k env)))
in (let _38_2653 = (let _109_1191 = (Microsoft_FStar_Tc_Rel.keq env' (Some (t)) k1 k2)
in (Support.All.pipe_left (Microsoft_FStar_Tc_Util.force_trivial env') _109_1191))
in k2))
end)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, k2, t, tags, r))
in (let env = (Microsoft_FStar_Tc_Env.push_sigelt env se)
in (se, env))))
end))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, t, tycon, quals, mutuals, r)) -> begin
(let _38_2671 = tycon
in (match (_38_2671) with
| (tname, _38_2668, _38_2670) -> begin
(let env = (Microsoft_FStar_Tc_Env.set_range env r)
in (let t = (tc_typ_check_trivial env t Microsoft_FStar_Absyn_Syntax.ktype)
in (let t = (norm_t env t)
in (let _38_2683 = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((formals, cod)) -> begin
(formals, (Microsoft_FStar_Absyn_Util.comp_result cod))
end
| _38_2680 -> begin
([], t)
end)
in (match (_38_2683) with
| (formals, result_t) -> begin
(let positivity_check = (fun ( formal ) -> (match ((Support.Prims.fst formal)) with
| Support.Microsoft.FStar.Util.Inl (_38_2687) -> begin
()
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let t = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.DeltaHard)::[]) env x.Microsoft_FStar_Absyn_Syntax.sort)
in (match (((Microsoft_FStar_Absyn_Util.is_function_typ t) && (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t))) with
| true -> begin
(let _38_2695 = (let _109_1194 = (Microsoft_FStar_Absyn_Util.function_formals t)
in (Support.All.pipe_right _109_1194 Support.Microsoft.FStar.Util.must))
in (match (_38_2695) with
| (formals, _38_2694) -> begin
(Support.All.pipe_right formals (Support.List.iter (fun ( _38_2699 ) -> (match (_38_2699) with
| (a, _38_2698) -> begin
(match (a) with
| Support.Microsoft.FStar.Util.Inl (_38_2701) -> begin
()
end
| Support.Microsoft.FStar.Util.Inr (y) -> begin
(let t = y.Microsoft_FStar_Absyn_Syntax.sort
in (Microsoft_FStar_Absyn_Visit.collect_from_typ (fun ( b ) ( t ) -> (match ((let _109_1198 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _109_1198.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (f) -> begin
(match ((Support.List.tryFind (Microsoft_FStar_Absyn_Syntax.lid_equals f.Microsoft_FStar_Absyn_Syntax.v) mutuals)) with
| None -> begin
()
end
| Some (tname) -> begin
(let _109_1204 = (let _109_1203 = (let _109_1202 = (let _109_1200 = (let _109_1199 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) lid _109_1199))
in (Microsoft_FStar_Tc_Errors.constructor_fails_the_positivity_check env _109_1200 tname))
in (let _109_1201 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (_109_1202, _109_1201)))
in Microsoft_FStar_Absyn_Syntax.Error (_109_1203))
in (raise (_109_1204)))
end)
end
| _38_2714 -> begin
()
end)) () t))
end)
end))))
end))
end
| false -> begin
()
end))
end))
in (let _38_2715 = (Support.All.pipe_right formals (Support.List.iter positivity_check))
in (let _38_2722 = (match ((Microsoft_FStar_Absyn_Util.destruct result_t tname)) with
| Some (_38_2718) -> begin
()
end
| _38_2721 -> begin
(let _109_1211 = (let _109_1210 = (let _109_1209 = (let _109_1207 = (let _109_1205 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) lid _109_1205))
in (let _109_1206 = (Microsoft_FStar_Absyn_Util.ftv tname Microsoft_FStar_Absyn_Syntax.kun)
in (Microsoft_FStar_Tc_Errors.constructor_builds_the_wrong_type env _109_1207 result_t _109_1206)))
in (let _109_1208 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (_109_1209, _109_1208)))
in Microsoft_FStar_Absyn_Syntax.Error (_109_1210))
in (raise (_109_1211)))
end)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, t, tycon, quals, mutuals, r))
in (let env = (Microsoft_FStar_Tc_Env.push_sigelt env se)
in (let _38_2726 = (match ((log env)) with
| true -> begin
(let _109_1213 = (let _109_1212 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (Support.Microsoft.FStar.Util.format2 "data %s : %s\n" lid.Microsoft_FStar_Absyn_Syntax.str _109_1212))
in (Support.All.pipe_left Support.Microsoft.FStar.Util.print_string _109_1213))
end
| false -> begin
()
end)
in (se, env)))))))
end)))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, r)) -> begin
(let env = (Microsoft_FStar_Tc_Env.set_range env r)
in (let t = (let _109_1214 = (tc_typ_check_trivial env t Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.All.pipe_right _109_1214 (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.SNComp)::[]) env)))
in (let _38_2736 = (Microsoft_FStar_Tc_Util.check_uvars r t)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, r))
in (let env = (Microsoft_FStar_Tc_Env.push_sigelt env se)
in (let _38_2740 = (match ((log env)) with
| true -> begin
(let _109_1216 = (let _109_1215 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (Support.Microsoft.FStar.Util.format2 "val %s : %s\n" lid.Microsoft_FStar_Absyn_Syntax.str _109_1215))
in (Support.All.pipe_left Support.Microsoft.FStar.Util.print_string _109_1216))
end
| false -> begin
()
end)
in (se, env)))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_assume ((lid, phi, quals, r)) -> begin
(let env = (Microsoft_FStar_Tc_Env.set_range env r)
in (let phi = (let _109_1217 = (tc_typ_check_trivial env phi Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.All.pipe_right _109_1217 (norm_t env)))
in (let _38_2750 = (Microsoft_FStar_Tc_Util.check_uvars r phi)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_assume ((lid, phi, quals, r))
in (let env = (Microsoft_FStar_Tc_Env.push_sigelt env se)
in (se, env))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, r, lids, quals)) -> begin
(let env = (Microsoft_FStar_Tc_Env.set_range env r)
in (let _38_2803 = (Support.All.pipe_right (Support.Prims.snd lbs) (Support.List.fold_left (fun ( _38_2763 ) ( lb ) -> (match (_38_2763) with
| (gen, lbs) -> begin
(let _38_2800 = (match (lb) with
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inl (_38_2772); Microsoft_FStar_Absyn_Syntax.lbtyp = _38_2770; Microsoft_FStar_Absyn_Syntax.lbeff = _38_2768; Microsoft_FStar_Absyn_Syntax.lbdef = _38_2766} -> begin
(Support.All.failwith "impossible")
end
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (l); Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _38_2777; Microsoft_FStar_Absyn_Syntax.lbdef = e} -> begin
(let _38_2797 = (match ((Microsoft_FStar_Tc_Env.try_lookup_val_decl env l)) with
| None -> begin
(gen, lb)
end
| Some ((t', _38_2785)) -> begin
(let _38_2788 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _109_1220 = (Microsoft_FStar_Absyn_Print.typ_to_string t')
in (Support.Microsoft.FStar.Util.fprint2 "Using annotation %s for let binding %s\n" _109_1220 l.Microsoft_FStar_Absyn_Syntax.str))
end
| false -> begin
()
end)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(let _109_1221 = (Microsoft_FStar_Absyn_Syntax.mk_lb (Support.Microsoft.FStar.Util.Inr (l), Microsoft_FStar_Absyn_Const.effect_ALL_lid, t', e))
in (false, _109_1221))
end
| _38_2792 -> begin
(let _38_2793 = (match ((not (deserialized))) with
| true -> begin
(let _109_1223 = (let _109_1222 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format1 "%s: Warning: Annotation from val declaration overrides inline type annotation\n" _109_1222))
in (Support.All.pipe_left Support.Microsoft.FStar.Util.print_string _109_1223))
end
| false -> begin
()
end)
in (let _109_1224 = (Microsoft_FStar_Absyn_Syntax.mk_lb (Support.Microsoft.FStar.Util.Inr (l), Microsoft_FStar_Absyn_Const.effect_ALL_lid, t', e))
in (false, _109_1224)))
end))
end)
in (match (_38_2797) with
| (gen, lb) -> begin
(gen, lb)
end))
end)
in (match (_38_2800) with
| (gen, lb) -> begin
(gen, (lb)::lbs)
end))
end)) (true, [])))
in (match (_38_2803) with
| (generalize, lbs') -> begin
(let lbs' = (Support.List.rev lbs')
in (let e = (let _109_1229 = (let _109_1228 = (let _109_1227 = (syn' env Microsoft_FStar_Tc_Recheck.t_unit)
in (Support.All.pipe_left _109_1227 (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant Microsoft_FStar_Absyn_Syntax.Const_unit)))
in (((Support.Prims.fst lbs), lbs'), _109_1228))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_let _109_1229 None r))
in (let _38_2838 = (match ((tc_exp (let _38_2806 = env
in {Microsoft_FStar_Tc_Env.solver = _38_2806.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _38_2806.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _38_2806.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _38_2806.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _38_2806.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _38_2806.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _38_2806.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _38_2806.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _38_2806.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _38_2806.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _38_2806.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _38_2806.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = generalize; Microsoft_FStar_Tc_Env.letrecs = _38_2806.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _38_2806.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _38_2806.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = _38_2806.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = _38_2806.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _38_2806.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _38_2806.Microsoft_FStar_Tc_Env.default_effects}) e)) with
| ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_let ((lbs, e)); Microsoft_FStar_Absyn_Syntax.tk = _38_2815; Microsoft_FStar_Absyn_Syntax.pos = _38_2813; Microsoft_FStar_Absyn_Syntax.fvs = _38_2811; Microsoft_FStar_Absyn_Syntax.uvs = _38_2809}, _38_2822, g) when (Microsoft_FStar_Tc_Rel.is_trivial g) -> begin
(let quals = (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((_38_2826, Microsoft_FStar_Absyn_Syntax.MaskedEffect))) -> begin
(Microsoft_FStar_Absyn_Syntax.HasMaskedEffect)::quals
end
| _38_2832 -> begin
quals
end)
in (Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _38_2835 -> begin
(Support.All.failwith "impossible")
end)
in (match (_38_2838) with
| (se, lbs) -> begin
(let _38_2844 = (match ((log env)) with
| true -> begin
(let _109_1235 = (let _109_1234 = (Support.All.pipe_right (Support.Prims.snd lbs) (Support.List.map (fun ( lb ) -> (let should_log = (match ((let _109_1231 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (Microsoft_FStar_Tc_Env.try_lookup_val_decl env _109_1231))) with
| None -> begin
true
end
| _38_2842 -> begin
false
end)
in (match (should_log) with
| true -> begin
(let _109_1233 = (Microsoft_FStar_Absyn_Print.lbname_to_string lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (let _109_1232 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
in (Support.Microsoft.FStar.Util.format2 "let %s : %s" _109_1233 _109_1232)))
end
| false -> begin
""
end)))))
in (Support.All.pipe_right _109_1234 (Support.String.concat "\n")))
in (Support.Microsoft.FStar.Util.fprint1 "%s\n" _109_1235))
end
| false -> begin
()
end)
in (let env = (Microsoft_FStar_Tc_Env.push_sigelt env se)
in (se, env)))
end))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_main ((e, r)) -> begin
(let env = (Microsoft_FStar_Tc_Env.set_range env r)
in (let env = (Microsoft_FStar_Tc_Env.set_expected_typ env Microsoft_FStar_Tc_Recheck.t_unit)
in (let _38_2856 = (tc_exp env e)
in (match (_38_2856) with
| (e, c, g1) -> begin
(let g1 = (Microsoft_FStar_Tc_Rel.solve_deferred_constraints env g1)
in (let _38_2862 = (let _109_1239 = (let _109_1236 = (Microsoft_FStar_Absyn_Util.ml_comp Microsoft_FStar_Tc_Recheck.t_unit r)
in Some (_109_1236))
in (let _109_1238 = (let _109_1237 = (c.Microsoft_FStar_Absyn_Syntax.comp ())
in (e, _109_1237))
in (check_expected_effect env _109_1239 _109_1238)))
in (match (_38_2862) with
| (e, _38_2860, g) -> begin
(let _38_2863 = (let _109_1240 = (Microsoft_FStar_Tc_Rel.conj_guard g1 g)
in (Microsoft_FStar_Tc_Util.discharge_guard env _109_1240))
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_main ((e, r))
in (let env = (Microsoft_FStar_Tc_Env.push_sigelt env se)
in (se, env))))
end)))
end))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, quals, lids, r)) -> begin
(let env = (Microsoft_FStar_Tc_Env.set_range env r)
in (let _38_2882 = (Support.All.pipe_right ses (Support.List.partition (fun ( _38_14 ) -> (match (_38_14) with
| Microsoft_FStar_Absyn_Syntax.Sig_tycon (_38_2876) -> begin
true
end
| _38_2879 -> begin
false
end))))
in (match (_38_2882) with
| (tycons, rest) -> begin
(let _38_2891 = (Support.All.pipe_right rest (Support.List.partition (fun ( _38_15 ) -> (match (_38_15) with
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_38_2885) -> begin
true
end
| _38_2888 -> begin
false
end))))
in (match (_38_2891) with
| (abbrevs, rest) -> begin
(let recs = (Support.All.pipe_right abbrevs (Support.List.map (fun ( _38_16 ) -> (match (_38_16) with
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, k, t, [], r)) -> begin
(let k = (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(let _109_1244 = (Microsoft_FStar_Tc_Rel.new_kvar r tps)
in (Support.All.pipe_right _109_1244 Support.Prims.fst))
end
| _38_2903 -> begin
k
end)
in (Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, [], [], [], r)), t))
end
| _38_2906 -> begin
(Support.All.failwith "impossible")
end))))
in (let _38_2910 = (Support.List.split recs)
in (match (_38_2910) with
| (recs, abbrev_defs) -> begin
(let msg = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _109_1245 = (Microsoft_FStar_Absyn_Print.sigelt_to_string_short se)
in (Support.Microsoft.FStar.Util.format1 "Recursive bindings: %s" _109_1245))
end
| false -> begin
""
end)
in (let _38_2912 = (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.push msg)
in (let _38_2919 = (tc_decls false env tycons deserialized)
in (match (_38_2919) with
| (tycons, _38_2916, _38_2918) -> begin
(let _38_2925 = (tc_decls false env recs deserialized)
in (match (_38_2925) with
| (recs, _38_2922, _38_2924) -> begin
(let env1 = (Microsoft_FStar_Tc_Env.push_sigelt env (Microsoft_FStar_Absyn_Syntax.Sig_bundle (((Support.List.append tycons recs), quals, lids, r))))
in (let _38_2932 = (tc_decls false env1 rest deserialized)
in (match (_38_2932) with
| (rest, _38_2929, _38_2931) -> begin
(let abbrevs = (Support.List.map2 (fun ( se ) ( t ) -> (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, [], [], [], r)) -> begin
(let tt = (let _109_1248 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_ascribed (t, k) t.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Util.close_with_lam tps _109_1248))
in (let _38_2948 = (tc_typ_trivial env1 tt)
in (match (_38_2948) with
| (tt, _38_2947) -> begin
(let _38_2957 = (match (tt.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, t)) -> begin
(bs, t)
end
| _38_2954 -> begin
([], tt)
end)
in (match (_38_2957) with
| (tps, t) -> begin
(let _109_1250 = (let _109_1249 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in (lid, tps, _109_1249, t, [], r))
in Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_109_1250))
end))
end)))
end
| _38_2959 -> begin
(let _109_1252 = (let _109_1251 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format1 "(%s) Impossible" _109_1251))
in (Support.All.failwith _109_1252))
end)) recs abbrev_defs)
in (let _38_2961 = (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.pop msg)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_bundle (((Support.List.append (Support.List.append tycons abbrevs) rest), quals, lids, r))
in (let env = (Microsoft_FStar_Tc_Env.push_sigelt env se)
in (se, env)))))
end)))
end))
end))))
end)))
end))
end)))
end))
and tc_decls = (fun ( for_export ) ( env ) ( ses ) ( deserialized ) -> (let _38_2985 = (Support.All.pipe_right ses (Support.List.fold_left (fun ( _38_2972 ) ( se ) -> (match (_38_2972) with
| (ses, all_non_private, env) -> begin
(let _38_2974 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _109_1260 = (let _109_1259 = (Microsoft_FStar_Absyn_Print.sigelt_to_string se)
in (Support.Microsoft.FStar.Util.format1 "Checking sigelt\t%s\n" _109_1259))
in (Support.Microsoft.FStar.Util.print_string _109_1260))
end
| false -> begin
()
end)
in (let _38_2978 = (tc_decl env se deserialized)
in (match (_38_2978) with
| (se, env) -> begin
(let _38_2979 = (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.encode_sig env se)
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
in (match (_38_2985) with
| (ses, all_non_private, env) -> begin
(let _109_1261 = (Support.All.pipe_right (Support.List.rev all_non_private) Support.List.flatten)
in ((Support.List.rev ses), _109_1261, env))
end)))
and non_private = (fun ( env ) ( se ) -> (let is_private = (fun ( quals ) -> (Support.List.contains Microsoft_FStar_Absyn_Syntax.Private quals))
in (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, quals, _38_2993, _38_2995)) -> begin
(se)::[]
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((_38_2999, _38_3001, _38_3003, _38_3005, _38_3007, quals, r)) -> begin
(match ((is_private quals)) with
| true -> begin
[]
end
| false -> begin
(se)::[]
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((l, bs, k, t, quals, r)) -> begin
(match ((is_private quals)) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.Sig_tycon ((l, bs, k, [], [], (Microsoft_FStar_Absyn_Syntax.Assumption)::quals, r)))::[]
end
| false -> begin
(se)::[]
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_assume ((_38_3021, _38_3023, quals, _38_3026)) -> begin
(match ((is_private quals)) with
| true -> begin
[]
end
| false -> begin
(se)::[]
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_38_3030, _38_3032, quals, _38_3035)) -> begin
(match ((is_private quals)) with
| true -> begin
[]
end
| false -> begin
(se)::[]
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_main (_38_3039) -> begin
[]
end
| (Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_pragma (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_)) -> begin
(se)::[]
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon (_38_3057) -> begin
(Support.All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, r, l, _38_3063)) -> begin
(let check_priv = (fun ( lbs ) -> (let is_priv = (fun ( _38_17 ) -> (match (_38_17) with
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (l); Microsoft_FStar_Absyn_Syntax.lbtyp = _38_3074; Microsoft_FStar_Absyn_Syntax.lbeff = _38_3072; Microsoft_FStar_Absyn_Syntax.lbdef = _38_3070} -> begin
(match ((Microsoft_FStar_Tc_Env.try_lookup_val_decl env l)) with
| Some ((_38_3079, qs)) -> begin
(Support.List.contains Microsoft_FStar_Absyn_Syntax.Private qs)
end
| _38_3084 -> begin
false
end)
end
| _38_3086 -> begin
false
end))
in (let some_priv = (Support.All.pipe_right lbs (Support.Microsoft.FStar.Util.for_some is_priv))
in (match (some_priv) with
| true -> begin
(match ((Support.All.pipe_right lbs (Support.Microsoft.FStar.Util.for_some (fun ( x ) -> (let _109_1271 = (is_priv x)
in (Support.All.pipe_right _109_1271 Support.Prims.op_Negation)))))) with
| true -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Some but not all functions in this mutually recursive nest are marked private", r))))
end
| false -> begin
true
end)
end
| false -> begin
false
end))))
in (let _38_3093 = (Support.All.pipe_right (Support.Prims.snd lbs) (Support.List.partition (fun ( lb ) -> ((Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function lb.Microsoft_FStar_Absyn_Syntax.lbtyp) && (let _109_1273 = (Microsoft_FStar_Absyn_Util.is_lemma lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
in (Support.All.pipe_left Support.Prims.op_Negation _109_1273))))))
in (match (_38_3093) with
| (pure_funs, rest) -> begin
(match ((pure_funs, rest)) with
| (_38_3097::_38_3095, _38_3102::_38_3100) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Pure functions cannot be mutually recursive with impure functions", r))))
end
| (_38_3108::_38_3106, []) -> begin
(match ((check_priv pure_funs)) with
| true -> begin
[]
end
| false -> begin
(se)::[]
end)
end
| ([], _38_3116::_38_3114) -> begin
(match ((check_priv rest)) with
| true -> begin
[]
end
| false -> begin
(Support.All.pipe_right rest (Support.List.collect (fun ( lb ) -> (match (lb.Microsoft_FStar_Absyn_Syntax.lbname) with
| Support.Microsoft.FStar.Util.Inl (_38_3121) -> begin
(Support.All.failwith "impossible")
end
| Support.Microsoft.FStar.Util.Inr (l) -> begin
(let _109_1277 = (let _109_1276 = (let _109_1275 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (l, lb.Microsoft_FStar_Absyn_Syntax.lbtyp, (Microsoft_FStar_Absyn_Syntax.Assumption)::[], _109_1275))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_109_1276))
in (_109_1277)::[])
end))))
end)
end
| ([], []) -> begin
(Support.All.failwith "Impossible")
end)
end)))
end)))

let get_exports = (fun ( env ) ( modul ) ( non_private_decls ) -> (let assume_vals = (fun ( decls ) -> (Support.All.pipe_right decls (Support.List.map (fun ( _38_18 ) -> (match (_38_18) with
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, r)) -> begin
Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, (Microsoft_FStar_Absyn_Syntax.Assumption)::quals, r))
end
| s -> begin
s
end)))))
in (match (modul.Microsoft_FStar_Absyn_Syntax.is_interface) with
| true -> begin
non_private_decls
end
| false -> begin
(let exports = (let _109_1289 = (Microsoft_FStar_Tc_Env.modules env)
in (Support.Microsoft.FStar.Util.find_map _109_1289 (fun ( m ) -> (match ((m.Microsoft_FStar_Absyn_Syntax.is_interface && (Microsoft_FStar_Absyn_Syntax.lid_equals modul.Microsoft_FStar_Absyn_Syntax.name m.Microsoft_FStar_Absyn_Syntax.name))) with
| true -> begin
(let _109_1288 = (Support.All.pipe_right m.Microsoft_FStar_Absyn_Syntax.exports assume_vals)
in Some (_109_1288))
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

let tc_partial_modul = (fun ( env ) ( modul ) -> (let name = (Support.Microsoft.FStar.Util.format2 "%s %s" (match (modul.Microsoft_FStar_Absyn_Syntax.is_interface) with
| true -> begin
"interface"
end
| false -> begin
"module"
end) modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)
in (let msg = (Support.String.strcat "Internals for " name)
in (let env = (let _38_3150 = env
in (let _109_1294 = (not ((Microsoft_FStar_Options.should_verify modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)))
in {Microsoft_FStar_Tc_Env.solver = _38_3150.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _38_3150.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _38_3150.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _38_3150.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _38_3150.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _38_3150.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _38_3150.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _38_3150.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _38_3150.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _38_3150.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _38_3150.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _38_3150.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _38_3150.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _38_3150.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _38_3150.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _38_3150.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = _38_3150.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = modul.Microsoft_FStar_Absyn_Syntax.is_interface; Microsoft_FStar_Tc_Env.admit = _109_1294; Microsoft_FStar_Tc_Env.default_effects = _38_3150.Microsoft_FStar_Tc_Env.default_effects}))
in (let _38_3153 = (match ((not ((Microsoft_FStar_Absyn_Syntax.lid_equals modul.Microsoft_FStar_Absyn_Syntax.name Microsoft_FStar_Absyn_Const.prims_lid)))) with
| true -> begin
(env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.push msg)
end
| false -> begin
()
end)
in (let env = (Microsoft_FStar_Tc_Env.set_current_module env modul.Microsoft_FStar_Absyn_Syntax.name)
in (let _38_3159 = (tc_decls true env modul.Microsoft_FStar_Absyn_Syntax.declarations modul.Microsoft_FStar_Absyn_Syntax.is_deserialized)
in (match (_38_3159) with
| (ses, non_private_decls, env) -> begin
((let _38_3160 = modul
in {Microsoft_FStar_Absyn_Syntax.name = _38_3160.Microsoft_FStar_Absyn_Syntax.name; Microsoft_FStar_Absyn_Syntax.declarations = ses; Microsoft_FStar_Absyn_Syntax.exports = _38_3160.Microsoft_FStar_Absyn_Syntax.exports; Microsoft_FStar_Absyn_Syntax.is_interface = _38_3160.Microsoft_FStar_Absyn_Syntax.is_interface; Microsoft_FStar_Absyn_Syntax.is_deserialized = _38_3160.Microsoft_FStar_Absyn_Syntax.is_deserialized}), non_private_decls, env)
end))))))))

let tc_more_partial_modul = (fun ( env ) ( modul ) ( decls ) -> (let _38_3168 = (tc_decls true env decls false)
in (match (_38_3168) with
| (ses, non_private_decls, env) -> begin
(let modul = (let _38_3169 = modul
in {Microsoft_FStar_Absyn_Syntax.name = _38_3169.Microsoft_FStar_Absyn_Syntax.name; Microsoft_FStar_Absyn_Syntax.declarations = (Support.List.append modul.Microsoft_FStar_Absyn_Syntax.declarations ses); Microsoft_FStar_Absyn_Syntax.exports = _38_3169.Microsoft_FStar_Absyn_Syntax.exports; Microsoft_FStar_Absyn_Syntax.is_interface = _38_3169.Microsoft_FStar_Absyn_Syntax.is_interface; Microsoft_FStar_Absyn_Syntax.is_deserialized = _38_3169.Microsoft_FStar_Absyn_Syntax.is_deserialized})
in (modul, non_private_decls, env))
end)))

let finish_partial_modul = (fun ( env ) ( modul ) ( npds ) -> (let exports = (get_exports env modul npds)
in (let modul = (let _38_3176 = modul
in {Microsoft_FStar_Absyn_Syntax.name = _38_3176.Microsoft_FStar_Absyn_Syntax.name; Microsoft_FStar_Absyn_Syntax.declarations = _38_3176.Microsoft_FStar_Absyn_Syntax.declarations; Microsoft_FStar_Absyn_Syntax.exports = exports; Microsoft_FStar_Absyn_Syntax.is_interface = modul.Microsoft_FStar_Absyn_Syntax.is_interface; Microsoft_FStar_Absyn_Syntax.is_deserialized = modul.Microsoft_FStar_Absyn_Syntax.is_deserialized})
in (let env = (Microsoft_FStar_Tc_Env.finish_module env modul)
in (let _38_3186 = (match ((not ((Microsoft_FStar_Absyn_Syntax.lid_equals modul.Microsoft_FStar_Absyn_Syntax.name Microsoft_FStar_Absyn_Const.prims_lid)))) with
| true -> begin
(let _38_3180 = (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.pop (Support.String.strcat "Ending modul " modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str))
in (let _38_3182 = (match (((not (modul.Microsoft_FStar_Absyn_Syntax.is_interface)) || (let _109_1307 = (Support.ST.read Microsoft_FStar_Options.admit_fsi)
in (Support.List.contains modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str _109_1307)))) with
| true -> begin
(env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.encode_modul env modul)
end
| false -> begin
()
end)
in (let _38_3184 = (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.refresh ())
in (let _109_1308 = (Microsoft_FStar_Options.reset_options ())
in (Support.All.pipe_right _109_1308 Support.Prims.ignore)))))
end
| false -> begin
()
end)
in (modul, env))))))

let tc_modul = (fun ( env ) ( modul ) -> (let _38_3193 = (tc_partial_modul env modul)
in (match (_38_3193) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

let add_modul_to_tcenv = (fun ( en ) ( m ) -> (let do_sigelt = (fun ( en ) ( elt ) -> (let env = (Microsoft_FStar_Tc_Env.push_sigelt en elt)
in (let _38_3200 = (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.encode_sig env elt)
in env)))
in (let en = (Microsoft_FStar_Tc_Env.set_current_module en m.Microsoft_FStar_Absyn_Syntax.name)
in (let _109_1321 = (Support.List.fold_left do_sigelt en m.Microsoft_FStar_Absyn_Syntax.exports)
in (Microsoft_FStar_Tc_Env.finish_module _109_1321 m)))))

let check_module = (fun ( env ) ( m ) -> (let _38_3205 = (match (((let _109_1326 = (Support.ST.read Microsoft_FStar_Options.debug)
in (Support.List.length _109_1326)) <> 0)) with
| true -> begin
(let _109_1327 = (Microsoft_FStar_Absyn_Print.sli m.Microsoft_FStar_Absyn_Syntax.name)
in (Support.Microsoft.FStar.Util.fprint2 "Checking %s: %s\n" (match (m.Microsoft_FStar_Absyn_Syntax.is_interface) with
| true -> begin
"i\'face"
end
| false -> begin
"module"
end) _109_1327))
end
| false -> begin
()
end)
in (let _38_3218 = (match (m.Microsoft_FStar_Absyn_Syntax.is_deserialized) with
| true -> begin
(let env' = (add_modul_to_tcenv env m)
in (m, env'))
end
| false -> begin
(let _38_3210 = (tc_modul env m)
in (match (_38_3210) with
| (m, env) -> begin
(let _38_3214 = (match ((Support.ST.read Microsoft_FStar_Options.serialize_mods)) with
| true -> begin
(let c_file_name = (let _109_1333 = (let _109_1332 = (let _109_1330 = (let _109_1329 = (let _109_1328 = (Microsoft_FStar_Options.get_fstar_home ())
in (Support.String.strcat _109_1328 "/"))
in (Support.String.strcat _109_1329 Microsoft_FStar_Options.cache_dir))
in (Support.String.strcat _109_1330 "/"))
in (let _109_1331 = (Microsoft_FStar_Absyn_Syntax.text_of_lid m.Microsoft_FStar_Absyn_Syntax.name)
in (Support.String.strcat _109_1332 _109_1331)))
in (Support.String.strcat _109_1333 ".cache"))
in (let _38_3212 = (let _109_1336 = (let _109_1335 = (let _109_1334 = (Microsoft_FStar_Absyn_Syntax.text_of_lid m.Microsoft_FStar_Absyn_Syntax.name)
in (Support.String.strcat "Serializing module " _109_1334))
in (Support.String.strcat _109_1335 "\n"))
in (Support.Microsoft.FStar.Util.print_string _109_1336))
in (let _109_1337 = (Support.Microsoft.FStar.Util.get_owriter c_file_name)
in (Microsoft_FStar_Absyn_SSyntax.serialize_modul _109_1337 m))))
end
| false -> begin
()
end)
in (m, env))
end))
end)
in (match (_38_3218) with
| (m, env) -> begin
(let _38_3219 = (match ((Microsoft_FStar_Options.should_dump m.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
(let _109_1338 = (Microsoft_FStar_Absyn_Print.modul_to_string m)
in (Support.Microsoft.FStar.Util.fprint1 "%s\n" _109_1338))
end
| false -> begin
()
end)
in ((m)::[], env))
end))))




