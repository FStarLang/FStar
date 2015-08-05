
let syn' = (fun ( env ) ( k ) -> (let _68_15987 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Syntax.syn _68_15987 (Some (k)))))

let log = (fun ( env ) -> ((Support.ST.read Microsoft_FStar_Options.log_types) && (not ((let _68_15990 = (Microsoft_FStar_Tc_Env.current_module env)
in (Microsoft_FStar_Absyn_Syntax.lid_equals Microsoft_FStar_Absyn_Const.prims_lid _68_15990))))))

let rng = (fun ( env ) -> (Microsoft_FStar_Tc_Env.get_range env))

let instantiate_both = (fun ( env ) -> (let _36_24 = env
in {Microsoft_FStar_Tc_Env.solver = _36_24.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_24.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_24.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_24.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_24.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_24.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_24.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_24.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_24.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = true; Microsoft_FStar_Tc_Env.instantiate_vargs = true; Microsoft_FStar_Tc_Env.effects = _36_24.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_24.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _36_24.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _36_24.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_24.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = _36_24.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = _36_24.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_24.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_24.Microsoft_FStar_Tc_Env.default_effects}))

let no_inst = (fun ( env ) -> (let _36_27 = env
in {Microsoft_FStar_Tc_Env.solver = _36_27.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_27.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_27.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_27.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_27.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_27.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_27.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_27.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_27.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = false; Microsoft_FStar_Tc_Env.instantiate_vargs = false; Microsoft_FStar_Tc_Env.effects = _36_27.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_27.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _36_27.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _36_27.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_27.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = _36_27.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = _36_27.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_27.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_27.Microsoft_FStar_Tc_Env.default_effects}))

let mk_lex_list = (fun ( vs ) -> (Support.List.fold_right (fun ( v ) ( tl ) -> (let r = (match ((tl.Microsoft_FStar_Absyn_Syntax.pos = Microsoft_FStar_Absyn_Syntax.dummyRange)) with
| true -> begin
v.Microsoft_FStar_Absyn_Syntax.pos
end
| false -> begin
(Support.Microsoft.FStar.Range.union_ranges v.Microsoft_FStar_Absyn_Syntax.pos tl.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (let _68_16010 = (let _68_16009 = (let _68_16008 = (let _68_16003 = (let _68_16002 = (Microsoft_FStar_Tc_Recheck.recompute_typ v)
in (Support.Prims.pipe_left (fun ( _68_16001 ) -> Support.Microsoft.FStar.Util.Inl (_68_16001)) _68_16002))
in (_68_16003, Some (Microsoft_FStar_Absyn_Syntax.Implicit)))
in (let _68_16007 = (let _68_16006 = (Microsoft_FStar_Absyn_Syntax.varg v)
in (let _68_16005 = (let _68_16004 = (Microsoft_FStar_Absyn_Syntax.varg tl)
in (_68_16004)::[])
in (_68_16006)::_68_16005))
in (_68_16008)::_68_16007))
in (Microsoft_FStar_Absyn_Util.lex_pair, _68_16009))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _68_16010 (Some (Microsoft_FStar_Absyn_Util.lex_t)) r)))) vs Microsoft_FStar_Absyn_Util.lex_top))

let is_eq = (fun ( _36_1 ) -> (match (_36_1) with
| Some (Microsoft_FStar_Absyn_Syntax.Equality) -> begin
true
end
| _36_37 -> begin
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

let norm_t = (fun ( env ) ( t ) -> (let _68_16023 = (steps env)
in (Microsoft_FStar_Tc_Normalize.norm_typ _68_16023 env t)))

let norm_k = (fun ( env ) ( k ) -> (let _68_16028 = (steps env)
in (Microsoft_FStar_Tc_Normalize.norm_kind _68_16028 env k)))

let norm_c = (fun ( env ) ( c ) -> (let _68_16033 = (steps env)
in (Microsoft_FStar_Tc_Normalize.norm_comp _68_16033 env c)))

let fxv_check = (fun ( head ) ( env ) ( kt ) ( fvs ) -> (let rec aux = (fun ( norm ) ( kt ) -> (match ((Support.Microsoft.FStar.Util.set_is_empty fvs)) with
| true -> begin
()
end
| false -> begin
(let fvs' = (match (kt) with
| Support.Microsoft.FStar.Util.Inl (k) -> begin
(let _68_16052 = (match (norm) with
| true -> begin
(norm_k env k)
end
| false -> begin
k
end)
in (Microsoft_FStar_Absyn_Util.freevars_kind _68_16052))
end
| Support.Microsoft.FStar.Util.Inr (t) -> begin
(let _68_16053 = (match (norm) with
| true -> begin
(norm_t env t)
end
| false -> begin
t
end)
in (Microsoft_FStar_Absyn_Util.freevars_typ _68_16053))
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
(let fail = (fun ( _36_61 ) -> (match (()) with
| () -> begin
(let escaping = (let _68_16058 = (let _68_16057 = (Support.Microsoft.FStar.Util.set_elements a)
in (Support.Prims.pipe_right _68_16057 (Support.List.map (fun ( x ) -> (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)))))
in (Support.Prims.pipe_right _68_16058 (Support.String.concat ", ")))
in (let msg = (match (((Support.Microsoft.FStar.Util.set_count a) > 1)) with
| true -> begin
(let _68_16059 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env head)
in (Support.Microsoft.FStar.Util.format2 "Bound variables \'{%s}\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" escaping _68_16059))
end
| false -> begin
(let _68_16060 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env head)
in (Support.Microsoft.FStar.Util.format2 "Bound variable \'%s\' in the type of \'%s\' escapes because of impure applications; add explicit let-bindings" escaping _68_16060))
end)
in (let _68_16063 = (let _68_16062 = (let _68_16061 = (Microsoft_FStar_Tc_Env.get_range env)
in (msg, _68_16061))
in Microsoft_FStar_Absyn_Syntax.Error (_68_16062))
in (raise (_68_16063)))))
end))
in (match (kt) with
| Support.Microsoft.FStar.Util.Inl (k) -> begin
(let s = (Microsoft_FStar_Tc_Util.new_kvar env)
in (match ((Microsoft_FStar_Tc_Rel.try_keq env k s)) with
| Some (g) -> begin
(Microsoft_FStar_Tc_Rel.try_discharge_guard env g)
end
| _36_71 -> begin
(fail ())
end))
end
| Support.Microsoft.FStar.Util.Inr (t) -> begin
(let s = (Microsoft_FStar_Tc_Util.new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (match ((Microsoft_FStar_Tc_Rel.try_teq env t s)) with
| Some (g) -> begin
(Microsoft_FStar_Tc_Rel.try_discharge_guard env g)
end
| _36_78 -> begin
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

let maybe_make_subst = (fun ( _36_2 ) -> (match (_36_2) with
| Support.Microsoft.FStar.Util.Inl ((Some (a), t)) -> begin
(Support.Microsoft.FStar.Util.Inl ((a, t)))::[]
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), e)) -> begin
(Support.Microsoft.FStar.Util.Inr ((x, e)))::[]
end
| _36_99 -> begin
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
(let _68_16074 = (let _68_16073 = (let _68_16072 = (Microsoft_FStar_Absyn_Util.btvar_to_typ b)
in (a.Microsoft_FStar_Absyn_Syntax.v, _68_16072))
in Support.Microsoft.FStar.Util.Inl (_68_16073))
in (_68_16074)::s)
end)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(match ((Microsoft_FStar_Absyn_Util.bvar_eq x y)) with
| true -> begin
s
end
| false -> begin
(let _68_16077 = (let _68_16076 = (let _68_16075 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (x.Microsoft_FStar_Absyn_Syntax.v, _68_16075))
in Support.Microsoft.FStar.Util.Inr (_68_16076))
in (_68_16077)::s)
end)
end
| _36_114 -> begin
(failwith ("impossible"))
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
| _36_129 -> begin
(failwith ("Impossible"))
end)
end))

let set_lcomp_result = (fun ( lc ) ( t ) -> (let _36_132 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _36_132.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = t; Microsoft_FStar_Absyn_Syntax.cflags = _36_132.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = (fun ( _36_134 ) -> (match (()) with
| () -> begin
(let _68_16086 = (lc.Microsoft_FStar_Absyn_Syntax.comp ())
in (Microsoft_FStar_Absyn_Util.set_result_typ _68_16086 t))
end))}))

let value_check_expected_typ = (fun ( env ) ( e ) ( tlc ) -> (let lc = (match (tlc) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _68_16093 = (match ((not ((Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t)))) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Total t)
end
| false -> begin
(Microsoft_FStar_Tc_Util.return_value env t e)
end)
in (Microsoft_FStar_Tc_Util.lcomp_of_comp _68_16093))
end
| Support.Microsoft.FStar.Util.Inr (lc) -> begin
lc
end)
in (let t = lc.Microsoft_FStar_Absyn_Syntax.res_typ
in (let _36_158 = (match ((Microsoft_FStar_Tc_Env.expected_typ env)) with
| None -> begin
(e, lc, Microsoft_FStar_Tc_Rel.trivial_guard)
end
| Some (t') -> begin
(let _36_147 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_16095 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (let _68_16094 = (Microsoft_FStar_Absyn_Print.typ_to_string t')
in (Support.Microsoft.FStar.Util.fprint2 "Computed return type %s; expected type %s\n" _68_16095 _68_16094)))
end
| false -> begin
()
end)
in (let _36_151 = (Microsoft_FStar_Tc_Util.check_and_ascribe env e t t')
in (match (_36_151) with
| (e, g) -> begin
(let _36_154 = (let _68_16101 = (Support.Prims.pipe_left (fun ( _68_16100 ) -> Some (_68_16100)) (Microsoft_FStar_Tc_Errors.subtyping_failed env t t'))
in (Microsoft_FStar_Tc_Util.strengthen_precondition _68_16101 env e lc g))
in (match (_36_154) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))
end)))
end)
in (match (_36_158) with
| (e, lc, g) -> begin
(let _36_159 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_16102 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string lc)
in (Support.Microsoft.FStar.Util.fprint1 "Return comp type is %s\n" _68_16102))
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

let check_expected_effect = (fun ( env ) ( copt ) ( _36_171 ) -> (match (_36_171) with
| (e, c) -> begin
(let expected_c_opt = (match (copt) with
| Some (_36_173) -> begin
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
(let _68_16115 = (norm_c env c)
in (e, _68_16115, Microsoft_FStar_Tc_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(let _36_187 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_16118 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_16117 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (let _68_16116 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string expected_c)
in (Support.Microsoft.FStar.Util.fprint3 "(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _68_16118 _68_16117 _68_16116))))
end
| false -> begin
()
end)
in (let c = (norm_c env c)
in (let expected_c' = (let _68_16119 = (Support.Prims.pipe_left Microsoft_FStar_Tc_Util.lcomp_of_comp expected_c)
in (Microsoft_FStar_Tc_Util.refresh_comp_label env true _68_16119))
in (let _36_195 = (let _68_16120 = (expected_c'.Microsoft_FStar_Absyn_Syntax.comp ())
in (Support.Prims.pipe_left (Microsoft_FStar_Tc_Util.check_comp env e c) _68_16120))
in (match (_36_195) with
| (e, _36_193, g) -> begin
(let _36_196 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_16122 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_16121 = (Microsoft_FStar_Tc_Rel.guard_to_string env g)
in (Support.Microsoft.FStar.Util.fprint2 "(%s) DONE check_expected_effect; guard is: %s\n" _68_16122 _68_16121)))
end
| false -> begin
()
end)
in (e, expected_c, g))
end)))))
end))
end))

let no_logical_guard = (fun ( env ) ( _36_202 ) -> (match (_36_202) with
| (te, kt, f) -> begin
(match ((Microsoft_FStar_Tc_Rel.guard_f f)) with
| Microsoft_FStar_Tc_Rel.Trivial -> begin
(te, kt, f)
end
| Microsoft_FStar_Tc_Rel.NonTrivial (f) -> begin
(let _68_16128 = (let _68_16127 = (let _68_16126 = (Microsoft_FStar_Tc_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _68_16125 = (Microsoft_FStar_Tc_Env.get_range env)
in (_68_16126, _68_16125)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_16127))
in (raise (_68_16128)))
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
(let _68_16135 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint1 "Expected type is %s" _68_16135))
end))

let with_implicits = (fun ( imps ) ( _36_220 ) -> (match (_36_220) with
| (e, l, g) -> begin
(e, l, (let _36_221 = g
in {Microsoft_FStar_Tc_Rel.guard_f = _36_221.Microsoft_FStar_Tc_Rel.guard_f; Microsoft_FStar_Tc_Rel.deferred = _36_221.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = (Support.List.append imps g.Microsoft_FStar_Tc_Rel.implicits)}))
end))

let add_implicit = (fun ( u ) ( g ) -> (let _36_225 = g
in {Microsoft_FStar_Tc_Rel.guard_f = _36_225.Microsoft_FStar_Tc_Rel.guard_f; Microsoft_FStar_Tc_Rel.deferred = _36_225.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = (u)::g.Microsoft_FStar_Tc_Rel.implicits}))

let rec tc_kind = (fun ( env ) ( k ) -> (let k = (Microsoft_FStar_Absyn_Util.compress_kind k)
in (let w = (fun ( f ) -> (f k.Microsoft_FStar_Absyn_Syntax.pos))
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Kind_lam (_)) | (Microsoft_FStar_Absyn_Syntax.Kind_delayed (_)) -> begin
(failwith ("impossible"))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) -> begin
(k, Microsoft_FStar_Tc_Rel.trivial_guard)
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((u, args)) -> begin
(let _36_244 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _68_16186 = (Support.Microsoft.FStar.Range.string_of_range k.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_16185 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (Support.Microsoft.FStar.Util.fprint2 "(%s) - Checking kind %s" _68_16186 _68_16185)))
end
| false -> begin
()
end)
in (let _36_249 = (Microsoft_FStar_Tc_Env.clear_expected_typ env)
in (match (_36_249) with
| (env, _36_248) -> begin
(let _36_252 = (tc_args env args)
in (match (_36_252) with
| (args, g) -> begin
(let _68_16188 = (Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Kind_uvar (u, args)))
in (_68_16188, g))
end))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev (((l, args), {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_unknown; Microsoft_FStar_Absyn_Syntax.tk = _36_263; Microsoft_FStar_Absyn_Syntax.pos = _36_261; Microsoft_FStar_Absyn_Syntax.fvs = _36_259; Microsoft_FStar_Absyn_Syntax.uvs = _36_257})) -> begin
(let _36_272 = (Microsoft_FStar_Tc_Env.lookup_kind_abbrev env l)
in (match (_36_272) with
| (_36_269, binders, body) -> begin
(let _36_275 = (tc_args env args)
in (match (_36_275) with
| (args, g) -> begin
(match (((Support.List.length binders) <> (Support.List.length args))) with
| true -> begin
(let _68_16192 = (let _68_16191 = (let _68_16190 = (let _68_16189 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.String.strcat "Unexpected number of arguments to kind abbreviation " _68_16189))
in (_68_16190, k.Microsoft_FStar_Absyn_Syntax.pos))
in Microsoft_FStar_Absyn_Syntax.Error (_68_16191))
in (raise (_68_16192)))
end
| false -> begin
(let _36_308 = (Support.List.fold_left2 (fun ( _36_279 ) ( b ) ( a ) -> (match (_36_279) with
| (subst, args, guards) -> begin
(match (((Support.Prims.fst b), (Support.Prims.fst a))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (t)) -> begin
(let _36_289 = (let _68_16196 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (tc_typ_check env t _68_16196))
in (match (_36_289) with
| (t, g) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::subst
in (let _68_16198 = (let _68_16197 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (_68_16197)::args)
in (subst, _68_16198, (g)::guards)))
end))
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (e)) -> begin
(let env = (let _68_16199 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Tc_Env.set_expected_typ env _68_16199))
in (let _36_301 = (tc_ghost_exp env e)
in (match (_36_301) with
| (e, _36_299, g) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, e)))::subst
in (let _68_16201 = (let _68_16200 = (Microsoft_FStar_Absyn_Syntax.varg e)
in (_68_16200)::args)
in (subst, _68_16201, (g)::guards)))
end)))
end
| _36_304 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Ill-typed argument to kind abbreviation", (Microsoft_FStar_Absyn_Util.range_of_arg a)))))
end)
end)) ([], [], []) binders args)
in (match (_36_308) with
| (subst, args, guards) -> begin
(let args = (Support.List.rev args)
in (let k = (Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown)))
in (let k' = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.DeltaHard)::[]) env k)
in (let k = (Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), k')))
in (let _68_16204 = (Support.List.fold_left Microsoft_FStar_Tc_Rel.conj_guard g guards)
in (k', _68_16204))))))
end))
end)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((kabr, k)) -> begin
(let _36_319 = (tc_kind env k)
in (match (_36_319) with
| (k, f) -> begin
(let _36_322 = (Support.Prims.pipe_left (tc_args env) (Support.Prims.snd kabr))
in (match (_36_322) with
| (args, g) -> begin
(let kabr = ((Support.Prims.fst kabr), args)
in (let kk = (Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Kind_abbrev (kabr, k)))
in (let _68_16206 = (Microsoft_FStar_Tc_Rel.conj_guard f g)
in (kk, _68_16206))))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _36_332 = (tc_binders env bs)
in (match (_36_332) with
| (bs, env, g) -> begin
(let _36_335 = (tc_kind env k)
in (match (_36_335) with
| (k, f) -> begin
(let f = (Microsoft_FStar_Tc_Rel.close_guard bs f)
in (let _68_16209 = (Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, k)))
in (let _68_16208 = (Microsoft_FStar_Tc_Rel.conj_guard g f)
in (_68_16209, _68_16208))))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(let _68_16210 = (Microsoft_FStar_Tc_Util.new_kvar env)
in (_68_16210, Microsoft_FStar_Tc_Rel.trivial_guard))
end))))
and tc_vbinder = (fun ( env ) ( x ) -> (let _36_342 = (tc_typ_check env x.Microsoft_FStar_Absyn_Syntax.sort Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_36_342) with
| (t, g) -> begin
(let x = (let _36_343 = x
in {Microsoft_FStar_Absyn_Syntax.v = _36_343.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _36_343.Microsoft_FStar_Absyn_Syntax.p})
in (let env' = (let _68_16213 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (maybe_push_binding env _68_16213))
in (x, env', g)))
end)))
and tc_binders = (fun ( env ) ( bs ) -> (let rec aux = (fun ( env ) ( bs ) -> (match (bs) with
| [] -> begin
([], env, Microsoft_FStar_Tc_Rel.trivial_guard)
end
| (b, imp)::bs -> begin
(match (b) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _36_362 = (tc_kind env a.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_36_362) with
| (k, g) -> begin
(let b = (Support.Microsoft.FStar.Util.Inl ((let _36_363 = a
in {Microsoft_FStar_Absyn_Syntax.v = _36_363.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _36_363.Microsoft_FStar_Absyn_Syntax.p})), imp)
in (let env' = (maybe_push_binding env b)
in (let _36_370 = (aux env' bs)
in (match (_36_370) with
| (bs, env', g') -> begin
(let _68_16221 = (let _68_16220 = (Microsoft_FStar_Tc_Rel.close_guard ((b)::[]) g')
in (Microsoft_FStar_Tc_Rel.conj_guard g _68_16220))
in ((b)::bs, env', _68_16221))
end))))
end))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _36_376 = (tc_vbinder env x)
in (match (_36_376) with
| (x, env', g) -> begin
(let b = (Support.Microsoft.FStar.Util.Inr (x), imp)
in (let _36_381 = (aux env' bs)
in (match (_36_381) with
| (bs, env', g') -> begin
(let _68_16223 = (let _68_16222 = (Microsoft_FStar_Tc_Rel.close_guard ((b)::[]) g')
in (Microsoft_FStar_Tc_Rel.conj_guard g _68_16222))
in ((b)::bs, env', _68_16223))
end)))
end))
end)
end))
in (aux env bs)))
and tc_args = (fun ( env ) ( args ) -> (Support.List.fold_right (fun ( _36_386 ) ( _36_389 ) -> (match ((_36_386, _36_389)) with
| ((arg, imp), (args, g)) -> begin
(match (arg) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _36_396 = (tc_typ env t)
in (match (_36_396) with
| (t, _36_394, g') -> begin
(let _68_16228 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (((Support.Microsoft.FStar.Util.Inl (t), imp))::args, _68_16228))
end))
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(let _36_403 = (tc_ghost_exp env e)
in (match (_36_403) with
| (e, _36_401, g') -> begin
(let _68_16229 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (((Support.Microsoft.FStar.Util.Inr (e), imp))::args, _68_16229))
end))
end)
end)) args ([], Microsoft_FStar_Tc_Rel.trivial_guard)))
and tc_comp = (fun ( env ) ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(let _36_410 = (tc_typ_check env t Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_36_410) with
| (t, g) -> begin
(let _68_16232 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (_68_16232, g))
end))
end
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
(let kc = (Microsoft_FStar_Tc_Env.lookup_effect_lid env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let head = (Microsoft_FStar_Absyn_Util.ftv c.Microsoft_FStar_Absyn_Syntax.effect_name kc)
in (let tc = (let _68_16235 = (let _68_16234 = (let _68_16233 = (Microsoft_FStar_Absyn_Syntax.targ c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (_68_16233)::c.Microsoft_FStar_Absyn_Syntax.effect_args)
in (head, _68_16234))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_16235 None c.Microsoft_FStar_Absyn_Syntax.result_typ.Microsoft_FStar_Absyn_Syntax.pos))
in (let _36_418 = (tc_typ_check env tc Microsoft_FStar_Absyn_Syntax.keffect)
in (match (_36_418) with
| (tc, f) -> begin
(let _36_422 = (Microsoft_FStar_Absyn_Util.head_and_args tc)
in (match (_36_422) with
| (_36_420, args) -> begin
(let _36_434 = (match (args) with
| (Support.Microsoft.FStar.Util.Inl (res), _36_427)::args -> begin
(res, args)
end
| _36_431 -> begin
(failwith ("Impossible"))
end)
in (match (_36_434) with
| (res, args) -> begin
(let _36_450 = (let _68_16237 = (Support.Prims.pipe_right c.Microsoft_FStar_Absyn_Syntax.flags (Support.List.map (fun ( _36_3 ) -> (match (_36_3) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _36_441 = (Microsoft_FStar_Tc_Env.clear_expected_typ env)
in (match (_36_441) with
| (env, _36_440) -> begin
(let _36_446 = (tc_ghost_exp env e)
in (match (_36_446) with
| (e, _36_444, g) -> begin
(Microsoft_FStar_Absyn_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, Microsoft_FStar_Tc_Rel.trivial_guard)
end))))
in (Support.Prims.pipe_right _68_16237 Support.List.unzip))
in (match (_36_450) with
| (flags, guards) -> begin
(let _68_16239 = (Microsoft_FStar_Absyn_Syntax.mk_Comp (let _36_451 = c
in {Microsoft_FStar_Absyn_Syntax.effect_name = _36_451.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = res; Microsoft_FStar_Absyn_Syntax.effect_args = args; Microsoft_FStar_Absyn_Syntax.flags = _36_451.Microsoft_FStar_Absyn_Syntax.flags}))
in (let _68_16238 = (Support.List.fold_left Microsoft_FStar_Tc_Rel.conj_guard f guards)
in (_68_16239, _68_16238)))
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
in (let a = (let _36_463 = a
in {Microsoft_FStar_Absyn_Syntax.v = _36_463.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _36_463.Microsoft_FStar_Absyn_Syntax.p})
in (let t = (Support.Prims.pipe_left (w k) (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar a))
in (let _36_470 = (Microsoft_FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_36_470) with
| (t, k, implicits) -> begin
(Support.Prims.pipe_left (with_implicits implicits) (t, k, Microsoft_FStar_Tc_Rel.trivial_guard))
end)))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (i) when (Microsoft_FStar_Absyn_Syntax.lid_equals i.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.eqT_lid) -> begin
(let k = (Microsoft_FStar_Tc_Util.new_kvar env)
in (let qk = (Microsoft_FStar_Absyn_Util.eqT_k k)
in (let i = (let _36_475 = i
in {Microsoft_FStar_Absyn_Syntax.v = _36_475.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = qk; Microsoft_FStar_Absyn_Syntax.p = _36_475.Microsoft_FStar_Absyn_Syntax.p})
in (let _68_16262 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.Microsoft_FStar_Absyn_Syntax.pos)
in (_68_16262, qk, Microsoft_FStar_Tc_Rel.trivial_guard)))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (i) when ((Microsoft_FStar_Absyn_Syntax.lid_equals i.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.allTyp_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals i.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.exTyp_lid)) -> begin
(let k = (Microsoft_FStar_Tc_Util.new_kvar env)
in (let qk = (Microsoft_FStar_Absyn_Util.allT_k k)
in (let i = (let _36_482 = i
in {Microsoft_FStar_Absyn_Syntax.v = _36_482.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = qk; Microsoft_FStar_Absyn_Syntax.p = _36_482.Microsoft_FStar_Absyn_Syntax.p})
in (let _68_16263 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.Microsoft_FStar_Absyn_Syntax.pos)
in (_68_16263, qk, Microsoft_FStar_Tc_Rel.trivial_guard)))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (i) -> begin
(let k = (match ((Microsoft_FStar_Tc_Env.try_lookup_effect_lid env i.Microsoft_FStar_Absyn_Syntax.v)) with
| Some (k) -> begin
k
end
| _36_490 -> begin
(Microsoft_FStar_Tc_Env.lookup_typ_lid env i.Microsoft_FStar_Absyn_Syntax.v)
end)
in (let i = (let _36_492 = i
in {Microsoft_FStar_Absyn_Syntax.v = _36_492.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _36_492.Microsoft_FStar_Absyn_Syntax.p})
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_const i (Some (k)) t.Microsoft_FStar_Absyn_Syntax.pos)
in (let _36_499 = (Microsoft_FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_36_499) with
| (t, k, imps) -> begin
(Support.Prims.pipe_left (with_implicits imps) (t, k, Microsoft_FStar_Tc_Rel.trivial_guard))
end)))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, cod)) -> begin
(let _36_507 = (tc_binders env bs)
in (match (_36_507) with
| (bs, env, g) -> begin
(let _36_510 = (tc_comp env cod)
in (match (_36_510) with
| (cod, f) -> begin
(let t = (Support.Prims.pipe_left (w Microsoft_FStar_Absyn_Syntax.ktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, cod)))
in (let _36_550 = (match ((Microsoft_FStar_Absyn_Util.is_smt_lemma t)) with
| true -> begin
(match (cod.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp ({Microsoft_FStar_Absyn_Syntax.effect_name = _36_533; Microsoft_FStar_Absyn_Syntax.result_typ = _36_531; Microsoft_FStar_Absyn_Syntax.effect_args = (Support.Microsoft.FStar.Util.Inl (pre), _36_527)::(Support.Microsoft.FStar.Util.Inl (post), _36_522)::(Support.Microsoft.FStar.Util.Inr (pats), _36_517)::[]; Microsoft_FStar_Absyn_Syntax.flags = _36_513}) -> begin
(let fvs = (Microsoft_FStar_Absyn_Util.freevars_exp pats)
in (match ((Support.Prims.pipe_right bs (Support.Microsoft.FStar.Util.find_opt (fun ( _36_540 ) -> (match (_36_540) with
| (b, _36_539) -> begin
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
(let _68_16268 = (let _68_16267 = (Microsoft_FStar_Absyn_Print.binder_to_string b)
in (Support.Microsoft.FStar.Util.format1 "Pattern misses at least one bound variables: %s" _68_16267))
in (Microsoft_FStar_Tc_Errors.warn t.Microsoft_FStar_Absyn_Syntax.pos _68_16268))
end))
end
| _36_549 -> begin
()
end)
end
| false -> begin
()
end)
in (let _68_16270 = (let _68_16269 = (Microsoft_FStar_Tc_Rel.close_guard bs f)
in (Microsoft_FStar_Tc_Rel.conj_guard g _68_16269))
in (t, Microsoft_FStar_Absyn_Syntax.ktype, _68_16270))))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, t)) -> begin
(let _36_559 = (tc_binders env bs)
in (match (_36_559) with
| (bs, env, g) -> begin
(let _36_563 = (tc_typ env t)
in (match (_36_563) with
| (t, k, f) -> begin
(let k = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, k) top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_16275 = (Support.Prims.pipe_left (w k) (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, t)))
in (let _68_16274 = (let _68_16273 = (Microsoft_FStar_Tc_Rel.close_guard bs f)
in (Support.Prims.pipe_left (Microsoft_FStar_Tc_Rel.conj_guard g) _68_16273))
in (_68_16275, k, _68_16274))))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, phi)) -> begin
(let _36_572 = (tc_vbinder env x)
in (match (_36_572) with
| (x, env, f1) -> begin
(let _36_576 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_16278 = (Support.Microsoft.FStar.Range.string_of_range top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_16277 = (Microsoft_FStar_Absyn_Print.typ_to_string phi)
in (let _68_16276 = (match ((Microsoft_FStar_Tc_Env.expected_typ env)) with
| None -> begin
"None"
end
| Some (t) -> begin
(Microsoft_FStar_Absyn_Print.typ_to_string t)
end)
in (Support.Microsoft.FStar.Util.fprint3 "(%s) Checking refinement formula %s; env expects type %s\n" _68_16278 _68_16277 _68_16276))))
end
| false -> begin
()
end)
in (let _36_580 = (tc_typ_check env phi Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_36_580) with
| (phi, f2) -> begin
(let _68_16285 = (Support.Prims.pipe_left (w Microsoft_FStar_Absyn_Syntax.ktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (x, phi)))
in (let _68_16284 = (let _68_16283 = (let _68_16282 = (let _68_16281 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_68_16281)::[])
in (Microsoft_FStar_Tc_Rel.close_guard _68_16282 f2))
in (Microsoft_FStar_Tc_Rel.conj_guard f1 _68_16283))
in (_68_16285, Microsoft_FStar_Absyn_Syntax.ktype, _68_16284)))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(let _36_585 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _68_16288 = (Support.Microsoft.FStar.Range.string_of_range top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_16287 = (Support.Prims.pipe_left Support.Microsoft.FStar.Util.string_of_int (Support.List.length args))
in (let _68_16286 = (Microsoft_FStar_Absyn_Print.typ_to_string top)
in (Support.Microsoft.FStar.Util.fprint3 "(%s) Checking type application (%s): %s\n" _68_16288 _68_16287 _68_16286))))
end
| false -> begin
()
end)
in (let _36_590 = (tc_typ (no_inst env) head)
in (match (_36_590) with
| (head, k1', f1) -> begin
(let args0 = args
in (let k1 = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.WHNF)::(Microsoft_FStar_Tc_Normalize.Beta)::[]) env k1')
in (let _36_593 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _68_16292 = (Support.Microsoft.FStar.Range.string_of_range head.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_16291 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (let _68_16290 = (Microsoft_FStar_Absyn_Print.kind_to_string k1')
in (let _68_16289 = (Microsoft_FStar_Absyn_Print.kind_to_string k1)
in (Support.Microsoft.FStar.Util.fprint4 "(%s) head %s has kind %s ... after norm %s\n" _68_16292 _68_16291 _68_16290 _68_16289)))))
end
| false -> begin
()
end)
in (let check_app = (fun ( _36_596 ) -> (match (()) with
| () -> begin
(match (k1.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_uvar (_36_598) -> begin
(let _36_602 = (tc_args env args)
in (match (_36_602) with
| (args, g) -> begin
(let fvs = (Microsoft_FStar_Absyn_Util.freevars_kind k1)
in (let binders = (Microsoft_FStar_Absyn_Util.binders_of_freevars fvs)
in (let kres = (let _68_16295 = (Microsoft_FStar_Tc_Rel.new_kvar k1.Microsoft_FStar_Absyn_Syntax.pos binders)
in (Support.Prims.pipe_right _68_16295 Support.Prims.fst))
in (let bs = (let _68_16296 = (Microsoft_FStar_Tc_Util.tks_of_args args)
in (Microsoft_FStar_Absyn_Util.null_binders_of_tks _68_16296))
in (let kar = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) k1.Microsoft_FStar_Absyn_Syntax.pos)
in (let _36_608 = (let _68_16297 = (Microsoft_FStar_Tc_Rel.keq env None k1 kar)
in (Support.Prims.pipe_left (Microsoft_FStar_Tc_Util.force_trivial env) _68_16297))
in (kres, args, g)))))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((formals, kres)) -> begin
(let rec check_args = (fun ( outargs ) ( subst ) ( g ) ( formals ) ( args ) -> (match ((formals, args)) with
| ([], []) -> begin
(let _68_16308 = (Microsoft_FStar_Absyn_Util.subst_kind subst kres)
in (_68_16308, (Support.List.rev outargs), g))
end
| (((_, None)::_, (_, Some (Microsoft_FStar_Absyn_Syntax.Implicit))::_)) | (((_, Some (Microsoft_FStar_Absyn_Syntax.Equality))::_, (_, Some (Microsoft_FStar_Absyn_Syntax.Implicit))::_)) -> begin
(let _68_16312 = (let _68_16311 = (let _68_16310 = (let _68_16309 = (Support.List.hd args)
in (Microsoft_FStar_Absyn_Util.range_of_arg _68_16309))
in ("Argument is marked as instantiating an implicit parameter; although the expected parameter is explicit", _68_16310))
in Microsoft_FStar_Absyn_Syntax.Error (_68_16311))
in (raise (_68_16312)))
end
| (((Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest, (_, None)::_)) | (((Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest, [])) -> begin
(let formal = (Support.List.hd formals)
in (let _36_681 = (let _68_16313 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Tc_Util.new_implicit_tvar env _68_16313))
in (match (_36_681) with
| (t, u) -> begin
(let targ = (Support.Microsoft.FStar.Util.Inl (t), Some (Microsoft_FStar_Absyn_Syntax.Implicit))
in (let g = (add_implicit (Support.Microsoft.FStar.Util.Inl (u)) g)
in (let subst = (maybe_extend_subst subst formal targ)
in (check_args ((targ)::outargs) subst g rest args))))
end)))
end
| (((Support.Microsoft.FStar.Util.Inr (x), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest, (_, None)::_)) | (((Support.Microsoft.FStar.Util.Inr (x), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest, [])) -> begin
(let formal = (Support.List.hd formals)
in (let _36_710 = (let _68_16314 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Tc_Util.new_implicit_evar env _68_16314))
in (match (_36_710) with
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
in (let _36_731 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_16316 = (Microsoft_FStar_Absyn_Print.arg_to_string actual)
in (let _68_16315 = (Microsoft_FStar_Absyn_Print.kind_to_string formal_k)
in (Support.Microsoft.FStar.Util.fprint2 "Checking argument %s against expected kind %s\n" _68_16316 _68_16315)))
end
| false -> begin
()
end)
in (let _36_737 = (tc_typ_check (let _36_733 = env
in {Microsoft_FStar_Tc_Env.solver = _36_733.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_733.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_733.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_733.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_733.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_733.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_733.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_733.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_733.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _36_733.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _36_733.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _36_733.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_733.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _36_733.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _36_733.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_733.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = (is_eq aqual); Microsoft_FStar_Tc_Env.is_iface = _36_733.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_733.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_733.Microsoft_FStar_Tc_Env.default_effects}) t formal_k)
in (match (_36_737) with
| (t, g') -> begin
(let _36_738 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_16317 = (Microsoft_FStar_Tc_Rel.guard_to_string env g')
in (Support.Microsoft.FStar.Util.fprint1 ">>>Got guard %s\n" _68_16317))
end
| false -> begin
()
end)
in (let actual = (Support.Microsoft.FStar.Util.Inl (t), imp)
in (let g' = (let _68_16319 = (let _68_16318 = (Microsoft_FStar_Tc_Util.short_circuit_typ (Support.Microsoft.FStar.Util.Inl (head)) outargs)
in (Support.Prims.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula _68_16318))
in (Microsoft_FStar_Tc_Rel.imp_guard _68_16319 g'))
in (let subst = (maybe_extend_subst subst formal actual)
in (let _68_16320 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _68_16320 formals actuals))))))
end))))
end
| ((Support.Microsoft.FStar.Util.Inr (x), aqual), (Support.Microsoft.FStar.Util.Inr (v), imp)) -> begin
(let tx = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let env' = (Microsoft_FStar_Tc_Env.set_expected_typ env tx)
in (let env' = (let _36_754 = env'
in {Microsoft_FStar_Tc_Env.solver = _36_754.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_754.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_754.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_754.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_754.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_754.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_754.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_754.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_754.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _36_754.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _36_754.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _36_754.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_754.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _36_754.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _36_754.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_754.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = (is_eq aqual); Microsoft_FStar_Tc_Env.is_iface = _36_754.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_754.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_754.Microsoft_FStar_Tc_Env.default_effects})
in (let _36_757 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_16322 = (Microsoft_FStar_Absyn_Print.arg_to_string actual)
in (let _68_16321 = (Microsoft_FStar_Absyn_Print.typ_to_string tx)
in (Support.Microsoft.FStar.Util.fprint2 "Checking argument %s against expected type %s\n" _68_16322 _68_16321)))
end
| false -> begin
()
end)
in (let _36_763 = (tc_ghost_exp env' v)
in (match (_36_763) with
| (v, _36_761, g') -> begin
(let actual = (Support.Microsoft.FStar.Util.Inr (v), imp)
in (let g' = (let _68_16324 = (let _68_16323 = (Microsoft_FStar_Tc_Util.short_circuit_typ (Support.Microsoft.FStar.Util.Inl (head)) outargs)
in (Support.Prims.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula _68_16323))
in (Microsoft_FStar_Tc_Rel.imp_guard _68_16324 g'))
in (let subst = (maybe_extend_subst subst formal actual)
in (let _68_16325 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _68_16325 formals actuals)))))
end))))))
end
| ((Support.Microsoft.FStar.Util.Inl (a), _36_770), (Support.Microsoft.FStar.Util.Inr (v), imp)) -> begin
(match (a.Microsoft_FStar_Absyn_Syntax.sort.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
(let tv = (Microsoft_FStar_Absyn_Util.b2t v)
in (let _68_16327 = (let _68_16326 = (Microsoft_FStar_Absyn_Syntax.targ tv)
in (_68_16326)::actuals)
in (check_args outargs subst g ((formal)::formals) _68_16327)))
end
| _36_780 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Expected a type; got an expression", v.Microsoft_FStar_Absyn_Syntax.pos))))
end)
end
| ((Support.Microsoft.FStar.Util.Inr (_36_782), _36_785), (Support.Microsoft.FStar.Util.Inl (_36_788), _36_791)) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Expected an expression; got a type", (Microsoft_FStar_Absyn_Util.range_of_arg actual)))))
end)
end
| (_36_795, []) -> begin
(let _68_16329 = (let _68_16328 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (formals, kres) kres.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Util.subst_kind subst _68_16328))
in (_68_16329, (Support.List.rev outargs), g))
end
| ([], _36_800) -> begin
(let _68_16337 = (let _68_16336 = (let _68_16335 = (let _68_16334 = (let _68_16332 = (let _68_16331 = (Support.Prims.pipe_right outargs (Support.List.filter (fun ( _36_4 ) -> (match (_36_4) with
| (_36_804, Some (Microsoft_FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _36_809 -> begin
true
end))))
in (Support.List.length _68_16331))
in (Support.Prims.pipe_right _68_16332 Support.Microsoft.FStar.Util.string_of_int))
in (let _68_16333 = (Support.Prims.pipe_right (Support.List.length args0) Support.Microsoft.FStar.Util.string_of_int)
in (Support.Microsoft.FStar.Util.format2 "Too many arguments to type; expected %s arguments but got %s" _68_16334 _68_16333)))
in (_68_16335, top.Microsoft_FStar_Absyn_Syntax.pos))
in Microsoft_FStar_Absyn_Syntax.Error (_68_16336))
in (raise (_68_16337)))
end))
in (check_args [] [] f1 formals args))
end
| _36_811 -> begin
(let _68_16340 = (let _68_16339 = (let _68_16338 = (Microsoft_FStar_Tc_Errors.expected_tcon_kind env top k1)
in (_68_16338, top.Microsoft_FStar_Absyn_Syntax.pos))
in Microsoft_FStar_Absyn_Syntax.Error (_68_16339))
in (raise (_68_16340)))
end)
end))
in (match ((let _68_16344 = (let _68_16341 = (Microsoft_FStar_Absyn_Util.compress_typ head)
in _68_16341.Microsoft_FStar_Absyn_Syntax.n)
in (let _68_16343 = (let _68_16342 = (Microsoft_FStar_Absyn_Util.compress_kind k1)
in _68_16342.Microsoft_FStar_Absyn_Syntax.n)
in (_68_16344, _68_16343)))) with
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_36_813), Microsoft_FStar_Absyn_Syntax.Kind_arrow ((formals, k))) when ((Support.List.length args) = (Support.List.length formals)) -> begin
(let result_k = (let s = (Support.List.map2 Microsoft_FStar_Absyn_Util.subst_formal formals args)
in (Microsoft_FStar_Absyn_Util.subst_kind s k))
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (head, args) (Some (result_k)) top.Microsoft_FStar_Absyn_Syntax.pos)
in (t, result_k, Microsoft_FStar_Tc_Rel.trivial_guard)))
end
| _36_824 -> begin
(let _36_828 = (check_app ())
in (match (_36_828) with
| (k, args, g) -> begin
(let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (head, args) (Some (k)) top.Microsoft_FStar_Absyn_Syntax.pos)
in (t, k, g))
end))
end)))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t1, k1)) -> begin
(let _36_836 = (tc_kind env k1)
in (match (_36_836) with
| (k1, f1) -> begin
(let _36_839 = (tc_typ_check env t1 k1)
in (match (_36_839) with
| (t1, f2) -> begin
(let _68_16348 = (Support.Prims.pipe_left (w k1) (Microsoft_FStar_Absyn_Syntax.mk_Typ_ascribed' (t1, k1)))
in (let _68_16347 = (Microsoft_FStar_Tc_Rel.conj_guard f1 f2)
in (_68_16348, k1, _68_16347)))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((u, k1)) when env.Microsoft_FStar_Tc_Env.check_uvars -> begin
(let s = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (s.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((u, k1)) -> begin
(let _36_851 = (tc_kind env k1)
in (match (_36_851) with
| (k1, g) -> begin
(let _36_855 = (Microsoft_FStar_Tc_Rel.new_tvar s.Microsoft_FStar_Absyn_Syntax.pos [] k1)
in (match (_36_855) with
| (_36_853, u') -> begin
(let _36_856 = (Microsoft_FStar_Absyn_Util.unchecked_unify u u')
in (u', k1, g))
end))
end))
end
| _36_859 -> begin
(tc_typ env s)
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((_36_861, k1)) -> begin
(let s = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (s.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((u, k1)) -> begin
(let _36_870 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_16350 = (Microsoft_FStar_Absyn_Print.typ_to_string s)
in (let _68_16349 = (Microsoft_FStar_Absyn_Print.kind_to_string k1)
in (Support.Microsoft.FStar.Util.fprint2 "Admitting un-instantiated uvar %s at kind %s\n" _68_16350 _68_16349)))
end
| false -> begin
()
end)
in (let _68_16353 = (Support.Prims.pipe_left (w k1) (Microsoft_FStar_Absyn_Syntax.mk_Typ_uvar' (u, k1)))
in (_68_16353, k1, Microsoft_FStar_Tc_Rel.trivial_guard)))
end
| _36_873 -> begin
(let _36_874 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_16355 = (Microsoft_FStar_Absyn_Print.typ_to_string s)
in (let _68_16354 = (Microsoft_FStar_Absyn_Print.kind_to_string k1)
in (Support.Microsoft.FStar.Util.fprint2 "Admitting instantiated uvar %s at kind %s\n" _68_16355 _68_16354)))
end
| false -> begin
()
end)
in (s, k1, Microsoft_FStar_Tc_Rel.trivial_guard))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r))) -> begin
(let _36_885 = (tc_typ env t)
in (match (_36_885) with
| (t, k, f) -> begin
(let _68_16356 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r))))
in (_68_16356, k, f))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, r, p))) -> begin
(let _36_896 = (tc_typ env t)
in (match (_36_896) with
| (t, k, f) -> begin
(let _68_16357 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, r, p))))
in (_68_16357, k, f))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, l))) -> begin
(let _36_905 = (tc_typ env t)
in (match (_36_905) with
| (t, k, f) -> begin
(let _68_16358 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, l))))
in (_68_16358, k, f))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((qbody, pats))) -> begin
(let _36_913 = (tc_typ_check env qbody Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_36_913) with
| (quant, f) -> begin
(let _36_916 = (tc_args env pats)
in (match (_36_916) with
| (pats, g) -> begin
(let _68_16361 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((quant, pats))))
in (let _68_16360 = (Microsoft_FStar_Tc_Util.force_tk quant)
in (let _68_16359 = (Microsoft_FStar_Tc_Rel.conj_guard f g)
in (_68_16361, _68_16360, _68_16359))))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(let k = (Microsoft_FStar_Tc_Util.new_kvar env)
in (let t = (Microsoft_FStar_Tc_Util.new_tvar env k)
in (t, k, Microsoft_FStar_Tc_Rel.trivial_guard)))
end
| _36_921 -> begin
(let _68_16363 = (let _68_16362 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format1 "Unexpected type : %s\n" _68_16362))
in (failwith (_68_16363)))
end))))))
and tc_typ_check = (fun ( env ) ( t ) ( k ) -> (let _36_928 = (tc_typ env t)
in (match (_36_928) with
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
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((_36_937, t1)) -> begin
(value_check_expected_typ env e (Support.Microsoft.FStar.Util.Inl (t1)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (Microsoft_FStar_Tc_Env.lookup_bvar env x)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar (let _36_944 = x
in {Microsoft_FStar_Absyn_Syntax.v = _36_944.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _36_944.Microsoft_FStar_Absyn_Syntax.p}) (Some (t)) e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _36_950 = (Microsoft_FStar_Tc_Util.maybe_instantiate env e t)
in (match (_36_950) with
| (e, t, implicits) -> begin
(let tc = (match ((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
Support.Microsoft.FStar.Util.Inl (t)
end
| false -> begin
(let _68_16370 = (let _68_16369 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (Support.Prims.pipe_left Microsoft_FStar_Tc_Util.lcomp_of_comp _68_16369))
in Support.Microsoft.FStar.Util.Inr (_68_16370))
end)
in (let _68_16371 = (value_check_expected_typ env e tc)
in (Support.Prims.pipe_left (with_implicits implicits) _68_16371)))
end))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((v, dc)) -> begin
(let t = (Microsoft_FStar_Tc_Env.lookup_lid env v.Microsoft_FStar_Absyn_Syntax.v)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar ((let _36_957 = v
in {Microsoft_FStar_Absyn_Syntax.v = _36_957.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _36_957.Microsoft_FStar_Absyn_Syntax.p}), dc) (Some (t)) e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _36_963 = (Microsoft_FStar_Tc_Util.maybe_instantiate env e t)
in (match (_36_963) with
| (e, t, implicits) -> begin
(let tc = (match ((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
Support.Microsoft.FStar.Util.Inl (t)
end
| false -> begin
(let _68_16373 = (let _68_16372 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (Support.Prims.pipe_left Microsoft_FStar_Tc_Util.lcomp_of_comp _68_16372))
in Support.Microsoft.FStar.Util.Inr (_68_16373))
end)
in (let is_data_ctor = (fun ( _36_5 ) -> (match (_36_5) with
| (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) | (Some (Microsoft_FStar_Absyn_Syntax.Record_ctor (_))) -> begin
true
end
| _36_973 -> begin
false
end))
in (match (((is_data_ctor dc) && (not ((Microsoft_FStar_Tc_Env.is_datacon env v.Microsoft_FStar_Absyn_Syntax.v))))) with
| true -> begin
(let _68_16379 = (let _68_16378 = (let _68_16377 = (Support.Microsoft.FStar.Util.format1 "Expected a data constructor; got %s" v.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
in (let _68_16376 = (Microsoft_FStar_Tc_Env.get_range env)
in (_68_16377, _68_16376)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_16378))
in (raise (_68_16379)))
end
| false -> begin
(let _68_16380 = (value_check_expected_typ env e tc)
in (Support.Prims.pipe_left (with_implicits implicits) _68_16380))
end)))
end))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let t = (Microsoft_FStar_Tc_Recheck.typing_const e.Microsoft_FStar_Absyn_Syntax.pos c)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c (Some (t)) e.Microsoft_FStar_Absyn_Syntax.pos)
in (value_check_expected_typ env e (Support.Microsoft.FStar.Util.Inl (t)))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let fail = (fun ( msg ) ( t ) -> (let _68_16385 = (let _68_16384 = (let _68_16383 = (Microsoft_FStar_Tc_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_68_16383, top.Microsoft_FStar_Absyn_Syntax.pos))
in Microsoft_FStar_Absyn_Syntax.Error (_68_16384))
in (raise (_68_16385))))
in (let rec expected_function_typ = (fun ( env ) ( t0 ) -> (match (t0) with
| None -> begin
(let _36_994 = (match (env.Microsoft_FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _36_993 -> begin
(failwith ("Impossible"))
end)
in (let _36_999 = (tc_binders env bs)
in (match (_36_999) with
| (bs, envbody, g) -> begin
(None, bs, [], None, envbody, g)
end)))
end
| Some (t) -> begin
(let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (let rec as_function_typ = (fun ( norm ) ( t ) -> (match ((let _68_16394 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _68_16394.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let _36_1028 = (match (env.Microsoft_FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _36_1027 -> begin
(failwith ("Impossible"))
end)
in (let _36_1033 = (tc_binders env bs)
in (match (_36_1033) with
| (bs, envbody, g) -> begin
(let _36_1037 = (Microsoft_FStar_Tc_Env.clear_expected_typ envbody)
in (match (_36_1037) with
| (envbody, _36_1036) -> begin
(Some ((t, true)), bs, [], None, envbody, g)
end))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs', c)) -> begin
(let rec tc_binders = (fun ( _36_1047 ) ( bs_annot ) ( c ) ( bs ) -> (match (_36_1047) with
| (out, env, g, subst) -> begin
(match ((bs_annot, bs)) with
| ([], []) -> begin
(let _68_16403 = (Microsoft_FStar_Absyn_Util.subst_comp subst c)
in ((Support.List.rev out), env, g, _68_16403))
end
| (hdannot::tl_annot, hd::tl) -> begin
(match ((hdannot, hd)) with
| ((Support.Microsoft.FStar.Util.Inl (_36_1062), _36_1065), (Support.Microsoft.FStar.Util.Inr (_36_1068), _36_1071)) -> begin
(let env = (maybe_push_binding env hdannot)
in (tc_binders ((hdannot)::out, env, g, subst) tl_annot c bs))
end
| ((Support.Microsoft.FStar.Util.Inl (a), _36_1078), (Support.Microsoft.FStar.Util.Inl (b), imp)) -> begin
(let ka = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _36_1096 = (match (b.Microsoft_FStar_Absyn_Syntax.sort.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(ka, Microsoft_FStar_Tc_Rel.trivial_guard)
end
| _36_1088 -> begin
(let _36_1091 = (tc_kind env b.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_36_1091) with
| (k, g1) -> begin
(let g2 = (Microsoft_FStar_Tc_Rel.keq env None ka k)
in (let g = (let _68_16404 = (Microsoft_FStar_Tc_Rel.conj_guard g1 g2)
in (Microsoft_FStar_Tc_Rel.conj_guard g _68_16404))
in (k, g)))
end))
end)
in (match (_36_1096) with
| (k, g) -> begin
(let b = (Support.Microsoft.FStar.Util.Inl ((let _36_1097 = b
in {Microsoft_FStar_Absyn_Syntax.v = _36_1097.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _36_1097.Microsoft_FStar_Absyn_Syntax.p})), imp)
in (let env = (maybe_push_binding env b)
in (let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders ((b)::out, env, g, subst) tl_annot c tl))))
end)))
end
| ((Support.Microsoft.FStar.Util.Inr (x), _36_1105), (Support.Microsoft.FStar.Util.Inr (y), imp)) -> begin
(let tx = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _36_1127 = (match ((let _68_16405 = (Microsoft_FStar_Absyn_Util.unmeta_typ y.Microsoft_FStar_Absyn_Syntax.sort)
in _68_16405.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(tx, g)
end
| _36_1115 -> begin
(let _36_1116 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_16406 = (Microsoft_FStar_Absyn_Print.binder_to_string hd)
in (Support.Microsoft.FStar.Util.fprint1 "Checking binder %s\n" _68_16406))
end
| false -> begin
()
end)
in (let _36_1122 = (tc_typ env y.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_36_1122) with
| (t, _36_1120, g1) -> begin
(let g2 = (Microsoft_FStar_Tc_Rel.teq env tx t)
in (let g = (let _68_16407 = (Microsoft_FStar_Tc_Rel.conj_guard g1 g2)
in (Microsoft_FStar_Tc_Rel.conj_guard g _68_16407))
in (t, g)))
end)))
end)
in (match (_36_1127) with
| (t, g) -> begin
(let b = (Support.Microsoft.FStar.Util.Inr ((let _36_1128 = y
in {Microsoft_FStar_Absyn_Syntax.v = _36_1128.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _36_1128.Microsoft_FStar_Absyn_Syntax.p})), imp)
in (let env = (maybe_push_binding env b)
in (let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders ((b)::out, env, g, subst) tl_annot c tl))))
end)))
end
| _36_1134 -> begin
(let _68_16410 = (let _68_16409 = (Microsoft_FStar_Absyn_Print.binder_to_string hdannot)
in (let _68_16408 = (Microsoft_FStar_Absyn_Print.binder_to_string hd)
in (Support.Microsoft.FStar.Util.format2 "Annotated %s; given %s" _68_16409 _68_16408)))
in (fail _68_16410 t))
end)
end
| ([], _36_1137) -> begin
(match ((Microsoft_FStar_Absyn_Util.is_total_comp c)) with
| true -> begin
(match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.comp_result c) (whnf env))) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs_annot, c')); Microsoft_FStar_Absyn_Syntax.tk = _36_1146; Microsoft_FStar_Absyn_Syntax.pos = _36_1144; Microsoft_FStar_Absyn_Syntax.fvs = _36_1142; Microsoft_FStar_Absyn_Syntax.uvs = _36_1140} -> begin
(tc_binders (out, env, g, subst) bs_annot c' bs)
end
| t -> begin
(let _68_16412 = (let _68_16411 = (Microsoft_FStar_Absyn_Print.tag_of_typ t)
in (Support.Microsoft.FStar.Util.format1 "More arguments than annotated type (%s)" _68_16411))
in (fail _68_16412 t))
end)
end
| false -> begin
(fail "Curried function, but not total" t)
end)
end
| (_36_1154, []) -> begin
(let c = (let _68_16413 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs_annot, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) c.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Util.total_comp _68_16413 c.Microsoft_FStar_Absyn_Syntax.pos))
in (let _68_16414 = (Microsoft_FStar_Absyn_Util.subst_comp subst c)
in ((Support.List.rev out), env, g, _68_16414)))
end)
end))
in (let mk_letrec_environment = (fun ( actuals ) ( env ) -> (match (env.Microsoft_FStar_Tc_Env.letrecs) with
| [] -> begin
(env, [])
end
| letrecs -> begin
(let _36_1163 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_16419 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint1 "Building let-rec environment... type of this abstraction is %s\n" _68_16419))
end
| false -> begin
()
end)
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let env = (let _36_1166 = env
in {Microsoft_FStar_Tc_Env.solver = _36_1166.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_1166.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_1166.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_1166.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_1166.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_1166.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_1166.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_1166.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_1166.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _36_1166.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _36_1166.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _36_1166.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_1166.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = []; Microsoft_FStar_Tc_Env.top_level = _36_1166.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_1166.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = _36_1166.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = _36_1166.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_1166.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_1166.Microsoft_FStar_Tc_Env.default_effects})
in (let filter_types_and_functions = (fun ( bs ) -> (Support.Prims.pipe_right bs (Support.List.collect (fun ( b ) -> (match (b) with
| (Support.Microsoft.FStar.Util.Inl (_36_1173), _36_1176) -> begin
[]
end
| (Support.Microsoft.FStar.Util.Inr (x), _36_1181) -> begin
(match ((let _68_16425 = (let _68_16424 = (let _68_16423 = (Microsoft_FStar_Absyn_Util.unrefine x.Microsoft_FStar_Absyn_Syntax.sort)
in (whnf env _68_16423))
in (Microsoft_FStar_Absyn_Util.unrefine _68_16424))
in _68_16425.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_36_1184) -> begin
[]
end
| _36_1187 -> begin
(let _68_16426 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (_68_16426)::[])
end)
end)))))
in (let precedes = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.precedes_lid Microsoft_FStar_Absyn_Syntax.kun)
in (let as_lex_list = (fun ( dec ) -> (let _36_1194 = (Microsoft_FStar_Absyn_Util.head_and_args_e dec)
in (match (_36_1194) with
| (head, _36_1193) -> begin
(match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _36_1197)) when (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.lexcons_lid) -> begin
dec
end
| _36_1201 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (let prev_dec = (let ct = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c)
in (match ((Support.Prims.pipe_right ct.Microsoft_FStar_Absyn_Syntax.flags (Support.List.tryFind (fun ( _36_6 ) -> (match (_36_6) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (_36_1205) -> begin
true
end
| _36_1208 -> begin
false
end))))) with
| Some (Microsoft_FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(let _36_1212 = (match (((Support.List.length bs') <> (Support.List.length actuals))) with
| true -> begin
(let _68_16435 = (let _68_16434 = (let _68_16433 = (let _68_16431 = (Support.Microsoft.FStar.Util.string_of_int (Support.List.length bs'))
in (let _68_16430 = (Support.Microsoft.FStar.Util.string_of_int (Support.List.length actuals))
in (Support.Microsoft.FStar.Util.format2 "Decreases clause on a function with an unexpected number of arguments (expected %s; got %s)" _68_16431 _68_16430)))
in (let _68_16432 = (Microsoft_FStar_Tc_Env.get_range env)
in (_68_16433, _68_16432)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_16434))
in (raise (_68_16435)))
end
| false -> begin
()
end)
in (let dec = (as_lex_list dec)
in (let subst = (Support.List.map2 (fun ( b ) ( a ) -> (match ((b, a)) with
| ((Support.Microsoft.FStar.Util.Inl (formal), _36_1220), (Support.Microsoft.FStar.Util.Inl (actual), _36_1225)) -> begin
(let _68_16439 = (let _68_16438 = (Microsoft_FStar_Absyn_Util.btvar_to_typ actual)
in (formal.Microsoft_FStar_Absyn_Syntax.v, _68_16438))
in Support.Microsoft.FStar.Util.Inl (_68_16439))
end
| ((Support.Microsoft.FStar.Util.Inr (formal), _36_1231), (Support.Microsoft.FStar.Util.Inr (actual), _36_1236)) -> begin
(let _68_16441 = (let _68_16440 = (Microsoft_FStar_Absyn_Util.bvar_to_exp actual)
in (formal.Microsoft_FStar_Absyn_Syntax.v, _68_16440))
in Support.Microsoft.FStar.Util.Inr (_68_16441))
end
| _36_1240 -> begin
(failwith ("impossible"))
end)) bs' actuals)
in (Microsoft_FStar_Absyn_Util.subst_exp subst dec))))
end
| _36_1243 -> begin
(let actual_args = (Support.Prims.pipe_right actuals filter_types_and_functions)
in (match (actual_args) with
| i::[] -> begin
i
end
| _36_1248 -> begin
(mk_lex_list actual_args)
end))
end))
in (let letrecs = (Support.Prims.pipe_right letrecs (Support.List.map (fun ( _36_1252 ) -> (match (_36_1252) with
| (l, t0) -> begin
(let t = (Microsoft_FStar_Absyn_Util.alpha_typ t0)
in (match ((let _68_16443 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _68_16443.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((formals, c)) -> begin
(match ((Support.Microsoft.FStar.Util.prefix formals)) with
| (bs, (Support.Microsoft.FStar.Util.Inr (x), imp)) -> begin
(let y = (Microsoft_FStar_Absyn_Util.gen_bvar_p x.Microsoft_FStar_Absyn_Syntax.p x.Microsoft_FStar_Absyn_Syntax.sort)
in (let ct = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c)
in (let precedes = (match ((Support.Prims.pipe_right ct.Microsoft_FStar_Absyn_Syntax.flags (Support.List.tryFind (fun ( _36_7 ) -> (match (_36_7) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (_36_1268) -> begin
true
end
| _36_1271 -> begin
false
end))))) with
| Some (Microsoft_FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(let dec = (as_lex_list dec)
in (let dec = (let subst = (let _68_16447 = (let _68_16446 = (let _68_16445 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (x.Microsoft_FStar_Absyn_Syntax.v, _68_16445))
in Support.Microsoft.FStar.Util.Inr (_68_16446))
in (_68_16447)::[])
in (Microsoft_FStar_Absyn_Util.subst_exp subst dec))
in (let _68_16452 = (let _68_16451 = (let _68_16450 = (Microsoft_FStar_Absyn_Syntax.varg dec)
in (let _68_16449 = (let _68_16448 = (Microsoft_FStar_Absyn_Syntax.varg prev_dec)
in (_68_16448)::[])
in (_68_16450)::_68_16449))
in (precedes, _68_16451))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_16452 None r))))
end
| _36_1279 -> begin
(let formal_args = (let _68_16455 = (let _68_16454 = (let _68_16453 = (Microsoft_FStar_Absyn_Syntax.v_binder y)
in (_68_16453)::[])
in (Support.List.append bs _68_16454))
in (Support.Prims.pipe_right _68_16455 filter_types_and_functions))
in (let lhs = (match (formal_args) with
| i::[] -> begin
i
end
| _36_1284 -> begin
(mk_lex_list formal_args)
end)
in (let _68_16460 = (let _68_16459 = (let _68_16458 = (Microsoft_FStar_Absyn_Syntax.varg lhs)
in (let _68_16457 = (let _68_16456 = (Microsoft_FStar_Absyn_Syntax.varg prev_dec)
in (_68_16456)::[])
in (_68_16458)::_68_16457))
in (precedes, _68_16459))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_16460 None r))))
end)
in (let refined_domain = (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (y, precedes) None r)
in (let bs = (Support.List.append bs (((Support.Microsoft.FStar.Util.Inr ((let _36_1288 = x
in {Microsoft_FStar_Absyn_Syntax.v = _36_1288.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = refined_domain; Microsoft_FStar_Absyn_Syntax.p = _36_1288.Microsoft_FStar_Absyn_Syntax.p})), imp))::[]))
in (let t' = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None r)
in (let _36_1292 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_16463 = (Microsoft_FStar_Absyn_Print.lbname_to_string l)
in (let _68_16462 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (let _68_16461 = (Microsoft_FStar_Absyn_Print.typ_to_string t')
in (Support.Microsoft.FStar.Util.fprint3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _68_16463 _68_16462 _68_16461))))
end
| false -> begin
()
end)
in (let _36_1299 = (let _68_16465 = (let _68_16464 = (Microsoft_FStar_Tc_Env.clear_expected_typ env)
in (Support.Prims.pipe_right _68_16464 Support.Prims.fst))
in (tc_typ _68_16465 t'))
in (match (_36_1299) with
| (t', _36_1296, _36_1298) -> begin
(l, t')
end)))))))))
end
| _36_1301 -> begin
(failwith ("Impossible"))
end)
end
| _36_1303 -> begin
(failwith ("Impossible"))
end))
end))))
in (let _68_16471 = (Support.Prims.pipe_right letrecs (Support.List.fold_left (fun ( env ) ( _36_1308 ) -> (match (_36_1308) with
| (x, t) -> begin
(Microsoft_FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end)) env))
in (let _68_16470 = (Support.Prims.pipe_right letrecs (Support.List.collect (fun ( _36_8 ) -> (match (_36_8) with
| (Support.Microsoft.FStar.Util.Inl (x), t) -> begin
(let _68_16469 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_68_16469)::[])
end
| _36_1315 -> begin
[]
end))))
in (_68_16471, _68_16470)))))))))))
end))
in (let _36_1320 = (tc_binders ([], env, Microsoft_FStar_Tc_Rel.trivial_guard, []) bs' c bs)
in (match (_36_1320) with
| (bs, envbody, g, c) -> begin
(let _36_1323 = (match ((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
(mk_letrec_environment bs envbody)
end
| false -> begin
(envbody, [])
end)
in (match (_36_1323) with
| (envbody, letrecs) -> begin
(let envbody = (Microsoft_FStar_Tc_Env.set_expected_typ envbody (Microsoft_FStar_Absyn_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, g))
end))
end))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((b, _36_1327)) -> begin
(let _36_1337 = (as_function_typ norm b.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_36_1337) with
| (_36_1331, bs, bs', copt, env, g) -> begin
(Some ((t, false)), bs, bs', copt, env, g)
end))
end
| _36_1339 -> begin
(match ((not (norm))) with
| true -> begin
(let _68_16472 = (whnf env t)
in (as_function_typ true _68_16472))
end
| false -> begin
(let _36_1348 = (expected_function_typ env None)
in (match (_36_1348) with
| (_36_1341, bs, _36_1344, c_opt, envbody, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, g)
end))
end)
end))
in (as_function_typ false t)))
end))
in (let use_eq = env.Microsoft_FStar_Tc_Env.use_eq
in (let _36_1352 = (Microsoft_FStar_Tc_Env.clear_expected_typ env)
in (match (_36_1352) with
| (env, topt) -> begin
(let _36_1359 = (expected_function_typ env topt)
in (match (_36_1359) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, g) -> begin
(let _36_1365 = (tc_exp (let _36_1360 = envbody
in {Microsoft_FStar_Tc_Env.solver = _36_1360.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_1360.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_1360.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_1360.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_1360.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_1360.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_1360.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_1360.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_1360.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _36_1360.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _36_1360.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _36_1360.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_1360.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _36_1360.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = false; Microsoft_FStar_Tc_Env.check_uvars = _36_1360.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = use_eq; Microsoft_FStar_Tc_Env.is_iface = _36_1360.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_1360.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_1360.Microsoft_FStar_Tc_Env.default_effects}) body)
in (match (_36_1365) with
| (body, cbody, guard_body) -> begin
(let _36_1366 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _68_16475 = (Microsoft_FStar_Absyn_Print.exp_to_string body)
in (let _68_16474 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string cbody)
in (let _68_16473 = (Microsoft_FStar_Tc_Rel.guard_to_string env guard_body)
in (Support.Microsoft.FStar.Util.fprint3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _68_16475 _68_16474 _68_16473))))
end
| false -> begin
()
end)
in (let guard_body = (Microsoft_FStar_Tc_Rel.solve_deferred_constraints envbody guard_body)
in (let _36_1369 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Implicits")))) with
| true -> begin
(let _68_16476 = (Support.Prims.pipe_left Support.Microsoft.FStar.Util.string_of_int (Support.List.length guard_body.Microsoft_FStar_Tc_Rel.implicits))
in (Support.Microsoft.FStar.Util.fprint1 "Introduced %s implicits in body of abstraction\n" _68_16476))
end
| false -> begin
()
end)
in (let _36_1376 = (let _68_16478 = (let _68_16477 = (cbody.Microsoft_FStar_Absyn_Syntax.comp ())
in (body, _68_16477))
in (check_expected_effect (let _36_1371 = envbody
in {Microsoft_FStar_Tc_Env.solver = _36_1371.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_1371.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_1371.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_1371.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_1371.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_1371.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_1371.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_1371.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_1371.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _36_1371.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _36_1371.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _36_1371.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_1371.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _36_1371.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _36_1371.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_1371.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = use_eq; Microsoft_FStar_Tc_Env.is_iface = _36_1371.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_1371.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_1371.Microsoft_FStar_Tc_Env.default_effects}) c_opt _68_16478))
in (match (_36_1376) with
| (body, cbody, guard) -> begin
(let guard = (Microsoft_FStar_Tc_Rel.conj_guard guard_body guard)
in (let guard = (match ((env.Microsoft_FStar_Tc_Env.top_level || (not ((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str))))) with
| true -> begin
(let _36_1378 = (let _68_16479 = (Microsoft_FStar_Tc_Rel.conj_guard g guard)
in (Microsoft_FStar_Tc_Util.discharge_guard envbody _68_16479))
in (let _36_1380 = Microsoft_FStar_Tc_Rel.trivial_guard
in {Microsoft_FStar_Tc_Rel.guard_f = _36_1380.Microsoft_FStar_Tc_Rel.guard_f; Microsoft_FStar_Tc_Rel.deferred = _36_1380.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = guard.Microsoft_FStar_Tc_Rel.implicits}))
end
| false -> begin
(let guard = (Microsoft_FStar_Tc_Rel.close_guard (Support.List.append bs letrec_binders) guard)
in (Microsoft_FStar_Tc_Rel.conj_guard g guard))
end)
in (let tfun_computed = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, cbody) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) top.Microsoft_FStar_Absyn_Syntax.pos)
in (let e = (let _68_16481 = (let _68_16480 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (bs, body) (Some (tfun_computed)) top.Microsoft_FStar_Absyn_Syntax.pos)
in (_68_16480, tfun_computed, Some (Microsoft_FStar_Absyn_Const.effect_Tot_lid)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed _68_16481 None top.Microsoft_FStar_Absyn_Syntax.pos))
in (let _36_1403 = (match (tfun_opt) with
| Some ((t, use_teq)) -> begin
(let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_36_1392) -> begin
(let _68_16484 = (let _68_16483 = (let _68_16482 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (bs, body) (Some (t)) e.Microsoft_FStar_Absyn_Syntax.pos)
in (_68_16482, t, Some (Microsoft_FStar_Absyn_Const.effect_Tot_lid)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed _68_16483 None top.Microsoft_FStar_Absyn_Syntax.pos))
in (_68_16484, t, guard))
end
| _36_1395 -> begin
(let _36_1398 = (match (use_teq) with
| true -> begin
(let _68_16485 = (Microsoft_FStar_Tc_Rel.teq env t tfun_computed)
in (e, _68_16485))
end
| false -> begin
(Microsoft_FStar_Tc_Util.check_and_ascribe env e tfun_computed t)
end)
in (match (_36_1398) with
| (e, guard') -> begin
(let _68_16487 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed (e, t, Some (Microsoft_FStar_Absyn_Const.effect_Tot_lid)) None top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_16486 = (Microsoft_FStar_Tc_Rel.conj_guard guard guard')
in (_68_16487, t, _68_16486)))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_36_1403) with
| (e, tfun, guard) -> begin
(let _36_1404 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_16490 = (Microsoft_FStar_Absyn_Print.typ_to_string tfun)
in (let _68_16489 = (Microsoft_FStar_Absyn_Print.tag_of_typ tfun)
in (let _68_16488 = (Microsoft_FStar_Tc_Rel.guard_to_string env guard)
in (Support.Microsoft.FStar.Util.fprint3 "!!!!!!!!!!!!!!!Annotating lambda with type %s (%s)\nGuard is %s\n" _68_16490 _68_16489 _68_16488))))
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
in (let _36_1409 = (let _68_16492 = (Microsoft_FStar_Tc_Util.lcomp_of_comp c)
in (Microsoft_FStar_Tc_Util.strengthen_precondition None env e _68_16492 guard))
in (match (_36_1409) with
| (c, g) -> begin
(e, c, g)
end))))
end))))))
end)))))
end))
end))
end)))))
end
| _36_1411 -> begin
(let _68_16494 = (let _68_16493 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format1 "Unexpected value: %s" _68_16493))
in (failwith (_68_16494)))
end))))
and tc_exp = (fun ( env ) ( e ) -> (let env = (match ((e.Microsoft_FStar_Absyn_Syntax.pos = Microsoft_FStar_Absyn_Syntax.dummyRange)) with
| true -> begin
env
end
| false -> begin
(Microsoft_FStar_Tc_Env.set_range env e.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (let _36_1415 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_16499 = (let _68_16497 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range _68_16497))
in (let _68_16498 = (Microsoft_FStar_Absyn_Print.tag_of_exp e)
in (Support.Microsoft.FStar.Util.fprint2 "%s (%s)\n" _68_16499 _68_16498)))
end
| false -> begin
()
end)
in (let w = (fun ( lc ) -> (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Syntax.syn e.Microsoft_FStar_Absyn_Syntax.pos) (Some (lc.Microsoft_FStar_Absyn_Syntax.res_typ))))
in (let top = e
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_36_1421) -> begin
(let _68_16523 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (tc_exp env _68_16523))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_abs (_)) -> begin
(tc_value env e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e1, t1, _36_1441)) -> begin
(let _36_1446 = (tc_typ_check env t1 Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_36_1446) with
| (t1, f) -> begin
(let _36_1450 = (let _68_16524 = (Microsoft_FStar_Tc_Env.set_expected_typ env t1)
in (tc_exp _68_16524 e1))
in (match (_36_1450) with
| (e1, c, g) -> begin
(let _36_1454 = (let _68_16528 = (Microsoft_FStar_Tc_Env.set_range env t1.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Tc_Util.strengthen_precondition (Some ((fun ( _36_1451 ) -> (match (()) with
| () -> begin
Microsoft_FStar_Tc_Errors.ill_kinded_type
end)))) _68_16528 e1 c f))
in (match (_36_1454) with
| (c, f) -> begin
(let _36_1458 = (let _68_16532 = (let _68_16531 = (w c)
in (Support.Prims.pipe_left _68_16531 (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed (e1, t1, Some (c.Microsoft_FStar_Absyn_Syntax.eff_name)))))
in (comp_check_expected_typ env _68_16532 c))
in (match (_36_1458) with
| (e, c, f2) -> begin
(let _68_16534 = (let _68_16533 = (Microsoft_FStar_Tc_Rel.conj_guard g f2)
in (Microsoft_FStar_Tc_Rel.conj_guard f _68_16533))
in (e, c, _68_16534))
end))
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.Sequence))) -> begin
(match ((let _68_16535 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _68_16535.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_let (((_36_1465, {Microsoft_FStar_Absyn_Syntax.lbname = x; Microsoft_FStar_Absyn_Syntax.lbtyp = _36_1470; Microsoft_FStar_Absyn_Syntax.lbeff = _36_1468; Microsoft_FStar_Absyn_Syntax.lbdef = e1}::[]), e2)) -> begin
(let _36_1481 = (let _68_16536 = (Microsoft_FStar_Tc_Env.set_expected_typ env Microsoft_FStar_Tc_Recheck.t_unit)
in (tc_exp _68_16536 e1))
in (match (_36_1481) with
| (e1, c1, g1) -> begin
(let _36_1485 = (tc_exp env e2)
in (match (_36_1485) with
| (e2, c2, g2) -> begin
(let c = (Microsoft_FStar_Tc_Util.bind env (Some (e1)) c1 (None, c2))
in (let _68_16549 = (let _68_16547 = (let _68_16546 = (let _68_16545 = (let _68_16544 = (w c)
in (let _68_16543 = (let _68_16542 = (let _68_16541 = (let _68_16540 = (let _68_16539 = (Microsoft_FStar_Absyn_Syntax.mk_lb (x, c1.Microsoft_FStar_Absyn_Syntax.eff_name, Microsoft_FStar_Tc_Recheck.t_unit, e1))
in (_68_16539)::[])
in (false, _68_16540))
in (_68_16541, e2))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_let _68_16542))
in (Support.Prims.pipe_left _68_16544 _68_16543)))
in (_68_16545, Microsoft_FStar_Absyn_Syntax.Sequence))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_68_16546))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _68_16547))
in (let _68_16548 = (Microsoft_FStar_Tc_Rel.conj_guard g1 g2)
in (_68_16549, c, _68_16548))))
end))
end))
end
| _36_1488 -> begin
(let _36_1492 = (tc_exp env e)
in (match (_36_1492) with
| (e, c, g) -> begin
(let _68_16550 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.Sequence))))
in (_68_16550, c, g))
end))
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, i))) -> begin
(let _36_1501 = (tc_exp env e)
in (match (_36_1501) with
| (e, c, g) -> begin
(let _68_16551 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, i))))
in (_68_16551, c, g))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args)) -> begin
(let env0 = env
in (let env = (let _68_16553 = (let _68_16552 = (Microsoft_FStar_Tc_Env.clear_expected_typ env)
in (Support.Prims.pipe_right _68_16552 Support.Prims.fst))
in (Support.Prims.pipe_right _68_16553 instantiate_both))
in (let _36_1508 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_16555 = (Support.Microsoft.FStar.Range.string_of_range top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_16554 = (Microsoft_FStar_Absyn_Print.exp_to_string top)
in (Support.Microsoft.FStar.Util.fprint2 "(%s) Checking app %s\n" _68_16555 _68_16554)))
end
| false -> begin
()
end)
in (let _36_1513 = (tc_exp (no_inst env) head)
in (match (_36_1513) with
| (head, chead, g_head) -> begin
(let aux = (fun ( _36_1515 ) -> (match (()) with
| () -> begin
(let n_args = (Support.List.length args)
in (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _36_1519)) when (((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.op_And) || (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.op_Or)) && (n_args = 2)) -> begin
(let env = (Microsoft_FStar_Tc_Env.set_expected_typ env Microsoft_FStar_Absyn_Util.t_bool)
in (match (args) with
| (Support.Microsoft.FStar.Util.Inr (e1), _36_1531)::(Support.Microsoft.FStar.Util.Inr (e2), _36_1526)::[] -> begin
(let _36_1537 = (tc_exp env e1)
in (match (_36_1537) with
| (e1, c1, g1) -> begin
(let _36_1541 = (tc_exp env e2)
in (match (_36_1541) with
| (e2, c2, g2) -> begin
(let x = (Microsoft_FStar_Absyn_Util.gen_bvar Microsoft_FStar_Absyn_Util.t_bool)
in (let xexp = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (let c2 = (match ((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.op_And)) with
| true -> begin
(let _68_16561 = (let _68_16558 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Util.b2t _68_16558))
in (let _68_16560 = (let _68_16559 = (Microsoft_FStar_Tc_Util.return_value env Microsoft_FStar_Absyn_Util.t_bool xexp)
in (Support.Prims.pipe_right _68_16559 Microsoft_FStar_Tc_Util.lcomp_of_comp))
in (Microsoft_FStar_Tc_Util.ite env _68_16561 c2 _68_16560)))
end
| false -> begin
(let _68_16565 = (let _68_16562 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Util.b2t _68_16562))
in (let _68_16564 = (let _68_16563 = (Microsoft_FStar_Tc_Util.return_value env Microsoft_FStar_Absyn_Util.t_bool xexp)
in (Support.Prims.pipe_right _68_16563 Microsoft_FStar_Tc_Util.lcomp_of_comp))
in (Microsoft_FStar_Tc_Util.ite env _68_16565 _68_16564 c2)))
end)
in (let c = (let _68_16568 = (let _68_16567 = (Support.Prims.pipe_left (fun ( _68_16566 ) -> Some (_68_16566)) (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, Microsoft_FStar_Absyn_Util.t_bool))))
in (_68_16567, c2))
in (Microsoft_FStar_Tc_Util.bind env None c1 _68_16568))
in (let e = (let _68_16573 = (let _68_16572 = (let _68_16571 = (Microsoft_FStar_Absyn_Syntax.varg e1)
in (let _68_16570 = (let _68_16569 = (Microsoft_FStar_Absyn_Syntax.varg e2)
in (_68_16569)::[])
in (_68_16571)::_68_16570))
in (head, _68_16572))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _68_16573 (Some (Microsoft_FStar_Absyn_Util.t_bool)) top.Microsoft_FStar_Absyn_Syntax.pos))
in (let _68_16575 = (let _68_16574 = (Microsoft_FStar_Tc_Rel.conj_guard g1 g2)
in (Microsoft_FStar_Tc_Rel.conj_guard g_head _68_16574))
in (e, c, _68_16575)))))))
end))
end))
end
| _36_1548 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Expected two boolean arguments", head.Microsoft_FStar_Absyn_Syntax.pos))))
end))
end
| _36_1550 -> begin
(let thead = chead.Microsoft_FStar_Absyn_Syntax.res_typ
in (let _36_1552 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_16577 = (Support.Microsoft.FStar.Range.string_of_range head.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_16576 = (Microsoft_FStar_Absyn_Print.typ_to_string thead)
in (Support.Microsoft.FStar.Util.fprint2 "(%s) Type of head is %s\n" _68_16577 _68_16576)))
end
| false -> begin
()
end)
in (let rec check_function_app = (fun ( norm ) ( tf ) -> (match ((let _68_16582 = (Microsoft_FStar_Absyn_Util.unrefine tf)
in _68_16582.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let rec tc_args = (fun ( env ) ( args ) -> (match (args) with
| [] -> begin
([], [], Microsoft_FStar_Tc_Rel.trivial_guard)
end
| (Support.Microsoft.FStar.Util.Inl (t), _36_1585)::_36_1581 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Explicit type applications on a term with unknown type; add an annotation?", t.Microsoft_FStar_Absyn_Syntax.pos))))
end
| (Support.Microsoft.FStar.Util.Inr (e), imp)::tl -> begin
(let _36_1597 = (tc_exp env e)
in (match (_36_1597) with
| (e, c, g_e) -> begin
(let _36_1601 = (tc_args env tl)
in (match (_36_1601) with
| (args, comps, g_rest) -> begin
(let _68_16587 = (Microsoft_FStar_Tc_Rel.conj_guard g_e g_rest)
in (((Support.Microsoft.FStar.Util.Inr (e), imp))::args, (c)::comps, _68_16587))
end))
end))
end))
in (let _36_1605 = (tc_args env args)
in (match (_36_1605) with
| (args, comps, g_args) -> begin
(let bs = (let _68_16588 = (Microsoft_FStar_Tc_Util.tks_of_args args)
in (Microsoft_FStar_Absyn_Util.null_binders_of_tks _68_16588))
in (let cres = (let _68_16589 = (Microsoft_FStar_Tc_Util.new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Util.ml_comp _68_16589 top.Microsoft_FStar_Absyn_Syntax.pos))
in (let _36_1608 = (let _68_16591 = (let _68_16590 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, cres) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) tf.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Tc_Rel.teq env tf _68_16590))
in (Support.Prims.pipe_left (Microsoft_FStar_Tc_Util.force_trivial env) _68_16591))
in (let comp = (let _68_16594 = (Support.Prims.pipe_left Microsoft_FStar_Tc_Util.lcomp_of_comp cres)
in (Support.List.fold_right (fun ( c ) ( out ) -> (Microsoft_FStar_Tc_Util.bind env None c (None, out))) ((chead)::comps) _68_16594))
in (let _68_16596 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (head, args) (Some (comp.Microsoft_FStar_Absyn_Syntax.res_typ)) top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_16595 = (Microsoft_FStar_Tc_Rel.conj_guard g_head g_args)
in (_68_16596, comp, _68_16595)))))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let vars = (Microsoft_FStar_Tc_Env.binders env)
in (let rec tc_args = (fun ( _36_1625 ) ( bs ) ( cres ) ( args ) -> (match (_36_1625) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest, (_36_1639, None)::_36_1637) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _36_1645 = (fxv_check head env (Support.Microsoft.FStar.Util.Inl (k)) fvs)
in (let _36_1649 = (let _68_16632 = (let _68_16631 = (Support.List.hd args)
in (Microsoft_FStar_Absyn_Util.range_of_arg _68_16631))
in (Microsoft_FStar_Tc_Rel.new_tvar _68_16632 vars k))
in (match (_36_1649) with
| (targ, u) -> begin
(let _36_1650 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _68_16634 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (let _68_16633 = (Microsoft_FStar_Absyn_Print.typ_to_string targ)
in (Support.Microsoft.FStar.Util.fprint2 "Instantiating %s to %s" _68_16634 _68_16633)))
end
| false -> begin
()
end)
in (let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, targ)))::subst
in (let arg = (let _68_16635 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inl (targ), _68_16635))
in (let _68_16644 = (let _68_16643 = (let _68_16642 = (let _68_16641 = (let _68_16640 = (Microsoft_FStar_Tc_Util.as_uvar_t u)
in (_68_16640, u.Microsoft_FStar_Absyn_Syntax.pos))
in Support.Microsoft.FStar.Util.Inl (_68_16641))
in (add_implicit _68_16642 g))
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _68_16643, fvs))
in (tc_args _68_16644 rest cres args)))))
end))))
end
| ((Support.Microsoft.FStar.Util.Inr (x), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest, (_36_1664, None)::_36_1662) -> begin
(let t = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _36_1670 = (fxv_check head env (Support.Microsoft.FStar.Util.Inr (t)) fvs)
in (let _36_1674 = (Microsoft_FStar_Tc_Util.new_implicit_evar env t)
in (match (_36_1674) with
| (varg, u) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, varg)))::subst
in (let arg = (let _68_16645 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inr (varg), _68_16645))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, (add_implicit (Support.Microsoft.FStar.Util.Inr (u)) g), fvs) rest cres args)))
end))))
end
| ((Support.Microsoft.FStar.Util.Inl (a), aqual)::rest, (Support.Microsoft.FStar.Util.Inl (t), aq)::rest') -> begin
(let _36_1690 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _68_16651 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (let _68_16650 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint2 "\tGot a type arg for %s = %s\n" _68_16651 _68_16650)))
end
| false -> begin
()
end)
in (let k = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _36_1693 = (fxv_check head env (Support.Microsoft.FStar.Util.Inl (k)) fvs)
in (let _36_1699 = (tc_typ_check (let _36_1695 = env
in {Microsoft_FStar_Tc_Env.solver = _36_1695.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_1695.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_1695.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_1695.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_1695.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_1695.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_1695.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_1695.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_1695.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _36_1695.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _36_1695.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _36_1695.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_1695.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _36_1695.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _36_1695.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_1695.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = (is_eq aqual); Microsoft_FStar_Tc_Env.is_iface = _36_1695.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_1695.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_1695.Microsoft_FStar_Tc_Env.default_effects}) t k)
in (match (_36_1699) with
| (t, g') -> begin
(let f = (let _68_16652 = (Microsoft_FStar_Tc_Rel.guard_f g')
in (Microsoft_FStar_Tc_Util.label_guard Microsoft_FStar_Tc_Errors.ill_kinded_type t.Microsoft_FStar_Absyn_Syntax.pos _68_16652))
in (let g' = (let _36_1701 = g'
in {Microsoft_FStar_Tc_Rel.guard_f = f; Microsoft_FStar_Tc_Rel.deferred = _36_1701.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = _36_1701.Microsoft_FStar_Tc_Rel.implicits})
in (let arg = (Support.Microsoft.FStar.Util.Inl (t), aq)
in (let subst = (let _68_16653 = (Support.List.hd bs)
in (maybe_extend_subst subst _68_16653 arg))
in (let _68_16659 = (let _68_16658 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _68_16658, fvs))
in (tc_args _68_16659 rest cres rest'))))))
end)))))
end
| ((Support.Microsoft.FStar.Util.Inr (x), aqual)::rest, (Support.Microsoft.FStar.Util.Inr (e), aq)::rest') -> begin
(let _36_1719 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _68_16661 = (Microsoft_FStar_Absyn_Print.subst_to_string subst)
in (let _68_16660 = (Microsoft_FStar_Absyn_Print.typ_to_string x.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.Microsoft.FStar.Util.fprint2 "\tType of arg (before subst (%s)) = %s\n" _68_16661 _68_16660)))
end
| false -> begin
()
end)
in (let targ = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _36_1722 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _68_16662 = (Microsoft_FStar_Absyn_Print.typ_to_string targ)
in (Support.Microsoft.FStar.Util.fprint1 "\tType of arg (after subst) = %s\n" _68_16662))
end
| false -> begin
()
end)
in (let _36_1724 = (fxv_check head env (Support.Microsoft.FStar.Util.Inr (targ)) fvs)
in (let env = (Microsoft_FStar_Tc_Env.set_expected_typ env targ)
in (let env = (let _36_1727 = env
in {Microsoft_FStar_Tc_Env.solver = _36_1727.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_1727.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_1727.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_1727.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_1727.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_1727.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_1727.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_1727.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_1727.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _36_1727.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _36_1727.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _36_1727.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_1727.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _36_1727.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _36_1727.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_1727.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = (is_eq aqual); Microsoft_FStar_Tc_Env.is_iface = _36_1727.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_1727.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_1727.Microsoft_FStar_Tc_Env.default_effects})
in (let _36_1730 = (match (((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("EQ"))) && env.Microsoft_FStar_Tc_Env.use_eq)) with
| true -> begin
(let _68_16664 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _68_16663 = (Microsoft_FStar_Absyn_Print.typ_to_string targ)
in (Support.Microsoft.FStar.Util.fprint2 "Checking arg %s at type %s with an equality constraint!\n" _68_16664 _68_16663)))
end
| false -> begin
()
end)
in (let _36_1732 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_16667 = (Microsoft_FStar_Absyn_Print.tag_of_exp e)
in (let _68_16666 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _68_16665 = (Microsoft_FStar_Absyn_Print.typ_to_string targ)
in (Support.Microsoft.FStar.Util.fprint3 "Checking arg (%s) %s at type %s\n" _68_16667 _68_16666 _68_16665))))
end
| false -> begin
()
end)
in (let _36_1737 = (tc_exp env e)
in (match (_36_1737) with
| (e, c, g_e) -> begin
(let g = (Microsoft_FStar_Tc_Rel.conj_guard g g_e)
in (let _36_1739 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_16669 = (Microsoft_FStar_Tc_Rel.guard_to_string env g_e)
in (let _68_16668 = (Microsoft_FStar_Tc_Rel.guard_to_string env g)
in (Support.Microsoft.FStar.Util.fprint2 "Guard on this arg is %s;\naccumulated guard is %s\n" _68_16669 _68_16668)))
end
| false -> begin
()
end)
in (let arg = (Support.Microsoft.FStar.Util.Inr (e), aq)
in (match ((Microsoft_FStar_Absyn_Util.is_tot_or_gtot_lcomp c)) with
| true -> begin
(let subst = (let _68_16670 = (Support.List.hd bs)
in (maybe_extend_subst subst _68_16670 arg))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end
| false -> begin
(match ((Microsoft_FStar_Tc_Util.is_pure_or_ghost_effect env c.Microsoft_FStar_Absyn_Syntax.eff_name)) with
| true -> begin
(let subst = (let _68_16675 = (Support.List.hd bs)
in (maybe_extend_subst subst _68_16675 arg))
in (let _36_1746 = (((Some (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, targ))), c))::comps, g)
in (match (_36_1746) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end
| false -> begin
(match ((let _68_16680 = (Support.List.hd bs)
in (Microsoft_FStar_Absyn_Syntax.is_null_binder _68_16680))) with
| true -> begin
(let newx = (Microsoft_FStar_Absyn_Util.gen_bvar_p e.Microsoft_FStar_Absyn_Syntax.pos c.Microsoft_FStar_Absyn_Syntax.res_typ)
in (let arg' = (let _68_16681 = (Microsoft_FStar_Absyn_Util.bvar_to_exp newx)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.varg _68_16681))
in (let binding = Microsoft_FStar_Tc_Env.Binding_var ((newx.Microsoft_FStar_Absyn_Syntax.v, newx.Microsoft_FStar_Absyn_Syntax.sort))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (binding), c))::comps, g, fvs) rest cres rest'))))
end
| false -> begin
(let _68_16694 = (let _68_16693 = (let _68_16687 = (let _68_16686 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.varg _68_16686))
in (_68_16687)::arg_rets)
in (let _68_16692 = (let _68_16690 = (let _68_16689 = (Support.Prims.pipe_left (fun ( _68_16688 ) -> Some (_68_16688)) (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, targ))))
in (_68_16689, c))
in (_68_16690)::comps)
in (let _68_16691 = (Support.Microsoft.FStar.Util.set_add x fvs)
in (subst, (arg)::outargs, _68_16693, _68_16692, g, _68_16691))))
in (tc_args _68_16694 rest cres rest'))
end)
end)
end))))
end))))))))))
end
| ((Support.Microsoft.FStar.Util.Inr (_36_1753), _36_1756)::_36_1751, (Support.Microsoft.FStar.Util.Inl (_36_1762), _36_1765)::_36_1760) -> begin
(let _68_16698 = (let _68_16697 = (let _68_16696 = (let _68_16695 = (Support.List.hd args)
in (Microsoft_FStar_Absyn_Util.range_of_arg _68_16695))
in ("Expected an expression; got a type", _68_16696))
in Microsoft_FStar_Absyn_Syntax.Error (_68_16697))
in (raise (_68_16698)))
end
| ((Support.Microsoft.FStar.Util.Inl (_36_1772), _36_1775)::_36_1770, (Support.Microsoft.FStar.Util.Inr (_36_1781), _36_1784)::_36_1779) -> begin
(let _68_16702 = (let _68_16701 = (let _68_16700 = (let _68_16699 = (Support.List.hd args)
in (Microsoft_FStar_Absyn_Util.range_of_arg _68_16699))
in ("Expected a type; got an expression", _68_16700))
in Microsoft_FStar_Absyn_Syntax.Error (_68_16701))
in (raise (_68_16702)))
end
| (_36_1789, []) -> begin
(let _36_1792 = (fxv_check head env (Support.Microsoft.FStar.Util.Inr (cres.Microsoft_FStar_Absyn_Syntax.res_typ)) fvs)
in (let _36_1810 = (match (bs) with
| [] -> begin
(let cres = (Microsoft_FStar_Tc_Util.subst_lcomp subst cres)
in (let g = (Microsoft_FStar_Tc_Rel.conj_guard g_head g)
in (let refine_with_equality = ((Microsoft_FStar_Absyn_Util.is_pure_or_ghost_lcomp cres) && (Support.Prims.pipe_right comps (Support.Microsoft.FStar.Util.for_some (fun ( _36_1800 ) -> (match (_36_1800) with
| (_36_1798, c) -> begin
(not ((Microsoft_FStar_Absyn_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (let cres = (match (refine_with_equality) with
| true -> begin
(let _68_16704 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app_flat (head, (Support.List.rev arg_rets)) (Some (cres.Microsoft_FStar_Absyn_Syntax.res_typ)) top.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Tc_Util.maybe_assume_result_eq_pure_term env _68_16704 cres))
end
| false -> begin
(let _36_1802 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_16707 = (Microsoft_FStar_Absyn_Print.exp_to_string head)
in (let _68_16706 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string cres)
in (let _68_16705 = (Microsoft_FStar_Tc_Rel.guard_to_string env g)
in (Support.Microsoft.FStar.Util.fprint3 "Not refining result: f=%s; cres=%s; guard=%s\n" _68_16707 _68_16706 _68_16705))))
end
| false -> begin
()
end)
in cres)
end)
in (let _68_16708 = (Microsoft_FStar_Tc_Util.refresh_comp_label env false cres)
in (_68_16708, g))))))
end
| _36_1806 -> begin
(let g = (let _68_16709 = (Microsoft_FStar_Tc_Rel.conj_guard g_head g)
in (Support.Prims.pipe_right _68_16709 (Microsoft_FStar_Tc_Rel.solve_deferred_constraints env)))
in (let _68_16715 = (let _68_16714 = (let _68_16713 = (let _68_16712 = (let _68_16711 = (let _68_16710 = (cres.Microsoft_FStar_Absyn_Syntax.comp ())
in (bs, _68_16710))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _68_16711 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) top.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Util.subst_typ subst) _68_16712))
in (Microsoft_FStar_Absyn_Syntax.mk_Total _68_16713))
in (Support.Prims.pipe_left Microsoft_FStar_Tc_Util.lcomp_of_comp _68_16714))
in (_68_16715, g)))
end)
in (match (_36_1810) with
| (cres, g) -> begin
(let _36_1811 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_16716 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string cres)
in (Support.Microsoft.FStar.Util.fprint1 "\t Type of result cres is %s\n" _68_16716))
end
| false -> begin
()
end)
in (let comp = (Support.List.fold_left (fun ( out ) ( c ) -> (Microsoft_FStar_Tc_Util.bind env None (Support.Prims.snd c) ((Support.Prims.fst c), out))) cres comps)
in (let comp = (Microsoft_FStar_Tc_Util.bind env None chead (None, comp))
in (let app = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app_flat (head, (Support.List.rev outargs)) (Some (comp.Microsoft_FStar_Absyn_Syntax.res_typ)) top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _36_1820 = (Microsoft_FStar_Tc_Util.strengthen_precondition None env app comp g)
in (match (_36_1820) with
| (comp, g) -> begin
(let _36_1821 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_16722 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env app)
in (let _68_16721 = (let _68_16720 = (comp.Microsoft_FStar_Absyn_Syntax.comp ())
in (Microsoft_FStar_Absyn_Print.comp_typ_to_string _68_16720))
in (Support.Microsoft.FStar.Util.fprint2 "\t Type of app term %s is %s\n" _68_16722 _68_16721)))
end
| false -> begin
()
end)
in (app, comp, g))
end))))))
end)))
end
| ([], arg::_36_1825) -> begin
(let rec aux = (fun ( norm ) ( tres ) -> (let tres = (let _68_16727 = (Microsoft_FStar_Absyn_Util.compress_typ tres)
in (Support.Prims.pipe_right _68_16727 Microsoft_FStar_Absyn_Util.unrefine))
in (match (tres.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, cres')) -> begin
(let _36_1837 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_16728 = (Support.Microsoft.FStar.Range.string_of_range tres.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Microsoft.FStar.Util.fprint1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _68_16728))
end
| false -> begin
()
end)
in (let _68_16733 = (Microsoft_FStar_Tc_Util.lcomp_of_comp cres')
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs _68_16733 args)))
end
| _36_1840 when (not (norm)) -> begin
(let _68_16734 = (whnf env tres)
in (aux true _68_16734))
end
| _36_1842 -> begin
(let _68_16740 = (let _68_16739 = (let _68_16738 = (let _68_16736 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env tf)
in (let _68_16735 = (Microsoft_FStar_Absyn_Print.exp_to_string top)
in (Support.Microsoft.FStar.Util.format2 "Too many arguments to function of type %s; got %s" _68_16736 _68_16735)))
in (let _68_16737 = (Microsoft_FStar_Absyn_Syntax.argpos arg)
in (_68_16738, _68_16737)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_16739))
in (raise (_68_16740)))
end)))
in (aux false cres.Microsoft_FStar_Absyn_Syntax.res_typ))
end)
end))
in (let _68_16741 = (Microsoft_FStar_Tc_Util.lcomp_of_comp c)
in (tc_args ([], [], [], [], Microsoft_FStar_Tc_Rel.trivial_guard, Microsoft_FStar_Absyn_Syntax.no_fvs.Microsoft_FStar_Absyn_Syntax.fxvs) bs _68_16741 args))))
end
| _36_1844 -> begin
(match ((not (norm))) with
| true -> begin
(let _68_16742 = (whnf env tf)
in (check_function_app true _68_16742))
end
| false -> begin
(let _68_16745 = (let _68_16744 = (let _68_16743 = (Microsoft_FStar_Tc_Errors.expected_function_typ env tf)
in (_68_16743, head.Microsoft_FStar_Absyn_Syntax.pos))
in Microsoft_FStar_Absyn_Syntax.Error (_68_16744))
in (raise (_68_16745)))
end)
end))
in (let _68_16746 = (Microsoft_FStar_Absyn_Util.unrefine thead)
in (check_function_app false _68_16746)))))
end))
end))
in (let _36_1848 = (aux ())
in (match (_36_1848) with
| (e, c, g) -> begin
(let _36_1849 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Implicits")))) with
| true -> begin
(let _68_16747 = (Support.Prims.pipe_left Support.Microsoft.FStar.Util.string_of_int (Support.List.length g.Microsoft_FStar_Tc_Rel.implicits))
in (Support.Microsoft.FStar.Util.fprint1 "Introduced %s implicits in application\n" _68_16747))
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
in (let _36_1856 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _68_16752 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_16751 = (Microsoft_FStar_Absyn_Print.typ_to_string c.Microsoft_FStar_Absyn_Syntax.res_typ)
in (let _68_16750 = (let _68_16749 = (Microsoft_FStar_Tc_Env.expected_typ env0)
in (Support.Prims.pipe_right _68_16749 (fun ( x ) -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(Microsoft_FStar_Absyn_Print.typ_to_string t)
end))))
in (Support.Microsoft.FStar.Util.fprint3 "(%s) About to check %s against expected typ %s\n" _68_16752 _68_16751 _68_16750))))
end
| false -> begin
()
end)
in (let _36_1861 = (comp_check_expected_typ env0 e c)
in (match (_36_1861) with
| (e, c, g') -> begin
(let _68_16753 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (e, c, _68_16753))
end)))))
end)))
end)))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e1, eqns)) -> begin
(let _36_1868 = (Microsoft_FStar_Tc_Env.clear_expected_typ env)
in (match (_36_1868) with
| (env1, topt) -> begin
(let env1 = (instantiate_both env1)
in (let _36_1873 = (tc_exp env1 e1)
in (match (_36_1873) with
| (e1, c1, g1) -> begin
(let _36_1880 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(let res_t = (Microsoft_FStar_Tc_Util.new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (let _68_16754 = (Microsoft_FStar_Tc_Env.set_expected_typ env res_t)
in (_68_16754, res_t)))
end)
in (match (_36_1880) with
| (env_branches, res_t) -> begin
(let guard_x = (let _68_16756 = (Support.Prims.pipe_left (fun ( _68_16755 ) -> Some (_68_16755)) e1.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Util.new_bvd _68_16756))
in (let t_eqns = (Support.Prims.pipe_right eqns (Support.List.map (tc_eqn guard_x c1.Microsoft_FStar_Absyn_Syntax.res_typ env_branches)))
in (let _36_1897 = (let _36_1894 = (Support.List.fold_right (fun ( _36_1888 ) ( _36_1891 ) -> (match ((_36_1888, _36_1891)) with
| ((_36_1884, f, c, g), (caccum, gaccum)) -> begin
(let _68_16759 = (Microsoft_FStar_Tc_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _68_16759))
end)) t_eqns ([], Microsoft_FStar_Tc_Rel.trivial_guard))
in (match (_36_1894) with
| (cases, g) -> begin
(let _68_16760 = (Microsoft_FStar_Tc_Util.bind_cases env res_t cases)
in (_68_16760, g))
end))
in (match (_36_1897) with
| (c_branches, g_branches) -> begin
(let _36_1898 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _68_16764 = (Support.Microsoft.FStar.Range.string_of_range top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_16763 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string c1)
in (let _68_16762 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string c_branches)
in (let _68_16761 = (Microsoft_FStar_Tc_Rel.guard_to_string env g_branches)
in (Support.Microsoft.FStar.Util.fprint4 "(%s) comp\n\tscrutinee: %s\n\tbranches: %s\nguard = %s\n" _68_16764 _68_16763 _68_16762 _68_16761)))))
end
| false -> begin
()
end)
in (let cres = (let _68_16767 = (let _68_16766 = (Support.Prims.pipe_left (fun ( _68_16765 ) -> Some (_68_16765)) (Microsoft_FStar_Tc_Env.Binding_var ((guard_x, c1.Microsoft_FStar_Absyn_Syntax.res_typ))))
in (_68_16766, c_branches))
in (Microsoft_FStar_Tc_Util.bind env (Some (e1)) c1 _68_16767))
in (let e = (let _68_16774 = (w cres)
in (let _68_16773 = (let _68_16772 = (let _68_16771 = (Support.List.map (fun ( _36_1908 ) -> (match (_36_1908) with
| (f, _36_1903, _36_1905, _36_1907) -> begin
f
end)) t_eqns)
in (e1, _68_16771))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_match _68_16772))
in (Support.Prims.pipe_left _68_16774 _68_16773)))
in (let _68_16776 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed (e, cres.Microsoft_FStar_Absyn_Syntax.res_typ, Some (cres.Microsoft_FStar_Absyn_Syntax.eff_name)) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_16775 = (Microsoft_FStar_Tc_Rel.conj_guard g1 g_branches)
in (_68_16776, cres, _68_16775))))))
end))))
end))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((false, {Microsoft_FStar_Absyn_Syntax.lbname = x; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _36_1913; Microsoft_FStar_Absyn_Syntax.lbdef = e1}::[]), e2)) -> begin
(let env = (instantiate_both env)
in (let env0 = env
in (let topt = (Microsoft_FStar_Tc_Env.expected_typ env)
in (let top_level = (match (x) with
| Support.Microsoft.FStar.Util.Inr (_36_1926) -> begin
true
end
| _36_1929 -> begin
false
end)
in (let _36_1934 = (Microsoft_FStar_Tc_Env.clear_expected_typ env)
in (match (_36_1934) with
| (env1, _36_1933) -> begin
(let _36_1947 = (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(Microsoft_FStar_Tc_Rel.trivial_guard, env1)
end
| _36_1937 -> begin
(match ((top_level && (not (env.Microsoft_FStar_Tc_Env.generalize)))) with
| true -> begin
(let _68_16777 = (Microsoft_FStar_Tc_Env.set_expected_typ env1 t)
in (Microsoft_FStar_Tc_Rel.trivial_guard, _68_16777))
end
| false -> begin
(let _36_1940 = (tc_typ_check env1 t Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_36_1940) with
| (t, f) -> begin
(let _36_1941 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _68_16779 = (Support.Microsoft.FStar.Range.string_of_range top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_16778 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint2 "(%s) Checked type annotation %s\n" _68_16779 _68_16778)))
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
in (match (_36_1947) with
| (f, env1) -> begin
(let _36_1953 = (tc_exp (let _36_1948 = env1
in {Microsoft_FStar_Tc_Env.solver = _36_1948.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_1948.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_1948.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_1948.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_1948.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_1948.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_1948.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_1948.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_1948.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _36_1948.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _36_1948.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _36_1948.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_1948.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _36_1948.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_1948.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = _36_1948.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = _36_1948.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_1948.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_1948.Microsoft_FStar_Tc_Env.default_effects}) e1)
in (match (_36_1953) with
| (e1, c1, g1) -> begin
(let _36_1957 = (let _68_16783 = (Microsoft_FStar_Tc_Env.set_range env t.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Tc_Util.strengthen_precondition (Some ((fun ( _36_1954 ) -> (match (()) with
| () -> begin
Microsoft_FStar_Tc_Errors.ill_kinded_type
end)))) _68_16783 e1 c1 f))
in (match (_36_1957) with
| (c1, guard_f) -> begin
(match (x) with
| Support.Microsoft.FStar.Util.Inr (_36_1959) -> begin
(let _36_1970 = (match ((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
(let _36_1963 = (let _68_16784 = (Microsoft_FStar_Tc_Rel.conj_guard g1 guard_f)
in (Microsoft_FStar_Tc_Util.check_top_level env _68_16784 c1))
in (match (_36_1963) with
| (ok, c1) -> begin
(match (ok) with
| true -> begin
(e2, c1)
end
| false -> begin
(let _36_1964 = (match ((Support.ST.read Microsoft_FStar_Options.warn_top_level_effects)) with
| true -> begin
(let _68_16785 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Tc_Errors.warn _68_16785 Microsoft_FStar_Tc_Errors.top_level_effect))
end
| false -> begin
()
end)
in (let _68_16786 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e2, Microsoft_FStar_Absyn_Syntax.MaskedEffect))))
in (_68_16786, c1)))
end)
end))
end
| false -> begin
(let _36_1966 = (let _68_16787 = (Microsoft_FStar_Tc_Rel.conj_guard g1 guard_f)
in (Microsoft_FStar_Tc_Util.discharge_guard env _68_16787))
in (let _68_16788 = (c1.Microsoft_FStar_Absyn_Syntax.comp ())
in (e2, _68_16788)))
end)
in (match (_36_1970) with
| (e2, c1) -> begin
(let _36_1975 = (match (env.Microsoft_FStar_Tc_Env.generalize) with
| true -> begin
(let _68_16789 = (Microsoft_FStar_Tc_Util.generalize false env1 (((x, e1, c1))::[]))
in (Support.Prims.pipe_left Support.List.hd _68_16789))
end
| false -> begin
(x, e1, c1)
end)
in (match (_36_1975) with
| (_36_1972, e1, c1) -> begin
(let cres = (let _68_16790 = (Microsoft_FStar_Absyn_Util.ml_comp Microsoft_FStar_Tc_Recheck.t_unit top.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Prims.pipe_left Microsoft_FStar_Tc_Util.lcomp_of_comp _68_16790))
in (let cres = (match ((Microsoft_FStar_Absyn_Util.is_total_comp c1)) with
| true -> begin
cres
end
| false -> begin
(let _68_16791 = (Microsoft_FStar_Tc_Util.lcomp_of_comp c1)
in (Microsoft_FStar_Tc_Util.bind env None _68_16791 (None, cres)))
end)
in (let _36_1978 = (Support.ST.op_Colon_Equals e2.Microsoft_FStar_Absyn_Syntax.tk (Some (Microsoft_FStar_Tc_Recheck.t_unit)))
in (let _68_16800 = (let _68_16799 = (w cres)
in (let _68_16798 = (let _68_16797 = (let _68_16796 = (let _68_16795 = (let _68_16794 = (Microsoft_FStar_Absyn_Syntax.mk_lb (x, (Microsoft_FStar_Absyn_Util.comp_effect_name c1), (Microsoft_FStar_Absyn_Util.comp_result c1), e1))
in (_68_16794)::[])
in (false, _68_16795))
in (_68_16796, e2))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_let _68_16797))
in (Support.Prims.pipe_left _68_16799 _68_16798)))
in (_68_16800, cres, Microsoft_FStar_Tc_Rel.trivial_guard)))))
end))
end))
end
| Support.Microsoft.FStar.Util.Inl (bvd) -> begin
(let b = (binding_of_lb x c1.Microsoft_FStar_Absyn_Syntax.res_typ)
in (let _36_1986 = (let _68_16801 = (Microsoft_FStar_Tc_Env.push_local_binding env b)
in (tc_exp _68_16801 e2))
in (match (_36_1986) with
| (e2, c2, g2) -> begin
(let cres = (Microsoft_FStar_Tc_Util.bind env (Some (e1)) c1 (Some (b), c2))
in (let e = (let _68_16809 = (w cres)
in (let _68_16808 = (let _68_16807 = (let _68_16806 = (let _68_16805 = (let _68_16804 = (Microsoft_FStar_Absyn_Syntax.mk_lb (x, c1.Microsoft_FStar_Absyn_Syntax.eff_name, c1.Microsoft_FStar_Absyn_Syntax.res_typ, e1))
in (_68_16804)::[])
in (false, _68_16805))
in (_68_16806, e2))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_let _68_16807))
in (Support.Prims.pipe_left _68_16809 _68_16808)))
in (let g2 = (let _68_16818 = (let _68_16811 = (let _68_16810 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s bvd c1.Microsoft_FStar_Absyn_Syntax.res_typ))
in (_68_16810)::[])
in (Microsoft_FStar_Tc_Rel.close_guard _68_16811))
in (let _68_16817 = (let _68_16816 = (let _68_16815 = (let _68_16814 = (let _68_16813 = (Microsoft_FStar_Absyn_Util.bvd_to_exp bvd c1.Microsoft_FStar_Absyn_Syntax.res_typ)
in (Microsoft_FStar_Absyn_Util.mk_eq c1.Microsoft_FStar_Absyn_Syntax.res_typ c1.Microsoft_FStar_Absyn_Syntax.res_typ _68_16813 e1))
in (Support.Prims.pipe_left (fun ( _68_16812 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_68_16812)) _68_16814))
in (Microsoft_FStar_Tc_Rel.guard_of_guard_formula _68_16815))
in (Microsoft_FStar_Tc_Rel.imp_guard _68_16816 g2))
in (Support.Prims.pipe_left _68_16818 _68_16817)))
in (let guard = (let _68_16819 = (Microsoft_FStar_Tc_Rel.conj_guard g1 g2)
in (Microsoft_FStar_Tc_Rel.conj_guard guard_f _68_16819))
in (match (topt) with
| None -> begin
(let tres = cres.Microsoft_FStar_Absyn_Syntax.res_typ
in (let fvs = (Microsoft_FStar_Absyn_Util.freevars_typ tres)
in (match ((Support.Microsoft.FStar.Util.set_mem (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s bvd t) fvs.Microsoft_FStar_Absyn_Syntax.fxvs)) with
| true -> begin
(let t = (Microsoft_FStar_Tc_Util.new_tvar env0 Microsoft_FStar_Absyn_Syntax.ktype)
in (let _36_1995 = (let _68_16820 = (Microsoft_FStar_Tc_Rel.teq env tres t)
in (Support.Prims.pipe_left (Microsoft_FStar_Tc_Rel.try_discharge_guard env) _68_16820))
in (e, cres, guard)))
end
| false -> begin
(e, cres, guard)
end)))
end
| _36_1998 -> begin
(e, cres, guard)
end)))))
end)))
end)
end))
end))
end))
end))))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((false, _36_2001), _36_2004)) -> begin
(failwith ("impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((true, lbs), e1)) -> begin
(let env = (instantiate_both env)
in (let _36_2016 = (Microsoft_FStar_Tc_Env.clear_expected_typ env)
in (match (_36_2016) with
| (env0, topt) -> begin
(let is_inner_let = (Support.Prims.pipe_right lbs (Support.Microsoft.FStar.Util.for_some (fun ( _36_9 ) -> (match (_36_9) with
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inl (_36_2025); Microsoft_FStar_Absyn_Syntax.lbtyp = _36_2023; Microsoft_FStar_Absyn_Syntax.lbeff = _36_2021; Microsoft_FStar_Absyn_Syntax.lbdef = _36_2019} -> begin
true
end
| _36_2029 -> begin
false
end))))
in (let _36_2056 = (Support.Prims.pipe_right lbs (Support.List.fold_left (fun ( _36_2033 ) ( _36_2039 ) -> (match ((_36_2033, _36_2039)) with
| ((xts, env), {Microsoft_FStar_Absyn_Syntax.lbname = x; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _36_2036; Microsoft_FStar_Absyn_Syntax.lbdef = e}) -> begin
(let _36_2044 = (Microsoft_FStar_Tc_Util.extract_lb_annotation env t e)
in (match (_36_2044) with
| (_36_2041, t, check_t) -> begin
(let e = (Microsoft_FStar_Absyn_Util.unascribe e)
in (let t = (match ((not (check_t))) with
| true -> begin
t
end
| false -> begin
(match (((not (is_inner_let)) && (not (env.Microsoft_FStar_Tc_Env.generalize)))) with
| true -> begin
(let _36_2046 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_16824 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint1 "Type %s is marked as no-generalize\n" _68_16824))
end
| false -> begin
()
end)
in t)
end
| false -> begin
(let _68_16825 = (tc_typ_check_trivial (let _36_2048 = env0
in {Microsoft_FStar_Tc_Env.solver = _36_2048.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_2048.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_2048.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_2048.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_2048.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_2048.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_2048.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_2048.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_2048.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _36_2048.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _36_2048.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _36_2048.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_2048.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _36_2048.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _36_2048.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = true; Microsoft_FStar_Tc_Env.use_eq = _36_2048.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = _36_2048.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_2048.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_2048.Microsoft_FStar_Tc_Env.default_effects}) t Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_right _68_16825 (norm_t env)))
end)
end)
in (let env = (match (((Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t) && (Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str))) with
| true -> begin
(let _36_2051 = env
in {Microsoft_FStar_Tc_Env.solver = _36_2051.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_2051.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_2051.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_2051.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_2051.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_2051.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_2051.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_2051.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_2051.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _36_2051.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _36_2051.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _36_2051.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_2051.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = ((x, t))::env.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _36_2051.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_2051.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = _36_2051.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = _36_2051.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_2051.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_2051.Microsoft_FStar_Tc_Env.default_effects})
end
| false -> begin
(Microsoft_FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end)
in (((x, t, e))::xts, env))))
end))
end)) ([], env)))
in (match (_36_2056) with
| (lbs, env') -> begin
(let _36_2071 = (let _68_16831 = (let _68_16830 = (Support.Prims.pipe_right lbs Support.List.rev)
in (Support.Prims.pipe_right _68_16830 (Support.List.map (fun ( _36_2060 ) -> (match (_36_2060) with
| (x, t, e) -> begin
(let t = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env t)
in (let _36_2062 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_16829 = (Microsoft_FStar_Absyn_Print.lbname_to_string x)
in (let _68_16828 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _68_16827 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint3 "Checking %s = %s against type %s\n" _68_16829 _68_16828 _68_16827))))
end
| false -> begin
()
end)
in (let env' = (Microsoft_FStar_Tc_Env.set_expected_typ env' t)
in (let _36_2068 = (tc_total_exp env' e)
in (match (_36_2068) with
| (e, t, g) -> begin
((x, t, e), g)
end)))))
end)))))
in (Support.Prims.pipe_right _68_16831 Support.List.unzip))
in (match (_36_2071) with
| (lbs, gs) -> begin
(let g_lbs = (Support.List.fold_right Microsoft_FStar_Tc_Rel.conj_guard gs Microsoft_FStar_Tc_Rel.trivial_guard)
in (let _36_2090 = (match (((not (env.Microsoft_FStar_Tc_Env.generalize)) || is_inner_let)) with
| true -> begin
(let _68_16833 = (Support.List.map (fun ( _36_2076 ) -> (match (_36_2076) with
| (x, t, e) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_lb (x, Microsoft_FStar_Absyn_Const.effect_Tot_lid, t, e))
end)) lbs)
in (_68_16833, g_lbs))
end
| false -> begin
(let _36_2077 = (Microsoft_FStar_Tc_Util.discharge_guard env g_lbs)
in (let ecs = (let _68_16837 = (Support.Prims.pipe_right lbs (Support.List.map (fun ( _36_2082 ) -> (match (_36_2082) with
| (x, t, e) -> begin
(let _68_16836 = (let _68_16835 = (Microsoft_FStar_Absyn_Util.range_of_lb (x, t, e))
in (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Util.total_comp t) _68_16835))
in (x, e, _68_16836))
end))))
in (Microsoft_FStar_Tc_Util.generalize true env _68_16837))
in (let _68_16839 = (Support.List.map (fun ( _36_2087 ) -> (match (_36_2087) with
| (x, e, c) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_lb (x, Microsoft_FStar_Absyn_Const.effect_Tot_lid, (Microsoft_FStar_Absyn_Util.comp_result c), e))
end)) ecs)
in (_68_16839, Microsoft_FStar_Tc_Rel.trivial_guard))))
end)
in (match (_36_2090) with
| (lbs, g_lbs) -> begin
(match ((not (is_inner_let))) with
| true -> begin
(let cres = (let _68_16840 = (Microsoft_FStar_Absyn_Util.total_comp Microsoft_FStar_Tc_Recheck.t_unit top.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Prims.pipe_left Microsoft_FStar_Tc_Util.lcomp_of_comp _68_16840))
in (let _36_2092 = (Microsoft_FStar_Tc_Util.discharge_guard env g_lbs)
in (let _36_2094 = (Support.ST.op_Colon_Equals e1.Microsoft_FStar_Absyn_Syntax.tk (Some (Microsoft_FStar_Tc_Recheck.t_unit)))
in (let _68_16844 = (let _68_16843 = (w cres)
in (Support.Prims.pipe_left _68_16843 (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((true, lbs), e1))))
in (_68_16844, cres, Microsoft_FStar_Tc_Rel.trivial_guard)))))
end
| false -> begin
(let _36_2110 = (Support.Prims.pipe_right lbs (Support.List.fold_left (fun ( _36_2098 ) ( _36_2105 ) -> (match ((_36_2098, _36_2105)) with
| ((bindings, env), {Microsoft_FStar_Absyn_Syntax.lbname = x; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _36_2102; Microsoft_FStar_Absyn_Syntax.lbdef = _36_2100}) -> begin
(let b = (binding_of_lb x t)
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env b)
in ((b)::bindings, env)))
end)) ([], env)))
in (match (_36_2110) with
| (bindings, env) -> begin
(let _36_2114 = (tc_exp env e1)
in (match (_36_2114) with
| (e1, cres, g1) -> begin
(let guard = (Microsoft_FStar_Tc_Rel.conj_guard g_lbs g1)
in (let cres = (Microsoft_FStar_Tc_Util.close_comp env bindings cres)
in (let tres = (norm_t env cres.Microsoft_FStar_Absyn_Syntax.res_typ)
in (let cres = (let _36_2118 = cres
in {Microsoft_FStar_Absyn_Syntax.eff_name = _36_2118.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = tres; Microsoft_FStar_Absyn_Syntax.cflags = _36_2118.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = _36_2118.Microsoft_FStar_Absyn_Syntax.comp})
in (let e = (let _68_16849 = (w cres)
in (Support.Prims.pipe_left _68_16849 (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((true, lbs), e1))))
in (match (topt) with
| Some (_36_2123) -> begin
(e, cres, guard)
end
| None -> begin
(let fvs = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Util.freevars_typ tres)
in (match ((Support.Prims.pipe_right lbs (Support.List.tryFind (fun ( _36_10 ) -> (match (_36_10) with
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (_36_2135); Microsoft_FStar_Absyn_Syntax.lbtyp = _36_2133; Microsoft_FStar_Absyn_Syntax.lbeff = _36_2131; Microsoft_FStar_Absyn_Syntax.lbdef = _36_2129} -> begin
false
end
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inl (x); Microsoft_FStar_Absyn_Syntax.lbtyp = _36_2143; Microsoft_FStar_Absyn_Syntax.lbeff = _36_2141; Microsoft_FStar_Absyn_Syntax.lbdef = _36_2139} -> begin
(Support.Microsoft.FStar.Util.set_mem (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x Microsoft_FStar_Absyn_Syntax.tun) fvs.Microsoft_FStar_Absyn_Syntax.fxvs)
end))))) with
| Some ({Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inl (y); Microsoft_FStar_Absyn_Syntax.lbtyp = _36_2152; Microsoft_FStar_Absyn_Syntax.lbeff = _36_2150; Microsoft_FStar_Absyn_Syntax.lbdef = _36_2148}) -> begin
(let t' = (Microsoft_FStar_Tc_Util.new_tvar env0 Microsoft_FStar_Absyn_Syntax.ktype)
in (let _36_2158 = (let _68_16851 = (Microsoft_FStar_Tc_Rel.teq env tres t')
in (Support.Prims.pipe_left (Microsoft_FStar_Tc_Rel.try_discharge_guard env) _68_16851))
in (e, cres, guard)))
end
| _36_2161 -> begin
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
and tc_eqn = (fun ( scrutinee_x ) ( pat_t ) ( env ) ( _36_2168 ) -> (match (_36_2168) with
| (pattern, when_clause, branch) -> begin
(let tc_pat = (fun ( allow_implicits ) ( pat_t ) ( p0 ) -> (let _36_2176 = (Microsoft_FStar_Tc_Util.pat_as_exps allow_implicits env p0)
in (match (_36_2176) with
| (bindings, exps, p) -> begin
(let pat_env = (Support.List.fold_left Microsoft_FStar_Tc_Env.push_local_binding env bindings)
in (let _36_2185 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Pat")))) with
| true -> begin
(Support.Prims.pipe_right bindings (Support.List.iter (fun ( _36_11 ) -> (match (_36_11) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, t)) -> begin
(let _68_16864 = (Microsoft_FStar_Absyn_Print.strBvd x)
in (let _68_16863 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (Support.Microsoft.FStar.Util.fprint2 "Before tc ... pattern var %s  : %s\n" _68_16864 _68_16863)))
end
| _36_2184 -> begin
()
end))))
end
| false -> begin
()
end)
in (let _36_2190 = (Microsoft_FStar_Tc_Env.clear_expected_typ pat_env)
in (match (_36_2190) with
| (env1, _36_2189) -> begin
(let env1 = (let _36_2191 = env1
in {Microsoft_FStar_Tc_Env.solver = _36_2191.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_2191.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_2191.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_2191.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_2191.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_2191.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_2191.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_2191.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = true; Microsoft_FStar_Tc_Env.instantiate_targs = _36_2191.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _36_2191.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _36_2191.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_2191.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _36_2191.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _36_2191.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_2191.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = _36_2191.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = _36_2191.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_2191.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_2191.Microsoft_FStar_Tc_Env.default_effects})
in (let expected_pat_t = (Microsoft_FStar_Tc_Rel.unrefine env pat_t)
in (let exps = (Support.Prims.pipe_right exps (Support.List.map (fun ( e ) -> (let _36_2196 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_16867 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _68_16866 = (Microsoft_FStar_Absyn_Print.typ_to_string pat_t)
in (Support.Microsoft.FStar.Util.fprint2 "Checking pattern expression %s against expected type %s\n" _68_16867 _68_16866)))
end
| false -> begin
()
end)
in (let _36_2201 = (tc_exp env1 e)
in (match (_36_2201) with
| (e, lc, g) -> begin
(let _36_2202 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_16869 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env e)
in (let _68_16868 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env lc.Microsoft_FStar_Absyn_Syntax.res_typ)
in (Support.Microsoft.FStar.Util.fprint2 "Pre-checked pattern expression %s at type %s\n" _68_16869 _68_16868)))
end
| false -> begin
()
end)
in (let g' = (Microsoft_FStar_Tc_Rel.teq env lc.Microsoft_FStar_Absyn_Syntax.res_typ expected_pat_t)
in (let g = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (let _36_2206 = (let _68_16870 = (Microsoft_FStar_Tc_Rel.solve_deferred_constraints env g)
in (Support.Prims.pipe_left Support.Prims.ignore _68_16870))
in (let e' = (Microsoft_FStar_Tc_Normalize.norm_exp ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env e)
in (let _36_2209 = (match ((let _68_16873 = (let _68_16872 = (Microsoft_FStar_Absyn_Util.uvars_in_exp e')
in (let _68_16871 = (Microsoft_FStar_Absyn_Util.uvars_in_typ expected_pat_t)
in (Microsoft_FStar_Absyn_Util.uvars_included_in _68_16872 _68_16871)))
in (Support.Prims.pipe_left Support.Prims.op_Negation _68_16873))) with
| true -> begin
(let _68_16878 = (let _68_16877 = (let _68_16876 = (let _68_16875 = (Microsoft_FStar_Absyn_Print.exp_to_string e')
in (let _68_16874 = (Microsoft_FStar_Absyn_Print.typ_to_string expected_pat_t)
in (Support.Microsoft.FStar.Util.format2 "Implicit pattern variables in %s could not be resolved against expected type %s; please bind them explicitly" _68_16875 _68_16874)))
in (_68_16876, p.Microsoft_FStar_Absyn_Syntax.p))
in Microsoft_FStar_Absyn_Syntax.Error (_68_16877))
in (raise (_68_16878)))
end
| false -> begin
()
end)
in (let _36_2211 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_16879 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env e)
in (Support.Microsoft.FStar.Util.fprint1 "Done checking pattern expression %s\n" _68_16879))
end
| false -> begin
()
end)
in e)))))))
end))))))
in (let p = (Microsoft_FStar_Tc_Util.decorate_pattern env p exps)
in (let _36_2222 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Pat")))) with
| true -> begin
(Support.Prims.pipe_right bindings (Support.List.iter (fun ( _36_12 ) -> (match (_36_12) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, t)) -> begin
(let _68_16882 = (Microsoft_FStar_Absyn_Print.strBvd x)
in (let _68_16881 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint2 "Pattern var %s  : %s\n" _68_16882 _68_16881)))
end
| _36_2221 -> begin
()
end))))
end
| false -> begin
()
end)
in (p, bindings, pat_env, exps, Microsoft_FStar_Tc_Rel.trivial_guard))))))
end))))
end)))
in (let _36_2229 = (tc_pat true pat_t pattern)
in (match (_36_2229) with
| (pattern, bindings, pat_env, disj_exps, g_pat) -> begin
(let _36_2239 = (match (when_clause) with
| None -> begin
(None, Microsoft_FStar_Tc_Rel.trivial_guard)
end
| Some (e) -> begin
(match ((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("When clauses are not yet supported in --verify mode; they soon will be", e.Microsoft_FStar_Absyn_Syntax.pos))))
end
| false -> begin
(let _36_2236 = (let _68_16883 = (Microsoft_FStar_Tc_Env.set_expected_typ pat_env Microsoft_FStar_Tc_Recheck.t_bool)
in (tc_exp _68_16883 e))
in (match (_36_2236) with
| (e, c, g) -> begin
(Some (e), g)
end))
end)
end)
in (match (_36_2239) with
| (when_clause, g_when) -> begin
(let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _68_16885 = (Microsoft_FStar_Absyn_Util.mk_eq Microsoft_FStar_Absyn_Util.t_bool Microsoft_FStar_Absyn_Util.t_bool w Microsoft_FStar_Absyn_Const.exp_true_bool)
in (Support.Prims.pipe_left (fun ( _68_16884 ) -> Some (_68_16884)) _68_16885))
end)
in (let _36_2247 = (tc_exp pat_env branch)
in (match (_36_2247) with
| (branch, c, g_branch) -> begin
(let scrutinee = (Microsoft_FStar_Absyn_Util.bvd_to_exp scrutinee_x pat_t)
in (let _36_2252 = (let _68_16886 = (Microsoft_FStar_Tc_Env.push_local_binding env (Microsoft_FStar_Tc_Env.Binding_var ((scrutinee_x, pat_t))))
in (Support.Prims.pipe_right _68_16886 Microsoft_FStar_Tc_Env.clear_expected_typ))
in (match (_36_2252) with
| (scrutinee_env, _36_2251) -> begin
(let c = (let eqs = (Support.Prims.pipe_right disj_exps (Support.List.fold_left (fun ( fopt ) ( e ) -> (let e = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
fopt
end
| _36_2266 -> begin
(let clause = (let _68_16890 = (Microsoft_FStar_Tc_Recheck.recompute_typ scrutinee)
in (let _68_16889 = (Microsoft_FStar_Tc_Recheck.recompute_typ e)
in (Microsoft_FStar_Absyn_Util.mk_eq _68_16890 _68_16889 scrutinee e)))
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _68_16892 = (Microsoft_FStar_Absyn_Util.mk_disj clause f)
in (Support.Prims.pipe_left (fun ( _68_16891 ) -> Some (_68_16891)) _68_16892))
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
(let _68_16895 = (let _68_16894 = (Microsoft_FStar_Absyn_Util.mk_conj f w)
in (Support.Prims.pipe_left (fun ( _68_16893 ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_68_16893)) _68_16894))
in (Microsoft_FStar_Tc_Util.weaken_precondition env c _68_16895))
end
| (None, Some (w)) -> begin
(Microsoft_FStar_Tc_Util.weaken_precondition env c (Microsoft_FStar_Tc_Rel.NonTrivial (w)))
end)
in (Microsoft_FStar_Tc_Util.close_comp env bindings c)))
in (let discriminate = (fun ( scrutinee ) ( f ) -> (let disc = (let _68_16902 = (let _68_16900 = (Microsoft_FStar_Absyn_Util.mk_discriminator f.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Util.fvar None _68_16900))
in (let _68_16901 = (Microsoft_FStar_Absyn_Syntax.range_of_lid f.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Prims.pipe_left _68_16902 _68_16901)))
in (let disc = (let _68_16905 = (let _68_16904 = (let _68_16903 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.varg scrutinee)
in (_68_16903)::[])
in (disc, _68_16904))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _68_16905 None scrutinee.Microsoft_FStar_Absyn_Syntax.pos))
in (Microsoft_FStar_Absyn_Util.mk_eq Microsoft_FStar_Absyn_Util.t_bool Microsoft_FStar_Absyn_Util.t_bool disc Microsoft_FStar_Absyn_Const.exp_true_bool))))
in (let rec mk_guard = (fun ( scrutinee ) ( pat_exp ) -> (let pat_exp = (Microsoft_FStar_Absyn_Util.compress_exp pat_exp)
in (match (pat_exp.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) | (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_constant (Microsoft_FStar_Absyn_Syntax.Const_unit)) -> begin
(Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (_36_2324) -> begin
(let _68_16914 = (let _68_16913 = (let _68_16912 = (Microsoft_FStar_Absyn_Syntax.varg scrutinee)
in (let _68_16911 = (let _68_16910 = (Microsoft_FStar_Absyn_Syntax.varg pat_exp)
in (_68_16910)::[])
in (_68_16912)::_68_16911))
in (Microsoft_FStar_Absyn_Util.teq, _68_16913))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_16914 None scrutinee.Microsoft_FStar_Absyn_Syntax.pos))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((f, _36_2328)) -> begin
(discriminate scrutinee f)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((f, _36_2341)); Microsoft_FStar_Absyn_Syntax.tk = _36_2338; Microsoft_FStar_Absyn_Syntax.pos = _36_2336; Microsoft_FStar_Absyn_Syntax.fvs = _36_2334; Microsoft_FStar_Absyn_Syntax.uvs = _36_2332}, args)) -> begin
(let head = (discriminate scrutinee f)
in (let sub_term_guards = (let _68_16922 = (Support.Prims.pipe_right args (Support.List.mapi (fun ( i ) ( arg ) -> (match ((Support.Prims.fst arg)) with
| Support.Microsoft.FStar.Util.Inl (_36_2352) -> begin
[]
end
| Support.Microsoft.FStar.Util.Inr (ei) -> begin
(let projector = (Microsoft_FStar_Tc_Env.lookup_projector env f.Microsoft_FStar_Absyn_Syntax.v i)
in (let sub_term = (let _68_16920 = (let _68_16919 = (Microsoft_FStar_Absyn_Util.fvar None projector f.Microsoft_FStar_Absyn_Syntax.p)
in (let _68_16918 = (let _68_16917 = (Microsoft_FStar_Absyn_Syntax.varg scrutinee)
in (_68_16917)::[])
in (_68_16919, _68_16918)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _68_16920 None f.Microsoft_FStar_Absyn_Syntax.p))
in (let _68_16921 = (mk_guard sub_term ei)
in (_68_16921)::[])))
end))))
in (Support.Prims.pipe_right _68_16922 Support.List.flatten))
in (Microsoft_FStar_Absyn_Util.mk_conj_l ((head)::sub_term_guards))))
end
| _36_2360 -> begin
(let _68_16925 = (let _68_16924 = (Support.Microsoft.FStar.Range.string_of_range pat_exp.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_16923 = (Microsoft_FStar_Absyn_Print.exp_to_string pat_exp)
in (Support.Microsoft.FStar.Util.format2 "tc_eqn: Impossible (%s) %s" _68_16924 _68_16923)))
in (failwith (_68_16925)))
end)))
in (let mk_guard = (fun ( s ) ( tsc ) ( pat ) -> (match ((not ((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)))) with
| true -> begin
(Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
end
| false -> begin
(let t = (mk_guard s pat)
in (let _36_2369 = (tc_typ_check scrutinee_env t Microsoft_FStar_Absyn_Syntax.mk_Kind_type)
in (match (_36_2369) with
| (t, _36_2368) -> begin
t
end)))
end))
in (let path_guard = (let _68_16934 = (Support.Prims.pipe_right disj_exps (Support.List.map (fun ( e ) -> (let _68_16933 = (Microsoft_FStar_Tc_Normalize.norm_exp ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env e)
in (mk_guard scrutinee pat_t _68_16933)))))
in (Support.Prims.pipe_right _68_16934 Microsoft_FStar_Absyn_Util.mk_disj_l))
in (let path_guard = (match (when_condition) with
| None -> begin
path_guard
end
| Some (w) -> begin
(Microsoft_FStar_Absyn_Util.mk_conj path_guard w)
end)
in (let guard = (let _68_16935 = (Microsoft_FStar_Tc_Rel.conj_guard g_when g_branch)
in (Microsoft_FStar_Tc_Rel.conj_guard g_pat _68_16935))
in (let _36_2377 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_16936 = (Microsoft_FStar_Tc_Rel.guard_to_string env guard)
in (Support.Prims.pipe_left (Support.Microsoft.FStar.Util.fprint1 "Carrying guard from match: %s\n") _68_16936))
end
| false -> begin
()
end)
in (let _68_16938 = (let _68_16937 = (Microsoft_FStar_Tc_Rel.conj_guard g_when g_branch)
in (Microsoft_FStar_Tc_Rel.conj_guard g_pat _68_16937))
in ((pattern, when_clause, branch), path_guard, c, _68_16938))))))))))
end)))
end)))
end))
end)))
end))
and tc_kind_trivial = (fun ( env ) ( k ) -> (let _36_2383 = (tc_kind env k)
in (match (_36_2383) with
| (k, g) -> begin
(let _36_2384 = (Microsoft_FStar_Tc_Util.discharge_guard env g)
in k)
end)))
and tc_typ_trivial = (fun ( env ) ( t ) -> (let _36_2391 = (tc_typ env t)
in (match (_36_2391) with
| (t, k, g) -> begin
(let _36_2392 = (Microsoft_FStar_Tc_Util.discharge_guard env g)
in (t, k))
end)))
and tc_typ_check_trivial = (fun ( env ) ( t ) ( k ) -> (let _36_2399 = (tc_typ_check env t k)
in (match (_36_2399) with
| (t, f) -> begin
(let _36_2400 = (Microsoft_FStar_Tc_Util.discharge_guard env f)
in t)
end)))
and tc_total_exp = (fun ( env ) ( e ) -> (let _36_2407 = (tc_exp env e)
in (match (_36_2407) with
| (e, c, g) -> begin
(match ((Microsoft_FStar_Absyn_Util.is_total_lcomp c)) with
| true -> begin
(e, c.Microsoft_FStar_Absyn_Syntax.res_typ, g)
end
| false -> begin
(let g = (Microsoft_FStar_Tc_Rel.solve_deferred_constraints env g)
in (let c = (let _68_16948 = (c.Microsoft_FStar_Absyn_Syntax.comp ())
in (Support.Prims.pipe_right _68_16948 (norm_c env)))
in (match ((let _68_16950 = (let _68_16949 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Util.total_comp (Microsoft_FStar_Absyn_Util.comp_result c) _68_16949))
in (Microsoft_FStar_Tc_Rel.sub_comp env c _68_16950))) with
| Some (g') -> begin
(let _68_16951 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (e, (Microsoft_FStar_Absyn_Util.comp_result c), _68_16951))
end
| _36_2413 -> begin
(let _68_16954 = (let _68_16953 = (let _68_16952 = (Microsoft_FStar_Tc_Errors.expected_pure_expression e c)
in (_68_16952, e.Microsoft_FStar_Absyn_Syntax.pos))
in Microsoft_FStar_Absyn_Syntax.Error (_68_16953))
in (raise (_68_16954)))
end)))
end)
end)))
and tc_ghost_exp = (fun ( env ) ( e ) -> (let _36_2419 = (tc_exp env e)
in (match (_36_2419) with
| (e, c, g) -> begin
(match ((Microsoft_FStar_Absyn_Util.is_total_lcomp c)) with
| true -> begin
(e, c.Microsoft_FStar_Absyn_Syntax.res_typ, g)
end
| false -> begin
(let c = (let _68_16957 = (c.Microsoft_FStar_Absyn_Syntax.comp ())
in (Support.Prims.pipe_right _68_16957 (norm_c env)))
in (let expected_c = (Microsoft_FStar_Absyn_Util.gtotal_comp (Microsoft_FStar_Absyn_Util.comp_result c))
in (let g = (Microsoft_FStar_Tc_Rel.solve_deferred_constraints env g)
in (match ((Microsoft_FStar_Tc_Rel.sub_comp (let _36_2423 = env
in {Microsoft_FStar_Tc_Env.solver = _36_2423.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_2423.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_2423.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_2423.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_2423.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_2423.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_2423.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_2423.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_2423.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _36_2423.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _36_2423.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _36_2423.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_2423.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _36_2423.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _36_2423.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_2423.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = false; Microsoft_FStar_Tc_Env.is_iface = _36_2423.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_2423.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_2423.Microsoft_FStar_Tc_Env.default_effects}) c expected_c)) with
| Some (g') -> begin
(let _68_16958 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (e, (Microsoft_FStar_Absyn_Util.comp_result c), _68_16958))
end
| _36_2428 -> begin
(let _68_16961 = (let _68_16960 = (let _68_16959 = (Microsoft_FStar_Tc_Errors.expected_ghost_expression e c)
in (_68_16959, e.Microsoft_FStar_Absyn_Syntax.pos))
in Microsoft_FStar_Absyn_Syntax.Error (_68_16960))
in (raise (_68_16961)))
end))))
end)
end)))

let tc_tparams = (fun ( env ) ( tps ) -> (let _36_2434 = (tc_binders env tps)
in (match (_36_2434) with
| (tps, env, g) -> begin
(let _36_2435 = (Microsoft_FStar_Tc_Util.force_trivial env g)
in (tps, env))
end)))

let a_kwp_a = (fun ( env ) ( m ) ( s ) -> (match (s.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow (((Support.Microsoft.FStar.Util.Inl (a), _36_2454)::(Support.Microsoft.FStar.Util.Inl (wp), _36_2449)::(Support.Microsoft.FStar.Util.Inl (_36_2441), _36_2444)::[], _36_2458)) -> begin
(a, wp.Microsoft_FStar_Absyn_Syntax.sort)
end
| _36_2462 -> begin
(let _68_16975 = (let _68_16974 = (let _68_16973 = (Microsoft_FStar_Tc_Errors.unexpected_signature_for_monad env m s)
in (let _68_16972 = (Microsoft_FStar_Absyn_Syntax.range_of_lid m)
in (_68_16973, _68_16972)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_16974))
in (raise (_68_16975)))
end))

let rec tc_eff_decl = (fun ( env ) ( m ) -> (let _36_2468 = (tc_binders env m.Microsoft_FStar_Absyn_Syntax.binders)
in (match (_36_2468) with
| (binders, env, g) -> begin
(let _36_2469 = (Microsoft_FStar_Tc_Util.discharge_guard env g)
in (let mk = (tc_kind_trivial env m.Microsoft_FStar_Absyn_Syntax.signature)
in (let _36_2474 = (a_kwp_a env m.Microsoft_FStar_Absyn_Syntax.mname mk)
in (match (_36_2474) with
| (a, kwp_a) -> begin
(let a_typ = (Microsoft_FStar_Absyn_Util.btvar_to_typ a)
in (let b = (let _68_16989 = (Microsoft_FStar_Absyn_Syntax.range_of_lid m.Microsoft_FStar_Absyn_Syntax.mname)
in (Microsoft_FStar_Absyn_Util.gen_bvar_p _68_16989 Microsoft_FStar_Absyn_Syntax.ktype))
in (let b_typ = (Microsoft_FStar_Absyn_Util.btvar_to_typ b)
in (let kwp_b = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, b_typ)))::[]) kwp_a)
in (let kwlp_a = kwp_a
in (let kwlp_b = kwp_b
in (let a_kwp_b = (let _68_16992 = (let _68_16991 = (let _68_16990 = (Microsoft_FStar_Absyn_Syntax.null_v_binder a_typ)
in (_68_16990)::[])
in (_68_16991, kwp_b))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_16992 a_typ.Microsoft_FStar_Absyn_Syntax.pos))
in (let a_kwlp_b = a_kwp_b
in (let w = (fun ( k ) -> (let _68_17000 = (Microsoft_FStar_Absyn_Syntax.range_of_lid m.Microsoft_FStar_Absyn_Syntax.mname)
in (k _68_17000)))
in (let ret = (let expected_k = (let _68_17007 = (let _68_17006 = (let _68_17005 = (let _68_17004 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _68_17003 = (let _68_17002 = (Microsoft_FStar_Absyn_Syntax.null_v_binder a_typ)
in (_68_17002)::[])
in (_68_17004)::_68_17003))
in (_68_17005, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_17006))
in (Support.Prims.pipe_left w _68_17007))
in (let _68_17008 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.ret expected_k)
in (Support.Prims.pipe_right _68_17008 (norm_t env))))
in (let bind_wp = (let expected_k = (let _68_17023 = (let _68_17022 = (let _68_17021 = (let _68_17020 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _68_17019 = (let _68_17018 = (Microsoft_FStar_Absyn_Syntax.t_binder b)
in (let _68_17017 = (let _68_17016 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _68_17015 = (let _68_17014 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _68_17013 = (let _68_17012 = (Microsoft_FStar_Absyn_Syntax.null_t_binder a_kwp_b)
in (let _68_17011 = (let _68_17010 = (Microsoft_FStar_Absyn_Syntax.null_t_binder a_kwlp_b)
in (_68_17010)::[])
in (_68_17012)::_68_17011))
in (_68_17014)::_68_17013))
in (_68_17016)::_68_17015))
in (_68_17018)::_68_17017))
in (_68_17020)::_68_17019))
in (_68_17021, kwp_b))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_17022))
in (Support.Prims.pipe_left w _68_17023))
in (let _68_17024 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.bind_wp expected_k)
in (Support.Prims.pipe_right _68_17024 (norm_t env))))
in (let bind_wlp = (let expected_k = (let _68_17035 = (let _68_17034 = (let _68_17033 = (let _68_17032 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _68_17031 = (let _68_17030 = (Microsoft_FStar_Absyn_Syntax.t_binder b)
in (let _68_17029 = (let _68_17028 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _68_17027 = (let _68_17026 = (Microsoft_FStar_Absyn_Syntax.null_t_binder a_kwlp_b)
in (_68_17026)::[])
in (_68_17028)::_68_17027))
in (_68_17030)::_68_17029))
in (_68_17032)::_68_17031))
in (_68_17033, kwlp_b))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_17034))
in (Support.Prims.pipe_left w _68_17035))
in (let _68_17036 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.bind_wlp expected_k)
in (Support.Prims.pipe_right _68_17036 (norm_t env))))
in (let if_then_else = (let expected_k = (let _68_17047 = (let _68_17046 = (let _68_17045 = (let _68_17044 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _68_17043 = (let _68_17042 = (Microsoft_FStar_Absyn_Syntax.t_binder b)
in (let _68_17041 = (let _68_17040 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _68_17039 = (let _68_17038 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_68_17038)::[])
in (_68_17040)::_68_17039))
in (_68_17042)::_68_17041))
in (_68_17044)::_68_17043))
in (_68_17045, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_17046))
in (Support.Prims.pipe_left w _68_17047))
in (let _68_17048 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.if_then_else expected_k)
in (Support.Prims.pipe_right _68_17048 (norm_t env))))
in (let ite_wp = (let expected_k = (let _68_17057 = (let _68_17056 = (let _68_17055 = (let _68_17054 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _68_17053 = (let _68_17052 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _68_17051 = (let _68_17050 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_68_17050)::[])
in (_68_17052)::_68_17051))
in (_68_17054)::_68_17053))
in (_68_17055, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_17056))
in (Support.Prims.pipe_left w _68_17057))
in (let _68_17058 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.ite_wp expected_k)
in (Support.Prims.pipe_right _68_17058 (norm_t env))))
in (let ite_wlp = (let expected_k = (let _68_17065 = (let _68_17064 = (let _68_17063 = (let _68_17062 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _68_17061 = (let _68_17060 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (_68_17060)::[])
in (_68_17062)::_68_17061))
in (_68_17063, kwlp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_17064))
in (Support.Prims.pipe_left w _68_17065))
in (let _68_17066 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.ite_wlp expected_k)
in (Support.Prims.pipe_right _68_17066 (norm_t env))))
in (let wp_binop = (let expected_k = (let _68_17078 = (let _68_17077 = (let _68_17076 = (let _68_17075 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _68_17074 = (let _68_17073 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _68_17072 = (let _68_17071 = (let _68_17068 = (Microsoft_FStar_Absyn_Const.kbin Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Syntax.null_t_binder _68_17068))
in (let _68_17070 = (let _68_17069 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_68_17069)::[])
in (_68_17071)::_68_17070))
in (_68_17073)::_68_17072))
in (_68_17075)::_68_17074))
in (_68_17076, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_17077))
in (Support.Prims.pipe_left w _68_17078))
in (let _68_17079 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.wp_binop expected_k)
in (Support.Prims.pipe_right _68_17079 (norm_t env))))
in (let wp_as_type = (let expected_k = (let _68_17086 = (let _68_17085 = (let _68_17084 = (let _68_17083 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _68_17082 = (let _68_17081 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_68_17081)::[])
in (_68_17083)::_68_17082))
in (_68_17084, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_17085))
in (Support.Prims.pipe_left w _68_17086))
in (let _68_17087 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.wp_as_type expected_k)
in (Support.Prims.pipe_right _68_17087 (norm_t env))))
in (let close_wp = (let expected_k = (let _68_17096 = (let _68_17095 = (let _68_17094 = (let _68_17093 = (Microsoft_FStar_Absyn_Syntax.t_binder b)
in (let _68_17092 = (let _68_17091 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _68_17090 = (let _68_17089 = (Microsoft_FStar_Absyn_Syntax.null_t_binder a_kwp_b)
in (_68_17089)::[])
in (_68_17091)::_68_17090))
in (_68_17093)::_68_17092))
in (_68_17094, kwp_b))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_17095))
in (Support.Prims.pipe_left w _68_17096))
in (let _68_17097 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.close_wp expected_k)
in (Support.Prims.pipe_right _68_17097 (norm_t env))))
in (let close_wp_t = (let expected_k = (let _68_17110 = (let _68_17109 = (let _68_17108 = (let _68_17107 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _68_17106 = (let _68_17105 = (let _68_17104 = (let _68_17103 = (let _68_17102 = (let _68_17101 = (let _68_17100 = (Microsoft_FStar_Absyn_Syntax.null_t_binder Microsoft_FStar_Absyn_Syntax.ktype)
in (_68_17100)::[])
in (_68_17101, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_17102))
in (Support.Prims.pipe_left w _68_17103))
in (Microsoft_FStar_Absyn_Syntax.null_t_binder _68_17104))
in (_68_17105)::[])
in (_68_17107)::_68_17106))
in (_68_17108, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_17109))
in (Support.Prims.pipe_left w _68_17110))
in (let _68_17111 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.close_wp_t expected_k)
in (Support.Prims.pipe_right _68_17111 (norm_t env))))
in (let _36_2508 = (let expected_k = (let _68_17120 = (let _68_17119 = (let _68_17118 = (let _68_17117 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _68_17116 = (let _68_17115 = (Microsoft_FStar_Absyn_Syntax.null_t_binder Microsoft_FStar_Absyn_Syntax.ktype)
in (let _68_17114 = (let _68_17113 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_68_17113)::[])
in (_68_17115)::_68_17114))
in (_68_17117)::_68_17116))
in (_68_17118, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_17119))
in (Support.Prims.pipe_left w _68_17120))
in (let _68_17124 = (let _68_17121 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.assert_p expected_k)
in (Support.Prims.pipe_right _68_17121 (norm_t env)))
in (let _68_17123 = (let _68_17122 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.assume_p expected_k)
in (Support.Prims.pipe_right _68_17122 (norm_t env)))
in (_68_17124, _68_17123))))
in (match (_36_2508) with
| (assert_p, assume_p) -> begin
(let null_wp = (let expected_k = (let _68_17129 = (let _68_17128 = (let _68_17127 = (let _68_17126 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (_68_17126)::[])
in (_68_17127, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_17128))
in (Support.Prims.pipe_left w _68_17129))
in (let _68_17130 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.null_wp expected_k)
in (Support.Prims.pipe_right _68_17130 (norm_t env))))
in (let trivial_wp = (let expected_k = (let _68_17137 = (let _68_17136 = (let _68_17135 = (let _68_17134 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _68_17133 = (let _68_17132 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_68_17132)::[])
in (_68_17134)::_68_17133))
in (_68_17135, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_17136))
in (Support.Prims.pipe_left w _68_17137))
in (let _68_17138 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.trivial expected_k)
in (Support.Prims.pipe_right _68_17138 (norm_t env))))
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
(let _36_2527 = (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.refresh ())
in (let _36_2529 = (let _68_17142 = (Microsoft_FStar_Options.reset_options ())
in (Support.Prims.pipe_right _68_17142 Support.Prims.ignore))
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
(let _36_2544 = (let _68_17143 = (Microsoft_FStar_Tc_Env.lookup_effect_lid env sub.Microsoft_FStar_Absyn_Syntax.source)
in (a_kwp_a env sub.Microsoft_FStar_Absyn_Syntax.source _68_17143))
in (match (_36_2544) with
| (a, kwp_a_src) -> begin
(let _36_2547 = (let _68_17144 = (Microsoft_FStar_Tc_Env.lookup_effect_lid env sub.Microsoft_FStar_Absyn_Syntax.target)
in (a_kwp_a env sub.Microsoft_FStar_Absyn_Syntax.target _68_17144))
in (match (_36_2547) with
| (b, kwp_b_tgt) -> begin
(let kwp_a_tgt = (let _68_17148 = (let _68_17147 = (let _68_17146 = (let _68_17145 = (Microsoft_FStar_Absyn_Util.btvar_to_typ a)
in (b.Microsoft_FStar_Absyn_Syntax.v, _68_17145))
in Support.Microsoft.FStar.Util.Inl (_68_17146))
in (_68_17147)::[])
in (Microsoft_FStar_Absyn_Util.subst_kind _68_17148 kwp_b_tgt))
in (let expected_k = (let _68_17154 = (let _68_17153 = (let _68_17152 = (let _68_17151 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _68_17150 = (let _68_17149 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a_src)
in (_68_17149)::[])
in (_68_17151)::_68_17150))
in (_68_17152, kwp_a_tgt))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_17153))
in (Support.Prims.pipe_right r _68_17154))
in (let lift = (tc_typ_check_trivial env sub.Microsoft_FStar_Absyn_Syntax.lift expected_k)
in (let sub = (let _36_2551 = sub
in {Microsoft_FStar_Absyn_Syntax.source = _36_2551.Microsoft_FStar_Absyn_Syntax.source; Microsoft_FStar_Absyn_Syntax.target = _36_2551.Microsoft_FStar_Absyn_Syntax.target; Microsoft_FStar_Absyn_Syntax.lift = lift})
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_sub_effect ((sub, r))
in (let env = (Microsoft_FStar_Tc_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, _mutuals, _data, tags, r)) -> begin
(let env = (Microsoft_FStar_Tc_Env.set_range env r)
in (let _36_2568 = (tc_tparams env tps)
in (match (_36_2568) with
| (tps, env) -> begin
(let k = (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
Microsoft_FStar_Absyn_Syntax.ktype
end
| _36_2571 -> begin
(tc_kind_trivial env k)
end)
in (let _36_2573 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _68_17157 = (Microsoft_FStar_Absyn_Print.sli lid)
in (let _68_17156 = (let _68_17155 = (Microsoft_FStar_Absyn_Util.close_kind tps k)
in (Microsoft_FStar_Absyn_Print.kind_to_string _68_17155))
in (Support.Microsoft.FStar.Util.fprint2 "Checked %s at kind %s\n" _68_17157 _68_17156)))
end
| false -> begin
()
end)
in (let k = (norm_k env k)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, _mutuals, _data, tags, r))
in (let _36_2591 = (match ((Microsoft_FStar_Absyn_Util.compress_kind k)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_uvar (_36_2586); Microsoft_FStar_Absyn_Syntax.tk = _36_2584; Microsoft_FStar_Absyn_Syntax.pos = _36_2582; Microsoft_FStar_Absyn_Syntax.fvs = _36_2580; Microsoft_FStar_Absyn_Syntax.uvs = _36_2578} -> begin
(let _68_17158 = (Microsoft_FStar_Tc_Rel.keq env None k Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_left (Microsoft_FStar_Tc_Util.force_trivial env) _68_17158))
end
| _36_2590 -> begin
()
end)
in (let env = (Microsoft_FStar_Tc_Env.push_sigelt env se)
in (se, env)))))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev ((lid, tps, k, r)) -> begin
(let env0 = env
in (let env = (Microsoft_FStar_Tc_Env.set_range env r)
in (let _36_2604 = (tc_tparams env tps)
in (match (_36_2604) with
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
in (let _36_2619 = (tc_tparams env tps)
in (match (_36_2619) with
| (tps, env) -> begin
(let _36_2622 = (tc_comp env c)
in (match (_36_2622) with
| (c, g) -> begin
(let tags = (Support.Prims.pipe_right tags (Support.List.map (fun ( _36_13 ) -> (match (_36_13) with
| Microsoft_FStar_Absyn_Syntax.DefaultEffect (None) -> begin
(let c' = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _68_17161 = (Support.Prims.pipe_right c'.Microsoft_FStar_Absyn_Syntax.effect_name (fun ( _68_17160 ) -> Some (_68_17160)))
in Microsoft_FStar_Absyn_Syntax.DefaultEffect (_68_17161)))
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
in (let _36_2642 = (tc_tparams env tps)
in (match (_36_2642) with
| (tps, env') -> begin
(let _36_2648 = (let _68_17165 = (tc_typ_trivial env' t)
in (Support.Prims.pipe_right _68_17165 (fun ( _36_2645 ) -> (match (_36_2645) with
| (t, k) -> begin
(let _68_17164 = (norm_t env' t)
in (let _68_17163 = (norm_k env' k)
in (_68_17164, _68_17163)))
end))))
in (match (_36_2648) with
| (t, k1) -> begin
(let k2 = (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
k1
end
| _36_2651 -> begin
(let k2 = (let _68_17166 = (tc_kind_trivial env' k)
in (Support.Prims.pipe_right _68_17166 (norm_k env)))
in (let _36_2653 = (let _68_17167 = (Microsoft_FStar_Tc_Rel.keq env' (Some (t)) k1 k2)
in (Support.Prims.pipe_left (Microsoft_FStar_Tc_Util.force_trivial env') _68_17167))
in k2))
end)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, k2, t, tags, r))
in (let env = (Microsoft_FStar_Tc_Env.push_sigelt env se)
in (se, env))))
end))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, t, tycon, quals, mutuals, r)) -> begin
(let _36_2671 = tycon
in (match (_36_2671) with
| (tname, _36_2668, _36_2670) -> begin
(let env = (Microsoft_FStar_Tc_Env.set_range env r)
in (let t = (tc_typ_check_trivial env t Microsoft_FStar_Absyn_Syntax.ktype)
in (let t = (norm_t env t)
in (let _36_2683 = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((formals, cod)) -> begin
(formals, (Microsoft_FStar_Absyn_Util.comp_result cod))
end
| _36_2680 -> begin
([], t)
end)
in (match (_36_2683) with
| (formals, result_t) -> begin
(let positivity_check = (fun ( formal ) -> (match ((Support.Prims.fst formal)) with
| Support.Microsoft.FStar.Util.Inl (_36_2687) -> begin
()
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let t = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.DeltaHard)::[]) env x.Microsoft_FStar_Absyn_Syntax.sort)
in (match (((Microsoft_FStar_Absyn_Util.is_function_typ t) && (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t))) with
| true -> begin
(let _36_2695 = (let _68_17170 = (Microsoft_FStar_Absyn_Util.function_formals t)
in (Support.Prims.pipe_right _68_17170 Support.Microsoft.FStar.Util.must))
in (match (_36_2695) with
| (formals, _36_2694) -> begin
(Support.Prims.pipe_right formals (Support.List.iter (fun ( _36_2699 ) -> (match (_36_2699) with
| (a, _36_2698) -> begin
(match (a) with
| Support.Microsoft.FStar.Util.Inl (_36_2701) -> begin
()
end
| Support.Microsoft.FStar.Util.Inr (y) -> begin
(let t = y.Microsoft_FStar_Absyn_Syntax.sort
in (Microsoft_FStar_Absyn_Visit.collect_from_typ (fun ( b ) ( t ) -> (match ((let _68_17174 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _68_17174.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (f) -> begin
(match ((Support.List.tryFind (Microsoft_FStar_Absyn_Syntax.lid_equals f.Microsoft_FStar_Absyn_Syntax.v) mutuals)) with
| None -> begin
()
end
| Some (tname) -> begin
(let _68_17180 = (let _68_17179 = (let _68_17178 = (let _68_17176 = (let _68_17175 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) lid _68_17175))
in (Microsoft_FStar_Tc_Errors.constructor_fails_the_positivity_check env _68_17176 tname))
in (let _68_17177 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (_68_17178, _68_17177)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_17179))
in (raise (_68_17180)))
end)
end
| _36_2714 -> begin
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
in (let _36_2715 = (Support.Prims.pipe_right formals (Support.List.iter positivity_check))
in (let _36_2722 = (match ((Microsoft_FStar_Absyn_Util.destruct result_t tname)) with
| Some (_36_2718) -> begin
()
end
| _36_2721 -> begin
(let _68_17187 = (let _68_17186 = (let _68_17185 = (let _68_17183 = (let _68_17181 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) lid _68_17181))
in (let _68_17182 = (Microsoft_FStar_Absyn_Util.ftv tname Microsoft_FStar_Absyn_Syntax.kun)
in (Microsoft_FStar_Tc_Errors.constructor_builds_the_wrong_type env _68_17183 result_t _68_17182)))
in (let _68_17184 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (_68_17185, _68_17184)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_17186))
in (raise (_68_17187)))
end)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, t, tycon, quals, mutuals, r))
in (let env = (Microsoft_FStar_Tc_Env.push_sigelt env se)
in (let _36_2726 = (match ((log env)) with
| true -> begin
(let _68_17189 = (let _68_17188 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (Support.Microsoft.FStar.Util.format2 "data %s : %s\n" lid.Microsoft_FStar_Absyn_Syntax.str _68_17188))
in (Support.Prims.pipe_left Support.Microsoft.FStar.Util.print_string _68_17189))
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
in (let t = (let _68_17190 = (tc_typ_check_trivial env t Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_right _68_17190 (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.SNComp)::[]) env)))
in (let _36_2736 = (Microsoft_FStar_Tc_Util.check_uvars r t)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, r))
in (let env = (Microsoft_FStar_Tc_Env.push_sigelt env se)
in (let _36_2740 = (match ((log env)) with
| true -> begin
(let _68_17192 = (let _68_17191 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (Support.Microsoft.FStar.Util.format2 "val %s : %s\n" lid.Microsoft_FStar_Absyn_Syntax.str _68_17191))
in (Support.Prims.pipe_left Support.Microsoft.FStar.Util.print_string _68_17192))
end
| false -> begin
()
end)
in (se, env)))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_assume ((lid, phi, quals, r)) -> begin
(let env = (Microsoft_FStar_Tc_Env.set_range env r)
in (let phi = (let _68_17193 = (tc_typ_check_trivial env phi Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_right _68_17193 (norm_t env)))
in (let _36_2750 = (Microsoft_FStar_Tc_Util.check_uvars r phi)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_assume ((lid, phi, quals, r))
in (let env = (Microsoft_FStar_Tc_Env.push_sigelt env se)
in (se, env))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, r, lids, quals)) -> begin
(let env = (Microsoft_FStar_Tc_Env.set_range env r)
in (let _36_2803 = (Support.Prims.pipe_right (Support.Prims.snd lbs) (Support.List.fold_left (fun ( _36_2763 ) ( lb ) -> (match (_36_2763) with
| (gen, lbs) -> begin
(let _36_2800 = (match (lb) with
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inl (_36_2772); Microsoft_FStar_Absyn_Syntax.lbtyp = _36_2770; Microsoft_FStar_Absyn_Syntax.lbeff = _36_2768; Microsoft_FStar_Absyn_Syntax.lbdef = _36_2766} -> begin
(failwith ("impossible"))
end
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (l); Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _36_2777; Microsoft_FStar_Absyn_Syntax.lbdef = e} -> begin
(let _36_2797 = (match ((Microsoft_FStar_Tc_Env.try_lookup_val_decl env l)) with
| None -> begin
(gen, lb)
end
| Some ((t', _36_2785)) -> begin
(let _36_2788 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _68_17196 = (Microsoft_FStar_Absyn_Print.typ_to_string t')
in (Support.Microsoft.FStar.Util.fprint2 "Using annotation %s for let binding %s\n" _68_17196 l.Microsoft_FStar_Absyn_Syntax.str))
end
| false -> begin
()
end)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(let _68_17197 = (Microsoft_FStar_Absyn_Syntax.mk_lb (Support.Microsoft.FStar.Util.Inr (l), Microsoft_FStar_Absyn_Const.effect_ALL_lid, t', e))
in (false, _68_17197))
end
| _36_2792 -> begin
(let _36_2793 = (match ((not (deserialized))) with
| true -> begin
(let _68_17199 = (let _68_17198 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format1 "%s: Warning: Annotation from val declaration overrides inline type annotation\n" _68_17198))
in (Support.Prims.pipe_left Support.Microsoft.FStar.Util.print_string _68_17199))
end
| false -> begin
()
end)
in (let _68_17200 = (Microsoft_FStar_Absyn_Syntax.mk_lb (Support.Microsoft.FStar.Util.Inr (l), Microsoft_FStar_Absyn_Const.effect_ALL_lid, t', e))
in (false, _68_17200)))
end))
end)
in (match (_36_2797) with
| (gen, lb) -> begin
(gen, lb)
end))
end)
in (match (_36_2800) with
| (gen, lb) -> begin
(gen, (lb)::lbs)
end))
end)) (true, [])))
in (match (_36_2803) with
| (generalize, lbs') -> begin
(let lbs' = (Support.List.rev lbs')
in (let e = (let _68_17205 = (let _68_17204 = (let _68_17203 = (syn' env Microsoft_FStar_Tc_Recheck.t_unit)
in (Support.Prims.pipe_left _68_17203 (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant Microsoft_FStar_Absyn_Syntax.Const_unit)))
in (((Support.Prims.fst lbs), lbs'), _68_17204))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_let _68_17205 None r))
in (let _36_2838 = (match ((tc_exp (let _36_2806 = env
in {Microsoft_FStar_Tc_Env.solver = _36_2806.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_2806.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_2806.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_2806.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_2806.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_2806.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_2806.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_2806.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_2806.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _36_2806.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _36_2806.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _36_2806.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = generalize; Microsoft_FStar_Tc_Env.letrecs = _36_2806.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _36_2806.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_2806.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = _36_2806.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = _36_2806.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_2806.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_2806.Microsoft_FStar_Tc_Env.default_effects}) e)) with
| ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_let ((lbs, e)); Microsoft_FStar_Absyn_Syntax.tk = _36_2815; Microsoft_FStar_Absyn_Syntax.pos = _36_2813; Microsoft_FStar_Absyn_Syntax.fvs = _36_2811; Microsoft_FStar_Absyn_Syntax.uvs = _36_2809}, _36_2822, g) when (Microsoft_FStar_Tc_Rel.is_trivial g) -> begin
(let quals = (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((_36_2826, Microsoft_FStar_Absyn_Syntax.MaskedEffect))) -> begin
(Microsoft_FStar_Absyn_Syntax.HasMaskedEffect)::quals
end
| _36_2832 -> begin
quals
end)
in (Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _36_2835 -> begin
(failwith ("impossible"))
end)
in (match (_36_2838) with
| (se, lbs) -> begin
(let _36_2844 = (match ((log env)) with
| true -> begin
(let _68_17211 = (let _68_17210 = (Support.Prims.pipe_right (Support.Prims.snd lbs) (Support.List.map (fun ( lb ) -> (let should_log = (match ((let _68_17207 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (Microsoft_FStar_Tc_Env.try_lookup_val_decl env _68_17207))) with
| None -> begin
true
end
| _36_2842 -> begin
false
end)
in (match (should_log) with
| true -> begin
(let _68_17209 = (Microsoft_FStar_Absyn_Print.lbname_to_string lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (let _68_17208 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
in (Support.Microsoft.FStar.Util.format2 "let %s : %s" _68_17209 _68_17208)))
end
| false -> begin
""
end)))))
in (Support.Prims.pipe_right _68_17210 (Support.String.concat "\n")))
in (Support.Microsoft.FStar.Util.fprint1 "%s\n" _68_17211))
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
in (let _36_2856 = (tc_exp env e)
in (match (_36_2856) with
| (e, c, g1) -> begin
(let g1 = (Microsoft_FStar_Tc_Rel.solve_deferred_constraints env g1)
in (let _36_2862 = (let _68_17215 = (let _68_17212 = (Microsoft_FStar_Absyn_Util.ml_comp Microsoft_FStar_Tc_Recheck.t_unit r)
in Some (_68_17212))
in (let _68_17214 = (let _68_17213 = (c.Microsoft_FStar_Absyn_Syntax.comp ())
in (e, _68_17213))
in (check_expected_effect env _68_17215 _68_17214)))
in (match (_36_2862) with
| (e, _36_2860, g) -> begin
(let _36_2863 = (let _68_17216 = (Microsoft_FStar_Tc_Rel.conj_guard g1 g)
in (Microsoft_FStar_Tc_Util.discharge_guard env _68_17216))
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_main ((e, r))
in (let env = (Microsoft_FStar_Tc_Env.push_sigelt env se)
in (se, env))))
end)))
end))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, quals, lids, r)) -> begin
(let env = (Microsoft_FStar_Tc_Env.set_range env r)
in (let _36_2882 = (Support.Prims.pipe_right ses (Support.List.partition (fun ( _36_14 ) -> (match (_36_14) with
| Microsoft_FStar_Absyn_Syntax.Sig_tycon (_36_2876) -> begin
true
end
| _36_2879 -> begin
false
end))))
in (match (_36_2882) with
| (tycons, rest) -> begin
(let _36_2891 = (Support.Prims.pipe_right rest (Support.List.partition (fun ( _36_15 ) -> (match (_36_15) with
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_36_2885) -> begin
true
end
| _36_2888 -> begin
false
end))))
in (match (_36_2891) with
| (abbrevs, rest) -> begin
(let recs = (Support.Prims.pipe_right abbrevs (Support.List.map (fun ( _36_16 ) -> (match (_36_16) with
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, k, t, [], r)) -> begin
(let k = (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(let _68_17220 = (Microsoft_FStar_Tc_Rel.new_kvar r tps)
in (Support.Prims.pipe_right _68_17220 Support.Prims.fst))
end
| _36_2903 -> begin
k
end)
in (Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, [], [], [], r)), t))
end
| _36_2906 -> begin
(failwith ("impossible"))
end))))
in (let _36_2910 = (Support.List.split recs)
in (match (_36_2910) with
| (recs, abbrev_defs) -> begin
(let msg = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _68_17221 = (Microsoft_FStar_Absyn_Print.sigelt_to_string_short se)
in (Support.Microsoft.FStar.Util.format1 "Recursive bindings: %s" _68_17221))
end
| false -> begin
""
end)
in (let _36_2912 = (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.push msg)
in (let _36_2919 = (tc_decls false env tycons deserialized)
in (match (_36_2919) with
| (tycons, _36_2916, _36_2918) -> begin
(let _36_2925 = (tc_decls false env recs deserialized)
in (match (_36_2925) with
| (recs, _36_2922, _36_2924) -> begin
(let env1 = (Microsoft_FStar_Tc_Env.push_sigelt env (Microsoft_FStar_Absyn_Syntax.Sig_bundle (((Support.List.append tycons recs), quals, lids, r))))
in (let _36_2932 = (tc_decls false env1 rest deserialized)
in (match (_36_2932) with
| (rest, _36_2929, _36_2931) -> begin
(let abbrevs = (Support.List.map2 (fun ( se ) ( t ) -> (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, [], [], [], r)) -> begin
(let tt = (let _68_17224 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_ascribed (t, k) t.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Util.close_with_lam tps _68_17224))
in (let _36_2948 = (tc_typ_trivial env1 tt)
in (match (_36_2948) with
| (tt, _36_2947) -> begin
(let _36_2957 = (match (tt.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, t)) -> begin
(bs, t)
end
| _36_2954 -> begin
([], tt)
end)
in (match (_36_2957) with
| (tps, t) -> begin
(let _68_17226 = (let _68_17225 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in (lid, tps, _68_17225, t, [], r))
in Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_68_17226))
end))
end)))
end
| _36_2959 -> begin
(let _68_17228 = (let _68_17227 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format1 "(%s) Impossible" _68_17227))
in (failwith (_68_17228)))
end)) recs abbrev_defs)
in (let _36_2961 = (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.pop msg)
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
and tc_decls = (fun ( for_export ) ( env ) ( ses ) ( deserialized ) -> (let _36_2985 = (Support.Prims.pipe_right ses (Support.List.fold_left (fun ( _36_2972 ) ( se ) -> (match (_36_2972) with
| (ses, all_non_private, env) -> begin
(let _36_2974 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_17236 = (let _68_17235 = (Microsoft_FStar_Absyn_Print.sigelt_to_string se)
in (Support.Microsoft.FStar.Util.format1 "Checking sigelt\t%s\n" _68_17235))
in (Support.Microsoft.FStar.Util.print_string _68_17236))
end
| false -> begin
()
end)
in (let _36_2978 = (tc_decl env se deserialized)
in (match (_36_2978) with
| (se, env) -> begin
(let _36_2979 = (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.encode_sig env se)
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
in (match (_36_2985) with
| (ses, all_non_private, env) -> begin
(let _68_17237 = (Support.Prims.pipe_right (Support.List.rev all_non_private) Support.List.flatten)
in ((Support.List.rev ses), _68_17237, env))
end)))
and non_private = (fun ( env ) ( se ) -> (let is_private = (fun ( quals ) -> (Support.List.contains Microsoft_FStar_Absyn_Syntax.Private quals))
in (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, quals, _36_2993, _36_2995)) -> begin
(se)::[]
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((_36_2999, _36_3001, _36_3003, _36_3005, _36_3007, quals, r)) -> begin
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
| Microsoft_FStar_Absyn_Syntax.Sig_assume ((_36_3021, _36_3023, quals, _36_3026)) -> begin
(match ((is_private quals)) with
| true -> begin
[]
end
| false -> begin
(se)::[]
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_36_3030, _36_3032, quals, _36_3035)) -> begin
(match ((is_private quals)) with
| true -> begin
[]
end
| false -> begin
(se)::[]
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_main (_36_3039) -> begin
[]
end
| (Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_pragma (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_)) -> begin
(se)::[]
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon (_36_3057) -> begin
(failwith ("Impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, r, l, _36_3063)) -> begin
(let check_priv = (fun ( lbs ) -> (let is_priv = (fun ( _36_17 ) -> (match (_36_17) with
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (l); Microsoft_FStar_Absyn_Syntax.lbtyp = _36_3074; Microsoft_FStar_Absyn_Syntax.lbeff = _36_3072; Microsoft_FStar_Absyn_Syntax.lbdef = _36_3070} -> begin
(match ((Microsoft_FStar_Tc_Env.try_lookup_val_decl env l)) with
| Some ((_36_3079, qs)) -> begin
(Support.List.contains Microsoft_FStar_Absyn_Syntax.Private qs)
end
| _36_3084 -> begin
false
end)
end
| _36_3086 -> begin
false
end))
in (let some_priv = (Support.Prims.pipe_right lbs (Support.Microsoft.FStar.Util.for_some is_priv))
in (match (some_priv) with
| true -> begin
(match ((Support.Prims.pipe_right lbs (Support.Microsoft.FStar.Util.for_some (fun ( x ) -> (let _68_17247 = (is_priv x)
in (Support.Prims.pipe_right _68_17247 Support.Prims.op_Negation)))))) with
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
in (let _36_3093 = (Support.Prims.pipe_right (Support.Prims.snd lbs) (Support.List.partition (fun ( lb ) -> ((Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function lb.Microsoft_FStar_Absyn_Syntax.lbtyp) && (let _68_17249 = (Microsoft_FStar_Absyn_Util.is_lemma lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
in (Support.Prims.pipe_left Support.Prims.op_Negation _68_17249))))))
in (match (_36_3093) with
| (pure_funs, rest) -> begin
(match ((pure_funs, rest)) with
| (_36_3097::_36_3095, _36_3102::_36_3100) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Pure functions cannot be mutually recursive with impure functions", r))))
end
| (_36_3108::_36_3106, []) -> begin
(match ((check_priv pure_funs)) with
| true -> begin
[]
end
| false -> begin
(se)::[]
end)
end
| ([], _36_3116::_36_3114) -> begin
(match ((check_priv rest)) with
| true -> begin
[]
end
| false -> begin
(Support.Prims.pipe_right rest (Support.List.collect (fun ( lb ) -> (match (lb.Microsoft_FStar_Absyn_Syntax.lbname) with
| Support.Microsoft.FStar.Util.Inl (_36_3121) -> begin
(failwith ("impossible"))
end
| Support.Microsoft.FStar.Util.Inr (l) -> begin
(let _68_17253 = (let _68_17252 = (let _68_17251 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (l, lb.Microsoft_FStar_Absyn_Syntax.lbtyp, (Microsoft_FStar_Absyn_Syntax.Assumption)::[], _68_17251))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_68_17252))
in (_68_17253)::[])
end))))
end)
end
| ([], []) -> begin
(failwith ("Impossible"))
end)
end)))
end)))

let get_exports = (fun ( env ) ( modul ) ( non_private_decls ) -> (let assume_vals = (fun ( decls ) -> (Support.Prims.pipe_right decls (Support.List.map (fun ( _36_18 ) -> (match (_36_18) with
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
(let exports = (let _68_17265 = (Microsoft_FStar_Tc_Env.modules env)
in (Support.Microsoft.FStar.Util.find_map _68_17265 (fun ( m ) -> (match ((m.Microsoft_FStar_Absyn_Syntax.is_interface && (Microsoft_FStar_Absyn_Syntax.lid_equals modul.Microsoft_FStar_Absyn_Syntax.name m.Microsoft_FStar_Absyn_Syntax.name))) with
| true -> begin
(let _68_17264 = (Support.Prims.pipe_right m.Microsoft_FStar_Absyn_Syntax.exports assume_vals)
in Some (_68_17264))
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
in (let env = (let _36_3150 = env
in (let _68_17270 = (not ((Microsoft_FStar_Options.should_verify modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)))
in {Microsoft_FStar_Tc_Env.solver = _36_3150.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_3150.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_3150.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_3150.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_3150.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_3150.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_3150.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_3150.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_3150.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _36_3150.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _36_3150.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _36_3150.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_3150.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _36_3150.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _36_3150.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_3150.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = _36_3150.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = modul.Microsoft_FStar_Absyn_Syntax.is_interface; Microsoft_FStar_Tc_Env.admit = _68_17270; Microsoft_FStar_Tc_Env.default_effects = _36_3150.Microsoft_FStar_Tc_Env.default_effects}))
in (let _36_3153 = (match ((not ((Microsoft_FStar_Absyn_Syntax.lid_equals modul.Microsoft_FStar_Absyn_Syntax.name Microsoft_FStar_Absyn_Const.prims_lid)))) with
| true -> begin
(env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.push msg)
end
| false -> begin
()
end)
in (let env = (Microsoft_FStar_Tc_Env.set_current_module env modul.Microsoft_FStar_Absyn_Syntax.name)
in (let _36_3159 = (tc_decls true env modul.Microsoft_FStar_Absyn_Syntax.declarations modul.Microsoft_FStar_Absyn_Syntax.is_deserialized)
in (match (_36_3159) with
| (ses, non_private_decls, env) -> begin
((let _36_3160 = modul
in {Microsoft_FStar_Absyn_Syntax.name = _36_3160.Microsoft_FStar_Absyn_Syntax.name; Microsoft_FStar_Absyn_Syntax.declarations = ses; Microsoft_FStar_Absyn_Syntax.exports = _36_3160.Microsoft_FStar_Absyn_Syntax.exports; Microsoft_FStar_Absyn_Syntax.is_interface = _36_3160.Microsoft_FStar_Absyn_Syntax.is_interface; Microsoft_FStar_Absyn_Syntax.is_deserialized = _36_3160.Microsoft_FStar_Absyn_Syntax.is_deserialized}), non_private_decls, env)
end))))))))

let tc_more_partial_modul = (fun ( env ) ( modul ) ( decls ) -> (let _36_3168 = (tc_decls true env decls false)
in (match (_36_3168) with
| (ses, non_private_decls, env) -> begin
(let modul = (let _36_3169 = modul
in {Microsoft_FStar_Absyn_Syntax.name = _36_3169.Microsoft_FStar_Absyn_Syntax.name; Microsoft_FStar_Absyn_Syntax.declarations = (Support.List.append modul.Microsoft_FStar_Absyn_Syntax.declarations ses); Microsoft_FStar_Absyn_Syntax.exports = _36_3169.Microsoft_FStar_Absyn_Syntax.exports; Microsoft_FStar_Absyn_Syntax.is_interface = _36_3169.Microsoft_FStar_Absyn_Syntax.is_interface; Microsoft_FStar_Absyn_Syntax.is_deserialized = _36_3169.Microsoft_FStar_Absyn_Syntax.is_deserialized})
in (modul, non_private_decls, env))
end)))

let finish_partial_modul = (fun ( env ) ( modul ) ( npds ) -> (let exports = (get_exports env modul npds)
in (let modul = (let _36_3176 = modul
in {Microsoft_FStar_Absyn_Syntax.name = _36_3176.Microsoft_FStar_Absyn_Syntax.name; Microsoft_FStar_Absyn_Syntax.declarations = _36_3176.Microsoft_FStar_Absyn_Syntax.declarations; Microsoft_FStar_Absyn_Syntax.exports = exports; Microsoft_FStar_Absyn_Syntax.is_interface = modul.Microsoft_FStar_Absyn_Syntax.is_interface; Microsoft_FStar_Absyn_Syntax.is_deserialized = modul.Microsoft_FStar_Absyn_Syntax.is_deserialized})
in (let env = (Microsoft_FStar_Tc_Env.finish_module env modul)
in (let _36_3186 = (match ((not ((Microsoft_FStar_Absyn_Syntax.lid_equals modul.Microsoft_FStar_Absyn_Syntax.name Microsoft_FStar_Absyn_Const.prims_lid)))) with
| true -> begin
(let _36_3180 = (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.pop (Support.String.strcat "Ending modul " modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str))
in (let _36_3182 = (match (((not (modul.Microsoft_FStar_Absyn_Syntax.is_interface)) || (let _68_17283 = (Support.ST.read Microsoft_FStar_Options.admit_fsi)
in (Support.List.contains modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str _68_17283)))) with
| true -> begin
(env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.encode_modul env modul)
end
| false -> begin
()
end)
in (let _36_3184 = (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.refresh ())
in (let _68_17284 = (Microsoft_FStar_Options.reset_options ())
in (Support.Prims.pipe_right _68_17284 Support.Prims.ignore)))))
end
| false -> begin
()
end)
in (modul, env))))))

let tc_modul = (fun ( env ) ( modul ) -> (let _36_3193 = (tc_partial_modul env modul)
in (match (_36_3193) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

let add_modul_to_tcenv = (fun ( en ) ( m ) -> (let do_sigelt = (fun ( en ) ( elt ) -> (let env = (Microsoft_FStar_Tc_Env.push_sigelt en elt)
in (let _36_3200 = (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.encode_sig env elt)
in env)))
in (let en = (Microsoft_FStar_Tc_Env.set_current_module en m.Microsoft_FStar_Absyn_Syntax.name)
in (let _68_17297 = (Support.List.fold_left do_sigelt en m.Microsoft_FStar_Absyn_Syntax.exports)
in (Microsoft_FStar_Tc_Env.finish_module _68_17297 m)))))

let check_module = (fun ( env ) ( m ) -> (let _36_3205 = (match (((let _68_17302 = (Support.ST.read Microsoft_FStar_Options.debug)
in (Support.List.length _68_17302)) <> 0)) with
| true -> begin
(let _68_17303 = (Microsoft_FStar_Absyn_Print.sli m.Microsoft_FStar_Absyn_Syntax.name)
in (Support.Microsoft.FStar.Util.fprint2 "Checking %s: %s\n" (match (m.Microsoft_FStar_Absyn_Syntax.is_interface) with
| true -> begin
"i\'face"
end
| false -> begin
"module"
end) _68_17303))
end
| false -> begin
()
end)
in (let _36_3218 = (match (m.Microsoft_FStar_Absyn_Syntax.is_deserialized) with
| true -> begin
(let env' = (add_modul_to_tcenv env m)
in (m, env'))
end
| false -> begin
(let _36_3210 = (tc_modul env m)
in (match (_36_3210) with
| (m, env) -> begin
(let _36_3214 = (match ((Support.ST.read Microsoft_FStar_Options.serialize_mods)) with
| true -> begin
(let c_file_name = (let _68_17309 = (let _68_17308 = (let _68_17306 = (let _68_17305 = (let _68_17304 = (Microsoft_FStar_Options.get_fstar_home ())
in (Support.String.strcat _68_17304 "/"))
in (Support.String.strcat _68_17305 Microsoft_FStar_Options.cache_dir))
in (Support.String.strcat _68_17306 "/"))
in (let _68_17307 = (Microsoft_FStar_Absyn_Syntax.text_of_lid m.Microsoft_FStar_Absyn_Syntax.name)
in (Support.String.strcat _68_17308 _68_17307)))
in (Support.String.strcat _68_17309 ".cache"))
in (let _36_3212 = (let _68_17312 = (let _68_17311 = (let _68_17310 = (Microsoft_FStar_Absyn_Syntax.text_of_lid m.Microsoft_FStar_Absyn_Syntax.name)
in (Support.String.strcat "Serializing module " _68_17310))
in (Support.String.strcat _68_17311 "\n"))
in (Support.Microsoft.FStar.Util.print_string _68_17312))
in (let _68_17313 = (Support.Microsoft.FStar.Util.get_owriter c_file_name)
in (Microsoft_FStar_Absyn_SSyntax.serialize_modul _68_17313 m))))
end
| false -> begin
()
end)
in (m, env))
end))
end)
in (match (_36_3218) with
| (m, env) -> begin
(let _36_3219 = (match ((Microsoft_FStar_Options.should_dump m.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
(let _68_17314 = (Microsoft_FStar_Absyn_Print.modul_to_string m)
in (Support.Microsoft.FStar.Util.fprint1 "%s\n" _68_17314))
end
| false -> begin
()
end)
in ((m)::[], env))
end))))




