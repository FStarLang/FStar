
let syn' = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( k  :  'u36u3257 ) -> (let _52_12611 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Syntax.syn _52_12611 (Some (k)))))

let log = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) -> (let _52_12617 = (Support.ST.read Microsoft_FStar_Options.log_types)
in (let _52_12616 = (let _52_12615 = (let _52_12614 = (Microsoft_FStar_Tc_Env.current_module env)
in (Microsoft_FStar_Absyn_Syntax.lid_equals Microsoft_FStar_Absyn_Const.prims_lid _52_12614))
in (not (_52_12615)))
in (_52_12617 && _52_12616))))

let rng = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) -> (Microsoft_FStar_Tc_Env.get_range env))

let instantiate_both = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) -> (let _36_24 = env
in {Microsoft_FStar_Tc_Env.solver = _36_24.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_24.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_24.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_24.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_24.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_24.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_24.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_24.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_24.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = true; Microsoft_FStar_Tc_Env.instantiate_vargs = true; Microsoft_FStar_Tc_Env.effects = _36_24.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_24.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _36_24.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _36_24.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_24.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = _36_24.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = _36_24.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_24.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_24.Microsoft_FStar_Tc_Env.default_effects}))

let no_inst = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) -> (let _36_27 = env
in {Microsoft_FStar_Tc_Env.solver = _36_27.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_27.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_27.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_27.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_27.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_27.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_27.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_27.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_27.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = false; Microsoft_FStar_Tc_Env.instantiate_vargs = false; Microsoft_FStar_Tc_Env.effects = _36_27.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_27.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _36_27.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _36_27.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_27.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = _36_27.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = _36_27.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_27.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_27.Microsoft_FStar_Tc_Env.default_effects}))

let mk_lex_list = (fun ( vs  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax list ) -> (Support.List.fold_right (fun ( v  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) ( tl  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let r = (match ((tl.Microsoft_FStar_Absyn_Syntax.pos = Microsoft_FStar_Absyn_Syntax.dummyRange)) with
| true -> begin
v.Microsoft_FStar_Absyn_Syntax.pos
end
| false -> begin
(Support.Microsoft.FStar.Range.union_ranges v.Microsoft_FStar_Absyn_Syntax.pos tl.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (let _52_12637 = (let _52_12636 = (let _52_12635 = (let _52_12630 = (let _52_12629 = (Microsoft_FStar_Tc_Recheck.recompute_typ v)
in (Support.Prims.pipe_left (fun ( _52_12628  :  Microsoft_FStar_Absyn_Syntax.typ ) -> Support.Microsoft.FStar.Util.Inl (_52_12628)) _52_12629))
in (_52_12630, Some (Microsoft_FStar_Absyn_Syntax.Implicit)))
in (let _52_12634 = (let _52_12633 = (Microsoft_FStar_Absyn_Syntax.varg v)
in (let _52_12632 = (let _52_12631 = (Microsoft_FStar_Absyn_Syntax.varg tl)
in (_52_12631)::[])
in (_52_12633)::_52_12632))
in (_52_12635)::_52_12634))
in (Microsoft_FStar_Absyn_Util.lex_pair, _52_12636))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _52_12637 (Some (Microsoft_FStar_Absyn_Util.lex_t)) r)))) vs Microsoft_FStar_Absyn_Util.lex_top))

let is_eq = (fun ( _36_1  :  Microsoft_FStar_Absyn_Syntax.arg_qualifier option ) -> (match (_36_1) with
| Some (Microsoft_FStar_Absyn_Syntax.Equality) -> begin
true
end
| _ -> begin
false
end))

let steps = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) -> (match ((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
(Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.SNComp)::[]
end
| false -> begin
(Microsoft_FStar_Tc_Normalize.Beta)::[]
end))

let whnf = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.WHNF)::(Microsoft_FStar_Tc_Normalize.DeltaHard)::(Microsoft_FStar_Tc_Normalize.Beta)::[]) env t))

let norm_t = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let _52_12650 = (steps env)
in (Microsoft_FStar_Tc_Normalize.norm_typ _52_12650 env t)))

let norm_k = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( k  :  Microsoft_FStar_Absyn_Syntax.knd ) -> (let _52_12655 = (steps env)
in (Microsoft_FStar_Tc_Normalize.norm_kind _52_12655 env k)))

let norm_c = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( c  :  Microsoft_FStar_Absyn_Syntax.comp ) -> (let _52_12660 = (steps env)
in (Microsoft_FStar_Tc_Normalize.norm_comp _52_12660 env c)))

let fxv_check = (fun ( head  :  Microsoft_FStar_Absyn_Syntax.exp ) ( env  :  Microsoft_FStar_Tc_Env.env ) ( kt  :  (Microsoft_FStar_Absyn_Syntax.knd, Microsoft_FStar_Absyn_Syntax.typ) Support.Microsoft.FStar.Util.either ) ( fvs  :  Microsoft_FStar_Absyn_Syntax.bvvar Support.Microsoft.FStar.Util.set ) -> (let rec aux = (fun ( norm  :  bool ) ( kt  :  (Microsoft_FStar_Absyn_Syntax.knd, Microsoft_FStar_Absyn_Syntax.typ) Support.Microsoft.FStar.Util.either ) -> (match ((Support.Microsoft.FStar.Util.set_is_empty fvs)) with
| true -> begin
()
end
| false -> begin
(let fvs' = (match (kt) with
| Support.Microsoft.FStar.Util.Inl (k) -> begin
(let _52_12679 = (match (norm) with
| true -> begin
(norm_k env k)
end
| false -> begin
k
end)
in (Microsoft_FStar_Absyn_Util.freevars_kind _52_12679))
end
| Support.Microsoft.FStar.Util.Inr (t) -> begin
(let _52_12680 = (match (norm) with
| true -> begin
(norm_t env t)
end
| false -> begin
t
end)
in (Microsoft_FStar_Absyn_Util.freevars_typ _52_12680))
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
(let fail = (fun ( _36_61  :  unit ) -> (match (()) with
| () -> begin
(let escaping = (let _52_12685 = (let _52_12684 = (Support.Microsoft.FStar.Util.set_elements a)
in (Support.Prims.pipe_right _52_12684 (Support.List.map (fun ( x  :  ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t ) -> (Microsoft_FStar_Absyn_Print.strBvd x.Microsoft_FStar_Absyn_Syntax.v)))))
in (Support.Prims.pipe_right _52_12685 (Support.String.concat ", ")))
in (let msg = (match ((let _52_12686 = (Support.Microsoft.FStar.Util.set_count a)
in (_52_12686 > 1))) with
| true -> begin
(let _52_12687 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env head)
in (Support.Microsoft.FStar.Util.format2 "Bound variables \'{%s}\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" escaping _52_12687))
end
| false -> begin
(let _52_12688 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env head)
in (Support.Microsoft.FStar.Util.format2 "Bound variable \'%s\' in the type of \'%s\' escapes because of impure applications; add explicit let-bindings" escaping _52_12688))
end)
in (let _52_12691 = (let _52_12690 = (let _52_12689 = (Microsoft_FStar_Tc_Env.get_range env)
in (msg, _52_12689))
in Microsoft_FStar_Absyn_Syntax.Error (_52_12690))
in (raise (_52_12691)))))
end))
in (match (kt) with
| Support.Microsoft.FStar.Util.Inl (k) -> begin
(let s = (Microsoft_FStar_Tc_Util.new_kvar env)
in (match ((Microsoft_FStar_Tc_Rel.try_keq env k s)) with
| Some (g) -> begin
(Microsoft_FStar_Tc_Rel.try_discharge_guard env g)
end
| _ -> begin
(fail ())
end))
end
| Support.Microsoft.FStar.Util.Inr (t) -> begin
(let s = (Microsoft_FStar_Tc_Util.new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (match ((Microsoft_FStar_Tc_Rel.try_teq env t s)) with
| Some (g) -> begin
(Microsoft_FStar_Tc_Rel.try_discharge_guard env g)
end
| _ -> begin
(fail ())
end))
end))
end)
end)))
end))
in (aux false kt)))

let maybe_push_binding = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( b  :  Microsoft_FStar_Absyn_Syntax.binder ) -> (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
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

let maybe_make_subst = (fun ( _36_2  :  (('u36u4495 option * 'u36u4494), ('u36u4493 option * 'u36u4492)) Support.Microsoft.FStar.Util.either ) -> (match (_36_2) with
| Support.Microsoft.FStar.Util.Inl ((Some (a), t)) -> begin
(Support.Microsoft.FStar.Util.Inl ((a, t)))::[]
end
| Support.Microsoft.FStar.Util.Inr ((Some (x), e)) -> begin
(Support.Microsoft.FStar.Util.Inr ((x, e)))::[]
end
| _ -> begin
[]
end))

let maybe_alpha_subst = (fun ( s  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef * Microsoft_FStar_Absyn_Syntax.typ), ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef * Microsoft_FStar_Absyn_Syntax.exp)) Support.Microsoft.FStar.Util.either list ) ( b1  :  Microsoft_FStar_Absyn_Syntax.binder ) ( b2  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.bvar, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.bvar) Support.Microsoft.FStar.Util.either * 'u36u4637) ) -> (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b1)) with
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
(let _52_12702 = (let _52_12701 = (let _52_12700 = (Microsoft_FStar_Absyn_Util.btvar_to_typ b)
in (a.Microsoft_FStar_Absyn_Syntax.v, _52_12700))
in Support.Microsoft.FStar.Util.Inl (_52_12701))
in (_52_12702)::s)
end)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(match ((Microsoft_FStar_Absyn_Util.bvar_eq x y)) with
| true -> begin
s
end
| false -> begin
(let _52_12705 = (let _52_12704 = (let _52_12703 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (x.Microsoft_FStar_Absyn_Syntax.v, _52_12703))
in Support.Microsoft.FStar.Util.Inr (_52_12704))
in (_52_12705)::s)
end)
end
| _ -> begin
(failwith ("impossible"))
end)
end))

let maybe_extend_subst = (fun ( s  :  Microsoft_FStar_Absyn_Syntax.subst ) ( b  :  Microsoft_FStar_Absyn_Syntax.binder ) ( v  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * 'u36u4751) ) -> (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
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
| _ -> begin
(failwith ("Impossible"))
end)
end))

let set_lcomp_result = (fun ( lc  :  Microsoft_FStar_Absyn_Syntax.lcomp ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let _36_132 = lc
in {Microsoft_FStar_Absyn_Syntax.eff_name = _36_132.Microsoft_FStar_Absyn_Syntax.eff_name; Microsoft_FStar_Absyn_Syntax.res_typ = t; Microsoft_FStar_Absyn_Syntax.cflags = _36_132.Microsoft_FStar_Absyn_Syntax.cflags; Microsoft_FStar_Absyn_Syntax.comp = (fun ( _36_134  :  unit ) -> (match (()) with
| () -> begin
(let _52_12714 = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp lc ())
in (Microsoft_FStar_Absyn_Util.set_result_typ _52_12714 t))
end))}))

let value_check_expected_typ = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( e  :  Microsoft_FStar_Absyn_Syntax.exp ) ( tlc  :  ((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, Microsoft_FStar_Absyn_Syntax.lcomp) Support.Microsoft.FStar.Util.either ) -> (let lc = (match (tlc) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _52_12722 = (match ((let _52_12721 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t)
in (not (_52_12721)))) with
| true -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Total t)
end
| false -> begin
(Microsoft_FStar_Tc_Util.return_value env t e)
end)
in (Microsoft_FStar_Tc_Util.lcomp_of_comp _52_12722))
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
(let _52_12724 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (let _52_12723 = (Microsoft_FStar_Absyn_Print.typ_to_string t')
in (Support.Microsoft.FStar.Util.fprint2 "Computed return type %s; expected type %s\n" _52_12724 _52_12723)))
end
| false -> begin
()
end)
in (let _36_151 = (Microsoft_FStar_Tc_Util.check_and_ascribe env e t t')
in (match (_36_151) with
| (e, g) -> begin
(let _36_154 = (let _52_12730 = (Support.Prims.pipe_left (fun ( _52_12729  :  (unit  ->  string) ) -> Some (_52_12729)) (Microsoft_FStar_Tc_Errors.subtyping_failed env t t'))
in (Microsoft_FStar_Tc_Util.strengthen_precondition _52_12730 env e lc g))
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
(let _52_12731 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string lc)
in (Support.Microsoft.FStar.Util.fprint1 "Return comp type is %s\n" _52_12731))
end
| false -> begin
()
end)
in (e, lc, g))
end)))))

let comp_check_expected_typ = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( e  :  Microsoft_FStar_Absyn_Syntax.exp ) ( lc  :  Microsoft_FStar_Absyn_Syntax.lcomp ) -> (match ((Microsoft_FStar_Tc_Env.expected_typ env)) with
| None -> begin
(e, lc, Microsoft_FStar_Tc_Rel.trivial_guard)
end
| Some (t) -> begin
(Microsoft_FStar_Tc_Util.weaken_result_typ env e lc t)
end))

let check_expected_effect = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( copt  :  Microsoft_FStar_Absyn_Syntax.comp option ) ( _36_171  :  (Microsoft_FStar_Absyn_Syntax.exp * Microsoft_FStar_Absyn_Syntax.comp) ) -> (match (_36_171) with
| (e, c) -> begin
(let expected_c_opt = (match (copt) with
| Some (_) -> begin
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
(let _52_12744 = (norm_c env c)
in (e, _52_12744, Microsoft_FStar_Tc_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(let _36_187 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _52_12747 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_12746 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c)
in (let _52_12745 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string expected_c)
in (Support.Microsoft.FStar.Util.fprint3 "(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _52_12747 _52_12746 _52_12745))))
end
| false -> begin
()
end)
in (let c = (norm_c env c)
in (let expected_c' = (let _52_12748 = (Support.Prims.pipe_left Microsoft_FStar_Tc_Util.lcomp_of_comp expected_c)
in (Microsoft_FStar_Tc_Util.refresh_comp_label env true _52_12748))
in (let _36_195 = (let _52_12749 = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp expected_c' ())
in (Support.Prims.pipe_left (Microsoft_FStar_Tc_Util.check_comp env e c) _52_12749))
in (match (_36_195) with
| (e, _, g) -> begin
(let _36_196 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _52_12751 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_12750 = (Microsoft_FStar_Tc_Rel.guard_to_string env g)
in (Support.Microsoft.FStar.Util.fprint2 "(%s) DONE check_expected_effect; guard is: %s\n" _52_12751 _52_12750)))
end
| false -> begin
()
end)
in (e, expected_c, g))
end)))))
end))
end))

let no_logical_guard = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( _36_202  :  ('u36u5430 * 'u36u5429 * Microsoft_FStar_Tc_Rel.guard_t) ) -> (match (_36_202) with
| (te, kt, f) -> begin
(match ((Microsoft_FStar_Tc_Rel.guard_f f)) with
| Microsoft_FStar_Tc_Rel.Trivial -> begin
(te, kt, f)
end
| Microsoft_FStar_Tc_Rel.NonTrivial (f) -> begin
(let _52_12757 = (let _52_12756 = (let _52_12755 = (Microsoft_FStar_Tc_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _52_12754 = (Microsoft_FStar_Tc_Env.get_range env)
in (_52_12755, _52_12754)))
in Microsoft_FStar_Absyn_Syntax.Error (_52_12756))
in (raise (_52_12757)))
end)
end))

let binding_of_lb = (fun ( x  :  (Microsoft_FStar_Absyn_Syntax.bvvdef, Microsoft_FStar_Absyn_Syntax.lident) Support.Microsoft.FStar.Util.either ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (match (x) with
| Support.Microsoft.FStar.Util.Inl (bvd) -> begin
Microsoft_FStar_Tc_Env.Binding_var ((bvd, t))
end
| Support.Microsoft.FStar.Util.Inr (lid) -> begin
Microsoft_FStar_Tc_Env.Binding_lid ((lid, t))
end))

let print_expected_ty = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) -> (match ((Microsoft_FStar_Tc_Env.expected_typ env)) with
| None -> begin
(Support.Microsoft.FStar.Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _52_12764 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint1 "Expected type is %s" _52_12764))
end))

let with_implicits = (fun ( imps  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.uvar_basis Support.Microsoft.FStar.Unionfind.uvar * Int64.t), ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.uvar_basis Support.Microsoft.FStar.Unionfind.uvar * Int64.t)) Support.Microsoft.FStar.Util.either list ) ( _36_220  :  ('u36u5591 * 'u36u5590 * Microsoft_FStar_Tc_Rel.guard_t) ) -> (match (_36_220) with
| (e, l, g) -> begin
(e, l, (let _36_221 = g
in {Microsoft_FStar_Tc_Rel.guard_f = _36_221.Microsoft_FStar_Tc_Rel.guard_f; Microsoft_FStar_Tc_Rel.deferred = _36_221.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = (Support.List.append imps g.Microsoft_FStar_Tc_Rel.implicits)}))
end))

let add_implicit = (fun ( u  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.uvar_basis Support.Microsoft.FStar.Unionfind.uvar * Int64.t), ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.uvar_basis Support.Microsoft.FStar.Unionfind.uvar * Int64.t)) Support.Microsoft.FStar.Util.either ) ( g  :  Microsoft_FStar_Tc_Rel.guard_t ) -> (let _36_225 = g
in {Microsoft_FStar_Tc_Rel.guard_f = _36_225.Microsoft_FStar_Tc_Rel.guard_f; Microsoft_FStar_Tc_Rel.deferred = _36_225.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = (u)::g.Microsoft_FStar_Tc_Rel.implicits}))

let rec tc_kind = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( k  :  (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let k = (Microsoft_FStar_Absyn_Util.compress_kind k)
in (let w = (fun ( f  :  Support.Microsoft.FStar.Range.range  ->  Microsoft_FStar_Absyn_Syntax.knd ) -> (f k.Microsoft_FStar_Absyn_Syntax.pos))
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
(let _52_12815 = (Support.Microsoft.FStar.Range.string_of_range k.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_12814 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (Support.Microsoft.FStar.Util.fprint2 "(%s) - Checking kind %s" _52_12815 _52_12814)))
end
| false -> begin
()
end)
in (let _36_249 = (Microsoft_FStar_Tc_Env.clear_expected_typ env)
in (match (_36_249) with
| (env, _) -> begin
(let _36_252 = (tc_args env args)
in (match (_36_252) with
| (args, g) -> begin
(let _52_12817 = (Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Kind_uvar (u, args)))
in (_52_12817, g))
end))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev (((l, args), {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_unknown; Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(let _36_272 = (Microsoft_FStar_Tc_Env.lookup_kind_abbrev env l)
in (match (_36_272) with
| (_, binders, body) -> begin
(let _36_275 = (tc_args env args)
in (match (_36_275) with
| (args, g) -> begin
(match (((Support.List.length binders) <> (Support.List.length args))) with
| true -> begin
(let _52_12821 = (let _52_12820 = (let _52_12819 = (let _52_12818 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.String.strcat "Unexpected number of arguments to kind abbreviation " _52_12818))
in (_52_12819, k.Microsoft_FStar_Absyn_Syntax.pos))
in Microsoft_FStar_Absyn_Syntax.Error (_52_12820))
in (raise (_52_12821)))
end
| false -> begin
(let _36_308 = (Support.List.fold_left2 (fun ( _36_279  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef * (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax), ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef * (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax)) Support.Microsoft.FStar.Util.either list * Microsoft_FStar_Absyn_Syntax.arg list * Microsoft_FStar_Tc_Rel.guard_t list) ) ( b  :  Microsoft_FStar_Absyn_Syntax.binder ) ( a  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (_36_279) with
| (subst, args, guards) -> begin
(match (((Support.Prims.fst b), (Support.Prims.fst a))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (t)) -> begin
(let _36_289 = (let _52_12825 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (tc_typ_check env t _52_12825))
in (match (_36_289) with
| (t, g) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t)))::subst
in (let _52_12827 = (let _52_12826 = (Microsoft_FStar_Absyn_Syntax.targ t)
in (_52_12826)::args)
in (subst, _52_12827, (g)::guards)))
end))
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (e)) -> begin
(let env = (let _52_12828 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Tc_Env.set_expected_typ env _52_12828))
in (let _36_301 = (tc_ghost_exp env e)
in (match (_36_301) with
| (e, _, g) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, e)))::subst
in (let _52_12830 = (let _52_12829 = (Microsoft_FStar_Absyn_Syntax.varg e)
in (_52_12829)::args)
in (subst, _52_12830, (g)::guards)))
end)))
end
| _ -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Ill-typed argument to kind abbreviation", (Microsoft_FStar_Absyn_Util.range_of_arg a)))))
end)
end)) ([], [], []) binders args)
in (match (_36_308) with
| (subst, args, guards) -> begin
(let args = (Support.List.rev args)
in (let k = (Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown)))
in (let k' = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.DeltaHard)::[]) env k)
in (let k = (Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), k')))
in (let _52_12833 = (Support.List.fold_left Microsoft_FStar_Tc_Rel.conj_guard g guards)
in (k', _52_12833))))))
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
in (let _52_12835 = (Microsoft_FStar_Tc_Rel.conj_guard f g)
in (kk, _52_12835))))
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
in (let _52_12838 = (Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, k)))
in (let _52_12837 = (Microsoft_FStar_Tc_Rel.conj_guard g f)
in (_52_12838, _52_12837))))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(let _52_12839 = (Microsoft_FStar_Tc_Util.new_kvar env)
in (_52_12839, Microsoft_FStar_Tc_Rel.trivial_guard))
end))))
and tc_vbinder = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( x  :  ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t ) -> (let _36_342 = (tc_typ_check env x.Microsoft_FStar_Absyn_Syntax.sort Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_36_342) with
| (t, g) -> begin
(let x = (let _36_343 = x
in {Microsoft_FStar_Absyn_Syntax.v = _36_343.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _36_343.Microsoft_FStar_Absyn_Syntax.p})
in (let env' = (let _52_12842 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (maybe_push_binding env _52_12842))
in (x, env', g)))
end)))
and tc_binders = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( bs  :  Microsoft_FStar_Absyn_Syntax.binders ) -> (let rec aux = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( bs  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) -> (match (bs) with
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
(let _52_12850 = (let _52_12849 = (Microsoft_FStar_Tc_Rel.close_guard ((b)::[]) g')
in (Microsoft_FStar_Tc_Rel.conj_guard g _52_12849))
in ((b)::bs, env', _52_12850))
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
(let _52_12852 = (let _52_12851 = (Microsoft_FStar_Tc_Rel.close_guard ((b)::[]) g')
in (Microsoft_FStar_Tc_Rel.conj_guard g _52_12851))
in ((b)::bs, env', _52_12852))
end)))
end))
end)
end))
in (aux env bs)))
and tc_args = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( args  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) -> (Support.List.fold_right (fun ( _36_386  :  ((Microsoft_FStar_Absyn_Syntax.typ, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) ( _36_389  :  (((Microsoft_FStar_Absyn_Syntax.typ, Microsoft_FStar_Absyn_Syntax.exp) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list * Microsoft_FStar_Tc_Rel.guard_t) ) -> (match ((_36_386, _36_389)) with
| ((arg, imp), (args, g)) -> begin
(match (arg) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _36_396 = (tc_typ env t)
in (match (_36_396) with
| (t, _, g') -> begin
(let _52_12857 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (((Support.Microsoft.FStar.Util.Inl (t), imp))::args, _52_12857))
end))
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(let _36_403 = (tc_ghost_exp env e)
in (match (_36_403) with
| (e, _, g') -> begin
(let _52_12858 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (((Support.Microsoft.FStar.Util.Inr (e), imp))::args, _52_12858))
end))
end)
end)) args ([], Microsoft_FStar_Tc_Rel.trivial_guard)))
and tc_comp = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( c  :  (Microsoft_FStar_Absyn_Syntax.comp', unit) Microsoft_FStar_Absyn_Syntax.syntax ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(let _36_410 = (tc_typ_check env t Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_36_410) with
| (t, g) -> begin
(let _52_12861 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (_52_12861, g))
end))
end
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
(let kc = (Microsoft_FStar_Tc_Env.lookup_effect_lid env c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let head = (Microsoft_FStar_Absyn_Util.ftv c.Microsoft_FStar_Absyn_Syntax.effect_name kc)
in (let tc = (let _52_12864 = (let _52_12863 = (let _52_12862 = (Microsoft_FStar_Absyn_Syntax.targ c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (_52_12862)::c.Microsoft_FStar_Absyn_Syntax.effect_args)
in (head, _52_12863))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_12864 None c.Microsoft_FStar_Absyn_Syntax.result_typ.Microsoft_FStar_Absyn_Syntax.pos))
in (let _36_418 = (tc_typ_check env tc Microsoft_FStar_Absyn_Syntax.keffect)
in (match (_36_418) with
| (tc, f) -> begin
(let _36_422 = (Microsoft_FStar_Absyn_Util.head_and_args tc)
in (match (_36_422) with
| (_, args) -> begin
(let _36_434 = (match (args) with
| (Support.Microsoft.FStar.Util.Inl (res), _)::args -> begin
(res, args)
end
| _ -> begin
(failwith ("Impossible"))
end)
in (match (_36_434) with
| (res, args) -> begin
(let _36_450 = (let _52_12866 = (Support.Prims.pipe_right c.Microsoft_FStar_Absyn_Syntax.flags (Support.List.map (fun ( _36_3  :  Microsoft_FStar_Absyn_Syntax.cflags ) -> (match (_36_3) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _36_441 = (Microsoft_FStar_Tc_Env.clear_expected_typ env)
in (match (_36_441) with
| (env, _) -> begin
(let _36_446 = (tc_ghost_exp env e)
in (match (_36_446) with
| (e, _, g) -> begin
(Microsoft_FStar_Absyn_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, Microsoft_FStar_Tc_Rel.trivial_guard)
end))))
in (Support.Prims.pipe_right _52_12866 Support.List.unzip))
in (match (_36_450) with
| (flags, guards) -> begin
(let _52_12868 = (Microsoft_FStar_Absyn_Syntax.mk_Comp (let _36_451 = c
in {Microsoft_FStar_Absyn_Syntax.effect_name = _36_451.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = res; Microsoft_FStar_Absyn_Syntax.effect_args = args; Microsoft_FStar_Absyn_Syntax.flags = _36_451.Microsoft_FStar_Absyn_Syntax.flags}))
in (let _52_12867 = (Support.List.fold_left Microsoft_FStar_Tc_Rel.conj_guard f guards)
in (_52_12868, _52_12867)))
end))
end))
end))
end)))))
end))
and tc_typ = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let env = (Microsoft_FStar_Tc_Env.set_range env t.Microsoft_FStar_Absyn_Syntax.pos)
in (let w = (fun ( k  :  Microsoft_FStar_Absyn_Syntax.knd ) -> (Microsoft_FStar_Absyn_Syntax.syn t.Microsoft_FStar_Absyn_Syntax.pos (Some (k))))
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
in (let _52_12891 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.Microsoft_FStar_Absyn_Syntax.pos)
in (_52_12891, qk, Microsoft_FStar_Tc_Rel.trivial_guard)))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (i) when ((Microsoft_FStar_Absyn_Syntax.lid_equals i.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.allTyp_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals i.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.exTyp_lid)) -> begin
(let k = (Microsoft_FStar_Tc_Util.new_kvar env)
in (let qk = (Microsoft_FStar_Absyn_Util.allT_k k)
in (let i = (let _36_482 = i
in {Microsoft_FStar_Absyn_Syntax.v = _36_482.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = qk; Microsoft_FStar_Absyn_Syntax.p = _36_482.Microsoft_FStar_Absyn_Syntax.p})
in (let _52_12892 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.Microsoft_FStar_Absyn_Syntax.pos)
in (_52_12892, qk, Microsoft_FStar_Tc_Rel.trivial_guard)))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (i) -> begin
(let k = (match ((Microsoft_FStar_Tc_Env.try_lookup_effect_lid env i.Microsoft_FStar_Absyn_Syntax.v)) with
| Some (k) -> begin
k
end
| _ -> begin
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
| Microsoft_FStar_Absyn_Syntax.Comp ({Microsoft_FStar_Absyn_Syntax.effect_name = _; Microsoft_FStar_Absyn_Syntax.result_typ = _; Microsoft_FStar_Absyn_Syntax.effect_args = (Support.Microsoft.FStar.Util.Inl (pre), _)::(Support.Microsoft.FStar.Util.Inl (post), _)::(Support.Microsoft.FStar.Util.Inr (pats), _)::[]; Microsoft_FStar_Absyn_Syntax.flags = _}) -> begin
(let fvs = (Microsoft_FStar_Absyn_Util.freevars_exp pats)
in (match ((Support.Prims.pipe_right bs (Support.Microsoft.FStar.Util.find_opt (fun ( _36_540  :  ((Microsoft_FStar_Absyn_Syntax.btvar, Microsoft_FStar_Absyn_Syntax.bvvar) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (_36_540) with
| (b, _) -> begin
(match (b) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _52_12896 = (Support.Microsoft.FStar.Util.set_mem a fvs.Microsoft_FStar_Absyn_Syntax.ftvs)
in (not (_52_12896)))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _52_12897 = (Support.Microsoft.FStar.Util.set_mem x fvs.Microsoft_FStar_Absyn_Syntax.fxvs)
in (not (_52_12897)))
end)
end))))) with
| None -> begin
()
end
| Some (b) -> begin
(let _52_12899 = (let _52_12898 = (Microsoft_FStar_Absyn_Print.binder_to_string b)
in (Support.Microsoft.FStar.Util.format1 "Pattern misses at least one bound variables: %s" _52_12898))
in (Microsoft_FStar_Tc_Errors.warn t.Microsoft_FStar_Absyn_Syntax.pos _52_12899))
end))
end
| _ -> begin
()
end)
end
| false -> begin
()
end)
in (let _52_12901 = (let _52_12900 = (Microsoft_FStar_Tc_Rel.close_guard bs f)
in (Microsoft_FStar_Tc_Rel.conj_guard g _52_12900))
in (t, Microsoft_FStar_Absyn_Syntax.ktype, _52_12901))))
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
in (let _52_12906 = (Support.Prims.pipe_left (w k) (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, t)))
in (let _52_12905 = (let _52_12904 = (Microsoft_FStar_Tc_Rel.close_guard bs f)
in (Support.Prims.pipe_left (Microsoft_FStar_Tc_Rel.conj_guard g) _52_12904))
in (_52_12906, k, _52_12905))))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, phi)) -> begin
(let _36_572 = (tc_vbinder env x)
in (match (_36_572) with
| (x, env, f1) -> begin
(let _36_576 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _52_12909 = (Support.Microsoft.FStar.Range.string_of_range top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_12908 = (Microsoft_FStar_Absyn_Print.typ_to_string phi)
in (let _52_12907 = (match ((Microsoft_FStar_Tc_Env.expected_typ env)) with
| None -> begin
"None"
end
| Some (t) -> begin
(Microsoft_FStar_Absyn_Print.typ_to_string t)
end)
in (Support.Microsoft.FStar.Util.fprint3 "(%s) Checking refinement formula %s; env expects type %s\n" _52_12909 _52_12908 _52_12907))))
end
| false -> begin
()
end)
in (let _36_580 = (tc_typ_check env phi Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_36_580) with
| (phi, f2) -> begin
(let _52_12916 = (Support.Prims.pipe_left (w Microsoft_FStar_Absyn_Syntax.ktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (x, phi)))
in (let _52_12915 = (let _52_12914 = (let _52_12913 = (let _52_12912 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_52_12912)::[])
in (Microsoft_FStar_Tc_Rel.close_guard _52_12913 f2))
in (Microsoft_FStar_Tc_Rel.conj_guard f1 _52_12914))
in (_52_12916, Microsoft_FStar_Absyn_Syntax.ktype, _52_12915)))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(let _36_585 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _52_12919 = (Support.Microsoft.FStar.Range.string_of_range top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_12918 = (Support.Prims.pipe_left Support.Microsoft.FStar.Util.string_of_int (Support.List.length args))
in (let _52_12917 = (Microsoft_FStar_Absyn_Print.typ_to_string top)
in (Support.Microsoft.FStar.Util.fprint3 "(%s) Checking type application (%s): %s\n" _52_12919 _52_12918 _52_12917))))
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
(let _52_12923 = (Support.Microsoft.FStar.Range.string_of_range head.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_12922 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (let _52_12921 = (Microsoft_FStar_Absyn_Print.kind_to_string k1')
in (let _52_12920 = (Microsoft_FStar_Absyn_Print.kind_to_string k1)
in (Support.Microsoft.FStar.Util.fprint4 "(%s) head %s has kind %s ... after norm %s\n" _52_12923 _52_12922 _52_12921 _52_12920)))))
end
| false -> begin
()
end)
in (let check_app = (fun ( _36_596  :  unit ) -> (match (()) with
| () -> begin
(match (k1.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_uvar (_) -> begin
(let _36_602 = (tc_args env args)
in (match (_36_602) with
| (args, g) -> begin
(let fvs = (Microsoft_FStar_Absyn_Util.freevars_kind k1)
in (let binders = (Microsoft_FStar_Absyn_Util.binders_of_freevars fvs)
in (let kres = (let _52_12926 = (Microsoft_FStar_Tc_Rel.new_kvar k1.Microsoft_FStar_Absyn_Syntax.pos binders)
in (Support.Prims.pipe_right _52_12926 Support.Prims.fst))
in (let bs = (let _52_12927 = (Microsoft_FStar_Tc_Util.tks_of_args args)
in (Microsoft_FStar_Absyn_Util.null_binders_of_tks _52_12927))
in (let kar = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) k1.Microsoft_FStar_Absyn_Syntax.pos)
in (let _36_608 = (let _52_12928 = (Microsoft_FStar_Tc_Rel.keq env None k1 kar)
in (Support.Prims.pipe_left (Microsoft_FStar_Tc_Util.force_trivial env) _52_12928))
in (kres, args, g)))))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((formals, kres)) -> begin
(let rec check_args = (fun ( outargs  :  ((Microsoft_FStar_Absyn_Syntax.typ, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) ( subst  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef * (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax), ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef * (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax)) Support.Microsoft.FStar.Util.either list ) ( g  :  Microsoft_FStar_Tc_Rel.guard_t ) ( formals  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, Microsoft_FStar_Absyn_Syntax.knd) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) ( args  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) -> (match ((formals, args)) with
| ([], []) -> begin
(let _52_12939 = (Microsoft_FStar_Absyn_Util.subst_kind subst kres)
in (_52_12939, (Support.List.rev outargs), g))
end
| (((_, None)::_, (_, Some (Microsoft_FStar_Absyn_Syntax.Implicit))::_)) | (((_, Some (Microsoft_FStar_Absyn_Syntax.Equality))::_, (_, Some (Microsoft_FStar_Absyn_Syntax.Implicit))::_)) -> begin
(let _52_12943 = (let _52_12942 = (let _52_12941 = (let _52_12940 = (Support.List.hd args)
in (Microsoft_FStar_Absyn_Util.range_of_arg _52_12940))
in ("Argument is marked as instantiating an implicit parameter; although the expected parameter is explicit", _52_12941))
in Microsoft_FStar_Absyn_Syntax.Error (_52_12942))
in (raise (_52_12943)))
end
| (((Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest, (_, None)::_)) | (((Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest, [])) -> begin
(let formal = (Support.List.hd formals)
in (let _36_681 = (let _52_12944 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Tc_Util.new_implicit_tvar env _52_12944))
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
in (let _36_710 = (let _52_12945 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (Microsoft_FStar_Tc_Util.new_implicit_evar env _52_12945))
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
(let _52_12947 = (Microsoft_FStar_Absyn_Print.arg_to_string actual)
in (let _52_12946 = (Microsoft_FStar_Absyn_Print.kind_to_string formal_k)
in (Support.Microsoft.FStar.Util.fprint2 "Checking argument %s against expected kind %s\n" _52_12947 _52_12946)))
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
(let _52_12948 = (Microsoft_FStar_Tc_Rel.guard_to_string env g')
in (Support.Microsoft.FStar.Util.fprint1 ">>>Got guard %s\n" _52_12948))
end
| false -> begin
()
end)
in (let actual = (Support.Microsoft.FStar.Util.Inl (t), imp)
in (let g' = (let _52_12950 = (let _52_12949 = (Microsoft_FStar_Tc_Util.short_circuit_typ (Support.Microsoft.FStar.Util.Inl (head)) outargs)
in (Support.Prims.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula _52_12949))
in (Microsoft_FStar_Tc_Rel.imp_guard _52_12950 g'))
in (let subst = (maybe_extend_subst subst formal actual)
in (let _52_12951 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _52_12951 formals actuals))))))
end))))
end
| ((Support.Microsoft.FStar.Util.Inr (x), aqual), (Support.Microsoft.FStar.Util.Inr (v), imp)) -> begin
(let tx = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let env' = (Microsoft_FStar_Tc_Env.set_expected_typ env tx)
in (let env' = (let _36_754 = env'
in {Microsoft_FStar_Tc_Env.solver = _36_754.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_754.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_754.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_754.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_754.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_754.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_754.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_754.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_754.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _36_754.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _36_754.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _36_754.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_754.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _36_754.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _36_754.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_754.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = (is_eq aqual); Microsoft_FStar_Tc_Env.is_iface = _36_754.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_754.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_754.Microsoft_FStar_Tc_Env.default_effects})
in (let _36_757 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _52_12953 = (Microsoft_FStar_Absyn_Print.arg_to_string actual)
in (let _52_12952 = (Microsoft_FStar_Absyn_Print.typ_to_string tx)
in (Support.Microsoft.FStar.Util.fprint2 "Checking argument %s against expected type %s\n" _52_12953 _52_12952)))
end
| false -> begin
()
end)
in (let _36_763 = (tc_ghost_exp env' v)
in (match (_36_763) with
| (v, _, g') -> begin
(let actual = (Support.Microsoft.FStar.Util.Inr (v), imp)
in (let g' = (let _52_12955 = (let _52_12954 = (Microsoft_FStar_Tc_Util.short_circuit_typ (Support.Microsoft.FStar.Util.Inl (head)) outargs)
in (Support.Prims.pipe_left Microsoft_FStar_Tc_Rel.guard_of_guard_formula _52_12954))
in (Microsoft_FStar_Tc_Rel.imp_guard _52_12955 g'))
in (let subst = (maybe_extend_subst subst formal actual)
in (let _52_12956 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _52_12956 formals actuals)))))
end))))))
end
| ((Support.Microsoft.FStar.Util.Inl (a), _), (Support.Microsoft.FStar.Util.Inr (v), imp)) -> begin
(match (a.Microsoft_FStar_Absyn_Syntax.sort.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
(let tv = (Microsoft_FStar_Absyn_Util.b2t v)
in (let _52_12958 = (let _52_12957 = (Microsoft_FStar_Absyn_Syntax.targ tv)
in (_52_12957)::actuals)
in (check_args outargs subst g ((formal)::formals) _52_12958)))
end
| _ -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Expected a type; got an expression", v.Microsoft_FStar_Absyn_Syntax.pos))))
end)
end
| ((Support.Microsoft.FStar.Util.Inr (_), _), (Support.Microsoft.FStar.Util.Inl (_), _)) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Expected an expression; got a type", (Microsoft_FStar_Absyn_Util.range_of_arg actual)))))
end)
end
| (_, []) -> begin
(let _52_12960 = (let _52_12959 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (formals, kres) kres.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Util.subst_kind subst _52_12959))
in (_52_12960, (Support.List.rev outargs), g))
end
| ([], _) -> begin
(let _52_12968 = (let _52_12967 = (let _52_12966 = (let _52_12965 = (let _52_12963 = (let _52_12962 = (Support.Prims.pipe_right outargs (Support.List.filter (fun ( _36_4  :  ((Microsoft_FStar_Absyn_Syntax.typ, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (_36_4) with
| (_, Some (Microsoft_FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _ -> begin
true
end))))
in (Support.List.length _52_12962))
in (Support.Prims.pipe_right _52_12963 Support.Microsoft.FStar.Util.string_of_int))
in (let _52_12964 = (Support.Prims.pipe_right (Support.List.length args0) Support.Microsoft.FStar.Util.string_of_int)
in (Support.Microsoft.FStar.Util.format2 "Too many arguments to type; expected %s arguments but got %s" _52_12965 _52_12964)))
in (_52_12966, top.Microsoft_FStar_Absyn_Syntax.pos))
in Microsoft_FStar_Absyn_Syntax.Error (_52_12967))
in (raise (_52_12968)))
end))
in (check_args [] [] f1 formals args))
end
| _ -> begin
(let _52_12971 = (let _52_12970 = (let _52_12969 = (Microsoft_FStar_Tc_Errors.expected_tcon_kind env top k1)
in (_52_12969, top.Microsoft_FStar_Absyn_Syntax.pos))
in Microsoft_FStar_Absyn_Syntax.Error (_52_12970))
in (raise (_52_12971)))
end)
end))
in (match ((let _52_12975 = (let _52_12972 = (Microsoft_FStar_Absyn_Util.compress_typ head)
in _52_12972.Microsoft_FStar_Absyn_Syntax.n)
in (let _52_12974 = (let _52_12973 = (Microsoft_FStar_Absyn_Util.compress_kind k1)
in _52_12973.Microsoft_FStar_Absyn_Syntax.n)
in (_52_12975, _52_12974)))) with
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), Microsoft_FStar_Absyn_Syntax.Kind_arrow ((formals, k))) when ((Support.List.length args) = (Support.List.length formals)) -> begin
(let result_k = (let s = (Support.List.map2 Microsoft_FStar_Absyn_Util.subst_formal formals args)
in (Microsoft_FStar_Absyn_Util.subst_kind s k))
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (head, args) (Some (result_k)) top.Microsoft_FStar_Absyn_Syntax.pos)
in (t, result_k, Microsoft_FStar_Tc_Rel.trivial_guard)))
end
| _ -> begin
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
(let _52_12979 = (Support.Prims.pipe_left (w k1) (Microsoft_FStar_Absyn_Syntax.mk_Typ_ascribed' (t1, k1)))
in (let _52_12978 = (Microsoft_FStar_Tc_Rel.conj_guard f1 f2)
in (_52_12979, k1, _52_12978)))
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
| (_, u') -> begin
(let _36_856 = (Microsoft_FStar_Absyn_Util.unchecked_unify u u')
in (u', k1, g))
end))
end))
end
| _ -> begin
(tc_typ env s)
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((_, k1)) -> begin
(let s = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (s.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((u, k1)) -> begin
(let _36_870 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) Microsoft_FStar_Options.High)) with
| true -> begin
(let _52_12981 = (Microsoft_FStar_Absyn_Print.typ_to_string s)
in (let _52_12980 = (Microsoft_FStar_Absyn_Print.kind_to_string k1)
in (Support.Microsoft.FStar.Util.fprint2 "Admitting un-instantiated uvar %s at kind %s\n" _52_12981 _52_12980)))
end
| false -> begin
()
end)
in (let _52_12984 = (Support.Prims.pipe_left (w k1) (Microsoft_FStar_Absyn_Syntax.mk_Typ_uvar' (u, k1)))
in (_52_12984, k1, Microsoft_FStar_Tc_Rel.trivial_guard)))
end
| _ -> begin
(let _36_874 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) Microsoft_FStar_Options.High)) with
| true -> begin
(let _52_12986 = (Microsoft_FStar_Absyn_Print.typ_to_string s)
in (let _52_12985 = (Microsoft_FStar_Absyn_Print.kind_to_string k1)
in (Support.Microsoft.FStar.Util.fprint2 "Admitting instantiated uvar %s at kind %s\n" _52_12986 _52_12985)))
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
(let _52_12987 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r))))
in (_52_12987, k, f))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, r, p))) -> begin
(let _36_896 = (tc_typ env t)
in (match (_36_896) with
| (t, k, f) -> begin
(let _52_12988 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, r, p))))
in (_52_12988, k, f))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, l))) -> begin
(let _36_905 = (tc_typ env t)
in (match (_36_905) with
| (t, k, f) -> begin
(let _52_12989 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, l))))
in (_52_12989, k, f))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((qbody, pats))) -> begin
(let _36_913 = (tc_typ_check env qbody Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_36_913) with
| (quant, f) -> begin
(let _36_916 = (tc_args env pats)
in (match (_36_916) with
| (pats, g) -> begin
(let _52_12992 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((quant, pats))))
in (let _52_12991 = (Microsoft_FStar_Tc_Util.force_tk quant)
in (let _52_12990 = (Microsoft_FStar_Tc_Rel.conj_guard f g)
in (_52_12992, _52_12991, _52_12990))))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(let k = (Microsoft_FStar_Tc_Util.new_kvar env)
in (let t = (Microsoft_FStar_Tc_Util.new_tvar env k)
in (t, k, Microsoft_FStar_Tc_Rel.trivial_guard)))
end
| _ -> begin
(let _52_12994 = (let _52_12993 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format1 "Unexpected type : %s\n" _52_12993))
in (failwith (_52_12994)))
end))))))
and tc_typ_check = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( t  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) ( k  :  Microsoft_FStar_Absyn_Syntax.knd ) -> (let _36_928 = (tc_typ env t)
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
and tc_value = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( e  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let env = (Microsoft_FStar_Tc_Env.set_range env e.Microsoft_FStar_Absyn_Syntax.pos)
in (let top = e
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((_, t1)) -> begin
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
(let _52_13001 = (let _52_13000 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (Support.Prims.pipe_left Microsoft_FStar_Tc_Util.lcomp_of_comp _52_13000))
in Support.Microsoft.FStar.Util.Inr (_52_13001))
end)
in (let _52_13002 = (value_check_expected_typ env e tc)
in (Support.Prims.pipe_left (with_implicits implicits) _52_13002)))
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
(let _52_13004 = (let _52_13003 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (Support.Prims.pipe_left Microsoft_FStar_Tc_Util.lcomp_of_comp _52_13003))
in Support.Microsoft.FStar.Util.Inr (_52_13004))
end)
in (let is_data_ctor = (fun ( _36_5  :  Microsoft_FStar_Absyn_Syntax.fv_qual option ) -> (match (_36_5) with
| (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) | (Some (Microsoft_FStar_Absyn_Syntax.Record_ctor (_))) -> begin
true
end
| _ -> begin
false
end))
in (match ((let _52_13008 = (let _52_13007 = (Microsoft_FStar_Tc_Env.is_datacon env v.Microsoft_FStar_Absyn_Syntax.v)
in (not (_52_13007)))
in ((is_data_ctor dc) && _52_13008))) with
| true -> begin
(let _52_13012 = (let _52_13011 = (let _52_13010 = (Support.Microsoft.FStar.Util.format1 "Expected a data constructor; got %s" v.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
in (let _52_13009 = (Microsoft_FStar_Tc_Env.get_range env)
in (_52_13010, _52_13009)))
in Microsoft_FStar_Absyn_Syntax.Error (_52_13011))
in (raise (_52_13012)))
end
| false -> begin
(let _52_13013 = (value_check_expected_typ env e tc)
in (Support.Prims.pipe_left (with_implicits implicits) _52_13013))
end)))
end))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let t = (Microsoft_FStar_Tc_Recheck.typing_const e.Microsoft_FStar_Absyn_Syntax.pos c)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant c (Some (t)) e.Microsoft_FStar_Absyn_Syntax.pos)
in (value_check_expected_typ env e (Support.Microsoft.FStar.Util.Inl (t)))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let fail = (fun ( msg  :  string ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let _52_13018 = (let _52_13017 = (let _52_13016 = (Microsoft_FStar_Tc_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_52_13016, top.Microsoft_FStar_Absyn_Syntax.pos))
in Microsoft_FStar_Absyn_Syntax.Error (_52_13017))
in (raise (_52_13018))))
in (let rec expected_function_typ = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( t0  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax option ) -> (match (t0) with
| None -> begin
(let _36_994 = (match (env.Microsoft_FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _ -> begin
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
in (let rec as_function_typ = (fun ( norm  :  bool ) ( t  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (match ((let _52_13027 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _52_13027.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let _36_1028 = (match (env.Microsoft_FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _ -> begin
(failwith ("Impossible"))
end)
in (let _36_1033 = (tc_binders env bs)
in (match (_36_1033) with
| (bs, envbody, g) -> begin
(let _36_1037 = (Microsoft_FStar_Tc_Env.clear_expected_typ envbody)
in (match (_36_1037) with
| (envbody, _) -> begin
(Some ((t, true)), bs, [], None, envbody, g)
end))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs', c)) -> begin
(let rec tc_binders = (fun ( _36_1047  :  (((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list * Microsoft_FStar_Tc_Env.env * Microsoft_FStar_Tc_Rel.guard_t * (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef * (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax), ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef * (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax)) Support.Microsoft.FStar.Util.either list) ) ( bs_annot  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) ( c  :  (Microsoft_FStar_Absyn_Syntax.comp', unit) Microsoft_FStar_Absyn_Syntax.syntax ) ( bs  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) -> (match (_36_1047) with
| (out, env, g, subst) -> begin
(match ((bs_annot, bs)) with
| ([], []) -> begin
(let _52_13036 = (Microsoft_FStar_Absyn_Util.subst_comp subst c)
in ((Support.List.rev out), env, g, _52_13036))
end
| (hdannot::tl_annot, hd::tl) -> begin
(match ((hdannot, hd)) with
| ((Support.Microsoft.FStar.Util.Inl (_), _), (Support.Microsoft.FStar.Util.Inr (_), _)) -> begin
(let env = (maybe_push_binding env hdannot)
in (tc_binders ((hdannot)::out, env, g, subst) tl_annot c bs))
end
| ((Support.Microsoft.FStar.Util.Inl (a), _), (Support.Microsoft.FStar.Util.Inl (b), imp)) -> begin
(let ka = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _36_1096 = (match (b.Microsoft_FStar_Absyn_Syntax.sort.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(ka, Microsoft_FStar_Tc_Rel.trivial_guard)
end
| _ -> begin
(let _36_1091 = (tc_kind env b.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_36_1091) with
| (k, g1) -> begin
(let g2 = (Microsoft_FStar_Tc_Rel.keq env None ka k)
in (let g = (let _52_13037 = (Microsoft_FStar_Tc_Rel.conj_guard g1 g2)
in (Microsoft_FStar_Tc_Rel.conj_guard g _52_13037))
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
| ((Support.Microsoft.FStar.Util.Inr (x), _), (Support.Microsoft.FStar.Util.Inr (y), imp)) -> begin
(let tx = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _36_1127 = (match ((let _52_13038 = (Microsoft_FStar_Absyn_Util.unmeta_typ y.Microsoft_FStar_Absyn_Syntax.sort)
in _52_13038.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(tx, g)
end
| _ -> begin
(let _36_1116 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _52_13039 = (Microsoft_FStar_Absyn_Print.binder_to_string hd)
in (Support.Microsoft.FStar.Util.fprint1 "Checking binder %s\n" _52_13039))
end
| false -> begin
()
end)
in (let _36_1122 = (tc_typ env y.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_36_1122) with
| (t, _, g1) -> begin
(let g2 = (Microsoft_FStar_Tc_Rel.teq env tx t)
in (let g = (let _52_13040 = (Microsoft_FStar_Tc_Rel.conj_guard g1 g2)
in (Microsoft_FStar_Tc_Rel.conj_guard g _52_13040))
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
| _ -> begin
(let _52_13043 = (let _52_13042 = (Microsoft_FStar_Absyn_Print.binder_to_string hdannot)
in (let _52_13041 = (Microsoft_FStar_Absyn_Print.binder_to_string hd)
in (Support.Microsoft.FStar.Util.format2 "Annotated %s; given %s" _52_13042 _52_13041)))
in (fail _52_13043 t))
end)
end
| ([], _) -> begin
(match ((Microsoft_FStar_Absyn_Util.is_total_comp c)) with
| true -> begin
(match ((Support.Prims.pipe_right (Microsoft_FStar_Absyn_Util.comp_result c) (whnf env))) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs_annot, c')); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
(tc_binders (out, env, g, subst) bs_annot c' bs)
end
| t -> begin
(let _52_13045 = (let _52_13044 = (Microsoft_FStar_Absyn_Print.tag_of_typ t)
in (Support.Microsoft.FStar.Util.format1 "More arguments than annotated type (%s)" _52_13044))
in (fail _52_13045 t))
end)
end
| false -> begin
(fail "Curried function, but not total" t)
end)
end
| (_, []) -> begin
(let c = (let _52_13046 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs_annot, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) c.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Util.total_comp _52_13046 c.Microsoft_FStar_Absyn_Syntax.pos))
in (let _52_13047 = (Microsoft_FStar_Absyn_Util.subst_comp subst c)
in ((Support.List.rev out), env, g, _52_13047)))
end)
end))
in (let mk_letrec_environment = (fun ( actuals  :  ((Microsoft_FStar_Absyn_Syntax.btvar, Microsoft_FStar_Absyn_Syntax.bvvar) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) ( env  :  Microsoft_FStar_Tc_Env.env ) -> (match (env.Microsoft_FStar_Tc_Env.letrecs) with
| [] -> begin
(env, [])
end
| letrecs -> begin
(let _36_1163 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _52_13052 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint1 "Building let-rec environment... type of this abstraction is %s\n" _52_13052))
end
| false -> begin
()
end)
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let env = (let _36_1166 = env
in {Microsoft_FStar_Tc_Env.solver = _36_1166.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_1166.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_1166.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_1166.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_1166.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_1166.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_1166.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_1166.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_1166.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _36_1166.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _36_1166.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _36_1166.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_1166.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = []; Microsoft_FStar_Tc_Env.top_level = _36_1166.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_1166.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = _36_1166.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = _36_1166.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_1166.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_1166.Microsoft_FStar_Tc_Env.default_effects})
in (let filter_types_and_functions = (fun ( bs  :  Microsoft_FStar_Absyn_Syntax.binders ) -> (Support.Prims.pipe_right bs (Support.List.collect (fun ( b  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (b) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
[]
end
| (Support.Microsoft.FStar.Util.Inr (x), _) -> begin
(match ((let _52_13058 = (let _52_13057 = (let _52_13056 = (Microsoft_FStar_Absyn_Util.unrefine x.Microsoft_FStar_Absyn_Syntax.sort)
in (whnf env _52_13056))
in (Microsoft_FStar_Absyn_Util.unrefine _52_13057))
in _52_13058.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_) -> begin
[]
end
| _ -> begin
(let _52_13059 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (_52_13059)::[])
end)
end)))))
in (let precedes = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.precedes_lid Microsoft_FStar_Absyn_Syntax.kun)
in (let as_lex_list = (fun ( dec  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let _36_1194 = (Microsoft_FStar_Absyn_Util.head_and_args_e dec)
in (match (_36_1194) with
| (head, _) -> begin
(match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _)) when (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.lexcons_lid) -> begin
dec
end
| _ -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (let prev_dec = (let ct = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c)
in (match ((Support.Prims.pipe_right ct.Microsoft_FStar_Absyn_Syntax.flags (Support.List.tryFind (fun ( _36_6  :  Microsoft_FStar_Absyn_Syntax.cflags ) -> (match (_36_6) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (_) -> begin
true
end
| _ -> begin
false
end))))) with
| Some (Microsoft_FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(let _36_1212 = (match (((Support.List.length bs') <> (Support.List.length actuals))) with
| true -> begin
(let _52_13068 = (let _52_13067 = (let _52_13066 = (let _52_13064 = (Support.Microsoft.FStar.Util.string_of_int (Support.List.length bs'))
in (let _52_13063 = (Support.Microsoft.FStar.Util.string_of_int (Support.List.length actuals))
in (Support.Microsoft.FStar.Util.format2 "Decreases clause on a function with an unexpected number of arguments (expected %s; got %s)" _52_13064 _52_13063)))
in (let _52_13065 = (Microsoft_FStar_Tc_Env.get_range env)
in (_52_13066, _52_13065)))
in Microsoft_FStar_Absyn_Syntax.Error (_52_13067))
in (raise (_52_13068)))
end
| false -> begin
()
end)
in (let dec = (as_lex_list dec)
in (let subst = (Support.List.map2 (fun ( b  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) ( a  :  ((Microsoft_FStar_Absyn_Syntax.btvar, Microsoft_FStar_Absyn_Syntax.bvvar) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match ((b, a)) with
| ((Support.Microsoft.FStar.Util.Inl (formal), _), (Support.Microsoft.FStar.Util.Inl (actual), _)) -> begin
(let _52_13072 = (let _52_13071 = (Microsoft_FStar_Absyn_Util.btvar_to_typ actual)
in (formal.Microsoft_FStar_Absyn_Syntax.v, _52_13071))
in Support.Microsoft.FStar.Util.Inl (_52_13072))
end
| ((Support.Microsoft.FStar.Util.Inr (formal), _), (Support.Microsoft.FStar.Util.Inr (actual), _)) -> begin
(let _52_13074 = (let _52_13073 = (Microsoft_FStar_Absyn_Util.bvar_to_exp actual)
in (formal.Microsoft_FStar_Absyn_Syntax.v, _52_13073))
in Support.Microsoft.FStar.Util.Inr (_52_13074))
end
| _ -> begin
(failwith ("impossible"))
end)) bs' actuals)
in (Microsoft_FStar_Absyn_Util.subst_exp subst dec))))
end
| _ -> begin
(let actual_args = (Support.Prims.pipe_right actuals filter_types_and_functions)
in (match (actual_args) with
| i::[] -> begin
i
end
| _ -> begin
(mk_lex_list actual_args)
end))
end))
in (let letrecs = (Support.Prims.pipe_right letrecs (Support.List.map (fun ( _36_1252  :  (Microsoft_FStar_Absyn_Syntax.lbname * (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) ) -> (match (_36_1252) with
| (l, t0) -> begin
(let t = (Microsoft_FStar_Absyn_Util.alpha_typ t0)
in (match ((let _52_13076 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _52_13076.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((formals, c)) -> begin
(match ((Support.Microsoft.FStar.Util.prefix formals)) with
| (bs, (Support.Microsoft.FStar.Util.Inr (x), imp)) -> begin
(let y = (Microsoft_FStar_Absyn_Util.gen_bvar_p x.Microsoft_FStar_Absyn_Syntax.p x.Microsoft_FStar_Absyn_Syntax.sort)
in (let ct = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c)
in (let precedes = (match ((Support.Prims.pipe_right ct.Microsoft_FStar_Absyn_Syntax.flags (Support.List.tryFind (fun ( _36_7  :  Microsoft_FStar_Absyn_Syntax.cflags ) -> (match (_36_7) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (_) -> begin
true
end
| _ -> begin
false
end))))) with
| Some (Microsoft_FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(let dec = (as_lex_list dec)
in (let dec = (let subst = (let _52_13080 = (let _52_13079 = (let _52_13078 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (x.Microsoft_FStar_Absyn_Syntax.v, _52_13078))
in Support.Microsoft.FStar.Util.Inr (_52_13079))
in (_52_13080)::[])
in (Microsoft_FStar_Absyn_Util.subst_exp subst dec))
in (let _52_13085 = (let _52_13084 = (let _52_13083 = (Microsoft_FStar_Absyn_Syntax.varg dec)
in (let _52_13082 = (let _52_13081 = (Microsoft_FStar_Absyn_Syntax.varg prev_dec)
in (_52_13081)::[])
in (_52_13083)::_52_13082))
in (precedes, _52_13084))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_13085 None r))))
end
| _ -> begin
(let formal_args = (let _52_13088 = (let _52_13087 = (let _52_13086 = (Microsoft_FStar_Absyn_Syntax.v_binder y)
in (_52_13086)::[])
in (Support.List.append bs _52_13087))
in (Support.Prims.pipe_right _52_13088 filter_types_and_functions))
in (let lhs = (match (formal_args) with
| i::[] -> begin
i
end
| _ -> begin
(mk_lex_list formal_args)
end)
in (let _52_13093 = (let _52_13092 = (let _52_13091 = (Microsoft_FStar_Absyn_Syntax.varg lhs)
in (let _52_13090 = (let _52_13089 = (Microsoft_FStar_Absyn_Syntax.varg prev_dec)
in (_52_13089)::[])
in (_52_13091)::_52_13090))
in (precedes, _52_13092))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_13093 None r))))
end)
in (let refined_domain = (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (y, precedes) None r)
in (let bs = (Support.List.append bs (((Support.Microsoft.FStar.Util.Inr ((let _36_1288 = x
in {Microsoft_FStar_Absyn_Syntax.v = _36_1288.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = refined_domain; Microsoft_FStar_Absyn_Syntax.p = _36_1288.Microsoft_FStar_Absyn_Syntax.p})), imp))::[]))
in (let t' = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None r)
in (let _36_1292 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _52_13096 = (Microsoft_FStar_Absyn_Print.lbname_to_string l)
in (let _52_13095 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (let _52_13094 = (Microsoft_FStar_Absyn_Print.typ_to_string t')
in (Support.Microsoft.FStar.Util.fprint3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _52_13096 _52_13095 _52_13094))))
end
| false -> begin
()
end)
in (let _36_1299 = (let _52_13098 = (let _52_13097 = (Microsoft_FStar_Tc_Env.clear_expected_typ env)
in (Support.Prims.pipe_right _52_13097 Support.Prims.fst))
in (tc_typ _52_13098 t'))
in (match (_36_1299) with
| (t', _, _) -> begin
(l, t')
end)))))))))
end
| _ -> begin
(failwith ("Impossible"))
end)
end
| _ -> begin
(failwith ("Impossible"))
end))
end))))
in (let _52_13104 = (Support.Prims.pipe_right letrecs (Support.List.fold_left (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( _36_1308  :  ((Microsoft_FStar_Absyn_Syntax.bvvdef, Microsoft_FStar_Absyn_Syntax.lident) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.typ) ) -> (match (_36_1308) with
| (x, t) -> begin
(Microsoft_FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end)) env))
in (let _52_13103 = (Support.Prims.pipe_right letrecs (Support.List.collect (fun ( _36_8  :  (((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, Microsoft_FStar_Absyn_Syntax.l__LongIdent) Support.Microsoft.FStar.Util.either * (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) ) -> (match (_36_8) with
| (Support.Microsoft.FStar.Util.Inl (x), t) -> begin
(let _52_13102 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_52_13102)::[])
end
| _ -> begin
[]
end))))
in (_52_13104, _52_13103)))))))))))
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
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((b, _)) -> begin
(let _36_1337 = (as_function_typ norm b.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_36_1337) with
| (_, bs, bs', copt, env, g) -> begin
(Some ((t, false)), bs, bs', copt, env, g)
end))
end
| _ -> begin
(match ((not (norm))) with
| true -> begin
(let _52_13105 = (whnf env t)
in (as_function_typ true _52_13105))
end
| false -> begin
(let _36_1348 = (expected_function_typ env None)
in (match (_36_1348) with
| (_, bs, _, c_opt, envbody, g) -> begin
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
(let _52_13108 = (Microsoft_FStar_Absyn_Print.exp_to_string body)
in (let _52_13107 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string cbody)
in (let _52_13106 = (Microsoft_FStar_Tc_Rel.guard_to_string env guard_body)
in (Support.Microsoft.FStar.Util.fprint3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _52_13108 _52_13107 _52_13106))))
end
| false -> begin
()
end)
in (let guard_body = (Microsoft_FStar_Tc_Rel.solve_deferred_constraints envbody guard_body)
in (let _36_1369 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Implicits")))) with
| true -> begin
(let _52_13109 = (Support.Prims.pipe_left Support.Microsoft.FStar.Util.string_of_int (Support.List.length guard_body.Microsoft_FStar_Tc_Rel.implicits))
in (Support.Microsoft.FStar.Util.fprint1 "Introduced %s implicits in body of abstraction\n" _52_13109))
end
| false -> begin
()
end)
in (let _36_1376 = (let _52_13111 = (let _52_13110 = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp cbody ())
in (body, _52_13110))
in (check_expected_effect (let _36_1371 = envbody
in {Microsoft_FStar_Tc_Env.solver = _36_1371.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_1371.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_1371.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_1371.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_1371.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_1371.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_1371.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_1371.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_1371.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _36_1371.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _36_1371.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _36_1371.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_1371.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _36_1371.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _36_1371.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_1371.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = use_eq; Microsoft_FStar_Tc_Env.is_iface = _36_1371.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_1371.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_1371.Microsoft_FStar_Tc_Env.default_effects}) c_opt _52_13111))
in (match (_36_1376) with
| (body, cbody, guard) -> begin
(let guard = (Microsoft_FStar_Tc_Rel.conj_guard guard_body guard)
in (let guard = (match ((let _52_13113 = (let _52_13112 = (Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)
in (not (_52_13112)))
in (env.Microsoft_FStar_Tc_Env.top_level || _52_13113))) with
| true -> begin
(let _36_1378 = (let _52_13114 = (Microsoft_FStar_Tc_Rel.conj_guard g guard)
in (Microsoft_FStar_Tc_Util.discharge_guard envbody _52_13114))
in (let _36_1380 = Microsoft_FStar_Tc_Rel.trivial_guard
in {Microsoft_FStar_Tc_Rel.guard_f = _36_1380.Microsoft_FStar_Tc_Rel.guard_f; Microsoft_FStar_Tc_Rel.deferred = _36_1380.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = guard.Microsoft_FStar_Tc_Rel.implicits}))
end
| false -> begin
(let guard = (Microsoft_FStar_Tc_Rel.close_guard (Support.List.append bs letrec_binders) guard)
in (Microsoft_FStar_Tc_Rel.conj_guard g guard))
end)
in (let tfun_computed = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, cbody) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) top.Microsoft_FStar_Absyn_Syntax.pos)
in (let e = (let _52_13116 = (let _52_13115 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (bs, body) (Some (tfun_computed)) top.Microsoft_FStar_Absyn_Syntax.pos)
in (_52_13115, tfun_computed, Some (Microsoft_FStar_Absyn_Const.effect_Tot_lid)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed _52_13116 None top.Microsoft_FStar_Absyn_Syntax.pos))
in (let _36_1403 = (match (tfun_opt) with
| Some ((t, use_teq)) -> begin
(let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_) -> begin
(let _52_13119 = (let _52_13118 = (let _52_13117 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (bs, body) (Some (t)) e.Microsoft_FStar_Absyn_Syntax.pos)
in (_52_13117, t, Some (Microsoft_FStar_Absyn_Const.effect_Tot_lid)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed _52_13118 None top.Microsoft_FStar_Absyn_Syntax.pos))
in (_52_13119, t, guard))
end
| _ -> begin
(let _36_1398 = (match (use_teq) with
| true -> begin
(let _52_13120 = (Microsoft_FStar_Tc_Rel.teq env t tfun_computed)
in (e, _52_13120))
end
| false -> begin
(Microsoft_FStar_Tc_Util.check_and_ascribe env e tfun_computed t)
end)
in (match (_36_1398) with
| (e, guard') -> begin
(let _52_13122 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed (e, t, Some (Microsoft_FStar_Absyn_Const.effect_Tot_lid)) None top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_13121 = (Microsoft_FStar_Tc_Rel.conj_guard guard guard')
in (_52_13122, t, _52_13121)))
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
(let _52_13125 = (Microsoft_FStar_Absyn_Print.typ_to_string tfun)
in (let _52_13124 = (Microsoft_FStar_Absyn_Print.tag_of_typ tfun)
in (let _52_13123 = (Microsoft_FStar_Tc_Rel.guard_to_string env guard)
in (Support.Microsoft.FStar.Util.fprint3 "!!!!!!!!!!!!!!!Annotating lambda with type %s (%s)\nGuard is %s\n" _52_13125 _52_13124 _52_13123))))
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
in (let _36_1409 = (let _52_13127 = (Microsoft_FStar_Tc_Util.lcomp_of_comp c)
in (Microsoft_FStar_Tc_Util.strengthen_precondition None env e _52_13127 guard))
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
| _ -> begin
(let _52_13129 = (let _52_13128 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format1 "Unexpected value: %s" _52_13128))
in (failwith (_52_13129)))
end))))
and tc_exp = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( e  :  Microsoft_FStar_Absyn_Syntax.exp ) -> (let env = (match ((e.Microsoft_FStar_Absyn_Syntax.pos = Microsoft_FStar_Absyn_Syntax.dummyRange)) with
| true -> begin
env
end
| false -> begin
(Microsoft_FStar_Tc_Env.set_range env e.Microsoft_FStar_Absyn_Syntax.pos)
end)
in (let _36_1415 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _52_13134 = (let _52_13132 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range _52_13132))
in (let _52_13133 = (Microsoft_FStar_Absyn_Print.tag_of_exp e)
in (Support.Microsoft.FStar.Util.fprint2 "%s (%s)\n" _52_13134 _52_13133)))
end
| false -> begin
()
end)
in (let w = (fun ( lc  :  Microsoft_FStar_Absyn_Syntax.lcomp ) -> (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Syntax.syn e.Microsoft_FStar_Absyn_Syntax.pos) (Some (lc.Microsoft_FStar_Absyn_Syntax.res_typ))))
in (let top = e
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_) -> begin
(let _52_13158 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (tc_exp env _52_13158))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_abs (_)) -> begin
(tc_value env e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e1, t1, _)) -> begin
(let _36_1446 = (tc_typ_check env t1 Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_36_1446) with
| (t1, f) -> begin
(let _36_1450 = (let _52_13159 = (Microsoft_FStar_Tc_Env.set_expected_typ env t1)
in (tc_exp _52_13159 e1))
in (match (_36_1450) with
| (e1, c, g) -> begin
(let _36_1454 = (let _52_13163 = (Microsoft_FStar_Tc_Env.set_range env t1.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Tc_Util.strengthen_precondition (Some ((fun ( _36_1451  :  unit ) -> (match (()) with
| () -> begin
Microsoft_FStar_Tc_Errors.ill_kinded_type
end)))) _52_13163 e1 c f))
in (match (_36_1454) with
| (c, f) -> begin
(let _36_1458 = (let _52_13167 = (let _52_13166 = (w c)
in (Support.Prims.pipe_left _52_13166 (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed (e1, t1, Some (c.Microsoft_FStar_Absyn_Syntax.eff_name)))))
in (comp_check_expected_typ env _52_13167 c))
in (match (_36_1458) with
| (e, c, f2) -> begin
(let _52_13169 = (let _52_13168 = (Microsoft_FStar_Tc_Rel.conj_guard g f2)
in (Microsoft_FStar_Tc_Rel.conj_guard f _52_13168))
in (e, c, _52_13169))
end))
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.Sequence))) -> begin
(match ((let _52_13170 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _52_13170.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_let (((_, {Microsoft_FStar_Absyn_Syntax.lbname = x; Microsoft_FStar_Absyn_Syntax.lbtyp = _; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = e1}::[]), e2)) -> begin
(let _36_1481 = (let _52_13171 = (Microsoft_FStar_Tc_Env.set_expected_typ env Microsoft_FStar_Tc_Recheck.t_unit)
in (tc_exp _52_13171 e1))
in (match (_36_1481) with
| (e1, c1, g1) -> begin
(let _36_1485 = (tc_exp env e2)
in (match (_36_1485) with
| (e2, c2, g2) -> begin
(let c = (Microsoft_FStar_Tc_Util.bind env (Some (e1)) c1 (None, c2))
in (let _52_13184 = (let _52_13182 = (let _52_13181 = (let _52_13180 = (let _52_13179 = (w c)
in (let _52_13178 = (let _52_13177 = (let _52_13176 = (let _52_13175 = (let _52_13174 = (Microsoft_FStar_Absyn_Syntax.mk_lb (x, c1.Microsoft_FStar_Absyn_Syntax.eff_name, Microsoft_FStar_Tc_Recheck.t_unit, e1))
in (_52_13174)::[])
in (false, _52_13175))
in (_52_13176, e2))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_let _52_13177))
in (Support.Prims.pipe_left _52_13179 _52_13178)))
in (_52_13180, Microsoft_FStar_Absyn_Syntax.Sequence))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_52_13181))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _52_13182))
in (let _52_13183 = (Microsoft_FStar_Tc_Rel.conj_guard g1 g2)
in (_52_13184, c, _52_13183))))
end))
end))
end
| _ -> begin
(let _36_1492 = (tc_exp env e)
in (match (_36_1492) with
| (e, c, g) -> begin
(let _52_13185 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, Microsoft_FStar_Absyn_Syntax.Sequence))))
in (_52_13185, c, g))
end))
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, i))) -> begin
(let _36_1501 = (tc_exp env e)
in (match (_36_1501) with
| (e, c, g) -> begin
(let _52_13186 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, i))))
in (_52_13186, c, g))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args)) -> begin
(let env0 = env
in (let env = (let _52_13188 = (let _52_13187 = (Microsoft_FStar_Tc_Env.clear_expected_typ env)
in (Support.Prims.pipe_right _52_13187 Support.Prims.fst))
in (Support.Prims.pipe_right _52_13188 instantiate_both))
in (let _36_1508 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _52_13190 = (Support.Microsoft.FStar.Range.string_of_range top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_13189 = (Microsoft_FStar_Absyn_Print.exp_to_string top)
in (Support.Microsoft.FStar.Util.fprint2 "(%s) Checking app %s\n" _52_13190 _52_13189)))
end
| false -> begin
()
end)
in (let _36_1513 = (tc_exp (no_inst env) head)
in (match (_36_1513) with
| (head, chead, g_head) -> begin
(let aux = (fun ( _36_1515  :  unit ) -> (match (()) with
| () -> begin
(let n_args = (Support.List.length args)
in (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _)) when (((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.op_And) || (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.op_Or)) && (n_args = 2)) -> begin
(let env = (Microsoft_FStar_Tc_Env.set_expected_typ env Microsoft_FStar_Absyn_Util.t_bool)
in (match (args) with
| (Support.Microsoft.FStar.Util.Inr (e1), _)::(Support.Microsoft.FStar.Util.Inr (e2), _)::[] -> begin
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
(let _52_13196 = (let _52_13193 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Util.b2t _52_13193))
in (let _52_13195 = (let _52_13194 = (Microsoft_FStar_Tc_Util.return_value env Microsoft_FStar_Absyn_Util.t_bool xexp)
in (Support.Prims.pipe_right _52_13194 Microsoft_FStar_Tc_Util.lcomp_of_comp))
in (Microsoft_FStar_Tc_Util.ite env _52_13196 c2 _52_13195)))
end
| false -> begin
(let _52_13200 = (let _52_13197 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Util.b2t _52_13197))
in (let _52_13199 = (let _52_13198 = (Microsoft_FStar_Tc_Util.return_value env Microsoft_FStar_Absyn_Util.t_bool xexp)
in (Support.Prims.pipe_right _52_13198 Microsoft_FStar_Tc_Util.lcomp_of_comp))
in (Microsoft_FStar_Tc_Util.ite env _52_13200 _52_13199 c2)))
end)
in (let c = (let _52_13203 = (let _52_13202 = (Support.Prims.pipe_left (fun ( _52_13201  :  Microsoft_FStar_Tc_Env.binding ) -> Some (_52_13201)) (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, Microsoft_FStar_Absyn_Util.t_bool))))
in (_52_13202, c2))
in (Microsoft_FStar_Tc_Util.bind env None c1 _52_13203))
in (let e = (let _52_13208 = (let _52_13207 = (let _52_13206 = (Microsoft_FStar_Absyn_Syntax.varg e1)
in (let _52_13205 = (let _52_13204 = (Microsoft_FStar_Absyn_Syntax.varg e2)
in (_52_13204)::[])
in (_52_13206)::_52_13205))
in (head, _52_13207))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _52_13208 (Some (Microsoft_FStar_Absyn_Util.t_bool)) top.Microsoft_FStar_Absyn_Syntax.pos))
in (let _52_13210 = (let _52_13209 = (Microsoft_FStar_Tc_Rel.conj_guard g1 g2)
in (Microsoft_FStar_Tc_Rel.conj_guard g_head _52_13209))
in (e, c, _52_13210)))))))
end))
end))
end
| _ -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Expected two boolean arguments", head.Microsoft_FStar_Absyn_Syntax.pos))))
end))
end
| _ -> begin
(let thead = chead.Microsoft_FStar_Absyn_Syntax.res_typ
in (let _36_1552 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _52_13212 = (Support.Microsoft.FStar.Range.string_of_range head.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_13211 = (Microsoft_FStar_Absyn_Print.typ_to_string thead)
in (Support.Microsoft.FStar.Util.fprint2 "(%s) Type of head is %s\n" _52_13212 _52_13211)))
end
| false -> begin
()
end)
in (let rec check_function_app = (fun ( norm  :  bool ) ( tf  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (match ((let _52_13217 = (Microsoft_FStar_Absyn_Util.unrefine tf)
in _52_13217.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let rec tc_args = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( args  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, Microsoft_FStar_Absyn_Syntax.exp) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) -> (match (args) with
| [] -> begin
([], [], Microsoft_FStar_Tc_Rel.trivial_guard)
end
| (Support.Microsoft.FStar.Util.Inl (t), _)::_ -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Explicit type applications on a term with unknown type; add an annotation?", t.Microsoft_FStar_Absyn_Syntax.pos))))
end
| (Support.Microsoft.FStar.Util.Inr (e), imp)::tl -> begin
(let _36_1597 = (tc_exp env e)
in (match (_36_1597) with
| (e, c, g_e) -> begin
(let _36_1601 = (tc_args env tl)
in (match (_36_1601) with
| (args, comps, g_rest) -> begin
(let _52_13222 = (Microsoft_FStar_Tc_Rel.conj_guard g_e g_rest)
in (((Support.Microsoft.FStar.Util.Inr (e), imp))::args, (c)::comps, _52_13222))
end))
end))
end))
in (let _36_1605 = (tc_args env args)
in (match (_36_1605) with
| (args, comps, g_args) -> begin
(let bs = (let _52_13223 = (Microsoft_FStar_Tc_Util.tks_of_args args)
in (Microsoft_FStar_Absyn_Util.null_binders_of_tks _52_13223))
in (let cres = (let _52_13224 = (Microsoft_FStar_Tc_Util.new_tvar env Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Util.ml_comp _52_13224 top.Microsoft_FStar_Absyn_Syntax.pos))
in (let _36_1608 = (let _52_13226 = (let _52_13225 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, cres) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) tf.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Tc_Rel.teq env tf _52_13225))
in (Support.Prims.pipe_left (Microsoft_FStar_Tc_Util.force_trivial env) _52_13226))
in (let comp = (let _52_13229 = (Support.Prims.pipe_left Microsoft_FStar_Tc_Util.lcomp_of_comp cres)
in (Support.List.fold_right (fun ( c  :  Microsoft_FStar_Absyn_Syntax.lcomp ) ( out  :  Microsoft_FStar_Absyn_Syntax.lcomp ) -> (Microsoft_FStar_Tc_Util.bind env None c (None, out))) ((chead)::comps) _52_13229))
in (let _52_13231 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (head, args) (Some (comp.Microsoft_FStar_Absyn_Syntax.res_typ)) top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_13230 = (Microsoft_FStar_Tc_Rel.conj_guard g_head g_args)
in (_52_13231, comp, _52_13230)))))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let vars = (Microsoft_FStar_Tc_Env.binders env)
in (let rec tc_args = (fun ( _36_1625  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef * (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax), ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef * (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax)) Support.Microsoft.FStar.Util.either list * ((Microsoft_FStar_Absyn_Syntax.typ, Microsoft_FStar_Absyn_Syntax.exp) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.aqual) list * ((Microsoft_FStar_Absyn_Syntax.typ, Microsoft_FStar_Absyn_Syntax.exp) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.aqual) list * (Microsoft_FStar_Tc_Env.binding option * Microsoft_FStar_Absyn_Syntax.lcomp) list * Microsoft_FStar_Tc_Rel.guard_t * (Microsoft_FStar_Absyn_Syntax.bvvar list * (Microsoft_FStar_Absyn_Syntax.bvvar  ->  Microsoft_FStar_Absyn_Syntax.bvvar  ->  bool))) ) ( bs  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, Microsoft_FStar_Absyn_Syntax.knd) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) ( cres  :  Microsoft_FStar_Absyn_Syntax.lcomp ) ( args  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) list ) -> (match (_36_1625) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest, (_, None)::_) -> begin
(let k = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _36_1645 = (fxv_check head env (Support.Microsoft.FStar.Util.Inl (k)) fvs)
in (let _36_1649 = (let _52_13267 = (let _52_13266 = (Support.List.hd args)
in (Microsoft_FStar_Absyn_Util.range_of_arg _52_13266))
in (Microsoft_FStar_Tc_Rel.new_tvar _52_13267 vars k))
in (match (_36_1649) with
| (targ, u) -> begin
(let _36_1650 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _52_13269 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (let _52_13268 = (Microsoft_FStar_Absyn_Print.typ_to_string targ)
in (Support.Microsoft.FStar.Util.fprint2 "Instantiating %s to %s" _52_13269 _52_13268)))
end
| false -> begin
()
end)
in (let subst = (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, targ)))::subst
in (let arg = (let _52_13270 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inl (targ), _52_13270))
in (let _52_13279 = (let _52_13278 = (let _52_13277 = (let _52_13276 = (let _52_13275 = (Microsoft_FStar_Tc_Util.as_uvar_t u)
in (_52_13275, u.Microsoft_FStar_Absyn_Syntax.pos))
in Support.Microsoft.FStar.Util.Inl (_52_13276))
in (add_implicit _52_13277 g))
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _52_13278, fvs))
in (tc_args _52_13279 rest cres args)))))
end))))
end
| ((Support.Microsoft.FStar.Util.Inr (x), Some (Microsoft_FStar_Absyn_Syntax.Implicit))::rest, (_, None)::_) -> begin
(let t = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _36_1670 = (fxv_check head env (Support.Microsoft.FStar.Util.Inr (t)) fvs)
in (let _36_1674 = (Microsoft_FStar_Tc_Util.new_implicit_evar env t)
in (match (_36_1674) with
| (varg, u) -> begin
(let subst = (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, varg)))::subst
in (let arg = (let _52_13280 = (Microsoft_FStar_Absyn_Syntax.as_implicit true)
in (Support.Microsoft.FStar.Util.Inr (varg), _52_13280))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, (add_implicit (Support.Microsoft.FStar.Util.Inr (u)) g), fvs) rest cres args)))
end))))
end
| ((Support.Microsoft.FStar.Util.Inl (a), aqual)::rest, (Support.Microsoft.FStar.Util.Inl (t), aq)::rest') -> begin
(let _36_1690 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _52_13286 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (let _52_13285 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint2 "\tGot a type arg for %s = %s\n" _52_13286 _52_13285)))
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
(let f = (let _52_13287 = (Microsoft_FStar_Tc_Rel.guard_f g')
in (Microsoft_FStar_Tc_Util.label_guard Microsoft_FStar_Tc_Errors.ill_kinded_type t.Microsoft_FStar_Absyn_Syntax.pos _52_13287))
in (let g' = (let _36_1701 = g'
in {Microsoft_FStar_Tc_Rel.guard_f = f; Microsoft_FStar_Tc_Rel.deferred = _36_1701.Microsoft_FStar_Tc_Rel.deferred; Microsoft_FStar_Tc_Rel.implicits = _36_1701.Microsoft_FStar_Tc_Rel.implicits})
in (let arg = (Support.Microsoft.FStar.Util.Inl (t), aq)
in (let subst = (let _52_13288 = (Support.List.hd bs)
in (maybe_extend_subst subst _52_13288 arg))
in (let _52_13294 = (let _52_13293 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _52_13293, fvs))
in (tc_args _52_13294 rest cres rest'))))))
end)))))
end
| ((Support.Microsoft.FStar.Util.Inr (x), aqual)::rest, (Support.Microsoft.FStar.Util.Inr (e), aq)::rest') -> begin
(let _36_1719 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _52_13296 = (Microsoft_FStar_Absyn_Print.subst_to_string subst)
in (let _52_13295 = (Microsoft_FStar_Absyn_Print.typ_to_string x.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.Microsoft.FStar.Util.fprint2 "\tType of arg (before subst (%s)) = %s\n" _52_13296 _52_13295)))
end
| false -> begin
()
end)
in (let targ = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _36_1722 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _52_13297 = (Microsoft_FStar_Absyn_Print.typ_to_string targ)
in (Support.Microsoft.FStar.Util.fprint1 "\tType of arg (after subst) = %s\n" _52_13297))
end
| false -> begin
()
end)
in (let _36_1724 = (fxv_check head env (Support.Microsoft.FStar.Util.Inr (targ)) fvs)
in (let env = (Microsoft_FStar_Tc_Env.set_expected_typ env targ)
in (let env = (let _36_1727 = env
in {Microsoft_FStar_Tc_Env.solver = _36_1727.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_1727.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_1727.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_1727.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_1727.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_1727.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_1727.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_1727.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_1727.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _36_1727.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _36_1727.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _36_1727.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_1727.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _36_1727.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _36_1727.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_1727.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = (is_eq aqual); Microsoft_FStar_Tc_Env.is_iface = _36_1727.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_1727.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_1727.Microsoft_FStar_Tc_Env.default_effects})
in (let _36_1730 = (match ((let _52_13298 = (Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("EQ")))
in (_52_13298 && env.Microsoft_FStar_Tc_Env.use_eq))) with
| true -> begin
(let _52_13300 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _52_13299 = (Microsoft_FStar_Absyn_Print.typ_to_string targ)
in (Support.Microsoft.FStar.Util.fprint2 "Checking arg %s at type %s with an equality constraint!\n" _52_13300 _52_13299)))
end
| false -> begin
()
end)
in (let _36_1732 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _52_13303 = (Microsoft_FStar_Absyn_Print.tag_of_exp e)
in (let _52_13302 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _52_13301 = (Microsoft_FStar_Absyn_Print.typ_to_string targ)
in (Support.Microsoft.FStar.Util.fprint3 "Checking arg (%s) %s at type %s\n" _52_13303 _52_13302 _52_13301))))
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
(let _52_13305 = (Microsoft_FStar_Tc_Rel.guard_to_string env g_e)
in (let _52_13304 = (Microsoft_FStar_Tc_Rel.guard_to_string env g)
in (Support.Microsoft.FStar.Util.fprint2 "Guard on this arg is %s;\naccumulated guard is %s\n" _52_13305 _52_13304)))
end
| false -> begin
()
end)
in (let arg = (Support.Microsoft.FStar.Util.Inr (e), aq)
in (match ((Microsoft_FStar_Absyn_Util.is_total_lcomp c)) with
| true -> begin
(let subst = (let _52_13306 = (Support.List.hd bs)
in (maybe_extend_subst subst _52_13306 arg))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end
| false -> begin
(match ((Microsoft_FStar_Tc_Util.is_pure_effect env c.Microsoft_FStar_Absyn_Syntax.eff_name)) with
| true -> begin
(let subst = (let _52_13311 = (Support.List.hd bs)
in (maybe_extend_subst subst _52_13311 arg))
in (let _36_1746 = (((Some (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, targ))), c))::comps, g)
in (match (_36_1746) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end
| false -> begin
(match ((let _52_13316 = (Support.List.hd bs)
in (Microsoft_FStar_Absyn_Syntax.is_null_binder _52_13316))) with
| true -> begin
(let newx = (Microsoft_FStar_Absyn_Util.gen_bvar_p e.Microsoft_FStar_Absyn_Syntax.pos c.Microsoft_FStar_Absyn_Syntax.res_typ)
in (let arg' = (let _52_13317 = (Microsoft_FStar_Absyn_Util.bvar_to_exp newx)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.varg _52_13317))
in (let binding = Microsoft_FStar_Tc_Env.Binding_var ((newx.Microsoft_FStar_Absyn_Syntax.v, newx.Microsoft_FStar_Absyn_Syntax.sort))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (binding), c))::comps, g, fvs) rest cres rest'))))
end
| false -> begin
(let _52_13330 = (let _52_13329 = (let _52_13323 = (let _52_13322 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.varg _52_13322))
in (_52_13323)::arg_rets)
in (let _52_13328 = (let _52_13326 = (let _52_13325 = (Support.Prims.pipe_left (fun ( _52_13324  :  Microsoft_FStar_Tc_Env.binding ) -> Some (_52_13324)) (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, targ))))
in (_52_13325, c))
in (_52_13326)::comps)
in (let _52_13327 = (Support.Microsoft.FStar.Util.set_add x fvs)
in (subst, (arg)::outargs, _52_13329, _52_13328, g, _52_13327))))
in (tc_args _52_13330 rest cres rest'))
end)
end)
end))))
end))))))))))
end
| ((Support.Microsoft.FStar.Util.Inr (_), _)::_, (Support.Microsoft.FStar.Util.Inl (_), _)::_) -> begin
(let _52_13334 = (let _52_13333 = (let _52_13332 = (let _52_13331 = (Support.List.hd args)
in (Microsoft_FStar_Absyn_Util.range_of_arg _52_13331))
in ("Expected an expression; got a type", _52_13332))
in Microsoft_FStar_Absyn_Syntax.Error (_52_13333))
in (raise (_52_13334)))
end
| ((Support.Microsoft.FStar.Util.Inl (_), _)::_, (Support.Microsoft.FStar.Util.Inr (_), _)::_) -> begin
(let _52_13338 = (let _52_13337 = (let _52_13336 = (let _52_13335 = (Support.List.hd args)
in (Microsoft_FStar_Absyn_Util.range_of_arg _52_13335))
in ("Expected a type; got an expression", _52_13336))
in Microsoft_FStar_Absyn_Syntax.Error (_52_13337))
in (raise (_52_13338)))
end
| (_, []) -> begin
(let _36_1792 = (fxv_check head env (Support.Microsoft.FStar.Util.Inr (cres.Microsoft_FStar_Absyn_Syntax.res_typ)) fvs)
in (let _36_1810 = (match (bs) with
| [] -> begin
(let cres = (Microsoft_FStar_Tc_Util.subst_lcomp subst cres)
in (let g = (Microsoft_FStar_Tc_Rel.conj_guard g_head g)
in (let refine_with_equality = (let _52_13342 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_lcomp cres)
in (let _52_13341 = (Support.Prims.pipe_right comps (Support.Microsoft.FStar.Util.for_some (fun ( _36_1800  :  (Microsoft_FStar_Tc_Env.binding option * Microsoft_FStar_Absyn_Syntax.lcomp) ) -> (match (_36_1800) with
| (_, c) -> begin
(let _52_13340 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_lcomp c)
in (not (_52_13340)))
end))))
in (_52_13342 && _52_13341)))
in (let cres = (match (refine_with_equality) with
| true -> begin
(let _52_13343 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app_flat (head, (Support.List.rev arg_rets)) (Some (cres.Microsoft_FStar_Absyn_Syntax.res_typ)) top.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Tc_Util.maybe_assume_result_eq_pure_term env _52_13343 cres))
end
| false -> begin
(let _36_1802 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _52_13346 = (Microsoft_FStar_Absyn_Print.exp_to_string head)
in (let _52_13345 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string cres)
in (let _52_13344 = (Microsoft_FStar_Tc_Rel.guard_to_string env g)
in (Support.Microsoft.FStar.Util.fprint3 "Not refining result: f=%s; cres=%s; guard=%s\n" _52_13346 _52_13345 _52_13344))))
end
| false -> begin
()
end)
in cres)
end)
in (let _52_13347 = (Microsoft_FStar_Tc_Util.refresh_comp_label env false cres)
in (_52_13347, g))))))
end
| _ -> begin
(let g = (let _52_13348 = (Microsoft_FStar_Tc_Rel.conj_guard g_head g)
in (Support.Prims.pipe_right _52_13348 (Microsoft_FStar_Tc_Rel.solve_deferred_constraints env)))
in (let _52_13354 = (let _52_13353 = (let _52_13352 = (let _52_13351 = (let _52_13350 = (let _52_13349 = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp cres ())
in (bs, _52_13349))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _52_13350 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) top.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Util.subst_typ subst) _52_13351))
in (Microsoft_FStar_Absyn_Syntax.mk_Total _52_13352))
in (Support.Prims.pipe_left Microsoft_FStar_Tc_Util.lcomp_of_comp _52_13353))
in (_52_13354, g)))
end)
in (match (_36_1810) with
| (cres, g) -> begin
(let _36_1811 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _52_13355 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string cres)
in (Support.Microsoft.FStar.Util.fprint1 "\t Type of result cres is %s\n" _52_13355))
end
| false -> begin
()
end)
in (let comp = (Support.List.fold_left (fun ( out  :  Microsoft_FStar_Absyn_Syntax.lcomp ) ( c  :  (Microsoft_FStar_Tc_Env.binding option * Microsoft_FStar_Absyn_Syntax.lcomp) ) -> (Microsoft_FStar_Tc_Util.bind env None (Support.Prims.snd c) ((Support.Prims.fst c), out))) cres comps)
in (let comp = (Microsoft_FStar_Tc_Util.bind env None chead (None, comp))
in (let app = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app_flat (head, (Support.List.rev outargs)) (Some (comp.Microsoft_FStar_Absyn_Syntax.res_typ)) top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _36_1820 = (Microsoft_FStar_Tc_Util.strengthen_precondition None env app comp g)
in (match (_36_1820) with
| (comp, g) -> begin
(let _36_1821 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _52_13361 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env app)
in (let _52_13360 = (let _52_13359 = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp comp ())
in (Microsoft_FStar_Absyn_Print.comp_typ_to_string _52_13359))
in (Support.Microsoft.FStar.Util.fprint2 "\t Type of app term %s is %s\n" _52_13361 _52_13360)))
end
| false -> begin
()
end)
in (app, comp, g))
end))))))
end)))
end
| ([], arg::_) -> begin
(let rec aux = (fun ( norm  :  bool ) ( tres  :  (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let tres = (let _52_13366 = (Microsoft_FStar_Absyn_Util.compress_typ tres)
in (Support.Prims.pipe_right _52_13366 Microsoft_FStar_Absyn_Util.unrefine))
in (match (tres.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, cres')) -> begin
(let _36_1837 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _52_13367 = (Support.Microsoft.FStar.Range.string_of_range tres.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Microsoft.FStar.Util.fprint1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _52_13367))
end
| false -> begin
()
end)
in (let _52_13372 = (Microsoft_FStar_Tc_Util.lcomp_of_comp cres')
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs _52_13372 args)))
end
| _ when (not (norm)) -> begin
(let _52_13373 = (whnf env tres)
in (aux true _52_13373))
end
| _ -> begin
(let _52_13379 = (let _52_13378 = (let _52_13377 = (let _52_13375 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env tf)
in (let _52_13374 = (Microsoft_FStar_Absyn_Print.exp_to_string top)
in (Support.Microsoft.FStar.Util.format2 "Too many arguments to function of type %s; got %s" _52_13375 _52_13374)))
in (let _52_13376 = (Microsoft_FStar_Absyn_Syntax.argpos arg)
in (_52_13377, _52_13376)))
in Microsoft_FStar_Absyn_Syntax.Error (_52_13378))
in (raise (_52_13379)))
end)))
in (aux false cres.Microsoft_FStar_Absyn_Syntax.res_typ))
end)
end))
in (let _52_13380 = (Microsoft_FStar_Tc_Util.lcomp_of_comp c)
in (tc_args ([], [], [], [], Microsoft_FStar_Tc_Rel.trivial_guard, Microsoft_FStar_Absyn_Syntax.no_fvs.Microsoft_FStar_Absyn_Syntax.fxvs) bs _52_13380 args))))
end
| _ -> begin
(match ((not (norm))) with
| true -> begin
(let _52_13381 = (whnf env tf)
in (check_function_app true _52_13381))
end
| false -> begin
(let _52_13384 = (let _52_13383 = (let _52_13382 = (Microsoft_FStar_Tc_Errors.expected_function_typ env tf)
in (_52_13382, head.Microsoft_FStar_Absyn_Syntax.pos))
in Microsoft_FStar_Absyn_Syntax.Error (_52_13383))
in (raise (_52_13384)))
end)
end))
in (let _52_13385 = (Microsoft_FStar_Absyn_Util.unrefine thead)
in (check_function_app false _52_13385)))))
end))
end))
in (let _36_1848 = (aux ())
in (match (_36_1848) with
| (e, c, g) -> begin
(let _36_1849 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Implicits")))) with
| true -> begin
(let _52_13386 = (Support.Prims.pipe_left Support.Microsoft.FStar.Util.string_of_int (Support.List.length g.Microsoft_FStar_Tc_Rel.implicits))
in (Support.Microsoft.FStar.Util.fprint1 "Introduced %s implicits in application\n" _52_13386))
end
| false -> begin
()
end)
in (let c = (match ((let _52_13391 = (let _52_13389 = (Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)
in (let _52_13388 = (let _52_13387 = (Microsoft_FStar_Absyn_Util.is_lcomp_partial_return c)
in (not (_52_13387)))
in (_52_13389 && _52_13388)))
in (let _52_13390 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_lcomp c)
in (_52_13391 && _52_13390)))) with
| true -> begin
(Microsoft_FStar_Tc_Util.maybe_assume_result_eq_pure_term env e c)
end
| false -> begin
c
end)
in (let _36_1856 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _52_13396 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_13395 = (Microsoft_FStar_Absyn_Print.typ_to_string c.Microsoft_FStar_Absyn_Syntax.res_typ)
in (let _52_13394 = (let _52_13393 = (Microsoft_FStar_Tc_Env.expected_typ env0)
in (Support.Prims.pipe_right _52_13393 (fun ( x  :  Microsoft_FStar_Absyn_Syntax.typ option ) -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(Microsoft_FStar_Absyn_Print.typ_to_string t)
end))))
in (Support.Microsoft.FStar.Util.fprint3 "(%s) About to check %s against expected typ %s\n" _52_13396 _52_13395 _52_13394))))
end
| false -> begin
()
end)
in (let _36_1861 = (comp_check_expected_typ env0 e c)
in (match (_36_1861) with
| (e, c, g') -> begin
(let _52_13397 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (e, c, _52_13397))
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
in (let _52_13398 = (Microsoft_FStar_Tc_Env.set_expected_typ env res_t)
in (_52_13398, res_t)))
end)
in (match (_36_1880) with
| (env_branches, res_t) -> begin
(let guard_x = (let _52_13400 = (Support.Prims.pipe_left (fun ( _52_13399  :  Support.Microsoft.FStar.Range.range ) -> Some (_52_13399)) e1.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Util.new_bvd _52_13400))
in (let t_eqns = (Support.Prims.pipe_right eqns (Support.List.map (tc_eqn guard_x c1.Microsoft_FStar_Absyn_Syntax.res_typ env_branches)))
in (let _36_1897 = (let _36_1894 = (Support.List.fold_right (fun ( _36_1888  :  ((Microsoft_FStar_Absyn_Syntax.pat * Microsoft_FStar_Absyn_Syntax.exp option * Microsoft_FStar_Absyn_Syntax.exp) * Microsoft_FStar_Absyn_Syntax.typ * Microsoft_FStar_Absyn_Syntax.lcomp * Microsoft_FStar_Tc_Rel.guard_t) ) ( _36_1891  :  ((Microsoft_FStar_Absyn_Syntax.typ * Microsoft_FStar_Absyn_Syntax.lcomp) list * Microsoft_FStar_Tc_Rel.guard_t) ) -> (match ((_36_1888, _36_1891)) with
| ((_, f, c, g), (caccum, gaccum)) -> begin
(let _52_13403 = (Microsoft_FStar_Tc_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _52_13403))
end)) t_eqns ([], Microsoft_FStar_Tc_Rel.trivial_guard))
in (match (_36_1894) with
| (cases, g) -> begin
(let _52_13404 = (Microsoft_FStar_Tc_Util.bind_cases env res_t cases)
in (_52_13404, g))
end))
in (match (_36_1897) with
| (c_branches, g_branches) -> begin
(let _36_1898 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _52_13408 = (Support.Microsoft.FStar.Range.string_of_range top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_13407 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string c1)
in (let _52_13406 = (Microsoft_FStar_Absyn_Print.lcomp_typ_to_string c_branches)
in (let _52_13405 = (Microsoft_FStar_Tc_Rel.guard_to_string env g_branches)
in (Support.Microsoft.FStar.Util.fprint4 "(%s) comp\n\tscrutinee: %s\n\tbranches: %s\nguard = %s\n" _52_13408 _52_13407 _52_13406 _52_13405)))))
end
| false -> begin
()
end)
in (let cres = (let _52_13411 = (let _52_13410 = (Support.Prims.pipe_left (fun ( _52_13409  :  Microsoft_FStar_Tc_Env.binding ) -> Some (_52_13409)) (Microsoft_FStar_Tc_Env.Binding_var ((guard_x, c1.Microsoft_FStar_Absyn_Syntax.res_typ))))
in (_52_13410, c_branches))
in (Microsoft_FStar_Tc_Util.bind env (Some (e1)) c1 _52_13411))
in (let e = (let _52_13418 = (w cres)
in (let _52_13417 = (let _52_13416 = (let _52_13415 = (Support.List.map (fun ( _36_1908  :  ((Microsoft_FStar_Absyn_Syntax.pat * Microsoft_FStar_Absyn_Syntax.exp option * Microsoft_FStar_Absyn_Syntax.exp) * Microsoft_FStar_Absyn_Syntax.typ * Microsoft_FStar_Absyn_Syntax.lcomp * Microsoft_FStar_Tc_Rel.guard_t) ) -> (match (_36_1908) with
| (f, _, _, _) -> begin
f
end)) t_eqns)
in (e1, _52_13415))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_match _52_13416))
in (Support.Prims.pipe_left _52_13418 _52_13417)))
in (let _52_13420 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed (e, cres.Microsoft_FStar_Absyn_Syntax.res_typ, Some (cres.Microsoft_FStar_Absyn_Syntax.eff_name)) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_13419 = (Microsoft_FStar_Tc_Rel.conj_guard g1 g_branches)
in (_52_13420, cres, _52_13419))))))
end))))
end))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((false, {Microsoft_FStar_Absyn_Syntax.lbname = x; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = e1}::[]), e2)) -> begin
(let env = (instantiate_both env)
in (let env0 = env
in (let topt = (Microsoft_FStar_Tc_Env.expected_typ env)
in (let top_level = (match (x) with
| Support.Microsoft.FStar.Util.Inr (_) -> begin
true
end
| _ -> begin
false
end)
in (let _36_1934 = (Microsoft_FStar_Tc_Env.clear_expected_typ env)
in (match (_36_1934) with
| (env1, _) -> begin
(let _36_1947 = (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(Microsoft_FStar_Tc_Rel.trivial_guard, env1)
end
| _ -> begin
(match ((top_level && (not (env.Microsoft_FStar_Tc_Env.generalize)))) with
| true -> begin
(let _52_13421 = (Microsoft_FStar_Tc_Env.set_expected_typ env1 t)
in (Microsoft_FStar_Tc_Rel.trivial_guard, _52_13421))
end
| false -> begin
(let _36_1940 = (tc_typ_check env1 t Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_36_1940) with
| (t, f) -> begin
(let _36_1941 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _52_13423 = (Support.Microsoft.FStar.Range.string_of_range top.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_13422 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint2 "(%s) Checked type annotation %s\n" _52_13423 _52_13422)))
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
(let _36_1957 = (let _52_13427 = (Microsoft_FStar_Tc_Env.set_range env t.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Tc_Util.strengthen_precondition (Some ((fun ( _36_1954  :  unit ) -> (match (()) with
| () -> begin
Microsoft_FStar_Tc_Errors.ill_kinded_type
end)))) _52_13427 e1 c1 f))
in (match (_36_1957) with
| (c1, guard_f) -> begin
(match (x) with
| Support.Microsoft.FStar.Util.Inr (_) -> begin
(let _36_1970 = (match ((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
(let _36_1963 = (let _52_13428 = (Microsoft_FStar_Tc_Rel.conj_guard g1 guard_f)
in (Microsoft_FStar_Tc_Util.check_top_level env _52_13428 c1))
in (match (_36_1963) with
| (ok, c1) -> begin
(match (ok) with
| true -> begin
(e2, c1)
end
| false -> begin
(let _36_1964 = (match ((Support.ST.read Microsoft_FStar_Options.warn_top_level_effects)) with
| true -> begin
(let _52_13429 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Tc_Errors.warn _52_13429 Microsoft_FStar_Tc_Errors.top_level_effect))
end
| false -> begin
()
end)
in (let _52_13430 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e2, Microsoft_FStar_Absyn_Syntax.MaskedEffect))))
in (_52_13430, c1)))
end)
end))
end
| false -> begin
(let _36_1966 = (let _52_13431 = (Microsoft_FStar_Tc_Rel.conj_guard g1 guard_f)
in (Microsoft_FStar_Tc_Util.discharge_guard env _52_13431))
in (let _52_13432 = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp c1 ())
in (e2, _52_13432)))
end)
in (match (_36_1970) with
| (e2, c1) -> begin
(let _36_1975 = (match (env.Microsoft_FStar_Tc_Env.generalize) with
| true -> begin
(let _52_13433 = (Microsoft_FStar_Tc_Util.generalize false env1 (((x, e1, c1))::[]))
in (Support.Prims.pipe_left Support.List.hd _52_13433))
end
| false -> begin
(x, e1, c1)
end)
in (match (_36_1975) with
| (_, e1, c1) -> begin
(let cres = (let _52_13434 = (Microsoft_FStar_Absyn_Util.ml_comp Microsoft_FStar_Tc_Recheck.t_unit top.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Prims.pipe_left Microsoft_FStar_Tc_Util.lcomp_of_comp _52_13434))
in (let cres = (match ((Microsoft_FStar_Absyn_Util.is_total_comp c1)) with
| true -> begin
cres
end
| false -> begin
(let _52_13435 = (Microsoft_FStar_Tc_Util.lcomp_of_comp c1)
in (Microsoft_FStar_Tc_Util.bind env None _52_13435 (None, cres)))
end)
in (let _36_1978 = (Support.ST.op_Colon_Equals e2.Microsoft_FStar_Absyn_Syntax.tk (Some (Microsoft_FStar_Tc_Recheck.t_unit)))
in (let _52_13444 = (let _52_13443 = (w cres)
in (let _52_13442 = (let _52_13441 = (let _52_13440 = (let _52_13439 = (let _52_13438 = (Microsoft_FStar_Absyn_Syntax.mk_lb (x, (Microsoft_FStar_Absyn_Util.comp_effect_name c1), (Microsoft_FStar_Absyn_Util.comp_result c1), e1))
in (_52_13438)::[])
in (false, _52_13439))
in (_52_13440, e2))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_let _52_13441))
in (Support.Prims.pipe_left _52_13443 _52_13442)))
in (_52_13444, cres, Microsoft_FStar_Tc_Rel.trivial_guard)))))
end))
end))
end
| Support.Microsoft.FStar.Util.Inl (bvd) -> begin
(let b = (binding_of_lb x c1.Microsoft_FStar_Absyn_Syntax.res_typ)
in (let _36_1986 = (let _52_13445 = (Microsoft_FStar_Tc_Env.push_local_binding env b)
in (tc_exp _52_13445 e2))
in (match (_36_1986) with
| (e2, c2, g2) -> begin
(let cres = (Microsoft_FStar_Tc_Util.bind env (Some (e1)) c1 (Some (b), c2))
in (let e = (let _52_13453 = (w cres)
in (let _52_13452 = (let _52_13451 = (let _52_13450 = (let _52_13449 = (let _52_13448 = (Microsoft_FStar_Absyn_Syntax.mk_lb (x, c1.Microsoft_FStar_Absyn_Syntax.eff_name, c1.Microsoft_FStar_Absyn_Syntax.res_typ, e1))
in (_52_13448)::[])
in (false, _52_13449))
in (_52_13450, e2))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_let _52_13451))
in (Support.Prims.pipe_left _52_13453 _52_13452)))
in (let g2 = (let _52_13462 = (let _52_13455 = (let _52_13454 = (Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s bvd c1.Microsoft_FStar_Absyn_Syntax.res_typ))
in (_52_13454)::[])
in (Microsoft_FStar_Tc_Rel.close_guard _52_13455))
in (let _52_13461 = (let _52_13460 = (let _52_13459 = (let _52_13458 = (let _52_13457 = (Microsoft_FStar_Absyn_Util.bvd_to_exp bvd c1.Microsoft_FStar_Absyn_Syntax.res_typ)
in (Microsoft_FStar_Absyn_Util.mk_eq c1.Microsoft_FStar_Absyn_Syntax.res_typ c1.Microsoft_FStar_Absyn_Syntax.res_typ _52_13457 e1))
in (Support.Prims.pipe_left (fun ( _52_13456  :  Microsoft_FStar_Absyn_Syntax.formula ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_52_13456)) _52_13458))
in (Microsoft_FStar_Tc_Rel.guard_of_guard_formula _52_13459))
in (Microsoft_FStar_Tc_Rel.imp_guard _52_13460 g2))
in (Support.Prims.pipe_left _52_13462 _52_13461)))
in (let guard = (let _52_13463 = (Microsoft_FStar_Tc_Rel.conj_guard g1 g2)
in (Microsoft_FStar_Tc_Rel.conj_guard guard_f _52_13463))
in (match (topt) with
| None -> begin
(let tres = cres.Microsoft_FStar_Absyn_Syntax.res_typ
in (let fvs = (Microsoft_FStar_Absyn_Util.freevars_typ tres)
in (match ((Support.Microsoft.FStar.Util.set_mem (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s bvd t) fvs.Microsoft_FStar_Absyn_Syntax.fxvs)) with
| true -> begin
(let t = (Microsoft_FStar_Tc_Util.new_tvar env0 Microsoft_FStar_Absyn_Syntax.ktype)
in (let _36_1995 = (let _52_13464 = (Microsoft_FStar_Tc_Rel.teq env tres t)
in (Support.Prims.pipe_left (Microsoft_FStar_Tc_Rel.try_discharge_guard env) _52_13464))
in (e, cres, guard)))
end
| false -> begin
(e, cres, guard)
end)))
end
| _ -> begin
(e, cres, guard)
end)))))
end)))
end)
end))
end))
end))
end))))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((false, _), _)) -> begin
(failwith ("impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((true, lbs), e1)) -> begin
(let env = (instantiate_both env)
in (let _36_2016 = (Microsoft_FStar_Tc_Env.clear_expected_typ env)
in (match (_36_2016) with
| (env0, topt) -> begin
(let is_inner_let = (Support.Prims.pipe_right lbs (Support.Microsoft.FStar.Util.for_some (fun ( _36_9  :  Microsoft_FStar_Absyn_Syntax.letbinding ) -> (match (_36_9) with
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inl (_); Microsoft_FStar_Absyn_Syntax.lbtyp = _; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = _} -> begin
true
end
| _ -> begin
false
end))))
in (let _36_2056 = (Support.Prims.pipe_right lbs (Support.List.fold_left (fun ( _36_2033  :  ((Microsoft_FStar_Absyn_Syntax.lbname * Microsoft_FStar_Absyn_Syntax.typ * (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) list * Microsoft_FStar_Tc_Env.env) ) ( _36_2039  :  Microsoft_FStar_Absyn_Syntax.letbinding ) -> (match ((_36_2033, _36_2039)) with
| ((xts, env), {Microsoft_FStar_Absyn_Syntax.lbname = x; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = e}) -> begin
(let _36_2044 = (Microsoft_FStar_Tc_Util.extract_lb_annotation env t e)
in (match (_36_2044) with
| (_, t, check_t) -> begin
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
(let _52_13468 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint1 "Type %s is marked as no-generalize\n" _52_13468))
end
| false -> begin
()
end)
in t)
end
| false -> begin
(let _52_13469 = (tc_typ_check_trivial (let _36_2048 = env0
in {Microsoft_FStar_Tc_Env.solver = _36_2048.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_2048.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_2048.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_2048.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_2048.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_2048.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_2048.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_2048.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_2048.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _36_2048.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _36_2048.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _36_2048.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_2048.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _36_2048.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _36_2048.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = true; Microsoft_FStar_Tc_Env.use_eq = _36_2048.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = _36_2048.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_2048.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_2048.Microsoft_FStar_Tc_Env.default_effects}) t Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_right _52_13469 (norm_t env)))
end)
end)
in (let env = (match ((let _52_13471 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t)
in (let _52_13470 = (Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)
in (_52_13471 && _52_13470)))) with
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
(let _36_2071 = (let _52_13477 = (let _52_13476 = (Support.Prims.pipe_right lbs Support.List.rev)
in (Support.Prims.pipe_right _52_13476 (Support.List.map (fun ( _36_2060  :  (Microsoft_FStar_Absyn_Syntax.lbname * Microsoft_FStar_Absyn_Syntax.typ * (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) ) -> (match (_36_2060) with
| (x, t, e) -> begin
(let t = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env t)
in (let _36_2062 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _52_13475 = (Microsoft_FStar_Absyn_Print.lbname_to_string x)
in (let _52_13474 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _52_13473 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint3 "Checking %s = %s against type %s\n" _52_13475 _52_13474 _52_13473))))
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
in (Support.Prims.pipe_right _52_13477 Support.List.unzip))
in (match (_36_2071) with
| (lbs, gs) -> begin
(let g_lbs = (Support.List.fold_right Microsoft_FStar_Tc_Rel.conj_guard gs Microsoft_FStar_Tc_Rel.trivial_guard)
in (let _36_2090 = (match (((not (env.Microsoft_FStar_Tc_Env.generalize)) || is_inner_let)) with
| true -> begin
(let _52_13479 = (Support.List.map (fun ( _36_2076  :  (Microsoft_FStar_Absyn_Syntax.lbname * Microsoft_FStar_Absyn_Syntax.typ * Microsoft_FStar_Absyn_Syntax.exp) ) -> (match (_36_2076) with
| (x, t, e) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_lb (x, Microsoft_FStar_Absyn_Const.effect_Tot_lid, t, e))
end)) lbs)
in (_52_13479, g_lbs))
end
| false -> begin
(let _36_2077 = (Microsoft_FStar_Tc_Util.discharge_guard env g_lbs)
in (let ecs = (let _52_13483 = (Support.Prims.pipe_right lbs (Support.List.map (fun ( _36_2082  :  (((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, Microsoft_FStar_Absyn_Syntax.lident) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.typ * Microsoft_FStar_Absyn_Syntax.exp) ) -> (match (_36_2082) with
| (x, t, e) -> begin
(let _52_13482 = (let _52_13481 = (Microsoft_FStar_Absyn_Util.range_of_lb (x, t, e))
in (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Util.total_comp t) _52_13481))
in (x, e, _52_13482))
end))))
in (Microsoft_FStar_Tc_Util.generalize true env _52_13483))
in (let _52_13485 = (Support.List.map (fun ( _36_2087  :  (Microsoft_FStar_Absyn_Syntax.lbname * Microsoft_FStar_Absyn_Syntax.exp * (Microsoft_FStar_Absyn_Syntax.comp', unit) Microsoft_FStar_Absyn_Syntax.syntax) ) -> (match (_36_2087) with
| (x, e, c) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_lb (x, Microsoft_FStar_Absyn_Const.effect_Tot_lid, (Microsoft_FStar_Absyn_Util.comp_result c), e))
end)) ecs)
in (_52_13485, Microsoft_FStar_Tc_Rel.trivial_guard))))
end)
in (match (_36_2090) with
| (lbs, g_lbs) -> begin
(match ((not (is_inner_let))) with
| true -> begin
(let cres = (let _52_13486 = (Microsoft_FStar_Absyn_Util.total_comp Microsoft_FStar_Tc_Recheck.t_unit top.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Prims.pipe_left Microsoft_FStar_Tc_Util.lcomp_of_comp _52_13486))
in (let _36_2092 = (Microsoft_FStar_Tc_Util.discharge_guard env g_lbs)
in (let _36_2094 = (Support.ST.op_Colon_Equals e1.Microsoft_FStar_Absyn_Syntax.tk (Some (Microsoft_FStar_Tc_Recheck.t_unit)))
in (let _52_13490 = (let _52_13489 = (w cres)
in (Support.Prims.pipe_left _52_13489 (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((true, lbs), e1))))
in (_52_13490, cres, Microsoft_FStar_Tc_Rel.trivial_guard)))))
end
| false -> begin
(let _36_2110 = (Support.Prims.pipe_right lbs (Support.List.fold_left (fun ( _36_2098  :  (Microsoft_FStar_Tc_Env.binding list * Microsoft_FStar_Tc_Env.env) ) ( _36_2105  :  Microsoft_FStar_Absyn_Syntax.letbinding ) -> (match ((_36_2098, _36_2105)) with
| ((bindings, env), {Microsoft_FStar_Absyn_Syntax.lbname = x; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = _}) -> begin
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
in (let e = (let _52_13495 = (w cres)
in (Support.Prims.pipe_left _52_13495 (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((true, lbs), e1))))
in (match (topt) with
| Some (_) -> begin
(e, cres, guard)
end
| None -> begin
(let fvs = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Util.freevars_typ tres)
in (match ((Support.Prims.pipe_right lbs (Support.List.tryFind (fun ( _36_10  :  Microsoft_FStar_Absyn_Syntax.letbinding ) -> (match (_36_10) with
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (_); Microsoft_FStar_Absyn_Syntax.lbtyp = _; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = _} -> begin
false
end
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inl (x); Microsoft_FStar_Absyn_Syntax.lbtyp = _; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = _} -> begin
(Support.Microsoft.FStar.Util.set_mem (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x Microsoft_FStar_Absyn_Syntax.tun) fvs.Microsoft_FStar_Absyn_Syntax.fxvs)
end))))) with
| Some ({Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inl (y); Microsoft_FStar_Absyn_Syntax.lbtyp = _; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = _}) -> begin
(let t' = (Microsoft_FStar_Tc_Util.new_tvar env0 Microsoft_FStar_Absyn_Syntax.ktype)
in (let _36_2158 = (let _52_13497 = (Microsoft_FStar_Tc_Rel.teq env tres t')
in (Support.Prims.pipe_left (Microsoft_FStar_Tc_Rel.try_discharge_guard env) _52_13497))
in (e, cres, guard)))
end
| _ -> begin
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
and tc_eqn = (fun ( scrutinee_x  :  Microsoft_FStar_Absyn_Syntax.bvvdef ) ( pat_t  :  Microsoft_FStar_Absyn_Syntax.typ ) ( env  :  Microsoft_FStar_Tc_Env.env ) ( _36_2168  :  (Microsoft_FStar_Absyn_Syntax.pat * Microsoft_FStar_Absyn_Syntax.exp option * Microsoft_FStar_Absyn_Syntax.exp) ) -> (match (_36_2168) with
| (pattern, when_clause, branch) -> begin
(let tc_pat = (fun ( allow_implicits  :  bool ) ( pat_t  :  Microsoft_FStar_Absyn_Syntax.typ ) ( p0  :  Microsoft_FStar_Absyn_Syntax.pat ) -> (let _36_2176 = (Microsoft_FStar_Tc_Util.pat_as_exps allow_implicits env p0)
in (match (_36_2176) with
| (bindings, exps, p) -> begin
(let pat_env = (Support.List.fold_left Microsoft_FStar_Tc_Env.push_local_binding env bindings)
in (let _36_2185 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Pat")))) with
| true -> begin
(Support.Prims.pipe_right bindings (Support.List.iter (fun ( _36_11  :  Microsoft_FStar_Tc_Env.binding ) -> (match (_36_11) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, t)) -> begin
(let _52_13510 = (Microsoft_FStar_Absyn_Print.strBvd x)
in (let _52_13509 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (Support.Microsoft.FStar.Util.fprint2 "Before tc ... pattern var %s  : %s\n" _52_13510 _52_13509)))
end
| _ -> begin
()
end))))
end
| false -> begin
()
end)
in (let _36_2190 = (Microsoft_FStar_Tc_Env.clear_expected_typ pat_env)
in (match (_36_2190) with
| (env1, _) -> begin
(let env1 = (let _36_2191 = env1
in {Microsoft_FStar_Tc_Env.solver = _36_2191.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_2191.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_2191.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_2191.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_2191.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_2191.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_2191.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_2191.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = true; Microsoft_FStar_Tc_Env.instantiate_targs = _36_2191.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _36_2191.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _36_2191.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_2191.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _36_2191.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _36_2191.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_2191.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = _36_2191.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = _36_2191.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_2191.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_2191.Microsoft_FStar_Tc_Env.default_effects})
in (let expected_pat_t = (Microsoft_FStar_Tc_Rel.unrefine env pat_t)
in (let exps = (Support.Prims.pipe_right exps (Support.List.map (fun ( e  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let _36_2196 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _52_13513 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _52_13512 = (Microsoft_FStar_Absyn_Print.typ_to_string pat_t)
in (Support.Microsoft.FStar.Util.fprint2 "Checking pattern expression %s against expected type %s\n" _52_13513 _52_13512)))
end
| false -> begin
()
end)
in (let _36_2201 = (tc_exp env1 e)
in (match (_36_2201) with
| (e, lc, g) -> begin
(let _36_2202 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _52_13515 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env e)
in (let _52_13514 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env lc.Microsoft_FStar_Absyn_Syntax.res_typ)
in (Support.Microsoft.FStar.Util.fprint2 "Pre-checked pattern expression %s at type %s\n" _52_13515 _52_13514)))
end
| false -> begin
()
end)
in (let g' = (Microsoft_FStar_Tc_Rel.teq env lc.Microsoft_FStar_Absyn_Syntax.res_typ expected_pat_t)
in (let g = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (let _36_2206 = (let _52_13516 = (Microsoft_FStar_Tc_Rel.solve_deferred_constraints env g)
in (Support.Prims.pipe_left Support.Prims.ignore _52_13516))
in (let e' = (Microsoft_FStar_Tc_Normalize.norm_exp ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env e)
in (let _36_2209 = (match ((let _52_13519 = (let _52_13518 = (Microsoft_FStar_Absyn_Util.uvars_in_exp e')
in (let _52_13517 = (Microsoft_FStar_Absyn_Util.uvars_in_typ expected_pat_t)
in (Microsoft_FStar_Absyn_Util.uvars_included_in _52_13518 _52_13517)))
in (Support.Prims.pipe_left Support.Prims.op_Negation _52_13519))) with
| true -> begin
(let _52_13524 = (let _52_13523 = (let _52_13522 = (let _52_13521 = (Microsoft_FStar_Absyn_Print.exp_to_string e')
in (let _52_13520 = (Microsoft_FStar_Absyn_Print.typ_to_string expected_pat_t)
in (Support.Microsoft.FStar.Util.format2 "Implicit pattern variables in %s could not be resolved against expected type %s; please bind them explicitly" _52_13521 _52_13520)))
in (_52_13522, p.Microsoft_FStar_Absyn_Syntax.p))
in Microsoft_FStar_Absyn_Syntax.Error (_52_13523))
in (raise (_52_13524)))
end
| false -> begin
()
end)
in (let _36_2211 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _52_13525 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env e)
in (Support.Microsoft.FStar.Util.fprint1 "Done checking pattern expression %s\n" _52_13525))
end
| false -> begin
()
end)
in e)))))))
end))))))
in (let p = (Microsoft_FStar_Tc_Util.decorate_pattern env p exps)
in (let _36_2222 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Pat")))) with
| true -> begin
(Support.Prims.pipe_right bindings (Support.List.iter (fun ( _36_12  :  Microsoft_FStar_Tc_Env.binding ) -> (match (_36_12) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, t)) -> begin
(let _52_13528 = (Microsoft_FStar_Absyn_Print.strBvd x)
in (let _52_13527 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.fprint2 "Pattern var %s  : %s\n" _52_13528 _52_13527)))
end
| _ -> begin
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
(let _36_2236 = (let _52_13529 = (Microsoft_FStar_Tc_Env.set_expected_typ pat_env Microsoft_FStar_Tc_Recheck.t_bool)
in (tc_exp _52_13529 e))
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
(let _52_13531 = (Microsoft_FStar_Absyn_Util.mk_eq Microsoft_FStar_Absyn_Util.t_bool Microsoft_FStar_Absyn_Util.t_bool w Microsoft_FStar_Absyn_Const.exp_true_bool)
in (Support.Prims.pipe_left (fun ( _52_13530  :  Microsoft_FStar_Absyn_Syntax.typ ) -> Some (_52_13530)) _52_13531))
end)
in (let _36_2247 = (tc_exp pat_env branch)
in (match (_36_2247) with
| (branch, c, g_branch) -> begin
(let scrutinee = (Microsoft_FStar_Absyn_Util.bvd_to_exp scrutinee_x pat_t)
in (let _36_2252 = (let _52_13532 = (Microsoft_FStar_Tc_Env.push_local_binding env (Microsoft_FStar_Tc_Env.Binding_var ((scrutinee_x, pat_t))))
in (Support.Prims.pipe_right _52_13532 Microsoft_FStar_Tc_Env.clear_expected_typ))
in (match (_36_2252) with
| (scrutinee_env, _) -> begin
(let c = (let eqs = (Support.Prims.pipe_right disj_exps (Support.List.fold_left (fun ( fopt  :  Microsoft_FStar_Absyn_Syntax.typ option ) ( e  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let e = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
fopt
end
| _ -> begin
(let clause = (let _52_13536 = (Microsoft_FStar_Tc_Recheck.recompute_typ scrutinee)
in (let _52_13535 = (Microsoft_FStar_Tc_Recheck.recompute_typ e)
in (Microsoft_FStar_Absyn_Util.mk_eq _52_13536 _52_13535 scrutinee e)))
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _52_13538 = (Microsoft_FStar_Absyn_Util.mk_disj clause f)
in (Support.Prims.pipe_left (fun ( _52_13537  :  Microsoft_FStar_Absyn_Syntax.typ ) -> Some (_52_13537)) _52_13538))
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
(let _52_13541 = (let _52_13540 = (Microsoft_FStar_Absyn_Util.mk_conj f w)
in (Support.Prims.pipe_left (fun ( _52_13539  :  Microsoft_FStar_Absyn_Syntax.formula ) -> Microsoft_FStar_Tc_Rel.NonTrivial (_52_13539)) _52_13540))
in (Microsoft_FStar_Tc_Util.weaken_precondition env c _52_13541))
end
| (None, Some (w)) -> begin
(Microsoft_FStar_Tc_Util.weaken_precondition env c (Microsoft_FStar_Tc_Rel.NonTrivial (w)))
end)
in (Microsoft_FStar_Tc_Util.close_comp env bindings c)))
in (let discriminate = (fun ( scrutinee  :  Microsoft_FStar_Absyn_Syntax.exp ) ( f  :  (Microsoft_FStar_Absyn_Syntax.l__LongIdent, (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t ) -> (let disc = (let _52_13548 = (let _52_13546 = (Microsoft_FStar_Absyn_Util.mk_discriminator f.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Util.fvar None _52_13546))
in (let _52_13547 = (Microsoft_FStar_Absyn_Syntax.range_of_lid f.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Prims.pipe_left _52_13548 _52_13547)))
in (let disc = (let _52_13551 = (let _52_13550 = (let _52_13549 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.varg scrutinee)
in (_52_13549)::[])
in (disc, _52_13550))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _52_13551 None scrutinee.Microsoft_FStar_Absyn_Syntax.pos))
in (Microsoft_FStar_Absyn_Util.mk_eq Microsoft_FStar_Absyn_Util.t_bool Microsoft_FStar_Absyn_Util.t_bool disc Microsoft_FStar_Absyn_Const.exp_true_bool))))
in (let rec mk_guard = (fun ( scrutinee  :  Microsoft_FStar_Absyn_Syntax.exp ) ( pat_exp  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let pat_exp = (Microsoft_FStar_Absyn_Util.compress_exp pat_exp)
in (match (pat_exp.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) | (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_constant (Microsoft_FStar_Absyn_Syntax.Const_unit)) -> begin
(Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (_) -> begin
(let _52_13560 = (let _52_13559 = (let _52_13558 = (Microsoft_FStar_Absyn_Syntax.varg scrutinee)
in (let _52_13557 = (let _52_13556 = (Microsoft_FStar_Absyn_Syntax.varg pat_exp)
in (_52_13556)::[])
in (_52_13558)::_52_13557))
in (Microsoft_FStar_Absyn_Util.teq, _52_13559))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_13560 None scrutinee.Microsoft_FStar_Absyn_Syntax.pos))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((f, _)) -> begin
(discriminate scrutinee f)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((f, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args)) -> begin
(let head = (discriminate scrutinee f)
in (let sub_term_guards = (let _52_13568 = (Support.Prims.pipe_right args (Support.List.mapi (fun ( i  :  int ) ( arg  :  (((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax, (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match ((Support.Prims.fst arg)) with
| Support.Microsoft.FStar.Util.Inl (_) -> begin
[]
end
| Support.Microsoft.FStar.Util.Inr (ei) -> begin
(let projector = (Microsoft_FStar_Tc_Env.lookup_projector env f.Microsoft_FStar_Absyn_Syntax.v i)
in (let sub_term = (let _52_13566 = (let _52_13565 = (Microsoft_FStar_Absyn_Util.fvar None projector f.Microsoft_FStar_Absyn_Syntax.p)
in (let _52_13564 = (let _52_13563 = (Microsoft_FStar_Absyn_Syntax.varg scrutinee)
in (_52_13563)::[])
in (_52_13565, _52_13564)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app _52_13566 None f.Microsoft_FStar_Absyn_Syntax.p))
in (let _52_13567 = (mk_guard sub_term ei)
in (_52_13567)::[])))
end))))
in (Support.Prims.pipe_right _52_13568 Support.List.flatten))
in (Microsoft_FStar_Absyn_Util.mk_conj_l ((head)::sub_term_guards))))
end
| _ -> begin
(let _52_13571 = (let _52_13570 = (Support.Microsoft.FStar.Range.string_of_range pat_exp.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_13569 = (Microsoft_FStar_Absyn_Print.exp_to_string pat_exp)
in (Support.Microsoft.FStar.Util.format2 "tc_eqn: Impossible (%s) %s" _52_13570 _52_13569)))
in (failwith (_52_13571)))
end)))
in (let mk_guard = (fun ( s  :  Microsoft_FStar_Absyn_Syntax.exp ) ( tsc  :  Microsoft_FStar_Absyn_Syntax.typ ) ( pat  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (match ((let _52_13578 = (Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)
in (not (_52_13578)))) with
| true -> begin
(Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
end
| false -> begin
(let t = (mk_guard s pat)
in (let _36_2369 = (tc_typ_check scrutinee_env t Microsoft_FStar_Absyn_Syntax.mk_Kind_type)
in (match (_36_2369) with
| (t, _) -> begin
t
end)))
end))
in (let path_guard = (let _52_13581 = (Support.Prims.pipe_right disj_exps (Support.List.map (fun ( e  :  Microsoft_FStar_Absyn_Syntax.exp ) -> (let _52_13580 = (Microsoft_FStar_Tc_Normalize.norm_exp ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env e)
in (mk_guard scrutinee pat_t _52_13580)))))
in (Support.Prims.pipe_right _52_13581 Microsoft_FStar_Absyn_Util.mk_disj_l))
in (let path_guard = (match (when_condition) with
| None -> begin
path_guard
end
| Some (w) -> begin
(Microsoft_FStar_Absyn_Util.mk_conj path_guard w)
end)
in (let guard = (let _52_13582 = (Microsoft_FStar_Tc_Rel.conj_guard g_when g_branch)
in (Microsoft_FStar_Tc_Rel.conj_guard g_pat _52_13582))
in (let _36_2377 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _52_13583 = (Microsoft_FStar_Tc_Rel.guard_to_string env guard)
in (Support.Prims.pipe_left (Support.Microsoft.FStar.Util.fprint1 "Carrying guard from match: %s\n") _52_13583))
end
| false -> begin
()
end)
in (let _52_13585 = (let _52_13584 = (Microsoft_FStar_Tc_Rel.conj_guard g_when g_branch)
in (Microsoft_FStar_Tc_Rel.conj_guard g_pat _52_13584))
in ((pattern, when_clause, branch), path_guard, c, _52_13585))))))))))
end)))
end)))
end))
end)))
end))
and tc_kind_trivial = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( k  :  (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let _36_2383 = (tc_kind env k)
in (match (_36_2383) with
| (k, g) -> begin
(let _36_2384 = (Microsoft_FStar_Tc_Util.discharge_guard env g)
in k)
end)))
and tc_typ_trivial = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let _36_2391 = (tc_typ env t)
in (match (_36_2391) with
| (t, k, g) -> begin
(let _36_2392 = (Microsoft_FStar_Tc_Util.discharge_guard env g)
in (t, k))
end)))
and tc_typ_check_trivial = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) ( k  :  Microsoft_FStar_Absyn_Syntax.knd ) -> (let _36_2399 = (tc_typ_check env t k)
in (match (_36_2399) with
| (t, f) -> begin
(let _36_2400 = (Microsoft_FStar_Tc_Util.discharge_guard env f)
in t)
end)))
and tc_total_exp = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( e  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let _36_2407 = (tc_exp env e)
in (match (_36_2407) with
| (e, c, g) -> begin
(match ((Microsoft_FStar_Absyn_Util.is_total_lcomp c)) with
| true -> begin
(e, c.Microsoft_FStar_Absyn_Syntax.res_typ, g)
end
| false -> begin
(let g = (Microsoft_FStar_Tc_Rel.solve_deferred_constraints env g)
in (let c = (let _52_13595 = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp c ())
in (Support.Prims.pipe_right _52_13595 (norm_c env)))
in (match ((let _52_13597 = (let _52_13596 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Util.total_comp (Microsoft_FStar_Absyn_Util.comp_result c) _52_13596))
in (Microsoft_FStar_Tc_Rel.sub_comp env c _52_13597))) with
| Some (g') -> begin
(let _52_13598 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (e, (Microsoft_FStar_Absyn_Util.comp_result c), _52_13598))
end
| _ -> begin
(let _52_13601 = (let _52_13600 = (let _52_13599 = (Microsoft_FStar_Tc_Errors.expected_pure_expression e c)
in (_52_13599, e.Microsoft_FStar_Absyn_Syntax.pos))
in Microsoft_FStar_Absyn_Syntax.Error (_52_13600))
in (raise (_52_13601)))
end)))
end)
end)))
and tc_ghost_exp = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( e  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let _36_2419 = (tc_exp env e)
in (match (_36_2419) with
| (e, c, g) -> begin
(match ((Microsoft_FStar_Absyn_Util.is_total_lcomp c)) with
| true -> begin
(e, c.Microsoft_FStar_Absyn_Syntax.res_typ, g)
end
| false -> begin
(let c = (let _52_13604 = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp c ())
in (Support.Prims.pipe_right _52_13604 (norm_c env)))
in (let expected_c = (Microsoft_FStar_Absyn_Util.gtotal_comp (Microsoft_FStar_Absyn_Util.comp_result c))
in (let g = (Microsoft_FStar_Tc_Rel.solve_deferred_constraints env g)
in (match ((Microsoft_FStar_Tc_Rel.sub_comp (let _36_2423 = env
in {Microsoft_FStar_Tc_Env.solver = _36_2423.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_2423.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_2423.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_2423.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_2423.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_2423.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_2423.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_2423.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_2423.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _36_2423.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _36_2423.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _36_2423.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_2423.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _36_2423.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _36_2423.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_2423.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = false; Microsoft_FStar_Tc_Env.is_iface = _36_2423.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_2423.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_2423.Microsoft_FStar_Tc_Env.default_effects}) c expected_c)) with
| Some (g') -> begin
(let _52_13605 = (Microsoft_FStar_Tc_Rel.conj_guard g g')
in (e, (Microsoft_FStar_Absyn_Util.comp_result c), _52_13605))
end
| _ -> begin
(let _52_13608 = (let _52_13607 = (let _52_13606 = (Microsoft_FStar_Tc_Errors.expected_ghost_expression e c)
in (_52_13606, e.Microsoft_FStar_Absyn_Syntax.pos))
in Microsoft_FStar_Absyn_Syntax.Error (_52_13607))
in (raise (_52_13608)))
end))))
end)
end)))

let tc_tparams = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( tps  :  Microsoft_FStar_Absyn_Syntax.binders ) -> (let _36_2434 = (tc_binders env tps)
in (match (_36_2434) with
| (tps, env, g) -> begin
(let _36_2435 = (Microsoft_FStar_Tc_Util.force_trivial env g)
in (tps, env))
end)))

let a_kwp_a = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( m  :  Microsoft_FStar_Absyn_Syntax.l__LongIdent ) ( s  :  (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax ) -> (match (s.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow (((Support.Microsoft.FStar.Util.Inl (a), _)::(Support.Microsoft.FStar.Util.Inl (wp), _)::(Support.Microsoft.FStar.Util.Inl (_), _)::[], _)) -> begin
(a, wp.Microsoft_FStar_Absyn_Syntax.sort)
end
| _ -> begin
(let _52_13622 = (let _52_13621 = (let _52_13620 = (Microsoft_FStar_Tc_Errors.unexpected_signature_for_monad env m s)
in (let _52_13619 = (Microsoft_FStar_Absyn_Syntax.range_of_lid m)
in (_52_13620, _52_13619)))
in Microsoft_FStar_Absyn_Syntax.Error (_52_13621))
in (raise (_52_13622)))
end))

let rec tc_eff_decl = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( m  :  Microsoft_FStar_Absyn_Syntax.eff_decl ) -> (let _36_2468 = (tc_binders env m.Microsoft_FStar_Absyn_Syntax.binders)
in (match (_36_2468) with
| (binders, env, g) -> begin
(let _36_2469 = (Microsoft_FStar_Tc_Util.discharge_guard env g)
in (let mk = (tc_kind_trivial env m.Microsoft_FStar_Absyn_Syntax.signature)
in (let _36_2474 = (a_kwp_a env m.Microsoft_FStar_Absyn_Syntax.mname mk)
in (match (_36_2474) with
| (a, kwp_a) -> begin
(let a_typ = (Microsoft_FStar_Absyn_Util.btvar_to_typ a)
in (let b = (let _52_13636 = (Microsoft_FStar_Absyn_Syntax.range_of_lid m.Microsoft_FStar_Absyn_Syntax.mname)
in (Microsoft_FStar_Absyn_Util.gen_bvar_p _52_13636 Microsoft_FStar_Absyn_Syntax.ktype))
in (let b_typ = (Microsoft_FStar_Absyn_Util.btvar_to_typ b)
in (let kwp_b = (Microsoft_FStar_Absyn_Util.subst_kind ((Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, b_typ)))::[]) kwp_a)
in (let kwlp_a = kwp_a
in (let kwlp_b = kwp_b
in (let a_kwp_b = (let _52_13639 = (let _52_13638 = (let _52_13637 = (Microsoft_FStar_Absyn_Syntax.null_v_binder a_typ)
in (_52_13637)::[])
in (_52_13638, kwp_b))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_13639 a_typ.Microsoft_FStar_Absyn_Syntax.pos))
in (let a_kwlp_b = a_kwp_b
in (let w = (fun ( k  :  Support.Microsoft.FStar.Range.range  ->  Microsoft_FStar_Absyn_Syntax.knd ) -> (let _52_13647 = (Microsoft_FStar_Absyn_Syntax.range_of_lid m.Microsoft_FStar_Absyn_Syntax.mname)
in (k _52_13647)))
in (let ret = (let expected_k = (let _52_13654 = (let _52_13653 = (let _52_13652 = (let _52_13651 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _52_13650 = (let _52_13649 = (Microsoft_FStar_Absyn_Syntax.null_v_binder a_typ)
in (_52_13649)::[])
in (_52_13651)::_52_13650))
in (_52_13652, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_13653))
in (Support.Prims.pipe_left w _52_13654))
in (let _52_13655 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.ret expected_k)
in (Support.Prims.pipe_right _52_13655 (norm_t env))))
in (let bind_wp = (let expected_k = (let _52_13670 = (let _52_13669 = (let _52_13668 = (let _52_13667 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _52_13666 = (let _52_13665 = (Microsoft_FStar_Absyn_Syntax.t_binder b)
in (let _52_13664 = (let _52_13663 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _52_13662 = (let _52_13661 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _52_13660 = (let _52_13659 = (Microsoft_FStar_Absyn_Syntax.null_t_binder a_kwp_b)
in (let _52_13658 = (let _52_13657 = (Microsoft_FStar_Absyn_Syntax.null_t_binder a_kwlp_b)
in (_52_13657)::[])
in (_52_13659)::_52_13658))
in (_52_13661)::_52_13660))
in (_52_13663)::_52_13662))
in (_52_13665)::_52_13664))
in (_52_13667)::_52_13666))
in (_52_13668, kwp_b))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_13669))
in (Support.Prims.pipe_left w _52_13670))
in (let _52_13671 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.bind_wp expected_k)
in (Support.Prims.pipe_right _52_13671 (norm_t env))))
in (let bind_wlp = (let expected_k = (let _52_13682 = (let _52_13681 = (let _52_13680 = (let _52_13679 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _52_13678 = (let _52_13677 = (Microsoft_FStar_Absyn_Syntax.t_binder b)
in (let _52_13676 = (let _52_13675 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _52_13674 = (let _52_13673 = (Microsoft_FStar_Absyn_Syntax.null_t_binder a_kwlp_b)
in (_52_13673)::[])
in (_52_13675)::_52_13674))
in (_52_13677)::_52_13676))
in (_52_13679)::_52_13678))
in (_52_13680, kwlp_b))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_13681))
in (Support.Prims.pipe_left w _52_13682))
in (let _52_13683 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.bind_wlp expected_k)
in (Support.Prims.pipe_right _52_13683 (norm_t env))))
in (let if_then_else = (let expected_k = (let _52_13694 = (let _52_13693 = (let _52_13692 = (let _52_13691 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _52_13690 = (let _52_13689 = (Microsoft_FStar_Absyn_Syntax.t_binder b)
in (let _52_13688 = (let _52_13687 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _52_13686 = (let _52_13685 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_52_13685)::[])
in (_52_13687)::_52_13686))
in (_52_13689)::_52_13688))
in (_52_13691)::_52_13690))
in (_52_13692, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_13693))
in (Support.Prims.pipe_left w _52_13694))
in (let _52_13695 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.if_then_else expected_k)
in (Support.Prims.pipe_right _52_13695 (norm_t env))))
in (let ite_wp = (let expected_k = (let _52_13704 = (let _52_13703 = (let _52_13702 = (let _52_13701 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _52_13700 = (let _52_13699 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _52_13698 = (let _52_13697 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_52_13697)::[])
in (_52_13699)::_52_13698))
in (_52_13701)::_52_13700))
in (_52_13702, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_13703))
in (Support.Prims.pipe_left w _52_13704))
in (let _52_13705 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.ite_wp expected_k)
in (Support.Prims.pipe_right _52_13705 (norm_t env))))
in (let ite_wlp = (let expected_k = (let _52_13712 = (let _52_13711 = (let _52_13710 = (let _52_13709 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _52_13708 = (let _52_13707 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (_52_13707)::[])
in (_52_13709)::_52_13708))
in (_52_13710, kwlp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_13711))
in (Support.Prims.pipe_left w _52_13712))
in (let _52_13713 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.ite_wlp expected_k)
in (Support.Prims.pipe_right _52_13713 (norm_t env))))
in (let wp_binop = (let expected_k = (let _52_13725 = (let _52_13724 = (let _52_13723 = (let _52_13722 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _52_13721 = (let _52_13720 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _52_13719 = (let _52_13718 = (let _52_13715 = (Microsoft_FStar_Absyn_Const.kbin Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Syntax.null_t_binder _52_13715))
in (let _52_13717 = (let _52_13716 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_52_13716)::[])
in (_52_13718)::_52_13717))
in (_52_13720)::_52_13719))
in (_52_13722)::_52_13721))
in (_52_13723, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_13724))
in (Support.Prims.pipe_left w _52_13725))
in (let _52_13726 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.wp_binop expected_k)
in (Support.Prims.pipe_right _52_13726 (norm_t env))))
in (let wp_as_type = (let expected_k = (let _52_13733 = (let _52_13732 = (let _52_13731 = (let _52_13730 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _52_13729 = (let _52_13728 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_52_13728)::[])
in (_52_13730)::_52_13729))
in (_52_13731, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_13732))
in (Support.Prims.pipe_left w _52_13733))
in (let _52_13734 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.wp_as_type expected_k)
in (Support.Prims.pipe_right _52_13734 (norm_t env))))
in (let close_wp = (let expected_k = (let _52_13743 = (let _52_13742 = (let _52_13741 = (let _52_13740 = (Microsoft_FStar_Absyn_Syntax.t_binder b)
in (let _52_13739 = (let _52_13738 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _52_13737 = (let _52_13736 = (Microsoft_FStar_Absyn_Syntax.null_t_binder a_kwp_b)
in (_52_13736)::[])
in (_52_13738)::_52_13737))
in (_52_13740)::_52_13739))
in (_52_13741, kwp_b))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_13742))
in (Support.Prims.pipe_left w _52_13743))
in (let _52_13744 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.close_wp expected_k)
in (Support.Prims.pipe_right _52_13744 (norm_t env))))
in (let close_wp_t = (let expected_k = (let _52_13757 = (let _52_13756 = (let _52_13755 = (let _52_13754 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _52_13753 = (let _52_13752 = (let _52_13751 = (let _52_13750 = (let _52_13749 = (let _52_13748 = (let _52_13747 = (Microsoft_FStar_Absyn_Syntax.null_t_binder Microsoft_FStar_Absyn_Syntax.ktype)
in (_52_13747)::[])
in (_52_13748, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_13749))
in (Support.Prims.pipe_left w _52_13750))
in (Microsoft_FStar_Absyn_Syntax.null_t_binder _52_13751))
in (_52_13752)::[])
in (_52_13754)::_52_13753))
in (_52_13755, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_13756))
in (Support.Prims.pipe_left w _52_13757))
in (let _52_13758 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.close_wp_t expected_k)
in (Support.Prims.pipe_right _52_13758 (norm_t env))))
in (let _36_2508 = (let expected_k = (let _52_13767 = (let _52_13766 = (let _52_13765 = (let _52_13764 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _52_13763 = (let _52_13762 = (Microsoft_FStar_Absyn_Syntax.null_t_binder Microsoft_FStar_Absyn_Syntax.ktype)
in (let _52_13761 = (let _52_13760 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_52_13760)::[])
in (_52_13762)::_52_13761))
in (_52_13764)::_52_13763))
in (_52_13765, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_13766))
in (Support.Prims.pipe_left w _52_13767))
in (let _52_13771 = (let _52_13768 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.assert_p expected_k)
in (Support.Prims.pipe_right _52_13768 (norm_t env)))
in (let _52_13770 = (let _52_13769 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.assume_p expected_k)
in (Support.Prims.pipe_right _52_13769 (norm_t env)))
in (_52_13771, _52_13770))))
in (match (_36_2508) with
| (assert_p, assume_p) -> begin
(let null_wp = (let expected_k = (let _52_13776 = (let _52_13775 = (let _52_13774 = (let _52_13773 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (_52_13773)::[])
in (_52_13774, kwp_a))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_13775))
in (Support.Prims.pipe_left w _52_13776))
in (let _52_13777 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.null_wp expected_k)
in (Support.Prims.pipe_right _52_13777 (norm_t env))))
in (let trivial_wp = (let expected_k = (let _52_13784 = (let _52_13783 = (let _52_13782 = (let _52_13781 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _52_13780 = (let _52_13779 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_52_13779)::[])
in (_52_13781)::_52_13780))
in (_52_13782, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_13783))
in (Support.Prims.pipe_left w _52_13784))
in (let _52_13785 = (tc_typ_check_trivial env m.Microsoft_FStar_Absyn_Syntax.trivial expected_k)
in (Support.Prims.pipe_right _52_13785 (norm_t env))))
in {Microsoft_FStar_Absyn_Syntax.mname = m.Microsoft_FStar_Absyn_Syntax.mname; Microsoft_FStar_Absyn_Syntax.binders = binders; Microsoft_FStar_Absyn_Syntax.qualifiers = m.Microsoft_FStar_Absyn_Syntax.qualifiers; Microsoft_FStar_Absyn_Syntax.signature = mk; Microsoft_FStar_Absyn_Syntax.ret = ret; Microsoft_FStar_Absyn_Syntax.bind_wp = bind_wp; Microsoft_FStar_Absyn_Syntax.bind_wlp = bind_wlp; Microsoft_FStar_Absyn_Syntax.if_then_else = if_then_else; Microsoft_FStar_Absyn_Syntax.ite_wp = ite_wp; Microsoft_FStar_Absyn_Syntax.ite_wlp = ite_wlp; Microsoft_FStar_Absyn_Syntax.wp_binop = wp_binop; Microsoft_FStar_Absyn_Syntax.wp_as_type = wp_as_type; Microsoft_FStar_Absyn_Syntax.close_wp = close_wp; Microsoft_FStar_Absyn_Syntax.close_wp_t = close_wp_t; Microsoft_FStar_Absyn_Syntax.assert_p = assert_p; Microsoft_FStar_Absyn_Syntax.assume_p = assume_p; Microsoft_FStar_Absyn_Syntax.null_wp = null_wp; Microsoft_FStar_Absyn_Syntax.trivial = trivial_wp}))
end)))))))))))))))))))))
end))))
end)))
and tc_decl = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( se  :  Microsoft_FStar_Absyn_Syntax.sigelt ) ( deserialized  :  bool ) -> (match (se) with
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
(let _36_2527 = (Microsoft_FStar_Tc_Env_Mksolver_t.refresh env.Microsoft_FStar_Tc_Env.solver ())
in (let _36_2529 = (let _52_13789 = (Microsoft_FStar_Options.reset_options ())
in (Support.Prims.pipe_right _52_13789 Support.Prims.ignore))
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
(let _36_2544 = (let _52_13790 = (Microsoft_FStar_Tc_Env.lookup_effect_lid env sub.Microsoft_FStar_Absyn_Syntax.source)
in (a_kwp_a env sub.Microsoft_FStar_Absyn_Syntax.source _52_13790))
in (match (_36_2544) with
| (a, kwp_a_src) -> begin
(let _36_2547 = (let _52_13791 = (Microsoft_FStar_Tc_Env.lookup_effect_lid env sub.Microsoft_FStar_Absyn_Syntax.target)
in (a_kwp_a env sub.Microsoft_FStar_Absyn_Syntax.target _52_13791))
in (match (_36_2547) with
| (b, kwp_b_tgt) -> begin
(let kwp_a_tgt = (let _52_13795 = (let _52_13794 = (let _52_13793 = (let _52_13792 = (Microsoft_FStar_Absyn_Util.btvar_to_typ a)
in (b.Microsoft_FStar_Absyn_Syntax.v, _52_13792))
in Support.Microsoft.FStar.Util.Inl (_52_13793))
in (_52_13794)::[])
in (Microsoft_FStar_Absyn_Util.subst_kind _52_13795 kwp_b_tgt))
in (let expected_k = (let _52_13801 = (let _52_13800 = (let _52_13799 = (let _52_13798 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _52_13797 = (let _52_13796 = (Microsoft_FStar_Absyn_Syntax.null_t_binder kwp_a_src)
in (_52_13796)::[])
in (_52_13798)::_52_13797))
in (_52_13799, kwp_a_tgt))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_13800))
in (Support.Prims.pipe_right r _52_13801))
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
| _ -> begin
(tc_kind_trivial env k)
end)
in (let _36_2573 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Extreme)) with
| true -> begin
(let _52_13804 = (Microsoft_FStar_Absyn_Print.sli lid)
in (let _52_13803 = (let _52_13802 = (Microsoft_FStar_Absyn_Util.close_kind tps k)
in (Microsoft_FStar_Absyn_Print.kind_to_string _52_13802))
in (Support.Microsoft.FStar.Util.fprint2 "Checked %s at kind %s\n" _52_13804 _52_13803)))
end
| false -> begin
()
end)
in (let k = (norm_k env k)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, _mutuals, _data, tags, r))
in (let _36_2591 = (match ((Microsoft_FStar_Absyn_Util.compress_kind k)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
(let _52_13805 = (Microsoft_FStar_Tc_Rel.keq env None k Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_left (Microsoft_FStar_Tc_Util.force_trivial env) _52_13805))
end
| _ -> begin
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
(let tags = (Support.Prims.pipe_right tags (Support.List.map (fun ( _36_13  :  Microsoft_FStar_Absyn_Syntax.qualifier ) -> (match (_36_13) with
| Microsoft_FStar_Absyn_Syntax.DefaultEffect (None) -> begin
(let c' = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c)
in (let _52_13808 = (Support.Prims.pipe_right c'.Microsoft_FStar_Absyn_Syntax.effect_name (fun ( _52_13807  :  Microsoft_FStar_Absyn_Syntax.lident ) -> Some (_52_13807)))
in Microsoft_FStar_Absyn_Syntax.DefaultEffect (_52_13808)))
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
(let _36_2648 = (let _52_13812 = (tc_typ_trivial env' t)
in (Support.Prims.pipe_right _52_13812 (fun ( _36_2645  :  (Microsoft_FStar_Absyn_Syntax.typ * Microsoft_FStar_Absyn_Syntax.knd) ) -> (match (_36_2645) with
| (t, k) -> begin
(let _52_13811 = (norm_t env' t)
in (let _52_13810 = (norm_k env' k)
in (_52_13811, _52_13810)))
end))))
in (match (_36_2648) with
| (t, k1) -> begin
(let k2 = (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
k1
end
| _ -> begin
(let k2 = (let _52_13813 = (tc_kind_trivial env' k)
in (Support.Prims.pipe_right _52_13813 (norm_k env)))
in (let _36_2653 = (let _52_13814 = (Microsoft_FStar_Tc_Rel.keq env' (Some (t)) k1 k2)
in (Support.Prims.pipe_left (Microsoft_FStar_Tc_Util.force_trivial env') _52_13814))
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
| (tname, _, _) -> begin
(let env = (Microsoft_FStar_Tc_Env.set_range env r)
in (let t = (tc_typ_check_trivial env t Microsoft_FStar_Absyn_Syntax.ktype)
in (let t = (norm_t env t)
in (let _36_2683 = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((formals, cod)) -> begin
(formals, (Microsoft_FStar_Absyn_Util.comp_result cod))
end
| _ -> begin
([], t)
end)
in (match (_36_2683) with
| (formals, result_t) -> begin
(let positivity_check = (fun ( formal  :  Microsoft_FStar_Absyn_Syntax.binder ) -> (match ((Support.Prims.fst formal)) with
| Support.Microsoft.FStar.Util.Inl (_) -> begin
()
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let t = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.DeltaHard)::[]) env x.Microsoft_FStar_Absyn_Syntax.sort)
in (match ((let _52_13818 = (Microsoft_FStar_Absyn_Util.is_function_typ t)
in (let _52_13817 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t)
in (_52_13818 && _52_13817)))) with
| true -> begin
(let _36_2695 = (let _52_13819 = (Microsoft_FStar_Absyn_Util.function_formals t)
in (Support.Prims.pipe_right _52_13819 Support.Microsoft.FStar.Util.must))
in (match (_36_2695) with
| (formals, _) -> begin
(Support.Prims.pipe_right formals (Support.List.iter (fun ( _36_2699  :  ((((Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.withinfo_t, ((Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax Microsoft_FStar_Absyn_Syntax.bvdef, Microsoft_FStar_Absyn_Syntax.typ) Microsoft_FStar_Absyn_Syntax.withinfo_t) Support.Microsoft.FStar.Util.either * Microsoft_FStar_Absyn_Syntax.arg_qualifier option) ) -> (match (_36_2699) with
| (a, _) -> begin
(match (a) with
| Support.Microsoft.FStar.Util.Inl (_) -> begin
()
end
| Support.Microsoft.FStar.Util.Inr (y) -> begin
(let t = y.Microsoft_FStar_Absyn_Syntax.sort
in (Microsoft_FStar_Absyn_Visit.collect_from_typ (fun ( b  :  unit ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (match ((let _52_13823 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _52_13823.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (f) -> begin
(match ((Support.List.tryFind (Microsoft_FStar_Absyn_Syntax.lid_equals f.Microsoft_FStar_Absyn_Syntax.v) mutuals)) with
| None -> begin
()
end
| Some (tname) -> begin
(let _52_13829 = (let _52_13828 = (let _52_13827 = (let _52_13825 = (let _52_13824 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) lid _52_13824))
in (Microsoft_FStar_Tc_Errors.constructor_fails_the_positivity_check env _52_13825 tname))
in (let _52_13826 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (_52_13827, _52_13826)))
in Microsoft_FStar_Absyn_Syntax.Error (_52_13828))
in (raise (_52_13829)))
end)
end
| _ -> begin
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
| Some (_) -> begin
()
end
| _ -> begin
(let _52_13836 = (let _52_13835 = (let _52_13834 = (let _52_13832 = (let _52_13830 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (Microsoft_FStar_Absyn_Util.fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) lid _52_13830))
in (let _52_13831 = (Microsoft_FStar_Absyn_Util.ftv tname Microsoft_FStar_Absyn_Syntax.kun)
in (Microsoft_FStar_Tc_Errors.constructor_builds_the_wrong_type env _52_13832 result_t _52_13831)))
in (let _52_13833 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (_52_13834, _52_13833)))
in Microsoft_FStar_Absyn_Syntax.Error (_52_13835))
in (raise (_52_13836)))
end)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, t, tycon, quals, mutuals, r))
in (let env = (Microsoft_FStar_Tc_Env.push_sigelt env se)
in (let _36_2726 = (match ((log env)) with
| true -> begin
(let _52_13838 = (let _52_13837 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (Support.Microsoft.FStar.Util.format2 "data %s : %s\n" lid.Microsoft_FStar_Absyn_Syntax.str _52_13837))
in (Support.Prims.pipe_left Support.Microsoft.FStar.Util.print_string _52_13838))
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
in (let t = (let _52_13839 = (tc_typ_check_trivial env t Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_right _52_13839 (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.SNComp)::[]) env)))
in (let _36_2736 = (Microsoft_FStar_Tc_Util.check_uvars r t)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, r))
in (let env = (Microsoft_FStar_Tc_Env.push_sigelt env se)
in (let _36_2740 = (match ((log env)) with
| true -> begin
(let _52_13841 = (let _52_13840 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (Support.Microsoft.FStar.Util.format2 "val %s : %s\n" lid.Microsoft_FStar_Absyn_Syntax.str _52_13840))
in (Support.Prims.pipe_left Support.Microsoft.FStar.Util.print_string _52_13841))
end
| false -> begin
()
end)
in (se, env)))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_assume ((lid, phi, quals, r)) -> begin
(let env = (Microsoft_FStar_Tc_Env.set_range env r)
in (let phi = (let _52_13842 = (tc_typ_check_trivial env phi Microsoft_FStar_Absyn_Syntax.ktype)
in (Support.Prims.pipe_right _52_13842 (norm_t env)))
in (let _36_2750 = (Microsoft_FStar_Tc_Util.check_uvars r phi)
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_assume ((lid, phi, quals, r))
in (let env = (Microsoft_FStar_Tc_Env.push_sigelt env se)
in (se, env))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, r, lids, quals)) -> begin
(let env = (Microsoft_FStar_Tc_Env.set_range env r)
in (let _36_2803 = (Support.Prims.pipe_right (Support.Prims.snd lbs) (Support.List.fold_left (fun ( _36_2763  :  (bool * Microsoft_FStar_Absyn_Syntax.letbinding list) ) ( lb  :  Microsoft_FStar_Absyn_Syntax.letbinding ) -> (match (_36_2763) with
| (gen, lbs) -> begin
(let _36_2800 = (match (lb) with
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inl (_); Microsoft_FStar_Absyn_Syntax.lbtyp = _; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = _} -> begin
(failwith ("impossible"))
end
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (l); Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = e} -> begin
(let _36_2797 = (match ((Microsoft_FStar_Tc_Env.try_lookup_val_decl env l)) with
| None -> begin
(gen, lb)
end
| Some ((t', _)) -> begin
(let _36_2788 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Medium)) with
| true -> begin
(let _52_13845 = (Microsoft_FStar_Absyn_Print.typ_to_string t')
in (Support.Microsoft.FStar.Util.fprint2 "Using annotation %s for let binding %s\n" _52_13845 l.Microsoft_FStar_Absyn_Syntax.str))
end
| false -> begin
()
end)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
(let _52_13846 = (Microsoft_FStar_Absyn_Syntax.mk_lb (Support.Microsoft.FStar.Util.Inr (l), Microsoft_FStar_Absyn_Const.effect_ALL_lid, t', e))
in (false, _52_13846))
end
| _ -> begin
(let _36_2793 = (match ((not (deserialized))) with
| true -> begin
(let _52_13848 = (let _52_13847 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format1 "%s: Warning: Annotation from val declaration overrides inline type annotation\n" _52_13847))
in (Support.Prims.pipe_left Support.Microsoft.FStar.Util.print_string _52_13848))
end
| false -> begin
()
end)
in (let _52_13849 = (Microsoft_FStar_Absyn_Syntax.mk_lb (Support.Microsoft.FStar.Util.Inr (l), Microsoft_FStar_Absyn_Const.effect_ALL_lid, t', e))
in (false, _52_13849)))
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
in (let e = (let _52_13854 = (let _52_13853 = (let _52_13852 = (syn' env Microsoft_FStar_Tc_Recheck.t_unit)
in (Support.Prims.pipe_left _52_13852 (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant Microsoft_FStar_Absyn_Syntax.Const_unit)))
in (((Support.Prims.fst lbs), lbs'), _52_13853))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_let _52_13854 None r))
in (let _36_2838 = (match ((tc_exp (let _36_2806 = env
in {Microsoft_FStar_Tc_Env.solver = _36_2806.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_2806.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_2806.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_2806.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_2806.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_2806.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_2806.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_2806.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_2806.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _36_2806.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _36_2806.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _36_2806.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = generalize; Microsoft_FStar_Tc_Env.letrecs = _36_2806.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _36_2806.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_2806.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = _36_2806.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = _36_2806.Microsoft_FStar_Tc_Env.is_iface; Microsoft_FStar_Tc_Env.admit = _36_2806.Microsoft_FStar_Tc_Env.admit; Microsoft_FStar_Tc_Env.default_effects = _36_2806.Microsoft_FStar_Tc_Env.default_effects}) e)) with
| ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_let ((lbs, e)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _, g) when (Microsoft_FStar_Tc_Rel.is_trivial g) -> begin
(let quals = (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((_, Microsoft_FStar_Absyn_Syntax.MaskedEffect))) -> begin
(Microsoft_FStar_Absyn_Syntax.HasMaskedEffect)::quals
end
| _ -> begin
quals
end)
in (Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _ -> begin
(failwith ("impossible"))
end)
in (match (_36_2838) with
| (se, lbs) -> begin
(let _36_2844 = (match ((log env)) with
| true -> begin
(let _52_13860 = (let _52_13859 = (Support.Prims.pipe_right (Support.Prims.snd lbs) (Support.List.map (fun ( lb  :  Microsoft_FStar_Absyn_Syntax.letbinding ) -> (let should_log = (match ((let _52_13856 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (Microsoft_FStar_Tc_Env.try_lookup_val_decl env _52_13856))) with
| None -> begin
true
end
| _ -> begin
false
end)
in (match (should_log) with
| true -> begin
(let _52_13858 = (Microsoft_FStar_Absyn_Print.lbname_to_string lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (let _52_13857 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
in (Support.Microsoft.FStar.Util.format2 "let %s : %s" _52_13858 _52_13857)))
end
| false -> begin
""
end)))))
in (Support.Prims.pipe_right _52_13859 (Support.String.concat "\n")))
in (Support.Microsoft.FStar.Util.fprint1 "%s\n" _52_13860))
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
in (let _36_2862 = (let _52_13864 = (let _52_13861 = (Microsoft_FStar_Absyn_Util.ml_comp Microsoft_FStar_Tc_Recheck.t_unit r)
in Some (_52_13861))
in (let _52_13863 = (let _52_13862 = (Microsoft_FStar_Absyn_Syntax_Mklcomp.comp c ())
in (e, _52_13862))
in (check_expected_effect env _52_13864 _52_13863)))
in (match (_36_2862) with
| (e, _, g) -> begin
(let _36_2863 = (let _52_13865 = (Microsoft_FStar_Tc_Rel.conj_guard g1 g)
in (Microsoft_FStar_Tc_Util.discharge_guard env _52_13865))
in (let se = Microsoft_FStar_Absyn_Syntax.Sig_main ((e, r))
in (let env = (Microsoft_FStar_Tc_Env.push_sigelt env se)
in (se, env))))
end)))
end))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, quals, lids, r)) -> begin
(let env = (Microsoft_FStar_Tc_Env.set_range env r)
in (let _36_2882 = (Support.Prims.pipe_right ses (Support.List.partition (fun ( _36_14  :  Microsoft_FStar_Absyn_Syntax.sigelt ) -> (match (_36_14) with
| Microsoft_FStar_Absyn_Syntax.Sig_tycon (_) -> begin
true
end
| _ -> begin
false
end))))
in (match (_36_2882) with
| (tycons, rest) -> begin
(let _36_2891 = (Support.Prims.pipe_right rest (Support.List.partition (fun ( _36_15  :  Microsoft_FStar_Absyn_Syntax.sigelt ) -> (match (_36_15) with
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_) -> begin
true
end
| _ -> begin
false
end))))
in (match (_36_2891) with
| (abbrevs, rest) -> begin
(let recs = (Support.Prims.pipe_right abbrevs (Support.List.map (fun ( _36_16  :  Microsoft_FStar_Absyn_Syntax.sigelt ) -> (match (_36_16) with
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, k, t, [], r)) -> begin
(let k = (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(let _52_13869 = (Microsoft_FStar_Tc_Rel.new_kvar r tps)
in (Support.Prims.pipe_right _52_13869 Support.Prims.fst))
end
| _ -> begin
k
end)
in (Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, [], [], [], r)), t))
end
| _ -> begin
(failwith ("impossible"))
end))))
in (let _36_2910 = (Support.List.split recs)
in (match (_36_2910) with
| (recs, abbrev_defs) -> begin
(let msg = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _52_13870 = (Microsoft_FStar_Absyn_Print.sigelt_to_string_short se)
in (Support.Microsoft.FStar.Util.format1 "Recursive bindings: %s" _52_13870))
end
| false -> begin
""
end)
in (let _36_2912 = (Microsoft_FStar_Tc_Env_Mksolver_t.push env.Microsoft_FStar_Tc_Env.solver msg)
in (let _36_2919 = (tc_decls false env tycons deserialized)
in (match (_36_2919) with
| (tycons, _, _) -> begin
(let _36_2925 = (tc_decls false env recs deserialized)
in (match (_36_2925) with
| (recs, _, _) -> begin
(let env1 = (Microsoft_FStar_Tc_Env.push_sigelt env (Microsoft_FStar_Absyn_Syntax.Sig_bundle (((Support.List.append tycons recs), quals, lids, r))))
in (let _36_2932 = (tc_decls false env1 rest deserialized)
in (match (_36_2932) with
| (rest, _, _) -> begin
(let abbrevs = (Support.List.map2 (fun ( se  :  Microsoft_FStar_Absyn_Syntax.sigelt ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, [], [], [], r)) -> begin
(let tt = (let _52_13873 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_ascribed (t, k) t.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Util.close_with_lam tps _52_13873))
in (let _36_2948 = (tc_typ_trivial env1 tt)
in (match (_36_2948) with
| (tt, _) -> begin
(let _36_2957 = (match (tt.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, t)) -> begin
(bs, t)
end
| _ -> begin
([], tt)
end)
in (match (_36_2957) with
| (tps, t) -> begin
(let _52_13875 = (let _52_13874 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in (lid, tps, _52_13874, t, [], r))
in Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_52_13875))
end))
end)))
end
| _ -> begin
(let _52_13877 = (let _52_13876 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format1 "(%s) Impossible" _52_13876))
in (failwith (_52_13877)))
end)) recs abbrev_defs)
in (let _36_2961 = (Microsoft_FStar_Tc_Env_Mksolver_t.pop env.Microsoft_FStar_Tc_Env.solver msg)
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
and tc_decls = (fun ( for_export  :  bool ) ( env  :  Microsoft_FStar_Tc_Env.env ) ( ses  :  Microsoft_FStar_Absyn_Syntax.sigelt list ) ( deserialized  :  bool ) -> (let _36_2985 = (Support.Prims.pipe_right ses (Support.List.fold_left (fun ( _36_2972  :  (Microsoft_FStar_Absyn_Syntax.sigelt list * Microsoft_FStar_Absyn_Syntax.sigelt list list * Microsoft_FStar_Tc_Env.env) ) ( se  :  Microsoft_FStar_Absyn_Syntax.sigelt ) -> (match (_36_2972) with
| (ses, all_non_private, env) -> begin
(let _36_2974 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.Low)) with
| true -> begin
(let _52_13885 = (let _52_13884 = (Microsoft_FStar_Absyn_Print.sigelt_to_string se)
in (Support.Microsoft.FStar.Util.format1 "Checking sigelt\t%s\n" _52_13884))
in (Support.Microsoft.FStar.Util.print_string _52_13885))
end
| false -> begin
()
end)
in (let _36_2978 = (tc_decl env se deserialized)
in (match (_36_2978) with
| (se, env) -> begin
(let _36_2979 = (Microsoft_FStar_Tc_Env_Mksolver_t.encode_sig env.Microsoft_FStar_Tc_Env.solver env se)
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
(let _52_13886 = (Support.Prims.pipe_right (Support.List.rev all_non_private) Support.List.flatten)
in ((Support.List.rev ses), _52_13886, env))
end)))
and non_private = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( se  :  Microsoft_FStar_Absyn_Syntax.sigelt ) -> (let is_private = (fun ( quals  :  Microsoft_FStar_Absyn_Syntax.qualifier list ) -> (Support.List.contains Microsoft_FStar_Absyn_Syntax.Private quals))
in (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, quals, _, _)) -> begin
(se)::[]
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((_, _, _, _, _, quals, r)) -> begin
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
| Microsoft_FStar_Absyn_Syntax.Sig_assume ((_, _, quals, _)) -> begin
(match ((is_private quals)) with
| true -> begin
[]
end
| false -> begin
(se)::[]
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, _, quals, _)) -> begin
(match ((is_private quals)) with
| true -> begin
[]
end
| false -> begin
(se)::[]
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_main (_) -> begin
[]
end
| (Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_pragma (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_)) -> begin
(se)::[]
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon (_) -> begin
(failwith ("Impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, r, l, _)) -> begin
(let check_priv = (fun ( lbs  :  Microsoft_FStar_Absyn_Syntax.letbinding list ) -> (let is_priv = (fun ( _36_17  :  Microsoft_FStar_Absyn_Syntax.letbinding ) -> (match (_36_17) with
| {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (l); Microsoft_FStar_Absyn_Syntax.lbtyp = _; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = _} -> begin
(match ((Microsoft_FStar_Tc_Env.try_lookup_val_decl env l)) with
| Some ((_, qs)) -> begin
(Support.List.contains Microsoft_FStar_Absyn_Syntax.Private qs)
end
| _ -> begin
false
end)
end
| _ -> begin
false
end))
in (let some_priv = (Support.Prims.pipe_right lbs (Support.Microsoft.FStar.Util.for_some is_priv))
in (match (some_priv) with
| true -> begin
(match ((Support.Prims.pipe_right lbs (Support.Microsoft.FStar.Util.for_some (fun ( x  :  Microsoft_FStar_Absyn_Syntax.letbinding ) -> (let _52_13896 = (is_priv x)
in (Support.Prims.pipe_right _52_13896 Support.Prims.op_Negation)))))) with
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
in (let _36_3093 = (Support.Prims.pipe_right (Support.Prims.snd lbs) (Support.List.partition (fun ( lb  :  Microsoft_FStar_Absyn_Syntax.letbinding ) -> (let _52_13900 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
in (let _52_13899 = (let _52_13898 = (Microsoft_FStar_Absyn_Util.is_lemma lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
in (Support.Prims.pipe_left Support.Prims.op_Negation _52_13898))
in (_52_13900 && _52_13899))))))
in (match (_36_3093) with
| (pure_funs, rest) -> begin
(match ((pure_funs, rest)) with
| (_::_, _::_) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Pure functions cannot be mutually recursive with impure functions", r))))
end
| (_::_, []) -> begin
(match ((check_priv pure_funs)) with
| true -> begin
[]
end
| false -> begin
(se)::[]
end)
end
| ([], _::_) -> begin
(match ((check_priv rest)) with
| true -> begin
[]
end
| false -> begin
(Support.Prims.pipe_right rest (Support.List.collect (fun ( lb  :  Microsoft_FStar_Absyn_Syntax.letbinding ) -> (match (lb.Microsoft_FStar_Absyn_Syntax.lbname) with
| Support.Microsoft.FStar.Util.Inl (_) -> begin
(failwith ("impossible"))
end
| Support.Microsoft.FStar.Util.Inr (l) -> begin
(let _52_13904 = (let _52_13903 = (let _52_13902 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (l, lb.Microsoft_FStar_Absyn_Syntax.lbtyp, (Microsoft_FStar_Absyn_Syntax.Assumption)::[], _52_13902))
in Microsoft_FStar_Absyn_Syntax.Sig_val_decl (_52_13903))
in (_52_13904)::[])
end))))
end)
end
| ([], []) -> begin
(failwith ("Impossible"))
end)
end)))
end)))

let get_exports = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( modul  :  Microsoft_FStar_Absyn_Syntax.modul ) ( non_private_decls  :  Microsoft_FStar_Absyn_Syntax.sigelt list ) -> (let assume_vals = (fun ( decls  :  Microsoft_FStar_Absyn_Syntax.sigelt list ) -> (Support.Prims.pipe_right decls (Support.List.map (fun ( _36_18  :  Microsoft_FStar_Absyn_Syntax.sigelt ) -> (match (_36_18) with
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
(let exports = (let _52_13916 = (Microsoft_FStar_Tc_Env.modules env)
in (Support.Microsoft.FStar.Util.find_map _52_13916 (fun ( m  :  Microsoft_FStar_Absyn_Syntax.modul ) -> (match ((m.Microsoft_FStar_Absyn_Syntax.is_interface && (Microsoft_FStar_Absyn_Syntax.lid_equals modul.Microsoft_FStar_Absyn_Syntax.name m.Microsoft_FStar_Absyn_Syntax.name))) with
| true -> begin
(let _52_13915 = (Support.Prims.pipe_right m.Microsoft_FStar_Absyn_Syntax.exports assume_vals)
in Some (_52_13915))
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

let tc_partial_modul = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( modul  :  Microsoft_FStar_Absyn_Syntax.modul ) -> (let name = (Support.Microsoft.FStar.Util.format2 "%s %s" (match (modul.Microsoft_FStar_Absyn_Syntax.is_interface) with
| true -> begin
"interface"
end
| false -> begin
"module"
end) modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)
in (let msg = (Support.String.strcat "Internals for " name)
in (let env = (let _36_3150 = env
in (let _52_13922 = (let _52_13921 = (Microsoft_FStar_Options.should_verify modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)
in (not (_52_13921)))
in {Microsoft_FStar_Tc_Env.solver = _36_3150.Microsoft_FStar_Tc_Env.solver; Microsoft_FStar_Tc_Env.range = _36_3150.Microsoft_FStar_Tc_Env.range; Microsoft_FStar_Tc_Env.curmodule = _36_3150.Microsoft_FStar_Tc_Env.curmodule; Microsoft_FStar_Tc_Env.gamma = _36_3150.Microsoft_FStar_Tc_Env.gamma; Microsoft_FStar_Tc_Env.modules = _36_3150.Microsoft_FStar_Tc_Env.modules; Microsoft_FStar_Tc_Env.expected_typ = _36_3150.Microsoft_FStar_Tc_Env.expected_typ; Microsoft_FStar_Tc_Env.level = _36_3150.Microsoft_FStar_Tc_Env.level; Microsoft_FStar_Tc_Env.sigtab = _36_3150.Microsoft_FStar_Tc_Env.sigtab; Microsoft_FStar_Tc_Env.is_pattern = _36_3150.Microsoft_FStar_Tc_Env.is_pattern; Microsoft_FStar_Tc_Env.instantiate_targs = _36_3150.Microsoft_FStar_Tc_Env.instantiate_targs; Microsoft_FStar_Tc_Env.instantiate_vargs = _36_3150.Microsoft_FStar_Tc_Env.instantiate_vargs; Microsoft_FStar_Tc_Env.effects = _36_3150.Microsoft_FStar_Tc_Env.effects; Microsoft_FStar_Tc_Env.generalize = _36_3150.Microsoft_FStar_Tc_Env.generalize; Microsoft_FStar_Tc_Env.letrecs = _36_3150.Microsoft_FStar_Tc_Env.letrecs; Microsoft_FStar_Tc_Env.top_level = _36_3150.Microsoft_FStar_Tc_Env.top_level; Microsoft_FStar_Tc_Env.check_uvars = _36_3150.Microsoft_FStar_Tc_Env.check_uvars; Microsoft_FStar_Tc_Env.use_eq = _36_3150.Microsoft_FStar_Tc_Env.use_eq; Microsoft_FStar_Tc_Env.is_iface = modul.Microsoft_FStar_Absyn_Syntax.is_interface; Microsoft_FStar_Tc_Env.admit = _52_13922; Microsoft_FStar_Tc_Env.default_effects = _36_3150.Microsoft_FStar_Tc_Env.default_effects}))
in (let _36_3153 = (match ((not ((Microsoft_FStar_Absyn_Syntax.lid_equals modul.Microsoft_FStar_Absyn_Syntax.name Microsoft_FStar_Absyn_Const.prims_lid)))) with
| true -> begin
(Microsoft_FStar_Tc_Env_Mksolver_t.push env.Microsoft_FStar_Tc_Env.solver msg)
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

let tc_more_partial_modul = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( modul  :  Microsoft_FStar_Absyn_Syntax.modul ) ( decls  :  Microsoft_FStar_Absyn_Syntax.sigelt list ) -> (let _36_3168 = (tc_decls true env decls false)
in (match (_36_3168) with
| (ses, non_private_decls, env) -> begin
(let modul = (let _36_3169 = modul
in {Microsoft_FStar_Absyn_Syntax.name = _36_3169.Microsoft_FStar_Absyn_Syntax.name; Microsoft_FStar_Absyn_Syntax.declarations = (Support.List.append modul.Microsoft_FStar_Absyn_Syntax.declarations ses); Microsoft_FStar_Absyn_Syntax.exports = _36_3169.Microsoft_FStar_Absyn_Syntax.exports; Microsoft_FStar_Absyn_Syntax.is_interface = _36_3169.Microsoft_FStar_Absyn_Syntax.is_interface; Microsoft_FStar_Absyn_Syntax.is_deserialized = _36_3169.Microsoft_FStar_Absyn_Syntax.is_deserialized})
in (modul, non_private_decls, env))
end)))

let finish_partial_modul = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( modul  :  Microsoft_FStar_Absyn_Syntax.modul ) ( npds  :  Microsoft_FStar_Absyn_Syntax.sigelt list ) -> (let exports = (get_exports env modul npds)
in (let modul = (let _36_3176 = modul
in {Microsoft_FStar_Absyn_Syntax.name = _36_3176.Microsoft_FStar_Absyn_Syntax.name; Microsoft_FStar_Absyn_Syntax.declarations = _36_3176.Microsoft_FStar_Absyn_Syntax.declarations; Microsoft_FStar_Absyn_Syntax.exports = exports; Microsoft_FStar_Absyn_Syntax.is_interface = modul.Microsoft_FStar_Absyn_Syntax.is_interface; Microsoft_FStar_Absyn_Syntax.is_deserialized = modul.Microsoft_FStar_Absyn_Syntax.is_deserialized})
in (let env = (Microsoft_FStar_Tc_Env.finish_module env modul)
in (let _36_3186 = (match ((not ((Microsoft_FStar_Absyn_Syntax.lid_equals modul.Microsoft_FStar_Absyn_Syntax.name Microsoft_FStar_Absyn_Const.prims_lid)))) with
| true -> begin
(let _36_3180 = (Microsoft_FStar_Tc_Env_Mksolver_t.pop env.Microsoft_FStar_Tc_Env.solver (Support.String.strcat "Ending modul " modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str))
in (let _36_3182 = (match ((let _52_13936 = (let _52_13935 = (Support.ST.read Microsoft_FStar_Options.admit_fsi)
in (Support.List.contains modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str _52_13935))
in ((not (modul.Microsoft_FStar_Absyn_Syntax.is_interface)) || _52_13936))) with
| true -> begin
(Microsoft_FStar_Tc_Env_Mksolver_t.encode_modul env.Microsoft_FStar_Tc_Env.solver env modul)
end
| false -> begin
()
end)
in (let _36_3184 = (Microsoft_FStar_Tc_Env_Mksolver_t.refresh env.Microsoft_FStar_Tc_Env.solver ())
in (let _52_13937 = (Microsoft_FStar_Options.reset_options ())
in (Support.Prims.pipe_right _52_13937 Support.Prims.ignore)))))
end
| false -> begin
()
end)
in (modul, env))))))

let tc_modul = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( modul  :  Microsoft_FStar_Absyn_Syntax.modul ) -> (let _36_3193 = (tc_partial_modul env modul)
in (match (_36_3193) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

let add_modul_to_tcenv = (fun ( en  :  Microsoft_FStar_Tc_Env.env ) ( m  :  Microsoft_FStar_Absyn_Syntax.modul ) -> (let do_sigelt = (fun ( en  :  Microsoft_FStar_Tc_Env.env ) ( elt  :  Microsoft_FStar_Absyn_Syntax.sigelt ) -> (let env = (Microsoft_FStar_Tc_Env.push_sigelt en elt)
in (let _36_3200 = (Microsoft_FStar_Tc_Env_Mksolver_t.encode_sig env.Microsoft_FStar_Tc_Env.solver env elt)
in env)))
in (let en = (Microsoft_FStar_Tc_Env.set_current_module en m.Microsoft_FStar_Absyn_Syntax.name)
in (let _52_13950 = (Support.List.fold_left do_sigelt en m.Microsoft_FStar_Absyn_Syntax.exports)
in (Microsoft_FStar_Tc_Env.finish_module _52_13950 m)))))

let check_module = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( m  :  Microsoft_FStar_Absyn_Syntax.modul ) -> (let _36_3205 = (match ((let _52_13956 = (let _52_13955 = (Support.ST.read Microsoft_FStar_Options.debug)
in (Support.List.length _52_13955))
in (_52_13956 <> 0))) with
| true -> begin
(let _52_13957 = (Microsoft_FStar_Absyn_Print.sli m.Microsoft_FStar_Absyn_Syntax.name)
in (Support.Microsoft.FStar.Util.fprint2 "Checking %s: %s\n" (match (m.Microsoft_FStar_Absyn_Syntax.is_interface) with
| true -> begin
"i\'face"
end
| false -> begin
"module"
end) _52_13957))
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
(let c_file_name = (let _52_13963 = (let _52_13962 = (let _52_13960 = (let _52_13959 = (let _52_13958 = (Microsoft_FStar_Options.get_fstar_home ())
in (Support.String.strcat _52_13958 "/"))
in (Support.String.strcat _52_13959 Microsoft_FStar_Options.cache_dir))
in (Support.String.strcat _52_13960 "/"))
in (let _52_13961 = (Microsoft_FStar_Absyn_Syntax.text_of_lid m.Microsoft_FStar_Absyn_Syntax.name)
in (Support.String.strcat _52_13962 _52_13961)))
in (Support.String.strcat _52_13963 ".cache"))
in (let _36_3212 = (let _52_13966 = (let _52_13965 = (let _52_13964 = (Microsoft_FStar_Absyn_Syntax.text_of_lid m.Microsoft_FStar_Absyn_Syntax.name)
in (Support.String.strcat "Serializing module " _52_13964))
in (Support.String.strcat _52_13965 "\n"))
in (Support.Microsoft.FStar.Util.print_string _52_13966))
in (let _52_13967 = (Support.Microsoft.FStar.Util.get_owriter c_file_name)
in (Microsoft_FStar_Absyn_SSyntax.serialize_modul _52_13967 m))))
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
(let _52_13968 = (Microsoft_FStar_Absyn_Print.modul_to_string m)
in (Support.Microsoft.FStar.Util.fprint1 "%s\n" _52_13968))
end
| false -> begin
()
end)
in (match (m.Microsoft_FStar_Absyn_Syntax.is_interface) with
| true -> begin
((m)::[], env)
end
| false -> begin
((m)::[], env)
end))
end))))




