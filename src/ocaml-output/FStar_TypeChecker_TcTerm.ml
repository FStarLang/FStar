
open Prims

let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _60_7 = env
in {FStar_TypeChecker_Env.solver = _60_7.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _60_7.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _60_7.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _60_7.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _60_7.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _60_7.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _60_7.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _60_7.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _60_7.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _60_7.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _60_7.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _60_7.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _60_7.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _60_7.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _60_7.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _60_7.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _60_7.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _60_7.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _60_7.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _60_7.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _60_7.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _60_7.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _60_7.FStar_TypeChecker_Env.qname_and_index}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _60_10 = env
in {FStar_TypeChecker_Env.solver = _60_10.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _60_10.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _60_10.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _60_10.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _60_10.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _60_10.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _60_10.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _60_10.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _60_10.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _60_10.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _60_10.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _60_10.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _60_10.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _60_10.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _60_10.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _60_10.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _60_10.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _60_10.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _60_10.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _60_10.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _60_10.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _60_10.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _60_10.FStar_TypeChecker_Env.qname_and_index}))


let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (

let r = if (tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
v.FStar_Syntax_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos tl.FStar_Syntax_Syntax.pos)
end
in (let _158_12 = (let _158_11 = (FStar_Syntax_Syntax.as_arg v)
in (let _158_10 = (let _158_9 = (FStar_Syntax_Syntax.as_arg tl)
in (_158_9)::[])
in (_158_11)::_158_10))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _158_12 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _60_1 -> (match (_60_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _60_20 -> begin
false
end))


let steps = (fun env -> (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[])


let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Beta)::[]) env t))


let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize (steps env) env t))


let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (FStar_TypeChecker_Normalize.normalize_comp (steps env) env c))


let check_no_escape : FStar_Syntax_Syntax.term Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun head_opt env fvs kt -> (

let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
t
end
| _60_37 -> begin
(

let t = if try_norm then begin
(norm env t)
end else begin
t
end
in (

let fvs' = (FStar_Syntax_Free.names t)
in (match ((FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)) with
| None -> begin
t
end
| Some (x) -> begin
if (not (try_norm)) then begin
(aux true t)
end else begin
(

let fail = (fun _60_45 -> (match (()) with
| () -> begin
(

let msg = (match (head_opt) with
| None -> begin
(let _158_43 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _158_43))
end
| Some (head) -> begin
(let _158_45 = (FStar_Syntax_Print.bv_to_string x)
in (let _158_44 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _158_45 _158_44)))
end)
in (let _158_48 = (let _158_47 = (let _158_46 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (_158_46)))
in FStar_Syntax_Syntax.Error (_158_47))
in (Prims.raise _158_48)))
end))
in (

let s = (let _158_50 = (let _158_49 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _158_49))
in (FStar_TypeChecker_Util.new_uvar env _158_50))
in (match ((FStar_TypeChecker_Rel.try_teq env t s)) with
| Some (g) -> begin
(

let _60_53 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in s)
end
| _60_56 -> begin
(fail ())
end)))
end
end)))
end))
in (aux false kt)))


let push_binding = (fun env b -> (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))


let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.subst_t = (fun s b v -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
s
end else begin
(FStar_Syntax_Syntax.NT ((((Prims.fst b)), (v))))::s
end)


let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (

let _60_64 = lc
in {FStar_Syntax_Syntax.eff_name = _60_64.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _60_64.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _60_66 -> (match (()) with
| () -> begin
(let _158_64 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _158_64 t))
end))}))


let memo_tk : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun e t -> (

let _60_69 = (FStar_ST.op_Colon_Equals e.FStar_Syntax_Syntax.tk (Some (t.FStar_Syntax_Syntax.n)))
in e))


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let should_return = (fun t -> (match ((let _158_79 = (FStar_Syntax_Subst.compress t)
in _158_79.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_60_78, c) -> begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(

let t = (FStar_All.pipe_left FStar_Syntax_Util.unrefine (FStar_Syntax_Util.comp_result c))
in (match ((let _158_80 = (FStar_Syntax_Subst.compress t)
in _158_80.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (_60_86) -> begin
false
end
| _60_89 -> begin
true
end))
end else begin
false
end
end
| _60_91 -> begin
true
end))
in (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _158_81 = if ((not ((should_return t))) || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _158_81))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _60_120 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(let _158_82 = (memo_tk e t)
in ((_158_82), (lc), (guard)))
end
| Some (t') -> begin
(

let _60_101 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _158_84 = (FStar_Syntax_Print.term_to_string t)
in (let _158_83 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _158_84 _158_83)))
end else begin
()
end
in (

let _60_105 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_60_105) with
| (e, lc) -> begin
(

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _60_109 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_60_109) with
| (e, g) -> begin
(

let _60_110 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _158_88 = (FStar_Syntax_Print.term_to_string t)
in (let _158_87 = (FStar_Syntax_Print.term_to_string t')
in (let _158_86 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (let _158_85 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_Util.print4 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n" _158_88 _158_87 _158_86 _158_85)))))
end else begin
()
end
in (

let msg = if (FStar_TypeChecker_Rel.is_trivial g) then begin
None
end else begin
(FStar_All.pipe_left (fun _158_98 -> Some (_158_98)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
end
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let _60_116 = (FStar_TypeChecker_Util.strengthen_precondition msg env e lc g)
in (match (_60_116) with
| (lc, g) -> begin
(let _158_99 = (memo_tk e t')
in ((_158_99), ((set_lcomp_result lc t')), (g)))
end)))))
end)))
end)))
end)
in (match (_60_120) with
| (e, lc, g) -> begin
(

let _60_121 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _158_100 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _158_100))
end else begin
()
end
in ((e), (lc), (g)))
end))))))


let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
((e), (lc), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (t) -> begin
(

let _60_131 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_60_131) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _60_136 -> (match (_60_136) with
| (e, c) -> begin
(

let expected_c_opt = (match (copt) with
| Some (_60_138) -> begin
copt
end
| None -> begin
if ((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Syntax_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) then begin
(let _158_113 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (_158_113))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
if (FStar_Syntax_Util.is_pure_comp c) then begin
(let _158_114 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (_158_114))
end else begin
if (FStar_Syntax_Util.is_pure_or_ghost_comp c) then begin
(let _158_115 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (_158_115))
end else begin
None
end
end
end
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _158_116 = (norm_c env c)
in ((e), (_158_116), (FStar_TypeChecker_Rel.trivial_guard)))
end
| Some (expected_c) -> begin
(

let _60_145 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _158_119 = (FStar_Syntax_Print.term_to_string e)
in (let _158_118 = (FStar_Syntax_Print.comp_to_string c)
in (let _158_117 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _158_119 _158_118 _158_117))))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _60_148 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _158_122 = (FStar_Syntax_Print.term_to_string e)
in (let _158_121 = (FStar_Syntax_Print.comp_to_string c)
in (let _158_120 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _158_122 _158_121 _158_120))))
end else begin
()
end
in (

let _60_154 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_60_154) with
| (e, _60_152, g) -> begin
(

let g = (let _158_123 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _158_123 "could not prove post-condition" g))
in (

let _60_156 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _158_125 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _158_124 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _158_125 _158_124)))
end else begin
()
end
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e (FStar_Syntax_Util.comp_effect_name c) (FStar_Syntax_Util.comp_effect_name expected_c) (FStar_Syntax_Util.comp_result c))
in ((e), (expected_c), (g)))))
end)))))
end))
end))


let no_logical_guard = (fun env _60_163 -> (match (_60_163) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
((te), (kt), (f))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _158_131 = (let _158_130 = (let _158_129 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _158_128 = (FStar_TypeChecker_Env.get_range env)
in ((_158_129), (_158_128))))
in FStar_Syntax_Syntax.Error (_158_130))
in (Prims.raise _158_131))
end)
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _158_134 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _158_134))
end))


let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = _60_189; FStar_Syntax_Syntax.effect_name = _60_187; FStar_Syntax_Syntax.result_typ = _60_185; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, _60_179))::[]; FStar_Syntax_Syntax.flags = _60_176}) -> begin
(

let pat_vars = (let _158_139 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env pats)
in (FStar_Syntax_Free.names _158_139))
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _60_196 -> (match (_60_196) with
| (b, _60_195) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _60_200) -> begin
(let _158_142 = (let _158_141 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" _158_141))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _158_142))
end))
end
| _60_204 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end)


let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun env actuals expected_c -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
env.FStar_TypeChecker_Env.letrecs
end else begin
(match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let env = (

let _60_211 = env
in {FStar_TypeChecker_Env.solver = _60_211.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _60_211.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _60_211.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _60_211.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _60_211.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _60_211.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _60_211.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _60_211.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _60_211.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _60_211.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _60_211.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _60_211.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _60_211.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _60_211.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _60_211.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _60_211.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _60_211.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _60_211.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _60_211.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _60_211.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _60_211.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _60_211.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _60_211.FStar_TypeChecker_Env.qname_and_index})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _60_223 -> (match (_60_223) with
| (b, _60_222) -> begin
(

let t = (let _158_156 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _158_156))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _60_232 -> begin
(let _158_157 = (FStar_Syntax_Syntax.bv_to_name b)
in (_158_157)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let _60_238 = (FStar_Syntax_Util.head_and_args dec)
in (match (_60_238) with
| (head, _60_237) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _60_242 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let cflags = (FStar_Syntax_Util.comp_flags c)
in (match ((FStar_All.pipe_right cflags (FStar_List.tryFind (fun _60_2 -> (match (_60_2) with
| FStar_Syntax_Syntax.DECREASES (_60_246) -> begin
true
end
| _60_249 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _60_254 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| _60_259 -> begin
(mk_lex_list xs)
end))
end)))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun _60_264 -> (match (_60_264) with
| (l, t) -> begin
(match ((let _158_163 = (FStar_Syntax_Subst.compress t)
in _158_163.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _60_271 -> (match (_60_271) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _158_167 = (let _158_166 = (let _158_165 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_158_165))
in (FStar_Syntax_Syntax.new_bv _158_166 x.FStar_Syntax_Syntax.sort))
in ((_158_167), (imp)))
end else begin
((x), (imp))
end
end))))
in (

let _60_275 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_60_275) with
| (formals, c) -> begin
(

let dec = (decreases_clause formals c)
in (

let precedes = (let _158_171 = (let _158_170 = (FStar_Syntax_Syntax.as_arg dec)
in (let _158_169 = (let _158_168 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_158_168)::[])
in (_158_170)::_158_169))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _158_171 None r))
in (

let _60_282 = (FStar_Util.prefix formals)
in (match (_60_282) with
| (bs, (last, imp)) -> begin
(

let last = (

let _60_283 = last
in (let _158_172 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _60_283.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _60_283.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _158_172}))
in (

let refined_formals = (FStar_List.append bs ((((last), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (

let _60_288 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _158_175 = (FStar_Syntax_Print.lbname_to_string l)
in (let _158_174 = (FStar_Syntax_Print.term_to_string t)
in (let _158_173 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _158_175 _158_174 _158_173))))
end else begin
()
end
in ((l), (t'))))))
end))))
end)))
end
| _60_291 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Annotated type of \'let rec\' must be an arrow"), (t.FStar_Syntax_Syntax.pos)))))
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end)
end)


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let _60_294 = env
in {FStar_TypeChecker_Env.solver = _60_294.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _60_294.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _60_294.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _60_294.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _60_294.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _60_294.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _60_294.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _60_294.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _60_294.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _60_294.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _60_294.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _60_294.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _60_294.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _60_294.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _60_294.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _60_294.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _60_294.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _60_294.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _60_294.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _60_294.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _60_294.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _60_294.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _60_294.FStar_TypeChecker_Env.qname_and_index}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (

let _60_299 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _158_245 = (let _158_243 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _158_243))
in (let _158_244 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _158_245 _158_244)))
end else begin
()
end
in (

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_60_303) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let _60_344 = (tc_tot_or_gtot_term env e)
in (match (_60_344) with
| (e, c, g) -> begin
(

let g = (

let _60_345 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _60_345.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _60_345.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _60_345.FStar_TypeChecker_Env.implicits})
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let _60_355 = (FStar_Syntax_Util.type_u ())
in (match (_60_355) with
| (t, u) -> begin
(

let _60_359 = (tc_check_tot_or_gtot_term env e t)
in (match (_60_359) with
| (e, c, g) -> begin
(

let _60_366 = (

let _60_363 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_60_363) with
| (env, _60_362) -> begin
(tc_pats env pats)
end))
in (match (_60_366) with
| (pats, g') -> begin
(

let g' = (

let _60_367 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _60_367.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _60_367.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _60_367.FStar_TypeChecker_Env.implicits})
in (let _158_250 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_pattern (pats))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _158_249 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((_158_250), (c), (_158_249)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _158_251 = (FStar_Syntax_Subst.compress e)
in _158_251.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_60_376, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _60_383; FStar_Syntax_Syntax.lbtyp = _60_381; FStar_Syntax_Syntax.lbeff = _60_379; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _60_394 = (let _158_252 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _158_252 e1))
in (match (_60_394) with
| (e1, c1, g1) -> begin
(

let _60_398 = (tc_term env e2)
in (match (_60_398) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((None), (c2)))
in (

let e = (let _158_257 = (let _158_256 = (let _158_255 = (let _158_254 = (let _158_253 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_TypeChecker_Common.t_unit), (e1)))
in (_158_253)::[])
in ((false), (_158_254)))
in ((_158_255), (e2)))
in FStar_Syntax_Syntax.Tm_let (_158_256))
in (FStar_Syntax_Syntax.mk _158_257 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _158_258 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e), (c), (_158_258))))))
end))
end))
end
| _60_403 -> begin
(

let _60_407 = (tc_term env e)
in (match (_60_407) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (_60_411)) -> begin
(tc_term env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let _60_422 = (tc_term env e)
in (match (_60_422) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (m)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _60_428) -> begin
(

let _60_434 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_60_434) with
| (env0, _60_433) -> begin
(

let _60_439 = (tc_comp env0 expected_c)
in (match (_60_439) with
| (expected_c, _60_437, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (

let _60_444 = (let _158_259 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term _158_259 e))
in (match (_60_444) with
| (e, c', g') -> begin
(

let _60_448 = (let _158_261 = (let _158_260 = (c'.FStar_Syntax_Syntax.comp ())
in ((e), (_158_260)))
in (check_expected_effect env0 (Some (expected_c)) _158_261))
in (match (_60_448) with
| (e, expected_c, g'') -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t_res)), (Some ((FStar_Syntax_Util.comp_effect_name expected_c)))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let lc = (FStar_Syntax_Util.lcomp_of_comp expected_c)
in (

let f = (let _158_262 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _158_262))
in (

let _60_455 = (comp_check_expected_typ env e lc)
in (match (_60_455) with
| (e, c, f2) -> begin
(let _158_263 = (FStar_TypeChecker_Rel.conj_guard f f2)
in ((e), (c), (_158_263)))
end)))))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _60_460) -> begin
(

let _60_465 = (FStar_Syntax_Util.type_u ())
in (match (_60_465) with
| (k, u) -> begin
(

let _60_470 = (tc_check_tot_or_gtot_term env t k)
in (match (_60_470) with
| (t, _60_468, f) -> begin
(

let _60_474 = (let _158_264 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _158_264 e))
in (match (_60_474) with
| (e, c, g) -> begin
(

let _60_478 = (let _158_268 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _60_475 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _158_268 e c f))
in (match (_60_478) with
| (c, f) -> begin
(

let _60_482 = (let _158_269 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t)), (Some (c.FStar_Syntax_Syntax.eff_name))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _158_269 c))
in (match (_60_482) with
| (e, c, f2) -> begin
(let _158_271 = (let _158_270 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _158_270))
in ((e), (c), (_158_271)))
end))
end))
end))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (a)::(hd)::rest)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_)); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (a)::(hd)::rest)) -> begin
(

let rest = (hd)::rest
in (

let _60_518 = (FStar_Syntax_Util.head_and_args top)
in (match (_60_518) with
| (unary_op, _60_517) -> begin
(

let head = (let _158_272 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (Prims.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) None _158_272))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), (rest)))) None top.FStar_Syntax_Syntax.pos)
in (tc_term env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _60_526; FStar_Syntax_Syntax.pos = _60_524; FStar_Syntax_Syntax.vars = _60_522}, ((e, aqual))::[]) -> begin
(

let _60_536 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end else begin
()
end
in (

let _60_545 = (

let _60_541 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_60_541) with
| (env0, _60_540) -> begin
(tc_term env0 e)
end))
in (match (_60_545) with
| (e, c, g) -> begin
(

let _60_549 = (FStar_Syntax_Util.head_and_args top)
in (match (_60_549) with
| (reify_op, _60_548) -> begin
(

let u_c = (

let _60_555 = (tc_term env c.FStar_Syntax_Syntax.res_typ)
in (match (_60_555) with
| (_60_551, c, _60_554) -> begin
(match ((let _158_273 = (FStar_Syntax_Subst.compress c.FStar_Syntax_Syntax.res_typ)
in _158_273.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| _60_559 -> begin
(FStar_All.failwith "Unexpected result type of computation")
end)
end))
in (

let repr = (FStar_TypeChecker_Util.reify_comp env c u_c)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e), (aqual)))::[])))) (Some (repr.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let c = (let _158_274 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right _158_274 FStar_Syntax_Util.lcomp_of_comp))
in (

let _60_567 = (comp_check_expected_typ env e c)
in (match (_60_567) with
| (e, c, g') -> begin
(let _158_275 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), (c), (_158_275)))
end))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.tk = _60_573; FStar_Syntax_Syntax.pos = _60_571; FStar_Syntax_Syntax.vars = _60_569}, ((e, aqual))::[]) -> begin
(

let _60_584 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end else begin
()
end
in (

let no_reflect = (fun _60_587 -> (match (()) with
| () -> begin
(let _158_280 = (let _158_279 = (let _158_278 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((_158_278), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_158_279))
in (Prims.raise _158_280))
end))
in (

let _60_591 = (FStar_Syntax_Util.head_and_args top)
in (match (_60_591) with
| (reflect_op, _60_590) -> begin
(match ((FStar_TypeChecker_Env.effect_decl_opt env l)) with
| None -> begin
(no_reflect ())
end
| Some (ed) -> begin
if (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers FStar_Syntax_Syntax.contains_reflectable))) then begin
(no_reflect ())
end else begin
(

let _60_597 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_60_597) with
| (env_no_ex, topt) -> begin
(

let _60_625 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (let _158_286 = (let _158_285 = (let _158_284 = (let _158_283 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _158_282 = (let _158_281 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (_158_281)::[])
in (_158_283)::_158_282))
in ((repr), (_158_284)))
in FStar_Syntax_Syntax.Tm_app (_158_285))
in (FStar_Syntax_Syntax.mk _158_286 None top.FStar_Syntax_Syntax.pos))
in (

let _60_605 = (let _158_288 = (let _158_287 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _158_287 Prims.fst))
in (tc_tot_or_gtot_term _158_288 t))
in (match (_60_605) with
| (t, _60_603, g) -> begin
(match ((let _158_289 = (FStar_Syntax_Subst.compress t)
in _158_289.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_60_607, ((res, _60_614))::((wp, _60_610))::[]) -> begin
((t), (res), (wp), (g))
end
| _60_620 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))
in (match (_60_625) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let _60_639 = (

let _60_629 = (tc_tot_or_gtot_term env_no_ex e)
in (match (_60_629) with
| (e, c, g) -> begin
(

let _60_630 = if (let _158_290 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation _158_290)) then begin
(FStar_TypeChecker_Errors.add_errors env (((("Expected Tot, got a GTot computation"), (e.FStar_Syntax_Syntax.pos)))::[]))
end else begin
()
end
in (match ((FStar_TypeChecker_Rel.try_teq env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)) with
| None -> begin
(

let _60_633 = (let _158_295 = (let _158_294 = (let _158_293 = (let _158_292 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _158_291 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" _158_292 _158_291)))
in ((_158_293), (e.FStar_Syntax_Syntax.pos)))
in (_158_294)::[])
in (FStar_TypeChecker_Errors.add_errors env _158_295))
in (let _158_296 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e), (_158_296))))
end
| Some (g') -> begin
(let _158_298 = (let _158_297 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' _158_297))
in ((e), (_158_298)))
end))
end))
in (match (_60_639) with
| (e, g) -> begin
(

let c = (let _158_304 = (let _158_303 = (let _158_302 = (let _158_299 = (env.FStar_TypeChecker_Env.universe_of env res_typ)
in (_158_299)::[])
in (let _158_301 = (let _158_300 = (FStar_Syntax_Syntax.as_arg wp)
in (_158_300)::[])
in {FStar_Syntax_Syntax.comp_univs = _158_302; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = _158_301; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp _158_303))
in (FStar_All.pipe_right _158_304 FStar_Syntax_Util.lcomp_of_comp))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e), (aqual)))::[])))) (Some (res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let _60_645 = (comp_check_expected_typ env e c)
in (match (_60_645) with
| (e, c, g') -> begin
(let _158_305 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e), (c), (_158_305)))
end))))
end))
end))
end))
end
end)
end))))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let env0 = env
in (

let env = (let _158_307 = (let _158_306 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _158_306 Prims.fst))
in (FStar_All.pipe_right _158_307 instantiate_both))
in (

let _60_652 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _158_309 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _158_308 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _158_309 _158_308)))
end else begin
()
end
in (

let _60_657 = (tc_term (no_inst env) head)
in (match (_60_657) with
| (head, chead, g_head) -> begin
(

let _60_661 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _158_310 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _158_310))
end else begin
(let _158_311 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _158_311))
end
in (match (_60_661) with
| (e, c, g) -> begin
(

let _60_662 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _158_312 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _158_312))
end else begin
()
end
in (

let c = if (((FStar_TypeChecker_Env.should_verify env) && (not ((FStar_Syntax_Util.is_lcomp_partial_return c)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)) then begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e c)
end else begin
c
end
in (

let _60_668 = (comp_check_expected_typ env0 e c)
in (match (_60_668) with
| (e, c, g') -> begin
(

let gimp = (match ((let _158_313 = (FStar_Syntax_Subst.compress head)
in _158_313.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _60_671) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e), (c.FStar_Syntax_Syntax.res_typ), (head.FStar_Syntax_Syntax.pos))
in (

let _60_675 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _60_675.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _60_675.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _60_675.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _60_678 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (

let gres = (let _158_314 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _158_314))
in (

let _60_681 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _158_316 = (FStar_Syntax_Print.term_to_string e)
in (let _158_315 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" _158_316 _158_315)))
end else begin
()
end
in ((e), (c), (gres)))))
end))))
end))
end)))))
end
| FStar_Syntax_Syntax.Tm_match (e1, eqns) -> begin
(

let _60_689 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_60_689) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let _60_694 = (tc_term env1 e1)
in (match (_60_694) with
| (e1, c1, g1) -> begin
(

let _60_705 = (match (topt) with
| Some (t) -> begin
((env), (t))
end
| None -> begin
(

let _60_701 = (FStar_Syntax_Util.type_u ())
in (match (_60_701) with
| (k, _60_700) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _158_317 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in ((_158_317), (res_t))))
end))
end)
in (match (_60_705) with
| (env_branches, res_t) -> begin
(

let _60_706 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _158_318 = (FStar_Syntax_Print.term_to_string res_t)
in (FStar_Util.print1 "Tm_match: expected type of branches is %s\n" _158_318))
end else begin
()
end
in (

let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let _60_724 = (

let _60_721 = (FStar_List.fold_right (fun _60_715 _60_718 -> (match (((_60_715), (_60_718))) with
| ((_60_711, f, c, g), (caccum, gaccum)) -> begin
(let _158_321 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (_158_321)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_60_721) with
| (cases, g) -> begin
(let _158_322 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in ((_158_322), (g)))
end))
in (match (_60_724) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (guard_x)), (c_branches)))
in (

let e = (

let mk_match = (fun scrutinee -> (

let scrutinee = (FStar_TypeChecker_Util.maybe_lift env scrutinee c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let branches = (FStar_All.pipe_right t_eqns (FStar_List.map (fun _60_738 -> (match (_60_738) with
| ((pat, wopt, br), _60_734, lc, _60_737) -> begin
(let _158_326 = (FStar_TypeChecker_Util.maybe_lift env br lc.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ)
in ((pat), (wopt), (_158_326)))
end))))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (Some (cres.FStar_Syntax_Syntax.eff_name))))) None e.FStar_Syntax_Syntax.pos)))))
in if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c1.FStar_Syntax_Syntax.eff_name) then begin
(mk_match e1)
end else begin
(

let e_match = (let _158_327 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match _158_327))
in (

let lb = (let _158_328 = (FStar_TypeChecker_Env.norm_eff_name env c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = _158_328; FStar_Syntax_Syntax.lbdef = e1})
in (

let e = (let _158_333 = (let _158_332 = (let _158_331 = (let _158_330 = (let _158_329 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (_158_329)::[])
in (FStar_Syntax_Subst.close _158_330 e_match))
in ((((false), ((lb)::[]))), (_158_331)))
in FStar_Syntax_Syntax.Tm_let (_158_332))
in (FStar_Syntax_Syntax.mk _158_333 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ))))
end)
in (

let _60_745 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _158_336 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _158_335 = (let _158_334 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _158_334))
in (FStar_Util.print2 "(%s) comp type = %s\n" _158_336 _158_335)))
end else begin
()
end
in (let _158_337 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e), (cres), (_158_337))))))
end)))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_60_757); FStar_Syntax_Syntax.lbunivs = _60_755; FStar_Syntax_Syntax.lbtyp = _60_753; FStar_Syntax_Syntax.lbeff = _60_751; FStar_Syntax_Syntax.lbdef = _60_749})::[]), _60_763) -> begin
(

let _60_766 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _158_338 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _158_338))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _60_770), _60_773) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_60_788); FStar_Syntax_Syntax.lbunivs = _60_786; FStar_Syntax_Syntax.lbtyp = _60_784; FStar_Syntax_Syntax.lbeff = _60_782; FStar_Syntax_Syntax.lbdef = _60_780})::_60_778), _60_794) -> begin
(

let _60_797 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _158_339 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _158_339))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _60_801), _60_804) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let _60_818 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_60_818) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _158_353 = (let _158_352 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _158_352))
in FStar_Util.Inr (_158_353))
end
in (

let is_data_ctor = (fun _60_3 -> (match (_60_3) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _60_828 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _158_359 = (let _158_358 = (let _158_357 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _158_356 = (FStar_TypeChecker_Env.get_range env)
in ((_158_357), (_158_356))))
in FStar_Syntax_Syntax.Error (_158_358))
in (Prims.raise _158_359))
end else begin
(value_check_expected_typ env e tc implicits)
end))
end)))
in (

let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _158_361 = (let _158_360 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" _158_360))
in (FStar_All.failwith _158_361))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (match ((let _158_362 = (FStar_Syntax_Subst.compress t1)
in _158_362.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_60_839) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _60_842 -> begin
(

let imp = (("uvar in term"), (env), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let _60_844 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _60_844.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _60_844.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _60_844.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _60_859 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(

let _60_852 = (FStar_Syntax_Util.type_u ())
in (match (_60_852) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
end))
end
| Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end)
in (match (_60_859) with
| (t, _60_857, g0) -> begin
(

let _60_864 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (_60_864) with
| (e, _60_862, g1) -> begin
(let _158_365 = (let _158_363 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right _158_363 FStar_Syntax_Util.lcomp_of_comp))
in (let _158_364 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e), (_158_365), (_158_364))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = if env.FStar_TypeChecker_Env.use_bv_sorts then begin
x.FStar_Syntax_Syntax.sort
end else begin
(FStar_TypeChecker_Env.lookup_bv env x)
end
in (

let e = (FStar_Syntax_Syntax.bv_to_name (

let _60_868 = x
in {FStar_Syntax_Syntax.ppname = _60_868.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _60_868.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let _60_874 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_60_874) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _158_367 = (let _158_366 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _158_366))
in FStar_Util.Inr (_158_367))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _60_881; FStar_Syntax_Syntax.pos = _60_879; FStar_Syntax_Syntax.vars = _60_877}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let _60_891 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_60_891) with
| (us', t) -> begin
(

let _60_898 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _158_370 = (let _158_369 = (let _158_368 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (_158_368)))
in FStar_Syntax_Syntax.Error (_158_369))
in (Prims.raise _158_370))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _60_897 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (

let fv' = (

let _60_900 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _60_902 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _60_902.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _60_902.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _60_900.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _60_900.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _158_373 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _158_373 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let _60_910 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_60_910) with
| (us, t) -> begin
(

let _60_911 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Range"))) then begin
(let _158_383 = (let _158_374 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Syntax_Print.lid_to_string _158_374))
in (let _158_382 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _158_381 = (let _158_376 = (let _158_375 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.range_of_lid _158_375))
in (FStar_Range.string_of_range _158_376))
in (let _158_380 = (let _158_378 = (let _158_377 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.range_of_lid _158_377))
in (FStar_Range.string_of_use_range _158_378))
in (let _158_379 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print5 "Lookup up fvar %s at location %s (lid range = %s, %s); got type %s" _158_383 _158_382 _158_381 _158_380 _158_379))))))
end else begin
()
end
in (

let fv' = (

let _60_913 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _60_915 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _60_915.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _60_915.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _60_913.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _60_913.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _158_384 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _158_384 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let t = (tc_constant top.FStar_Syntax_Syntax.pos c)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _60_929 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_60_929) with
| (bs, c) -> begin
(

let env0 = env
in (

let _60_934 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_60_934) with
| (env, _60_933) -> begin
(

let _60_939 = (tc_binders env bs)
in (match (_60_939) with
| (bs, env, g, us) -> begin
(

let _60_943 = (tc_comp env c)
in (match (_60_943) with
| (c, uc, f) -> begin
(

let e = (

let _60_944 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _60_944.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _60_944.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _60_944.FStar_Syntax_Syntax.vars})
in (

let _60_947 = (check_smt_pat env e bs c)
in (

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _158_385 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _158_385))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u = (tc_universe env u)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) None top.FStar_Syntax_Syntax.pos)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let _60_963 = (let _158_387 = (let _158_386 = (FStar_Syntax_Syntax.mk_binder x)
in (_158_386)::[])
in (FStar_Syntax_Subst.open_term _158_387 phi))
in (match (_60_963) with
| (x, phi) -> begin
(

let env0 = env
in (

let _60_968 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_60_968) with
| (env, _60_967) -> begin
(

let _60_973 = (let _158_388 = (FStar_List.hd x)
in (tc_binder env _158_388))
in (match (_60_973) with
| (x, env, f1, u) -> begin
(

let _60_974 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _158_391 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _158_390 = (FStar_Syntax_Print.term_to_string phi)
in (let _158_389 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _158_391 _158_390 _158_389))))
end else begin
()
end
in (

let _60_979 = (FStar_Syntax_Util.type_u ())
in (match (_60_979) with
| (t_phi, _60_978) -> begin
(

let _60_984 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_60_984) with
| (phi, _60_982, f2) -> begin
(

let e = (

let _60_985 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _60_985.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _60_985.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _60_985.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _158_392 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _158_392))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _60_993) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (

let _60_999 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _158_393 = (FStar_Syntax_Print.term_to_string (

let _60_997 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))); FStar_Syntax_Syntax.tk = _60_997.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _60_997.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _60_997.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _158_393))
end else begin
()
end
in (

let _60_1003 = (FStar_Syntax_Subst.open_term bs body)
in (match (_60_1003) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _60_1005 -> begin
(let _158_396 = (let _158_395 = (FStar_Syntax_Print.term_to_string top)
in (let _158_394 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" _158_395 _158_394)))
in (FStar_All.failwith _158_396))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_60_1010) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_60_1013, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_60_1018, Some (_60_1020)) -> begin
(FStar_All.failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (_60_1025) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_60_1028) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_60_1031) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_60_1035) -> begin
FStar_TypeChecker_Common.t_range
end
| _60_1038 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _60_1044) -> begin
(

let _60_1049 = (FStar_Syntax_Util.type_u ())
in (match (_60_1049) with
| (k, u) -> begin
(

let _60_1054 = (tc_check_tot_or_gtot_term env t k)
in (match (_60_1054) with
| (t, _60_1052, g) -> begin
(let _158_401 = (FStar_Syntax_Syntax.mk_Total' t (Some (u)))
in ((_158_401), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t, _60_1057) -> begin
(

let _60_1062 = (FStar_Syntax_Util.type_u ())
in (match (_60_1062) with
| (k, u) -> begin
(

let _60_1067 = (tc_check_tot_or_gtot_term env t k)
in (match (_60_1067) with
| (t, _60_1065, g) -> begin
(let _158_402 = (FStar_Syntax_Syntax.mk_GTotal' t (Some (u)))
in ((_158_402), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (

let head = (match (c.FStar_Syntax_Syntax.comp_univs) with
| [] -> begin
head
end
| us -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((head), (us)))) None c0.FStar_Syntax_Syntax.pos)
end)
in (

let tc = (let _158_404 = (let _158_403 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_158_403)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _158_404 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let _60_1079 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_60_1079) with
| (tc, _60_1077, f) -> begin
(

let _60_1082 = (FStar_Syntax_Util.head_and_args tc)
in (match (_60_1082) with
| (head, args) -> begin
(

let comp_univs = (match ((let _158_405 = (FStar_Syntax_Subst.compress head)
in _158_405.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (_60_1084, us) -> begin
us
end
| _60_1089 -> begin
[]
end)
in (

let _60_1094 = (FStar_Syntax_Util.head_and_args tc)
in (match (_60_1094) with
| (_60_1092, args) -> begin
(

let _60_1097 = (let _158_407 = (FStar_List.hd args)
in (let _158_406 = (FStar_List.tl args)
in ((_158_407), (_158_406))))
in (match (_60_1097) with
| (res, args) -> begin
(

let _60_1113 = (let _158_409 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _60_4 -> (match (_60_4) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _60_1104 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_60_1104) with
| (env, _60_1103) -> begin
(

let _60_1109 = (tc_tot_or_gtot_term env e)
in (match (_60_1109) with
| (e, _60_1107, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e)), (g))
end))
end))
end
| f -> begin
((f), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right _158_409 FStar_List.unzip))
in (match (_60_1113) with
| (flags, guards) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (Prims.fst res))
in (

let c = (FStar_Syntax_Syntax.mk_Comp (

let _60_1115 = c
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = _60_1115.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _60_1115.FStar_Syntax_Syntax.flags}))
in (

let u_c = (match ((FStar_TypeChecker_Util.effect_repr env c u)) with
| None -> begin
u
end
| Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end)
in (let _158_410 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((c), (u_c), (_158_410))))))
end))
end))
end)))
end))
end)))))
end)))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_60_1128) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _158_415 = (aux u)
in FStar_Syntax_Syntax.U_succ (_158_415))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _158_416 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_158_416))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
u
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _158_417 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _158_417 Prims.snd))
end
| _60_1143 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _158_426 = (let _158_425 = (let _158_424 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in ((_158_424), (top.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_158_425))
in (Prims.raise _158_426)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun _60_1161 bs bs_expected -> (match (_60_1161) with
| (env, out, g, subst) -> begin
(match (((bs), (bs_expected))) with
| ([], []) -> begin
((env), ((FStar_List.rev out)), (None), (g), (subst))
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
(

let _60_1192 = (match (((imp), (imp'))) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _158_443 = (let _158_442 = (let _158_441 = (let _158_439 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _158_439))
in (let _158_440 = (FStar_Syntax_Syntax.range_of_bv hd)
in ((_158_441), (_158_440))))
in FStar_Syntax_Syntax.Error (_158_442))
in (Prims.raise _158_443))
end
| _60_1191 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _60_1209 = (match ((let _158_444 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _158_444.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| _60_1197 -> begin
(

let _60_1198 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _158_445 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _158_445))
end else begin
()
end
in (

let _60_1204 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_60_1204) with
| (t, _60_1202, g1) -> begin
(

let g2 = (let _158_447 = (FStar_TypeChecker_Env.get_range env)
in (let _158_446 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _158_447 "Type annotation on parameter incompatible with the expected type" _158_446)))
in (

let g = (let _158_448 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _158_448))
in ((t), (g))))
end)))
end)
in (match (_60_1209) with
| (t, g) -> begin
(

let hd = (

let _60_1210 = hd
in {FStar_Syntax_Syntax.ppname = _60_1210.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _60_1210.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env = (push_binding env b)
in (

let subst = (let _158_449 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _158_449))
in (aux ((env), ((b)::out), (g), (subst)) bs bs_expected))))))
end))))
end
| (rest, []) -> begin
((env), ((FStar_List.rev out)), (Some (FStar_Util.Inl (rest))), (g), (subst))
end
| ([], rest) -> begin
((env), ((FStar_List.rev out)), (Some (FStar_Util.Inr (rest))), (g), (subst))
end)
end))
in (aux ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs bs_expected)))
in (

let rec expected_function_typ = (fun env t0 body -> (match (t0) with
| None -> begin
(

let _60_1231 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _60_1230 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (

let _60_1238 = (tc_binders env bs)
in (match (_60_1238) with
| (bs, envbody, g, _60_1237) -> begin
(

let _60_1256 = (match ((let _158_456 = (FStar_Syntax_Subst.compress body)
in _158_456.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _60_1243) -> begin
(

let _60_1250 = (tc_comp envbody c)
in (match (_60_1250) with
| (c, _60_1248, g') -> begin
(let _158_457 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((Some (c)), (body), (_158_457)))
end))
end
| _60_1252 -> begin
((None), (body), (g))
end)
in (match (_60_1256) with
| (copt, body, g) -> begin
((None), (bs), ([]), (copt), (envbody), (body), (g))
end))
end)))
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm t -> (match ((let _158_462 = (FStar_Syntax_Subst.compress t)
in _158_462.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let _60_1283 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _60_1282 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _60_1290 = (tc_binders env bs)
in (match (_60_1290) with
| (bs, envbody, g, _60_1289) -> begin
(

let _60_1294 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_60_1294) with
| (envbody, _60_1293) -> begin
((Some (((t), (true)))), (bs), ([]), (None), (envbody), (body), (g))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _60_1297) -> begin
(

let _60_1308 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_60_1308) with
| (_60_1301, bs, bs', copt, env, body, g) -> begin
((Some (((t), (false)))), (bs), (bs'), (copt), (env), (body), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _60_1315 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_60_1315) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun _60_1326 c_expected -> (match (_60_1326) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _158_473 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in ((env), (bs), (guard), (_158_473)))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (let _158_474 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _158_474))
in (let _158_475 = (FStar_Syntax_Subst.subst_comp subst c)
in ((env), (bs), (guard), (_158_475))))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(

let c = (FStar_Syntax_Subst.subst_comp subst c_expected)
in if (FStar_Syntax_Util.is_named_tot c) then begin
(

let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _60_1347 = (check_binders env more_bs bs_expected)
in (match (_60_1347) with
| (env, bs', more, guard', subst) -> begin
(let _158_477 = (let _158_476 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env), ((FStar_List.append bs bs')), (more), (_158_476), (subst)))
in (handle_more _158_477 c_expected))
end))
end
| _60_1349 -> begin
(let _158_479 = (let _158_478 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _158_478))
in (fail _158_479 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _158_480 = (check_binders env bs bs_expected)
in (handle_more _158_480 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let _60_1355 = envbody
in {FStar_TypeChecker_Env.solver = _60_1355.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _60_1355.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _60_1355.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _60_1355.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _60_1355.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _60_1355.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _60_1355.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _60_1355.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _60_1355.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _60_1355.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _60_1355.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _60_1355.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _60_1355.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _60_1355.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _60_1355.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _60_1355.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _60_1355.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _60_1355.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _60_1355.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _60_1355.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _60_1355.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _60_1355.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _60_1355.FStar_TypeChecker_Env.qname_and_index})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _60_1360 _60_1363 -> (match (((_60_1360), (_60_1363))) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _60_1369 = (let _158_490 = (let _158_489 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _158_489 Prims.fst))
in (tc_term _158_490 t))
in (match (_60_1369) with
| (t, _60_1366, _60_1368) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l (([]), (t)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _158_491 = (FStar_Syntax_Syntax.mk_binder (

let _60_1373 = x
in {FStar_Syntax_Syntax.ppname = _60_1373.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _60_1373.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_158_491)::letrec_binders)
end
| _60_1376 -> begin
letrec_binders
end)
in ((env), (lb))))
end))
end)) ((envbody), ([])))))))
in (

let _60_1382 = (check_actuals_against_formals env bs bs_expected)
in (match (_60_1382) with
| (envbody, bs, g, c) -> begin
(

let _60_1385 = if (FStar_TypeChecker_Env.should_verify env) then begin
(mk_letrec_env envbody bs c)
end else begin
((envbody), ([]))
end
in (match (_60_1385) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in ((Some (((t), (false)))), (bs), (letrecs), (Some (c)), (envbody), (body), (g)))
end))
end))))
end))
end
| _60_1388 -> begin
if (not (norm)) then begin
(let _158_492 = (unfold_whnf env t)
in (as_function_typ true _158_492))
end else begin
(

let _60_1398 = (expected_function_typ env None body)
in (match (_60_1398) with
| (_60_1390, bs, _60_1393, c_opt, envbody, body, g) -> begin
((Some (((t), (false)))), (bs), ([]), (c_opt), (envbody), (body), (g))
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let _60_1402 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_60_1402) with
| (env, topt) -> begin
(

let _60_1406 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _158_493 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _158_493 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (

let _60_1415 = (expected_function_typ env topt body)
in (match (_60_1415) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let _60_1421 = (tc_term (

let _60_1416 = envbody
in {FStar_TypeChecker_Env.solver = _60_1416.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _60_1416.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _60_1416.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _60_1416.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _60_1416.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _60_1416.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _60_1416.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _60_1416.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _60_1416.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _60_1416.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _60_1416.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _60_1416.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _60_1416.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _60_1416.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _60_1416.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _60_1416.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _60_1416.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _60_1416.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _60_1416.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _60_1416.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _60_1416.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _60_1416.FStar_TypeChecker_Env.qname_and_index}) body)
in (match (_60_1421) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _60_1423 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _158_496 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _158_495 = (let _158_494 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _158_494))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _158_496 _158_495)))
end else begin
()
end
in (

let _60_1430 = (let _158_498 = (let _158_497 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body), (_158_497)))
in (check_expected_effect (

let _60_1425 = envbody
in {FStar_TypeChecker_Env.solver = _60_1425.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _60_1425.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _60_1425.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _60_1425.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _60_1425.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _60_1425.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _60_1425.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _60_1425.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _60_1425.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _60_1425.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _60_1425.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _60_1425.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _60_1425.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _60_1425.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _60_1425.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _60_1425.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _60_1425.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _60_1425.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _60_1425.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _60_1425.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _60_1425.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _60_1425.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _60_1425.FStar_TypeChecker_Env.qname_and_index}) c_opt _158_498))
in (match (_60_1430) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(let _158_499 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _158_499))
end else begin
(

let guard = (let _158_500 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) _158_500))
in guard)
end
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _158_504 = (let _158_503 = (let _158_502 = (FStar_All.pipe_right (FStar_Util.dflt cbody c_opt) FStar_Syntax_Util.lcomp_of_comp)
in (FStar_All.pipe_right _158_502 (fun _158_501 -> FStar_Util.Inl (_158_501))))
in Some (_158_503))
in (FStar_Syntax_Util.abs bs body _158_504))
in (

let _60_1453 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_60_1442) -> begin
((e), (t), (guard))
end
| _60_1445 -> begin
(

let _60_1448 = if use_teq then begin
(let _158_505 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in ((e), (_158_505)))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_60_1448) with
| (e, guard') -> begin
(let _158_506 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((e), (t), (_158_506)))
end))
end))
end
| None -> begin
((e), (tfun_computed), (guard))
end)
in (match (_60_1453) with
| (e, tfun, guard) -> begin
(

let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (

let _60_1457 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_60_1457) with
| (c, g) -> begin
((e), (c), (g))
end)))
end))))))
end))))
end))
end)))
end)))))))
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead ghead args expected_topt -> (

let n_args = (FStar_List.length args)
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let thead = chead.FStar_Syntax_Syntax.res_typ
in (

let _60_1467 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _158_515 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _158_514 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _158_515 _158_514)))
end else begin
()
end
in (

let monadic_application = (fun _60_1474 subst arg_comps_rev arg_rets guard fvs bs -> (match (_60_1474) with
| (head, chead, ghead, cres) -> begin
(

let rt = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _60_1482 = cres
in {FStar_Syntax_Syntax.eff_name = _60_1482.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = rt; FStar_Syntax_Syntax.cflags = _60_1482.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _60_1482.FStar_Syntax_Syntax.comp})
in (

let _60_1513 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun _60_5 -> (match (_60_5) with
| (_60_1490, _60_1492, FStar_Util.Inl (_60_1494)) -> begin
false
end
| (_60_1498, _60_1500, FStar_Util.Inr (c)) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _158_531 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _158_531 cres))
end else begin
(

let _60_1505 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _158_534 = (FStar_Syntax_Print.term_to_string head)
in (let _158_533 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _158_532 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _158_534 _158_533 _158_532))))
end else begin
()
end
in cres)
end
in ((cres), (g))))))
end
| _60_1509 -> begin
(

let g = (let _158_535 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right _158_535 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _158_540 = (let _158_539 = (let _158_538 = (let _158_537 = (let _158_536 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _158_536))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _158_537))
in (FStar_Syntax_Syntax.mk_Total _158_538))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _158_539))
in ((_158_540), (g))))
end)
in (match (_60_1513) with
| (cres, guard) -> begin
(

let _60_1514 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _158_541 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _158_541))
end else begin
()
end
in (

let _60_1539 = (FStar_List.fold_left (fun _60_1519 _60_1525 -> (match (((_60_1519), (_60_1525))) with
| ((args, out_c, monadic), ((e, q), x, c)) -> begin
(match (c) with
| FStar_Util.Inl (eff_name, arg_typ) -> begin
(let _158_546 = (let _158_545 = (let _158_544 = (FStar_TypeChecker_Util.maybe_lift env e eff_name out_c.FStar_Syntax_Syntax.eff_name arg_typ)
in ((_158_544), (q)))
in (_158_545)::args)
in ((_158_546), (out_c), (monadic)))
end
| FStar_Util.Inr (c) -> begin
(

let monadic = (monadic || (not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c))))
in (

let out_c = (FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env None c ((x), (out_c)))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e c.FStar_Syntax_Syntax.eff_name out_c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (((((e), (q)))::args), (out_c), (monadic))))))
end)
end)) (([]), (cres), (false)) arg_comps_rev)
in (match (_60_1539) with
| (args, comp, monadic) -> begin
(

let comp = (FStar_TypeChecker_Util.bind head.FStar_Syntax_Syntax.pos env None chead ((None), (comp)))
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app = if (monadic || (not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp comp)))) then begin
(FStar_TypeChecker_Util.maybe_monadic env app comp.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.res_typ)
end else begin
app
end
in (

let _60_1545 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (_60_1545) with
| (comp, g) -> begin
((app), (comp), (g))
end)))))
end)))
end))))
end))
in (

let rec tc_args = (fun head_info _60_1553 bs args -> (match (_60_1553) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args))) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (_60_1559))))::rest, ((_60_1567, None))::_60_1565) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let t = (check_no_escape (Some (head)) env fvs t)
in (

let _60_1578 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_60_1578) with
| (varg, _60_1576, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst
in (

let arg = (let _158_556 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (_158_556)))
in (let _158_558 = (let _158_557 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst), ((((arg), (None), (FStar_Util.Inl (((FStar_Syntax_Const.effect_Tot_lid), (t))))))::outargs), ((arg)::arg_rets), (_158_557), (fvs)))
in (tc_args head_info _158_558 rest args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
(

let _60_1610 = (match (((aqual), (aq))) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _60_1609 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifier"), (e.FStar_Syntax_Syntax.pos)))))
end)
in (

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let _60_1613 = x
in {FStar_Syntax_Syntax.ppname = _60_1613.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _60_1613.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (

let _60_1616 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _158_559 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _158_559))
end else begin
()
end
in (

let targ = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let _60_1620 = env
in {FStar_TypeChecker_Env.solver = _60_1620.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _60_1620.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _60_1620.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _60_1620.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _60_1620.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _60_1620.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _60_1620.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _60_1620.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _60_1620.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _60_1620.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _60_1620.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _60_1620.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _60_1620.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _60_1620.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _60_1620.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _60_1620.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _60_1620.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _60_1620.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _60_1620.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _60_1620.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _60_1620.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _60_1620.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _60_1620.FStar_TypeChecker_Env.qname_and_index})
in (

let _60_1623 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _158_562 = (FStar_Syntax_Print.tag_of_term e)
in (let _158_561 = (FStar_Syntax_Print.term_to_string e)
in (let _158_560 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _158_562 _158_561 _158_560))))
end else begin
()
end
in (

let _60_1628 = (tc_term env e)
in (match (_60_1628) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = ((e), (aq))
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(

let subst = (let _158_563 = (FStar_List.hd bs)
in (maybe_extend_subst subst _158_563 e))
in (tc_args head_info ((subst), ((((arg), (None), (FStar_Util.Inl (((c.FStar_Syntax_Syntax.eff_name), (c.FStar_Syntax_Syntax.res_typ))))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(

let subst = (let _158_564 = (FStar_List.hd bs)
in (maybe_extend_subst subst _158_564 e))
in (tc_args head_info ((subst), ((((arg), (Some (x)), (FStar_Util.Inr (c))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (let _158_565 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _158_565)) then begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _158_566 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _158_566))
in (tc_args head_info ((subst), ((((arg), (Some (newx)), (FStar_Util.Inr (c))))::outargs), ((arg')::arg_rets), (g), (fvs)) rest rest')))
end else begin
(let _158_570 = (let _158_569 = (let _158_568 = (let _158_567 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _158_567))
in (_158_568)::arg_rets)
in ((subst), ((((arg), (Some (x)), (FStar_Util.Inr (c))))::outargs), (_158_569), (g), ((x)::fvs)))
in (tc_args head_info _158_570 rest rest'))
end
end
end))
end))))))))))
end
| (_60_1636, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::_60_1641) -> begin
(

let _60_1648 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (_60_1648) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _158_575 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _158_575 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let _60_1659 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (_60_1659) with
| (bs, cres') -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp cres')))
in (

let _60_1661 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _158_576 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _158_576))
end else begin
()
end
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args)))
end))
end
| _60_1664 when (not (norm)) -> begin
(let _158_577 = (unfold_whnf env tres)
in (aux true _158_577))
end
| _60_1666 -> begin
(let _158_583 = (let _158_582 = (let _158_581 = (let _158_579 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (let _158_578 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _158_579 _158_578)))
in (let _158_580 = (FStar_Syntax_Syntax.argpos arg)
in ((_158_581), (_158_580))))
in FStar_Syntax_Syntax.Error (_158_582))
in (Prims.raise _158_583))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (match ((let _158_588 = (FStar_Syntax_Util.unrefine tf)
in _158_588.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl -> begin
(

let _60_1699 = (tc_term env e)
in (match (_60_1699) with
| (e, c, g_e) -> begin
(

let _60_1703 = (tc_args env tl)
in (match (_60_1703) with
| (args, comps, g_rest) -> begin
(let _158_593 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e), (imp)))::args), ((((e.FStar_Syntax_Syntax.pos), (c)))::comps), (_158_593)))
end))
end))
end))
in (

let _60_1707 = (tc_args env args)
in (match (_60_1707) with
| (args, comps, g_args) -> begin
(

let bs = (let _158_595 = (FStar_All.pipe_right comps (FStar_List.map (fun _60_1711 -> (match (_60_1711) with
| (_60_1709, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks _158_595))
in (

let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _60_1717 -> begin
FStar_Syntax_Util.ml_comp
end)
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _158_610 = (FStar_Syntax_Subst.compress t)
in _158_610.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_60_1723) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _60_1728 -> begin
ml_or_tot
end)
end)
in (

let cres = (let _158_615 = (let _158_614 = (let _158_613 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _158_613 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _158_614))
in (ml_or_tot _158_615 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (

let _60_1732 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _158_618 = (FStar_Syntax_Print.term_to_string head)
in (let _158_617 = (FStar_Syntax_Print.term_to_string tf)
in (let _158_616 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _158_618 _158_617 _158_616))))
end else begin
()
end
in (

let _60_1734 = (let _158_619 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _158_619))
in (

let comp = (let _158_622 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _60_1738 out -> (match (_60_1738) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c ((None), (out)))
end)) ((((head.FStar_Syntax_Syntax.pos), (chead)))::comps) _158_622))
in (let _158_624 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _158_623 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((_158_624), (comp), (_158_623))))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _60_1747 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_60_1747) with
| (bs, c) -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp c)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args))
end))
end
| _60_1750 -> begin
if (not (norm)) then begin
(let _158_625 = (unfold_whnf env tf)
in (check_function_app true _158_625))
end else begin
(let _158_628 = (let _158_627 = (let _158_626 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in ((_158_626), (head.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_158_627))
in (Prims.raise _158_628))
end
end))
in (let _158_630 = (let _158_629 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _158_629))
in (check_function_app false _158_630))))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let _60_1786 = (FStar_List.fold_left2 (fun _60_1767 _60_1770 _60_1773 -> (match (((_60_1767), (_60_1770), (_60_1773))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(

let _60_1774 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifiers"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _60_1779 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_60_1779) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (let _158_640 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _158_640 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _158_644 = (let _158_642 = (let _158_641 = (FStar_Syntax_Syntax.as_arg e)
in (_158_641)::[])
in (FStar_List.append seen _158_642))
in (let _158_643 = (FStar_TypeChecker_Rel.conj_guard guard g)
in ((_158_644), (_158_643), (ghost)))))))
end)))
end)) (([]), (g_head), (false)) args bs)
in (match (_60_1786) with
| (args, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = if ghost then begin
(let _158_645 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _158_645 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (

let _60_1791 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_60_1791) with
| (c, g) -> begin
((e), (c), (g))
end))))
end)))
end
| _60_1793 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let _60_1800 = (FStar_Syntax_Subst.open_branch branch)
in (match (_60_1800) with
| (pattern, when_clause, branch_exp) -> begin
(

let _60_1805 = branch
in (match (_60_1805) with
| (cpat, _60_1803, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _60_1813 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_60_1813) with
| (pat_bvs, exps, p) -> begin
(

let _60_1814 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _158_657 = (FStar_Syntax_Print.pat_to_string p0)
in (let _158_656 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _158_657 _158_656)))
end else begin
()
end
in (

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let _60_1820 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_60_1820) with
| (env1, _60_1819) -> begin
(

let env1 = (

let _60_1821 = env1
in {FStar_TypeChecker_Env.solver = _60_1821.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _60_1821.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _60_1821.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _60_1821.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _60_1821.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _60_1821.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _60_1821.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _60_1821.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _60_1821.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _60_1821.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _60_1821.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _60_1821.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _60_1821.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _60_1821.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _60_1821.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _60_1821.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _60_1821.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _60_1821.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _60_1821.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _60_1821.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _60_1821.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _60_1821.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _60_1821.FStar_TypeChecker_Env.qname_and_index})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _60_1860 = (let _158_680 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _60_1826 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _158_660 = (FStar_Syntax_Print.term_to_string e)
in (let _158_659 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _158_660 _158_659)))
end else begin
()
end
in (

let _60_1831 = (tc_term env1 e)
in (match (_60_1831) with
| (e, lc, g) -> begin
(

let _60_1832 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _158_662 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _158_661 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _158_662 _158_661)))
end else begin
()
end
in (

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let _60_1838 = (let _158_663 = (FStar_TypeChecker_Rel.discharge_guard env (

let _60_1836 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _60_1836.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _60_1836.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _60_1836.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _158_663 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _158_668 = (let _158_667 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _158_667 (FStar_List.map (fun _60_1846 -> (match (_60_1846) with
| (u, _60_1845) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _158_668 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _60_1854 = if (let _158_669 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _158_669)) then begin
(

let unresolved = (let _158_670 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _158_670 FStar_Util.set_elements))
in (let _158_678 = (let _158_677 = (let _158_676 = (let _158_675 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _158_674 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _158_673 = (let _158_672 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _60_1853 -> (match (_60_1853) with
| (u, _60_1852) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _158_672 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _158_675 _158_674 _158_673))))
in ((_158_676), (p.FStar_Syntax_Syntax.p)))
in FStar_Syntax_Syntax.Error (_158_677))
in (Prims.raise _158_678)))
end else begin
()
end
in (

let _60_1856 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _158_679 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _158_679))
end else begin
()
end
in ((e), (e'))))))))))))
end))))))
in (FStar_All.pipe_right _158_680 FStar_List.unzip))
in (match (_60_1860) with
| (exps, norm_exps) -> begin
(

let p = (FStar_TypeChecker_Util.decorate_pattern env p exps)
in ((p), (pat_bvs), (pat_env), (exps), (norm_exps)))
end))))
end))))
end)))
in (

let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (

let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (

let _60_1867 = (let _158_681 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _158_681 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_60_1867) with
| (scrutinee_env, _60_1866) -> begin
(

let _60_1873 = (tc_pat true pat_t pattern)
in (match (_60_1873) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let _60_1883 = (match (when_clause) with
| None -> begin
((None), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (e) -> begin
if (FStar_TypeChecker_Env.should_verify env) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("When clauses are not yet supported in --verify mode; they will be some day"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
(

let _60_1880 = (let _158_682 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _158_682 e))
in (match (_60_1880) with
| (e, c, g) -> begin
((Some (e)), (g))
end))
end
end)
in (match (_60_1883) with
| (when_clause, g_when) -> begin
(

let _60_1887 = (tc_term pat_env branch_exp)
in (match (_60_1887) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _158_684 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _158_683 -> Some (_158_683)) _158_684))
end)
in (

let _60_1945 = (

let eqs = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
None
end else begin
(FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _60_1905 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _158_688 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _158_687 -> Some (_158_687)) _158_688))
end))
end))) None))
end
in (

let _60_1913 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_60_1913) with
| (c, g_branch) -> begin
(

let _60_1940 = (match (((eqs), (when_condition))) with
| _60_1915 when (not ((FStar_TypeChecker_Env.should_verify env))) -> begin
((c), (g_when))
end
| (None, None) -> begin
((c), (g_when))
end
| (Some (f), None) -> begin
(

let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _158_691 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _158_690 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((_158_691), (_158_690))))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (let _158_692 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_158_692))
in (let _158_695 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _158_694 = (let _158_693 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _158_693 g_when))
in ((_158_695), (_158_694))))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _158_696 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in ((_158_696), (g_when)))))
end)
in (match (_60_1940) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _158_698 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _158_697 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in ((_158_698), (_158_697), (g_branch)))))
end))
end)))
in (match (_60_1945) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
FStar_Syntax_Util.t_true
end else begin
(

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> if ((let _158_708 = (let _158_707 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _158_707))
in (FStar_List.length _158_708)) > (Prims.parse_int "1")) then begin
(

let discriminator = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env discriminator)) with
| None -> begin
[]
end
| _60_1955 -> begin
(

let disc = (FStar_Syntax_Syntax.fvar discriminator FStar_Syntax_Syntax.Delta_equational None)
in (

let disc = (let _158_710 = (let _158_709 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_158_709)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _158_710 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _158_711 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_158_711)::[])))
end))
end else begin
[]
end)
in (

let fail = (fun _60_1959 -> (match (()) with
| () -> begin
(let _158_717 = (let _158_716 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _158_715 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _158_714 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _158_716 _158_715 _158_714))))
in (FStar_All.failwith _158_717))
end))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _60_1966) -> begin
(head_constructor t)
end
| _60_1970 -> begin
(fail ())
end))
in (

let pat_exp = (let _158_720 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _158_720 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_60_1995) -> begin
(let _158_725 = (let _158_724 = (let _158_723 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _158_722 = (let _158_721 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_158_721)::[])
in (_158_723)::_158_722))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _158_724 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_158_725)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _158_726 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _158_726))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(

let sub_term_guards = (let _158_732 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _60_2013 -> (match (_60_2013) with
| (ei, _60_2012) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _60_2017 -> begin
(

let sub_term = (let _158_731 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p) FStar_Syntax_Syntax.Delta_equational None)
in (let _158_730 = (let _158_729 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_158_729)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _158_731 _158_730 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _158_732 FStar_List.flatten))
in (let _158_733 = (discriminate scrutinee_tm f)
in (FStar_List.append _158_733 sub_term_guards)))
end)
end
| _60_2021 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(

let t = (let _158_738 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _158_738))
in (

let _60_2029 = (FStar_Syntax_Util.type_u ())
in (match (_60_2029) with
| (k, _60_2028) -> begin
(

let _60_2035 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_60_2035) with
| (t, _60_2032, _60_2034) -> begin
t
end))
end)))
end)
in (

let branch_guard = (let _158_739 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _158_739 FStar_Syntax_Util.mk_disj_l))
in (

let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
end
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (

let _60_2043 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _158_740 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _158_740))
end else begin
()
end
in (let _158_741 = (FStar_Syntax_Subst.close_branch ((pattern), (when_clause), (branch_exp)))
in ((_158_741), (branch_guard), (c), (guard))))))
end)))
end))
end))
end))
end)))))
end))
end)))
and check_top_level_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let _60_2060 = (check_let_bound_def true env lb)
in (match (_60_2060) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let _60_2074 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
((g1), (e1), (univ_vars), (c1))
end else begin
(

let g1 = (let _158_744 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _158_744 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _60_2062 = ()
in (

let _60_2069 = (let _158_748 = (let _158_747 = (let _158_746 = (let _158_745 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (_158_745)))
in (_158_746)::[])
in (FStar_TypeChecker_Util.generalize env _158_747))
in (FStar_List.hd _158_748))
in (match (_60_2069) with
| (_60_2065, univs, e1, c1) -> begin
((g1), (e1), (univs), ((FStar_Syntax_Util.lcomp_of_comp c1)))
end))))
end
in (match (_60_2074) with
| (g1, e1, univ_vars, c1) -> begin
(

let _60_2085 = if (FStar_TypeChecker_Env.should_verify env) then begin
(

let _60_2077 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_60_2077) with
| (ok, c1) -> begin
if ok then begin
((e2), (c1))
end else begin
(

let _60_2078 = if (FStar_Options.warn_top_level_effects ()) then begin
(let _158_749 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _158_749 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _158_750 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) None e2.FStar_Syntax_Syntax.pos)
in ((_158_750), (c1))))
end
end))
end else begin
(

let _60_2080 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (

let c = (let _158_751 = (c1.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_right _158_751 (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env)))
in ((e2), (c))))
end
in (match (_60_2085) with
| (e2, c1) -> begin
(

let cres = (let _158_752 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _158_752))
in (

let _60_2087 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _158_753 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((_158_753), (cres), (FStar_TypeChecker_Rel.trivial_guard))))))
end))
end))
end))
end
| _60_2091 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let _60_2102 = env
in {FStar_TypeChecker_Env.solver = _60_2102.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _60_2102.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _60_2102.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _60_2102.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _60_2102.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _60_2102.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _60_2102.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _60_2102.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _60_2102.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _60_2102.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _60_2102.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _60_2102.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _60_2102.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _60_2102.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _60_2102.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _60_2102.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _60_2102.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _60_2102.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _60_2102.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _60_2102.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _60_2102.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _60_2102.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _60_2102.FStar_TypeChecker_Env.qname_and_index})
in (

let _60_2111 = (let _158_757 = (let _158_756 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _158_756 Prims.fst))
in (check_let_bound_def false _158_757 lb))
in (match (_60_2111) with
| (e1, _60_2107, c1, g1, annotated) -> begin
(

let x = (

let _60_2112 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _60_2112.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _60_2112.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let _60_2117 = (let _158_759 = (let _158_758 = (FStar_Syntax_Syntax.mk_binder x)
in (_158_758)::[])
in (FStar_Syntax_Subst.open_term _158_759 e2))
in (match (_60_2117) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _60_2123 = (let _158_760 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _158_760 e2))
in (match (_60_2123) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (x)), (c2)))
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let e2 = (FStar_TypeChecker_Util.maybe_lift env e2 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.res_typ)
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let e = (let _158_763 = (let _158_762 = (let _158_761 = (FStar_Syntax_Subst.close xb e2)
in ((((false), ((lb)::[]))), (_158_761)))
in FStar_Syntax_Syntax.Tm_let (_158_762))
in (FStar_Syntax_Syntax.mk _158_763 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (let _158_766 = (let _158_765 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _158_765 e1))
in (FStar_All.pipe_left (fun _158_764 -> FStar_TypeChecker_Common.NonTrivial (_158_764)) _158_766))
in (

let g2 = (let _158_768 = (let _158_767 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _158_767 g2))
in (FStar_TypeChecker_Rel.close_guard xb _158_768))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if (let _158_769 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome _158_769)) then begin
(

let tt = (let _158_770 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_All.pipe_right _158_770 FStar_Option.get))
in (

let _60_2134 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Exports"))) then begin
(let _158_772 = (FStar_Syntax_Print.term_to_string tt)
in (let _158_771 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Got expected type from env %s\ncres.res_typ=%s\n" _158_772 _158_771)))
end else begin
()
end
in ((e), (cres), (guard))))
end else begin
(

let t = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (

let _60_2137 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Exports"))) then begin
(let _158_774 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (let _158_773 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checked %s has no escaping types; normalized to %s\n" _158_774 _158_773)))
end else begin
()
end
in ((e), ((

let _60_2139 = cres
in {FStar_Syntax_Syntax.eff_name = _60_2139.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _60_2139.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _60_2139.FStar_Syntax_Syntax.comp})), (guard))))
end)))))))))
end))))
end)))
end)))
end
| _60_2142 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _60_2154 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_60_2154) with
| (lbs, e2) -> begin
(

let _60_2157 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_60_2157) with
| (env0, topt) -> begin
(

let _60_2160 = (build_let_rec_env true env0 lbs)
in (match (_60_2160) with
| (lbs, rec_env) -> begin
(

let _60_2163 = (check_let_recs rec_env lbs)
in (match (_60_2163) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (let _158_777 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _158_777 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _158_780 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _158_780 (fun _158_779 -> Some (_158_779))))
in (

let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(

let ecs = (let _158_784 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _158_783 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (_158_783))))))
in (FStar_TypeChecker_Util.generalize env _158_784))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _60_2174 -> (match (_60_2174) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _158_786 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _158_786))
in (

let _60_2177 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _60_2181 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_60_2181) with
| (lbs, e2) -> begin
(let _158_788 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _158_787 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in ((_158_788), (cres), (_158_787))))
end)))))))
end))
end))
end))
end))
end
| _60_2183 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _60_2195 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_60_2195) with
| (lbs, e2) -> begin
(

let _60_2198 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_60_2198) with
| (env0, topt) -> begin
(

let _60_2201 = (build_let_rec_env false env0 lbs)
in (match (_60_2201) with
| (lbs, rec_env) -> begin
(

let _60_2204 = (check_let_recs rec_env lbs)
in (match (_60_2204) with
| (lbs, g_lbs) -> begin
(

let _60_2216 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let _60_2207 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _60_2207.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _60_2207.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let _60_2210 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _60_2210.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _60_2210.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _60_2210.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _60_2210.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (lb.FStar_Syntax_Syntax.lbtyp)))
in ((env), (lb)))))) env))
in (match (_60_2216) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let _60_2222 = (tc_term env e2)
in (match (_60_2222) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _60_2226 = cres
in {FStar_Syntax_Syntax.eff_name = _60_2226.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _60_2226.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _60_2226.FStar_Syntax_Syntax.comp})
in (

let _60_2231 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_60_2231) with
| (lbs, e2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_60_2234) -> begin
((e), (cres), (guard))
end
| None -> begin
(

let tres = (check_no_escape None env bvs tres)
in (

let cres = (

let _60_2238 = cres
in {FStar_Syntax_Syntax.eff_name = _60_2238.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _60_2238.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _60_2238.FStar_Syntax_Syntax.comp})
in ((e), (cres), (guard))))
end))
end))))))
end)))
end))
end))
end))
end))
end))
end
| _60_2242 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun t -> (

let _60_2252 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (_60_2252) with
| (_60_2250, c) -> begin
(

let quals = (FStar_TypeChecker_Env.lookup_effect_quals env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
end)))
in (

let _60_2282 = (FStar_List.fold_left (fun _60_2256 lb -> (match (_60_2256) with
| (lbs, env) -> begin
(

let _60_2261 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_60_2261) with
| (univ_vars, t, check_t) -> begin
(

let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (

let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (

let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(

let _60_2270 = (let _158_802 = (let _158_801 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _158_801))
in (tc_check_tot_or_gtot_term (

let _60_2264 = env0
in {FStar_TypeChecker_Env.solver = _60_2264.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _60_2264.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _60_2264.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _60_2264.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _60_2264.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _60_2264.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _60_2264.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _60_2264.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _60_2264.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _60_2264.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _60_2264.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _60_2264.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _60_2264.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _60_2264.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _60_2264.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _60_2264.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _60_2264.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _60_2264.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _60_2264.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _60_2264.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _60_2264.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _60_2264.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _60_2264.FStar_TypeChecker_Env.qname_and_index}) t _158_802))
in (match (_60_2270) with
| (t, _60_2268, g) -> begin
(

let _60_2271 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (

let env = if ((termination_check_enabled t) && (FStar_TypeChecker_Env.should_verify env)) then begin
(

let _60_2274 = env
in {FStar_TypeChecker_Env.solver = _60_2274.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _60_2274.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _60_2274.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _60_2274.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _60_2274.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _60_2274.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _60_2274.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _60_2274.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _60_2274.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _60_2274.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _60_2274.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _60_2274.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t)))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _60_2274.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _60_2274.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _60_2274.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _60_2274.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _60_2274.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _60_2274.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _60_2274.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _60_2274.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _60_2274.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _60_2274.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _60_2274.FStar_TypeChecker_Env.qname_and_index})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (t)))
end
in (

let lb = (

let _60_2277 = lb
in {FStar_Syntax_Syntax.lbname = _60_2277.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _60_2277.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb)::lbs), (env)))))))
end))
end)) (([]), (env)) lbs)
in (match (_60_2282) with
| (lbs, env) -> begin
(((FStar_List.rev lbs)), (env))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _60_2295 = (let _158_807 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _60_2289 = (let _158_806 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _158_806 lb.FStar_Syntax_Syntax.lbdef))
in (match (_60_2289) with
| (e, c, g) -> begin
(

let _60_2290 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in ((lb), (g))))
end)))))
in (FStar_All.pipe_right _158_807 FStar_List.unzip))
in (match (_60_2295) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _60_2303 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_60_2303) with
| (env1, _60_2302) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _60_2310 = (check_lbtyp top_level env lb)
in (match (_60_2310) with
| (topt, wf_annot, univ_vars, univ_opening, env1) -> begin
(

let _60_2311 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _60_2313 = ()
in (

let e1 = (FStar_Syntax_Subst.subst univ_opening e1)
in (

let _60_2321 = (tc_maybe_toplevel_term (

let _60_2316 = env1
in {FStar_TypeChecker_Env.solver = _60_2316.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _60_2316.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _60_2316.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _60_2316.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _60_2316.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _60_2316.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _60_2316.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _60_2316.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _60_2316.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _60_2316.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _60_2316.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _60_2316.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _60_2316.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _60_2316.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _60_2316.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _60_2316.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _60_2316.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _60_2316.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _60_2316.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _60_2316.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _60_2316.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _60_2316.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _60_2316.FStar_TypeChecker_Env.qname_and_index}) e1)
in (match (_60_2321) with
| (e1, c1, g1) -> begin
(

let _60_2325 = (let _158_814 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _60_2322 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _158_814 e1 c1 wf_annot))
in (match (_60_2325) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _60_2327 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _158_817 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _158_816 = (FStar_Syntax_Print.term_to_string c1.FStar_Syntax_Syntax.res_typ)
in (let _158_815 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print3 "checked top-level def %s, result type is %s, guard is %s\n" _158_817 _158_816 _158_815))))
end else begin
()
end
in (let _158_818 = (FStar_Option.isSome topt)
in ((e1), (univ_vars), (c1), (g1), (_158_818)))))
end))
end)))))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.subst_elt Prims.list * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _60_2334 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in ((None), (FStar_TypeChecker_Rel.trivial_guard), ([]), ([]), (env)))
end
| _60_2337 -> begin
(

let _60_2340 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (_60_2340) with
| (univ_opening, univ_vars) -> begin
(

let t = (FStar_Syntax_Subst.subst univ_opening t)
in (

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _158_822 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars), (univ_opening), (_158_822)))
end else begin
(

let _60_2346 = (FStar_Syntax_Util.type_u ())
in (match (_60_2346) with
| (k, _60_2345) -> begin
(

let _60_2351 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_60_2351) with
| (t, _60_2349, g) -> begin
(

let _60_2352 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _158_825 = (let _158_823 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _158_823))
in (let _158_824 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _158_825 _158_824)))
end else begin
()
end
in (

let t = (norm env1 t)
in (let _158_826 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (g), (univ_vars), (univ_opening), (_158_826)))))
end))
end))
end))
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _60_2358 -> (match (_60_2358) with
| (x, imp) -> begin
(

let _60_2361 = (FStar_Syntax_Util.type_u ())
in (match (_60_2361) with
| (tu, u) -> begin
(

let _60_2362 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _158_831 = (FStar_Syntax_Print.bv_to_string x)
in (let _158_830 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _158_829 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binders %s:%s at type %s\n" _158_831 _158_830 _158_829))))
end else begin
()
end
in (

let _60_2368 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_60_2368) with
| (t, _60_2366, g) -> begin
(

let x = (((

let _60_2369 = x
in {FStar_Syntax_Syntax.ppname = _60_2369.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _60_2369.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in (

let _60_2372 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _158_833 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _158_832 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _158_833 _158_832)))
end else begin
()
end
in (let _158_834 = (push_binding env x)
in ((x), (_158_834), (g), (u)))))
end)))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universes) = (fun env bs -> (

let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
(([]), (env), (FStar_TypeChecker_Rel.trivial_guard), ([]))
end
| (b)::bs -> begin
(

let _60_2387 = (tc_binder env b)
in (match (_60_2387) with
| (b, env', g, u) -> begin
(

let _60_2392 = (aux env' bs)
in (match (_60_2392) with
| (bs, env', g', us) -> begin
(let _158_842 = (let _158_841 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _158_841))
in (((b)::bs), (env'), (_158_842), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun _60_2400 _60_2403 -> (match (((_60_2400), (_60_2403))) with
| ((t, imp), (args, g)) -> begin
(

let _60_2408 = (tc_term env t)
in (match (_60_2408) with
| (t, _60_2406, g') -> begin
(let _158_851 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t), (imp)))::args), (_158_851)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p _60_2412 -> (match (_60_2412) with
| (pats, g) -> begin
(

let _60_2415 = (tc_args env p)
in (match (_60_2415) with
| (args, g') -> begin
(let _158_854 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats), (_158_854)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _60_2421 = (tc_maybe_toplevel_term env e)
in (match (_60_2421) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
((e), (c), (g))
end else begin
(

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let c = (norm_c env c)
in (

let _60_2427 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _158_857 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in ((_158_857), (false)))
end else begin
(let _158_858 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in ((_158_858), (true)))
end
in (match (_60_2427) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _158_859 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (_158_859)))
end
| _60_2431 -> begin
if allow_ghost then begin
(let _158_862 = (let _158_861 = (let _158_860 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in ((_158_860), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_158_861))
in (Prims.raise _158_862))
end else begin
(let _158_865 = (let _158_864 = (let _158_863 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in ((_158_863), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_158_864))
in (Prims.raise _158_865))
end
end)
end)))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let _60_2441 = (tc_tot_or_gtot_term env t)
in (match (_60_2441) with
| (t, c, g) -> begin
(

let _60_2442 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in ((t), (c)))
end)))


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _60_2446 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _158_875 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _158_875))
end else begin
()
end
in (

let env = (

let _60_2448 = env
in {FStar_TypeChecker_Env.solver = _60_2448.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _60_2448.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _60_2448.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _60_2448.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _60_2448.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _60_2448.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _60_2448.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _60_2448.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _60_2448.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _60_2448.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _60_2448.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _60_2448.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _60_2448.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _60_2448.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _60_2448.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _60_2448.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _60_2448.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _60_2448.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _60_2448.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _60_2448.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _60_2448.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _60_2448.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _60_2448.FStar_TypeChecker_Env.qname_and_index})
in (

let _60_2464 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _60_2456) -> begin
(let _158_880 = (let _158_879 = (let _158_878 = (FStar_TypeChecker_Env.get_range env)
in (((Prims.strcat "Implicit argument: " msg)), (_158_878)))
in FStar_Syntax_Syntax.Error (_158_879))
in (Prims.raise _158_880))
end
in (match (_60_2464) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end else begin
(let _158_885 = (let _158_884 = (let _158_883 = (let _158_881 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _158_881))
in (let _158_882 = (FStar_TypeChecker_Env.get_range env)
in ((_158_883), (_158_882))))
in FStar_Syntax_Syntax.Error (_158_884))
in (Prims.raise _158_885))
end
end)))))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> (

let _60_2467 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _158_890 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "<start> universe_of %s\n" _158_890))
end else begin
()
end
in (

let _60_2472 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_60_2472) with
| (env, _60_2471) -> begin
(

let env = (

let _60_2473 = env
in {FStar_TypeChecker_Env.solver = _60_2473.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _60_2473.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _60_2473.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _60_2473.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _60_2473.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _60_2473.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _60_2473.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _60_2473.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _60_2473.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _60_2473.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _60_2473.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _60_2473.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _60_2473.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _60_2473.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _60_2473.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _60_2473.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _60_2473.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _60_2473.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _60_2473.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _60_2473.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _60_2473.FStar_TypeChecker_Env.qname_and_index})
in (

let fail = (fun e t -> (let _158_900 = (let _158_899 = (let _158_898 = (let _158_896 = (FStar_Syntax_Print.term_to_string e)
in (let _158_895 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" _158_896 _158_895)))
in (let _158_897 = (FStar_TypeChecker_Env.get_range env)
in ((_158_898), (_158_897))))
in FStar_Syntax_Syntax.Error (_158_899))
in (Prims.raise _158_900)))
in (

let ok = (fun u -> (

let _60_2481 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _158_905 = (FStar_Syntax_Print.tag_of_term e)
in (let _158_904 = (FStar_Syntax_Print.term_to_string e)
in (let _158_903 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.print3 "<end> universe_of (%s) %s is %s\n" _158_905 _158_904 _158_903))))
end else begin
()
end
in u))
in (

let universe_of_type = (fun e t -> (match ((let _158_910 = (FStar_Syntax_Util.unrefine t)
in _158_910.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(ok u)
end
| _60_2489 -> begin
(fail e t)
end))
in (

let _60_2492 = (FStar_Syntax_Util.head_and_args e)
in (match (_60_2492) with
| (head, args) -> begin
(match ((let _158_911 = (FStar_Syntax_Subst.compress head)
in _158_911.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_60_2494, t) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _158_912 = (FStar_Syntax_Subst.compress t)
in _158_912.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_60_2500, t) -> begin
(universe_of_type e (FStar_Syntax_Util.comp_result t))
end
| _60_2505 -> begin
(universe_of_type e t)
end))
end
| _60_2507 -> begin
(

let t = (match ((FStar_ST.read e.FStar_Syntax_Syntax.tk)) with
| (None) | (Some (FStar_Syntax_Syntax.Tm_unknown)) -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::[]) env e)
in (

let _60_2523 = (tc_term env e)
in (match (_60_2523) with
| (_60_2513, {FStar_Syntax_Syntax.eff_name = _60_2520; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _60_2517; FStar_Syntax_Syntax.comp = _60_2515}, g) -> begin
(

let _60_2524 = (let _158_914 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (FStar_All.pipe_right _158_914 Prims.ignore))
in t)
end)))
end
| Some (t) -> begin
(FStar_Syntax_Syntax.mk t None e.FStar_Syntax_Syntax.pos)
end)
in (let _158_915 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (FStar_All.pipe_left (universe_of_type e) _158_915)))
end)
end))))))
end))))




