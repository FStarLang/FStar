
open Prims

let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _58_7 = env
in {FStar_TypeChecker_Env.solver = _58_7.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_7.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_7.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_7.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_7.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_7.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_7.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_7.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_7.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _58_7.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_7.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_7.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_7.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_7.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_7.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_7.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_7.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_7.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_7.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_7.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_7.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_7.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_7.FStar_TypeChecker_Env.qname_and_index}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _58_10 = env
in {FStar_TypeChecker_Env.solver = _58_10.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_10.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_10.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_10.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_10.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_10.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_10.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_10.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_10.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _58_10.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_10.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_10.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_10.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_10.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_10.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_10.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_10.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_10.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_10.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_10.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_10.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_10.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_10.FStar_TypeChecker_Env.qname_and_index}))


let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (

let r = if (tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
v.FStar_Syntax_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos tl.FStar_Syntax_Syntax.pos)
end
in (let _153_12 = (let _153_11 = (FStar_Syntax_Syntax.as_arg v)
in (let _153_10 = (let _153_9 = (FStar_Syntax_Syntax.as_arg tl)
in (_153_9)::[])
in (_153_11)::_153_10))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _153_12 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _58_1 -> (match (_58_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _58_20 -> begin
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
| _58_37 -> begin
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

let fail = (fun _58_45 -> (match (()) with
| () -> begin
(

let msg = (match (head_opt) with
| None -> begin
(let _153_43 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _153_43))
end
| Some (head) -> begin
(let _153_45 = (FStar_Syntax_Print.bv_to_string x)
in (let _153_44 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _153_45 _153_44)))
end)
in (let _153_48 = (let _153_47 = (let _153_46 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (_153_46)))
in FStar_Syntax_Syntax.Error (_153_47))
in (Prims.raise _153_48)))
end))
in (

let s = (let _153_50 = (let _153_49 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _153_49))
in (FStar_TypeChecker_Util.new_uvar env _153_50))
in (match ((FStar_TypeChecker_Rel.try_teq env t s)) with
| Some (g) -> begin
(

let _58_53 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in s)
end
| _58_56 -> begin
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

let _58_64 = lc
in {FStar_Syntax_Syntax.eff_name = _58_64.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_64.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _58_66 -> (match (()) with
| () -> begin
(let _153_64 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _153_64 t))
end))}))


let memo_tk : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun e t -> (

let _58_69 = (FStar_ST.op_Colon_Equals e.FStar_Syntax_Syntax.tk (Some (t.FStar_Syntax_Syntax.n)))
in e))


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let should_return = (fun t -> (match ((let _153_79 = (FStar_Syntax_Subst.compress t)
in _153_79.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_78, c) -> begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(

let t = (FStar_All.pipe_left FStar_Syntax_Util.unrefine (FStar_Syntax_Util.comp_result c))
in (match ((let _153_80 = (FStar_Syntax_Subst.compress t)
in _153_80.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (_58_86) -> begin
false
end
| _58_89 -> begin
true
end))
end else begin
false
end
end
| _58_91 -> begin
true
end))
in (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _153_81 = if ((not ((should_return t))) || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _153_81))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _58_119 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(let _153_82 = (memo_tk e t)
in ((_153_82), (lc), (guard)))
end
| Some (t') -> begin
(

let _58_101 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_84 = (FStar_Syntax_Print.term_to_string t)
in (let _153_83 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _153_84 _153_83)))
end else begin
()
end
in (

let _58_105 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_58_105) with
| (e, lc) -> begin
(

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _58_109 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_58_109) with
| (e, g) -> begin
(

let _58_110 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_86 = (FStar_Syntax_Print.term_to_string t)
in (let _153_85 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _153_86 _153_85)))
end else begin
()
end
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let _58_115 = (let _153_92 = (FStar_All.pipe_left (fun _153_91 -> Some (_153_91)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _153_92 env e lc g))
in (match (_58_115) with
| (lc, g) -> begin
(let _153_93 = (memo_tk e t')
in ((_153_93), ((set_lcomp_result lc t')), (g)))
end))))
end)))
end)))
end)
in (match (_58_119) with
| (e, lc, g) -> begin
(

let _58_120 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_94 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _153_94))
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

let _58_130 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_58_130) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _58_135 -> (match (_58_135) with
| (e, c) -> begin
(

let expected_c_opt = (match (copt) with
| Some (_58_137) -> begin
copt
end
| None -> begin
if ((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Syntax_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) then begin
(let _153_107 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (_153_107))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
if (FStar_Syntax_Util.is_pure_comp c) then begin
(let _153_108 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (_153_108))
end else begin
if (FStar_Syntax_Util.is_pure_or_ghost_comp c) then begin
(let _153_109 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (_153_109))
end else begin
None
end
end
end
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _153_110 = (norm_c env c)
in ((e), (_153_110), (FStar_TypeChecker_Rel.trivial_guard)))
end
| Some (expected_c) -> begin
(

let _58_144 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_113 = (FStar_Syntax_Print.term_to_string e)
in (let _153_112 = (FStar_Syntax_Print.comp_to_string c)
in (let _153_111 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _153_113 _153_112 _153_111))))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _58_147 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_116 = (FStar_Syntax_Print.term_to_string e)
in (let _153_115 = (FStar_Syntax_Print.comp_to_string c)
in (let _153_114 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _153_116 _153_115 _153_114))))
end else begin
()
end
in (

let _58_153 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_58_153) with
| (e, _58_151, g) -> begin
(

let g = (let _153_117 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _153_117 "could not prove post-condition" g))
in (

let _58_155 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_119 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _153_118 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _153_119 _153_118)))
end else begin
()
end
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e (FStar_Syntax_Util.comp_effect_name c) (FStar_Syntax_Util.comp_effect_name expected_c))
in ((e), (expected_c), (g)))))
end)))))
end))
end))


let no_logical_guard = (fun env _58_162 -> (match (_58_162) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
((te), (kt), (f))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _153_125 = (let _153_124 = (let _153_123 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _153_122 = (FStar_TypeChecker_Env.get_range env)
in ((_153_123), (_153_122))))
in FStar_Syntax_Syntax.Error (_153_124))
in (Prims.raise _153_125))
end)
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _153_128 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _153_128))
end))


let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = _58_188; FStar_Syntax_Syntax.effect_name = _58_186; FStar_Syntax_Syntax.result_typ = _58_184; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, _58_178))::[]; FStar_Syntax_Syntax.flags = _58_175}) -> begin
(

let pat_vars = (let _153_133 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env pats)
in (FStar_Syntax_Free.names _153_133))
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _58_195 -> (match (_58_195) with
| (b, _58_194) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _58_199) -> begin
(let _153_136 = (let _153_135 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" _153_135))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _153_136))
end))
end
| _58_203 -> begin
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

let _58_210 = env
in {FStar_TypeChecker_Env.solver = _58_210.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_210.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_210.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_210.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_210.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_210.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_210.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_210.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_210.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_210.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_210.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_210.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _58_210.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_210.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_210.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_210.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_210.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_210.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_210.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_210.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_210.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_210.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_210.FStar_TypeChecker_Env.qname_and_index})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _58_222 -> (match (_58_222) with
| (b, _58_221) -> begin
(

let t = (let _153_150 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _153_150))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _58_231 -> begin
(let _153_151 = (FStar_Syntax_Syntax.bv_to_name b)
in (_153_151)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let _58_237 = (FStar_Syntax_Util.head_and_args dec)
in (match (_58_237) with
| (head, _58_236) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _58_241 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let cflags = (FStar_Syntax_Util.comp_flags c)
in (match ((FStar_All.pipe_right cflags (FStar_List.tryFind (fun _58_2 -> (match (_58_2) with
| FStar_Syntax_Syntax.DECREASES (_58_245) -> begin
true
end
| _58_248 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _58_253 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| _58_258 -> begin
(mk_lex_list xs)
end))
end)))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun _58_263 -> (match (_58_263) with
| (l, t) -> begin
(match ((let _153_157 = (FStar_Syntax_Subst.compress t)
in _153_157.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _58_270 -> (match (_58_270) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _153_161 = (let _153_160 = (let _153_159 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_153_159))
in (FStar_Syntax_Syntax.new_bv _153_160 x.FStar_Syntax_Syntax.sort))
in ((_153_161), (imp)))
end else begin
((x), (imp))
end
end))))
in (

let _58_274 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_58_274) with
| (formals, c) -> begin
(

let dec = (decreases_clause formals c)
in (

let precedes = (let _153_165 = (let _153_164 = (FStar_Syntax_Syntax.as_arg dec)
in (let _153_163 = (let _153_162 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_153_162)::[])
in (_153_164)::_153_163))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _153_165 None r))
in (

let _58_281 = (FStar_Util.prefix formals)
in (match (_58_281) with
| (bs, (last, imp)) -> begin
(

let last = (

let _58_282 = last
in (let _153_166 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _58_282.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_282.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _153_166}))
in (

let refined_formals = (FStar_List.append bs ((((last), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (

let _58_287 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_169 = (FStar_Syntax_Print.lbname_to_string l)
in (let _153_168 = (FStar_Syntax_Print.term_to_string t)
in (let _153_167 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _153_169 _153_168 _153_167))))
end else begin
()
end
in ((l), (t'))))))
end))))
end)))
end
| _58_290 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Annotated type of \'let rec\' must be an arrow"), (t.FStar_Syntax_Syntax.pos)))))
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end)
end)


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let _58_293 = env
in {FStar_TypeChecker_Env.solver = _58_293.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_293.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_293.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_293.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_293.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_293.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_293.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_293.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_293.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_293.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_293.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_293.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_293.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_293.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_293.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_293.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_293.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_293.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_293.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_293.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_293.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_293.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_293.FStar_TypeChecker_Env.qname_and_index}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (

let _58_298 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_239 = (let _153_237 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _153_237))
in (let _153_238 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _153_239 _153_238)))
end else begin
()
end
in (

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_58_302) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let _58_343 = (tc_tot_or_gtot_term env e)
in (match (_58_343) with
| (e, c, g) -> begin
(

let g = (

let _58_344 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_344.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_344.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_344.FStar_TypeChecker_Env.implicits})
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let _58_354 = (FStar_Syntax_Util.type_u ())
in (match (_58_354) with
| (t, u) -> begin
(

let _58_358 = (tc_check_tot_or_gtot_term env e t)
in (match (_58_358) with
| (e, c, g) -> begin
(

let _58_365 = (

let _58_362 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_362) with
| (env, _58_361) -> begin
(tc_pats env pats)
end))
in (match (_58_365) with
| (pats, g') -> begin
(

let g' = (

let _58_366 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_366.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_366.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_366.FStar_TypeChecker_Env.implicits})
in (let _153_244 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_pattern (pats))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _153_243 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((_153_244), (c), (_153_243)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _153_245 = (FStar_Syntax_Subst.compress e)
in _153_245.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_58_375, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _58_382; FStar_Syntax_Syntax.lbtyp = _58_380; FStar_Syntax_Syntax.lbeff = _58_378; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _58_393 = (let _153_246 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _153_246 e1))
in (match (_58_393) with
| (e1, c1, g1) -> begin
(

let _58_397 = (tc_term env e2)
in (match (_58_397) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((None), (c2)))
in (

let e = (let _153_251 = (let _153_250 = (let _153_249 = (let _153_248 = (let _153_247 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_TypeChecker_Common.t_unit), (e1)))
in (_153_247)::[])
in ((false), (_153_248)))
in ((_153_249), (e2)))
in FStar_Syntax_Syntax.Tm_let (_153_250))
in (FStar_Syntax_Syntax.mk _153_251 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _153_252 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e), (c), (_153_252))))))
end))
end))
end
| _58_402 -> begin
(

let _58_406 = (tc_term env e)
in (match (_58_406) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (_58_410)) -> begin
(tc_term env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let _58_421 = (tc_term env e)
in (match (_58_421) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (m)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _58_427) -> begin
(

let _58_433 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_433) with
| (env0, _58_432) -> begin
(

let _58_438 = (tc_comp env0 expected_c)
in (match (_58_438) with
| (expected_c, _58_436, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (

let _58_443 = (let _153_253 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term _153_253 e))
in (match (_58_443) with
| (e, c', g') -> begin
(

let _58_447 = (let _153_255 = (let _153_254 = (c'.FStar_Syntax_Syntax.comp ())
in ((e), (_153_254)))
in (check_expected_effect env0 (Some (expected_c)) _153_255))
in (match (_58_447) with
| (e, expected_c, g'') -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t_res)), (Some ((FStar_Syntax_Util.comp_effect_name expected_c)))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let lc = (FStar_Syntax_Util.lcomp_of_comp expected_c)
in (

let f = (let _153_256 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _153_256))
in (

let _58_454 = (comp_check_expected_typ env e lc)
in (match (_58_454) with
| (e, c, f2) -> begin
(let _153_257 = (FStar_TypeChecker_Rel.conj_guard f f2)
in ((e), (c), (_153_257)))
end)))))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _58_459) -> begin
(

let _58_464 = (FStar_Syntax_Util.type_u ())
in (match (_58_464) with
| (k, u) -> begin
(

let _58_469 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_469) with
| (t, _58_467, f) -> begin
(

let _58_473 = (let _153_258 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _153_258 e))
in (match (_58_473) with
| (e, c, g) -> begin
(

let _58_477 = (let _153_262 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_474 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _153_262 e c f))
in (match (_58_477) with
| (c, f) -> begin
(

let _58_481 = (let _153_263 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t)), (Some (c.FStar_Syntax_Syntax.eff_name))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _153_263 c))
in (match (_58_481) with
| (e, c, f2) -> begin
(let _153_265 = (let _153_264 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _153_264))
in ((e), (c), (_153_265)))
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

let _58_517 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_517) with
| (unary_op, _58_516) -> begin
(

let head = (let _153_266 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (Prims.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) None _153_266))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), (rest)))) None top.FStar_Syntax_Syntax.pos)
in (tc_term env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _58_525; FStar_Syntax_Syntax.pos = _58_523; FStar_Syntax_Syntax.vars = _58_521}, ((e, aqual))::[]) -> begin
(

let _58_535 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end else begin
()
end
in (

let _58_544 = (

let _58_540 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_540) with
| (env0, _58_539) -> begin
(tc_term env0 e)
end))
in (match (_58_544) with
| (e, c, g) -> begin
(

let _58_548 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_548) with
| (reify_op, _58_547) -> begin
(

let u_c = (

let _58_554 = (tc_term env c.FStar_Syntax_Syntax.res_typ)
in (match (_58_554) with
| (_58_550, c, _58_553) -> begin
(match ((let _153_267 = (FStar_Syntax_Subst.compress c.FStar_Syntax_Syntax.res_typ)
in _153_267.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| _58_558 -> begin
(FStar_All.failwith "Unexpected result type of computation")
end)
end))
in (

let repr = (FStar_TypeChecker_Util.reify_comp env c u_c)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e), (aqual)))::[])))) (Some (repr.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let c = (let _153_268 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right _153_268 FStar_Syntax_Util.lcomp_of_comp))
in (

let _58_566 = (comp_check_expected_typ env e c)
in (match (_58_566) with
| (e, c, g') -> begin
(let _153_269 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), (c), (_153_269)))
end))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.tk = _58_572; FStar_Syntax_Syntax.pos = _58_570; FStar_Syntax_Syntax.vars = _58_568}, ((e, aqual))::[]) -> begin
(

let _58_583 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end else begin
()
end
in (

let no_reflect = (fun _58_586 -> (match (()) with
| () -> begin
(let _153_274 = (let _153_273 = (let _153_272 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((_153_272), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_153_273))
in (Prims.raise _153_274))
end))
in (

let _58_590 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_590) with
| (reflect_op, _58_589) -> begin
(match ((FStar_TypeChecker_Env.effect_decl_opt env l)) with
| None -> begin
(no_reflect ())
end
| Some (ed) -> begin
if (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable)))) then begin
(no_reflect ())
end else begin
(

let _58_596 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_596) with
| (env_no_ex, topt) -> begin
(

let _58_624 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (let _153_280 = (let _153_279 = (let _153_278 = (let _153_277 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _153_276 = (let _153_275 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (_153_275)::[])
in (_153_277)::_153_276))
in ((repr), (_153_278)))
in FStar_Syntax_Syntax.Tm_app (_153_279))
in (FStar_Syntax_Syntax.mk _153_280 None top.FStar_Syntax_Syntax.pos))
in (

let _58_604 = (let _153_282 = (let _153_281 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _153_281 Prims.fst))
in (tc_tot_or_gtot_term _153_282 t))
in (match (_58_604) with
| (t, _58_602, g) -> begin
(match ((let _153_283 = (FStar_Syntax_Subst.compress t)
in _153_283.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_58_606, ((res, _58_613))::((wp, _58_609))::[]) -> begin
((t), (res), (wp), (g))
end
| _58_619 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))
in (match (_58_624) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let _58_638 = (

let _58_628 = (tc_tot_or_gtot_term env_no_ex e)
in (match (_58_628) with
| (e, c, g) -> begin
(

let _58_629 = if (let _153_284 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation _153_284)) then begin
(FStar_TypeChecker_Errors.add_errors env (((("Expected Tot, got a GTot computation"), (e.FStar_Syntax_Syntax.pos)))::[]))
end else begin
()
end
in (match ((FStar_TypeChecker_Rel.try_teq env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)) with
| None -> begin
(

let _58_632 = (let _153_289 = (let _153_288 = (let _153_287 = (let _153_286 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _153_285 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" _153_286 _153_285)))
in ((_153_287), (e.FStar_Syntax_Syntax.pos)))
in (_153_288)::[])
in (FStar_TypeChecker_Errors.add_errors env _153_289))
in (let _153_290 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e), (_153_290))))
end
| Some (g') -> begin
(let _153_292 = (let _153_291 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' _153_291))
in ((e), (_153_292)))
end))
end))
in (match (_58_638) with
| (e, g) -> begin
(

let c = (let _153_298 = (let _153_297 = (let _153_296 = (let _153_293 = (env.FStar_TypeChecker_Env.universe_of env res_typ)
in (_153_293)::[])
in (let _153_295 = (let _153_294 = (FStar_Syntax_Syntax.as_arg wp)
in (_153_294)::[])
in {FStar_Syntax_Syntax.comp_univs = _153_296; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = _153_295; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp _153_297))
in (FStar_All.pipe_right _153_298 FStar_Syntax_Util.lcomp_of_comp))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e), (aqual)))::[])))) (Some (res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let _58_644 = (comp_check_expected_typ env e c)
in (match (_58_644) with
| (e, c, g') -> begin
(let _153_299 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e), (c), (_153_299)))
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

let env = (let _153_301 = (let _153_300 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _153_300 Prims.fst))
in (FStar_All.pipe_right _153_301 instantiate_both))
in (

let _58_651 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_303 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _153_302 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _153_303 _153_302)))
end else begin
()
end
in (

let _58_656 = (tc_term (no_inst env) head)
in (match (_58_656) with
| (head, chead, g_head) -> begin
(

let _58_660 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _153_304 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _153_304))
end else begin
(let _153_305 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _153_305))
end
in (match (_58_660) with
| (e, c, g) -> begin
(

let _58_661 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _153_306 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _153_306))
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

let _58_667 = (comp_check_expected_typ env0 e c)
in (match (_58_667) with
| (e, c, g') -> begin
(

let gimp = (match ((let _153_307 = (FStar_Syntax_Subst.compress head)
in _153_307.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _58_670) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e), (c.FStar_Syntax_Syntax.res_typ), (head.FStar_Syntax_Syntax.pos))
in (

let _58_674 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_674.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_674.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_674.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _58_677 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (

let gres = (let _153_308 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _153_308))
in (

let _58_680 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _153_310 = (FStar_Syntax_Print.term_to_string e)
in (let _153_309 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" _153_310 _153_309)))
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

let _58_688 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_688) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let _58_693 = (tc_term env1 e1)
in (match (_58_693) with
| (e1, c1, g1) -> begin
(

let _58_704 = (match (topt) with
| Some (t) -> begin
((env), (t))
end
| None -> begin
(

let _58_700 = (FStar_Syntax_Util.type_u ())
in (match (_58_700) with
| (k, _58_699) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _153_311 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in ((_153_311), (res_t))))
end))
end)
in (match (_58_704) with
| (env_branches, res_t) -> begin
(

let _58_705 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _153_312 = (FStar_Syntax_Print.term_to_string res_t)
in (FStar_Util.print1 "Tm_match: expected type of branches is %s\n" _153_312))
end else begin
()
end
in (

let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let _58_723 = (

let _58_720 = (FStar_List.fold_right (fun _58_714 _58_717 -> (match (((_58_714), (_58_717))) with
| ((_58_710, f, c, g), (caccum, gaccum)) -> begin
(let _153_315 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (_153_315)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_58_720) with
| (cases, g) -> begin
(let _153_316 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in ((_153_316), (g)))
end))
in (match (_58_723) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (guard_x)), (c_branches)))
in (

let e = (

let mk_match = (fun scrutinee -> (

let scrutinee = (FStar_TypeChecker_Util.maybe_lift env scrutinee c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let branches = (FStar_All.pipe_right t_eqns (FStar_List.map (fun _58_737 -> (match (_58_737) with
| ((pat, wopt, br), _58_733, lc, _58_736) -> begin
(let _153_320 = (FStar_TypeChecker_Util.maybe_lift env br lc.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in ((pat), (wopt), (_153_320)))
end))))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (Some (cres.FStar_Syntax_Syntax.eff_name))))) None e.FStar_Syntax_Syntax.pos)))))
in if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c1.FStar_Syntax_Syntax.eff_name) then begin
(mk_match e1)
end else begin
(

let e_match = (let _153_321 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match _153_321))
in (

let lb = (let _153_322 = (FStar_TypeChecker_Env.norm_eff_name env c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = _153_322; FStar_Syntax_Syntax.lbdef = e1})
in (

let e = (let _153_327 = (let _153_326 = (let _153_325 = (let _153_324 = (let _153_323 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (_153_323)::[])
in (FStar_Syntax_Subst.close _153_324 e_match))
in ((((false), ((lb)::[]))), (_153_325)))
in FStar_Syntax_Syntax.Tm_let (_153_326))
in (FStar_Syntax_Syntax.mk _153_327 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ))))
end)
in (

let _58_744 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _153_330 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _153_329 = (let _153_328 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _153_328))
in (FStar_Util.print2 "(%s) comp type = %s\n" _153_330 _153_329)))
end else begin
()
end
in (let _153_331 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e), (cres), (_153_331))))))
end)))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_756); FStar_Syntax_Syntax.lbunivs = _58_754; FStar_Syntax_Syntax.lbtyp = _58_752; FStar_Syntax_Syntax.lbeff = _58_750; FStar_Syntax_Syntax.lbdef = _58_748})::[]), _58_762) -> begin
(

let _58_765 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_332 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _153_332))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _58_769), _58_772) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_787); FStar_Syntax_Syntax.lbunivs = _58_785; FStar_Syntax_Syntax.lbtyp = _58_783; FStar_Syntax_Syntax.lbeff = _58_781; FStar_Syntax_Syntax.lbdef = _58_779})::_58_777), _58_793) -> begin
(

let _58_796 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_333 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _153_333))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _58_800), _58_803) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let _58_817 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_817) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _153_347 = (let _153_346 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _153_346))
in FStar_Util.Inr (_153_347))
end
in (

let is_data_ctor = (fun _58_3 -> (match (_58_3) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _58_827 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _153_353 = (let _153_352 = (let _153_351 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _153_350 = (FStar_TypeChecker_Env.get_range env)
in ((_153_351), (_153_350))))
in FStar_Syntax_Syntax.Error (_153_352))
in (Prims.raise _153_353))
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
(let _153_355 = (let _153_354 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" _153_354))
in (FStar_All.failwith _153_355))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (match ((let _153_356 = (FStar_Syntax_Subst.compress t1)
in _153_356.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_838) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _58_841 -> begin
(

let imp = (("uvar in term"), (env), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let _58_843 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_843.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_843.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_843.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _58_858 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(

let _58_851 = (FStar_Syntax_Util.type_u ())
in (match (_58_851) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
end))
end
| Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end)
in (match (_58_858) with
| (t, _58_856, g0) -> begin
(

let _58_863 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (_58_863) with
| (e, _58_861, g1) -> begin
(let _153_359 = (let _153_357 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right _153_357 FStar_Syntax_Util.lcomp_of_comp))
in (let _153_358 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e), (_153_359), (_153_358))))
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

let _58_867 = x
in {FStar_Syntax_Syntax.ppname = _58_867.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_867.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let _58_873 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_873) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _153_361 = (let _153_360 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _153_360))
in FStar_Util.Inr (_153_361))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _58_880; FStar_Syntax_Syntax.pos = _58_878; FStar_Syntax_Syntax.vars = _58_876}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let _58_890 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_890) with
| (us', t) -> begin
(

let _58_897 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _153_364 = (let _153_363 = (let _153_362 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (_153_362)))
in FStar_Syntax_Syntax.Error (_153_363))
in (Prims.raise _153_364))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _58_896 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (

let fv' = (

let _58_899 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _58_901 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_901.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_901.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_899.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_899.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _153_367 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _153_367 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let _58_909 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_909) with
| (us, t) -> begin
(

let _58_910 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Range"))) then begin
(let _153_377 = (let _153_368 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Syntax_Print.lid_to_string _153_368))
in (let _153_376 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _153_375 = (let _153_370 = (let _153_369 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.range_of_lid _153_369))
in (FStar_Range.string_of_range _153_370))
in (let _153_374 = (let _153_372 = (let _153_371 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.range_of_lid _153_371))
in (FStar_Range.string_of_use_range _153_372))
in (let _153_373 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print5 "Lookup up fvar %s at location %s (lid range = %s, %s); got type %s" _153_377 _153_376 _153_375 _153_374 _153_373))))))
end else begin
()
end
in (

let fv' = (

let _58_912 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _58_914 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_914.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_914.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_912.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_912.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _153_378 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _153_378 us))
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

let _58_928 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_928) with
| (bs, c) -> begin
(

let env0 = env
in (

let _58_933 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_933) with
| (env, _58_932) -> begin
(

let _58_938 = (tc_binders env bs)
in (match (_58_938) with
| (bs, env, g, us) -> begin
(

let _58_942 = (tc_comp env c)
in (match (_58_942) with
| (c, uc, f) -> begin
(

let e = (

let _58_943 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _58_943.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_943.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_943.FStar_Syntax_Syntax.vars})
in (

let _58_946 = (check_smt_pat env e bs c)
in (

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _153_379 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _153_379))
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

let _58_962 = (let _153_381 = (let _153_380 = (FStar_Syntax_Syntax.mk_binder x)
in (_153_380)::[])
in (FStar_Syntax_Subst.open_term _153_381 phi))
in (match (_58_962) with
| (x, phi) -> begin
(

let env0 = env
in (

let _58_967 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_967) with
| (env, _58_966) -> begin
(

let _58_972 = (let _153_382 = (FStar_List.hd x)
in (tc_binder env _153_382))
in (match (_58_972) with
| (x, env, f1, u) -> begin
(

let _58_973 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_385 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _153_384 = (FStar_Syntax_Print.term_to_string phi)
in (let _153_383 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _153_385 _153_384 _153_383))))
end else begin
()
end
in (

let _58_978 = (FStar_Syntax_Util.type_u ())
in (match (_58_978) with
| (t_phi, _58_977) -> begin
(

let _58_983 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_58_983) with
| (phi, _58_981, f2) -> begin
(

let e = (

let _58_984 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _58_984.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_984.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_984.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _153_386 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _153_386))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _58_992) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (

let _58_998 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_387 = (FStar_Syntax_Print.term_to_string (

let _58_996 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))); FStar_Syntax_Syntax.tk = _58_996.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _58_996.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_996.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _153_387))
end else begin
()
end
in (

let _58_1002 = (FStar_Syntax_Subst.open_term bs body)
in (match (_58_1002) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _58_1004 -> begin
(let _153_390 = (let _153_389 = (FStar_Syntax_Print.term_to_string top)
in (let _153_388 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" _153_389 _153_388)))
in (FStar_All.failwith _153_390))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_58_1009) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_58_1012, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_58_1017, Some (_58_1019)) -> begin
(FStar_All.failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (_58_1024) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_58_1027) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_58_1030) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_58_1034) -> begin
FStar_TypeChecker_Common.t_range
end
| _58_1037 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _58_1043) -> begin
(

let _58_1048 = (FStar_Syntax_Util.type_u ())
in (match (_58_1048) with
| (k, u) -> begin
(

let _58_1053 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_1053) with
| (t, _58_1051, g) -> begin
(let _153_395 = (FStar_Syntax_Syntax.mk_Total' t (Some (u)))
in ((_153_395), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t, _58_1056) -> begin
(

let _58_1061 = (FStar_Syntax_Util.type_u ())
in (match (_58_1061) with
| (k, u) -> begin
(

let _58_1066 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_1066) with
| (t, _58_1064, g) -> begin
(let _153_396 = (FStar_Syntax_Syntax.mk_GTotal' t (Some (u)))
in ((_153_396), (u), (g)))
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

let tc = (let _153_398 = (let _153_397 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_153_397)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _153_398 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let _58_1078 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_58_1078) with
| (tc, _58_1076, f) -> begin
(

let _58_1081 = (FStar_Syntax_Util.head_and_args tc)
in (match (_58_1081) with
| (head, args) -> begin
(

let comp_univs = (match ((let _153_399 = (FStar_Syntax_Subst.compress head)
in _153_399.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (_58_1083, us) -> begin
us
end
| _58_1088 -> begin
[]
end)
in (

let _58_1093 = (FStar_Syntax_Util.head_and_args tc)
in (match (_58_1093) with
| (_58_1091, args) -> begin
(

let _58_1096 = (let _153_401 = (FStar_List.hd args)
in (let _153_400 = (FStar_List.tl args)
in ((_153_401), (_153_400))))
in (match (_58_1096) with
| (res, args) -> begin
(

let _58_1112 = (let _153_403 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _58_4 -> (match (_58_4) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _58_1103 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1103) with
| (env, _58_1102) -> begin
(

let _58_1108 = (tc_tot_or_gtot_term env e)
in (match (_58_1108) with
| (e, _58_1106, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e)), (g))
end))
end))
end
| f -> begin
((f), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right _153_403 FStar_List.unzip))
in (match (_58_1112) with
| (flags, guards) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (Prims.fst res))
in (

let c = (FStar_Syntax_Syntax.mk_Comp (

let _58_1114 = c
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = _58_1114.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _58_1114.FStar_Syntax_Syntax.flags}))
in (

let u_c = (match ((FStar_TypeChecker_Util.effect_repr env c u)) with
| None -> begin
u
end
| Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end)
in (let _153_404 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((c), (u_c), (_153_404))))))
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
| FStar_Syntax_Syntax.U_bvar (_58_1127) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _153_409 = (aux u)
in FStar_Syntax_Syntax.U_succ (_153_409))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _153_410 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_153_410))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _153_414 = (let _153_413 = (let _153_412 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _153_411 = (FStar_TypeChecker_Env.get_range env)
in ((_153_412), (_153_411))))
in FStar_Syntax_Syntax.Error (_153_413))
in (Prims.raise _153_414))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _153_415 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_415 Prims.snd))
end
| _58_1142 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _153_424 = (let _153_423 = (let _153_422 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in ((_153_422), (top.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_153_423))
in (Prims.raise _153_424)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun _58_1160 bs bs_expected -> (match (_58_1160) with
| (env, out, g, subst) -> begin
(match (((bs), (bs_expected))) with
| ([], []) -> begin
((env), ((FStar_List.rev out)), (None), (g), (subst))
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
(

let _58_1191 = (match (((imp), (imp'))) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _153_441 = (let _153_440 = (let _153_439 = (let _153_437 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _153_437))
in (let _153_438 = (FStar_Syntax_Syntax.range_of_bv hd)
in ((_153_439), (_153_438))))
in FStar_Syntax_Syntax.Error (_153_440))
in (Prims.raise _153_441))
end
| _58_1190 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _58_1208 = (match ((let _153_442 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _153_442.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| _58_1196 -> begin
(

let _58_1197 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_443 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _153_443))
end else begin
()
end
in (

let _58_1203 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_58_1203) with
| (t, _58_1201, g1) -> begin
(

let g2 = (let _153_445 = (FStar_TypeChecker_Env.get_range env)
in (let _153_444 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _153_445 "Type annotation on parameter incompatible with the expected type" _153_444)))
in (

let g = (let _153_446 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _153_446))
in ((t), (g))))
end)))
end)
in (match (_58_1208) with
| (t, g) -> begin
(

let hd = (

let _58_1209 = hd
in {FStar_Syntax_Syntax.ppname = _58_1209.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1209.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env = (push_binding env b)
in (

let subst = (let _153_447 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _153_447))
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

let _58_1230 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _58_1229 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (

let _58_1237 = (tc_binders env bs)
in (match (_58_1237) with
| (bs, envbody, g, _58_1236) -> begin
(

let _58_1255 = (match ((let _153_454 = (FStar_Syntax_Subst.compress body)
in _153_454.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _58_1242) -> begin
(

let _58_1249 = (tc_comp envbody c)
in (match (_58_1249) with
| (c, _58_1247, g') -> begin
(let _153_455 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((Some (c)), (body), (_153_455)))
end))
end
| _58_1251 -> begin
((None), (body), (g))
end)
in (match (_58_1255) with
| (copt, body, g) -> begin
((None), (bs), ([]), (copt), (envbody), (body), (g))
end))
end)))
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm t -> (match ((let _153_460 = (FStar_Syntax_Subst.compress t)
in _153_460.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let _58_1282 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _58_1281 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _58_1289 = (tc_binders env bs)
in (match (_58_1289) with
| (bs, envbody, g, _58_1288) -> begin
(

let _58_1293 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_58_1293) with
| (envbody, _58_1292) -> begin
((Some (((t), (true)))), (bs), ([]), (None), (envbody), (body), (g))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _58_1296) -> begin
(

let _58_1307 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_58_1307) with
| (_58_1300, bs, bs', copt, env, body, g) -> begin
((Some (((t), (false)))), (bs), (bs'), (copt), (env), (body), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _58_1314 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_58_1314) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun _58_1325 c_expected -> (match (_58_1325) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _153_471 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in ((env), (bs), (guard), (_153_471)))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (let _153_472 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _153_472))
in (let _153_473 = (FStar_Syntax_Subst.subst_comp subst c)
in ((env), (bs), (guard), (_153_473))))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(

let c = (FStar_Syntax_Subst.subst_comp subst c_expected)
in if (FStar_Syntax_Util.is_total_comp c) then begin
(

let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _58_1346 = (check_binders env more_bs bs_expected)
in (match (_58_1346) with
| (env, bs', more, guard', subst) -> begin
(let _153_475 = (let _153_474 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env), ((FStar_List.append bs bs')), (more), (_153_474), (subst)))
in (handle_more _153_475 c_expected))
end))
end
| _58_1348 -> begin
(let _153_477 = (let _153_476 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _153_476))
in (fail _153_477 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _153_478 = (check_binders env bs bs_expected)
in (handle_more _153_478 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let _58_1354 = envbody
in {FStar_TypeChecker_Env.solver = _58_1354.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1354.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1354.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1354.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1354.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1354.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1354.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1354.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1354.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1354.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1354.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1354.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _58_1354.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1354.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1354.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1354.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1354.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1354.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_1354.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_1354.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1354.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1354.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1354.FStar_TypeChecker_Env.qname_and_index})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _58_1359 _58_1362 -> (match (((_58_1359), (_58_1362))) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _58_1368 = (let _153_488 = (let _153_487 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _153_487 Prims.fst))
in (tc_term _153_488 t))
in (match (_58_1368) with
| (t, _58_1365, _58_1367) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l (([]), (t)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _153_489 = (FStar_Syntax_Syntax.mk_binder (

let _58_1372 = x
in {FStar_Syntax_Syntax.ppname = _58_1372.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1372.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_153_489)::letrec_binders)
end
| _58_1375 -> begin
letrec_binders
end)
in ((env), (lb))))
end))
end)) ((envbody), ([])))))))
in (

let _58_1381 = (check_actuals_against_formals env bs bs_expected)
in (match (_58_1381) with
| (envbody, bs, g, c) -> begin
(

let _58_1384 = if (FStar_TypeChecker_Env.should_verify env) then begin
(mk_letrec_env envbody bs c)
end else begin
((envbody), ([]))
end
in (match (_58_1384) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in ((Some (((t), (false)))), (bs), (letrecs), (Some (c)), (envbody), (body), (g)))
end))
end))))
end))
end
| _58_1387 -> begin
if (not (norm)) then begin
(let _153_490 = (unfold_whnf env t)
in (as_function_typ true _153_490))
end else begin
(

let _58_1397 = (expected_function_typ env None body)
in (match (_58_1397) with
| (_58_1389, bs, _58_1392, c_opt, envbody, body, g) -> begin
((Some (((t), (false)))), (bs), ([]), (c_opt), (envbody), (body), (g))
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let _58_1401 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1401) with
| (env, topt) -> begin
(

let _58_1405 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_491 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _153_491 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (

let _58_1414 = (expected_function_typ env topt body)
in (match (_58_1414) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let _58_1420 = (tc_term (

let _58_1415 = envbody
in {FStar_TypeChecker_Env.solver = _58_1415.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1415.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1415.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1415.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1415.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1415.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1415.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1415.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1415.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1415.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1415.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1415.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1415.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_1415.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1415.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1415.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1415.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_1415.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_1415.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1415.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1415.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1415.FStar_TypeChecker_Env.qname_and_index}) body)
in (match (_58_1420) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _58_1422 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _153_494 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _153_493 = (let _153_492 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _153_492))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _153_494 _153_493)))
end else begin
()
end
in (

let _58_1429 = (let _153_496 = (let _153_495 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body), (_153_495)))
in (check_expected_effect (

let _58_1424 = envbody
in {FStar_TypeChecker_Env.solver = _58_1424.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1424.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1424.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1424.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1424.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1424.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1424.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1424.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1424.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1424.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1424.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1424.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1424.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1424.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1424.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1424.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1424.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1424.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_1424.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_1424.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1424.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1424.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1424.FStar_TypeChecker_Env.qname_and_index}) c_opt _153_496))
in (match (_58_1429) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(let _153_497 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _153_497))
end else begin
(

let guard = (let _153_498 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) _153_498))
in guard)
end
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _153_501 = (let _153_500 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _153_499 -> FStar_Util.Inl (_153_499)))
in Some (_153_500))
in (FStar_Syntax_Util.abs bs body _153_501))
in (

let _58_1452 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_58_1441) -> begin
((e), (t), (guard))
end
| _58_1444 -> begin
(

let _58_1447 = if use_teq then begin
(let _153_502 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in ((e), (_153_502)))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_58_1447) with
| (e, guard') -> begin
(let _153_503 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((e), (t), (_153_503)))
end))
end))
end
| None -> begin
((e), (tfun_computed), (guard))
end)
in (match (_58_1452) with
| (e, tfun, guard) -> begin
(

let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (

let _58_1456 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_58_1456) with
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

let _58_1466 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_512 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _153_511 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _153_512 _153_511)))
end else begin
()
end
in (

let monadic_application = (fun _58_1473 subst arg_comps_rev arg_rets guard fvs bs -> (match (_58_1473) with
| (head, chead, ghead, cres) -> begin
(

let rt = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _58_1481 = cres
in {FStar_Syntax_Syntax.eff_name = _58_1481.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = rt; FStar_Syntax_Syntax.cflags = _58_1481.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_1481.FStar_Syntax_Syntax.comp})
in (

let _58_1512 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun _58_5 -> (match (_58_5) with
| (_58_1489, _58_1491, FStar_Util.Inl (_58_1493)) -> begin
false
end
| (_58_1497, _58_1499, FStar_Util.Inr (c)) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _153_528 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _153_528 cres))
end else begin
(

let _58_1504 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_531 = (FStar_Syntax_Print.term_to_string head)
in (let _153_530 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _153_529 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _153_531 _153_530 _153_529))))
end else begin
()
end
in cres)
end
in ((cres), (g))))))
end
| _58_1508 -> begin
(

let g = (let _153_532 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right _153_532 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _153_537 = (let _153_536 = (let _153_535 = (let _153_534 = (let _153_533 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _153_533))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _153_534))
in (FStar_Syntax_Syntax.mk_Total _153_535))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _153_536))
in ((_153_537), (g))))
end)
in (match (_58_1512) with
| (cres, guard) -> begin
(

let _58_1513 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_538 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _153_538))
end else begin
()
end
in (

let _58_1536 = (FStar_List.fold_left (fun _58_1518 _58_1524 -> (match (((_58_1518), (_58_1524))) with
| ((args, out_c, monadic), ((e, q), x, c)) -> begin
(match (c) with
| FStar_Util.Inl (eff_name) -> begin
(let _153_543 = (let _153_542 = (let _153_541 = (FStar_TypeChecker_Util.maybe_lift env e eff_name out_c.FStar_Syntax_Syntax.eff_name)
in ((_153_541), (q)))
in (_153_542)::args)
in ((_153_543), (out_c), (monadic)))
end
| FStar_Util.Inr (c) -> begin
(

let monadic = (monadic || (not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c))))
in (

let out_c = (FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env None c ((x), (out_c)))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e c.FStar_Syntax_Syntax.eff_name out_c.FStar_Syntax_Syntax.eff_name)
in (((((e), (q)))::args), (out_c), (monadic))))))
end)
end)) (([]), (cres), (false)) arg_comps_rev)
in (match (_58_1536) with
| (args, comp, monadic) -> begin
(

let comp = (FStar_TypeChecker_Util.bind head.FStar_Syntax_Syntax.pos env None chead ((None), (comp)))
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app = if monadic then begin
(FStar_TypeChecker_Util.maybe_monadic env app comp.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.res_typ)
end else begin
app
end
in (

let _58_1542 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (_58_1542) with
| (comp, g) -> begin
((app), (comp), (g))
end)))))
end)))
end))))
end))
in (

let rec tc_args = (fun head_info _58_1550 bs args -> (match (_58_1550) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args))) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (_58_1556))))::rest, ((_58_1564, None))::_58_1562) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let t = (check_no_escape (Some (head)) env fvs t)
in (

let _58_1575 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_58_1575) with
| (varg, _58_1573, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst
in (

let arg = (let _153_553 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (_153_553)))
in (let _153_555 = (let _153_554 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst), ((((arg), (None), (FStar_Util.Inl (FStar_Syntax_Const.effect_Tot_lid))))::outargs), ((arg)::arg_rets), (_153_554), (fvs)))
in (tc_args head_info _153_555 rest args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
(

let _58_1607 = (match (((aqual), (aq))) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _58_1606 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifier"), (e.FStar_Syntax_Syntax.pos)))))
end)
in (

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let _58_1610 = x
in {FStar_Syntax_Syntax.ppname = _58_1610.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1610.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (

let _58_1613 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _153_556 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _153_556))
end else begin
()
end
in (

let targ = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let _58_1617 = env
in {FStar_TypeChecker_Env.solver = _58_1617.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1617.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1617.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1617.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1617.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1617.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1617.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1617.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1617.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1617.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1617.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1617.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1617.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1617.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1617.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _58_1617.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1617.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1617.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_1617.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_1617.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1617.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1617.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1617.FStar_TypeChecker_Env.qname_and_index})
in (

let _58_1620 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_559 = (FStar_Syntax_Print.tag_of_term e)
in (let _153_558 = (FStar_Syntax_Print.term_to_string e)
in (let _153_557 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _153_559 _153_558 _153_557))))
end else begin
()
end
in (

let _58_1625 = (tc_term env e)
in (match (_58_1625) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = ((e), (aq))
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(

let subst = (let _153_560 = (FStar_List.hd bs)
in (maybe_extend_subst subst _153_560 e))
in (tc_args head_info ((subst), ((((arg), (None), (FStar_Util.Inl (c.FStar_Syntax_Syntax.eff_name))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(

let subst = (let _153_561 = (FStar_List.hd bs)
in (maybe_extend_subst subst _153_561 e))
in (tc_args head_info ((subst), ((((arg), (Some (x)), (FStar_Util.Inr (c))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (let _153_562 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _153_562)) then begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _153_563 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _153_563))
in (tc_args head_info ((subst), ((((arg), (Some (newx)), (FStar_Util.Inr (c))))::outargs), ((arg')::arg_rets), (g), (fvs)) rest rest')))
end else begin
(let _153_567 = (let _153_566 = (let _153_565 = (let _153_564 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _153_564))
in (_153_565)::arg_rets)
in ((subst), ((((arg), (Some (x)), (FStar_Util.Inr (c))))::outargs), (_153_566), (g), ((x)::fvs)))
in (tc_args head_info _153_567 rest rest'))
end
end
end))
end))))))))))
end
| (_58_1633, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::_58_1638) -> begin
(

let _58_1645 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (_58_1645) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _153_572 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _153_572 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let _58_1656 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (_58_1656) with
| (bs, cres') -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp cres')))
in (

let _58_1658 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_573 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _153_573))
end else begin
()
end
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args)))
end))
end
| _58_1661 when (not (norm)) -> begin
(let _153_574 = (unfold_whnf env tres)
in (aux true _153_574))
end
| _58_1663 -> begin
(let _153_580 = (let _153_579 = (let _153_578 = (let _153_576 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (let _153_575 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _153_576 _153_575)))
in (let _153_577 = (FStar_Syntax_Syntax.argpos arg)
in ((_153_578), (_153_577))))
in FStar_Syntax_Syntax.Error (_153_579))
in (Prims.raise _153_580))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (match ((let _153_585 = (FStar_Syntax_Util.unrefine tf)
in _153_585.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl -> begin
(

let _58_1696 = (tc_term env e)
in (match (_58_1696) with
| (e, c, g_e) -> begin
(

let _58_1700 = (tc_args env tl)
in (match (_58_1700) with
| (args, comps, g_rest) -> begin
(let _153_590 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e), (imp)))::args), ((((e.FStar_Syntax_Syntax.pos), (c)))::comps), (_153_590)))
end))
end))
end))
in (

let _58_1704 = (tc_args env args)
in (match (_58_1704) with
| (args, comps, g_args) -> begin
(

let bs = (let _153_592 = (FStar_All.pipe_right comps (FStar_List.map (fun _58_1708 -> (match (_58_1708) with
| (_58_1706, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks _153_592))
in (

let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _58_1714 -> begin
FStar_Syntax_Util.ml_comp
end)
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _153_607 = (FStar_Syntax_Subst.compress t)
in _153_607.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_58_1720) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _58_1725 -> begin
ml_or_tot
end)
end)
in (

let cres = (let _153_612 = (let _153_611 = (let _153_610 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_610 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _153_611))
in (ml_or_tot _153_612 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (

let _58_1729 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _153_615 = (FStar_Syntax_Print.term_to_string head)
in (let _153_614 = (FStar_Syntax_Print.term_to_string tf)
in (let _153_613 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _153_615 _153_614 _153_613))))
end else begin
()
end
in (

let _58_1731 = (let _153_616 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _153_616))
in (

let comp = (let _153_619 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _58_1735 out -> (match (_58_1735) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c ((None), (out)))
end)) ((((head.FStar_Syntax_Syntax.pos), (chead)))::comps) _153_619))
in (let _153_621 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _153_620 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((_153_621), (comp), (_153_620))))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _58_1744 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_1744) with
| (bs, c) -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp c)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args))
end))
end
| _58_1747 -> begin
if (not (norm)) then begin
(let _153_622 = (unfold_whnf env tf)
in (check_function_app true _153_622))
end else begin
(let _153_625 = (let _153_624 = (let _153_623 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in ((_153_623), (head.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_153_624))
in (Prims.raise _153_625))
end
end))
in (let _153_627 = (let _153_626 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _153_626))
in (check_function_app false _153_627))))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let _58_1783 = (FStar_List.fold_left2 (fun _58_1764 _58_1767 _58_1770 -> (match (((_58_1764), (_58_1767), (_58_1770))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(

let _58_1771 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifiers"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _58_1776 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_58_1776) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (let _153_637 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _153_637 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _153_641 = (let _153_639 = (let _153_638 = (FStar_Syntax_Syntax.as_arg e)
in (_153_638)::[])
in (FStar_List.append seen _153_639))
in (let _153_640 = (FStar_TypeChecker_Rel.conj_guard guard g)
in ((_153_641), (_153_640), (ghost)))))))
end)))
end)) (([]), (g_head), (false)) args bs)
in (match (_58_1783) with
| (args, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = if ghost then begin
(let _153_642 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _153_642 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (

let _58_1788 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_58_1788) with
| (c, g) -> begin
((e), (c), (g))
end))))
end)))
end
| _58_1790 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let _58_1797 = (FStar_Syntax_Subst.open_branch branch)
in (match (_58_1797) with
| (pattern, when_clause, branch_exp) -> begin
(

let _58_1802 = branch
in (match (_58_1802) with
| (cpat, _58_1800, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _58_1810 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_58_1810) with
| (pat_bvs, exps, p) -> begin
(

let _58_1811 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_654 = (FStar_Syntax_Print.pat_to_string p0)
in (let _153_653 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _153_654 _153_653)))
end else begin
()
end
in (

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let _58_1817 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_58_1817) with
| (env1, _58_1816) -> begin
(

let env1 = (

let _58_1818 = env1
in {FStar_TypeChecker_Env.solver = _58_1818.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1818.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1818.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1818.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1818.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1818.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1818.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1818.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _58_1818.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1818.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1818.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1818.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1818.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1818.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1818.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1818.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1818.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1818.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_1818.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_1818.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1818.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1818.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1818.FStar_TypeChecker_Env.qname_and_index})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _58_1857 = (let _153_677 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _58_1823 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_657 = (FStar_Syntax_Print.term_to_string e)
in (let _153_656 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _153_657 _153_656)))
end else begin
()
end
in (

let _58_1828 = (tc_term env1 e)
in (match (_58_1828) with
| (e, lc, g) -> begin
(

let _58_1829 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_659 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _153_658 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _153_659 _153_658)))
end else begin
()
end
in (

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let _58_1835 = (let _153_660 = (FStar_TypeChecker_Rel.discharge_guard env (

let _58_1833 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_1833.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_1833.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_1833.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _153_660 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _153_665 = (let _153_664 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _153_664 (FStar_List.map (fun _58_1843 -> (match (_58_1843) with
| (u, _58_1842) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _153_665 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _58_1851 = if (let _153_666 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _153_666)) then begin
(

let unresolved = (let _153_667 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _153_667 FStar_Util.set_elements))
in (let _153_675 = (let _153_674 = (let _153_673 = (let _153_672 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _153_671 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _153_670 = (let _153_669 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _58_1850 -> (match (_58_1850) with
| (u, _58_1849) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _153_669 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _153_672 _153_671 _153_670))))
in ((_153_673), (p.FStar_Syntax_Syntax.p)))
in FStar_Syntax_Syntax.Error (_153_674))
in (Prims.raise _153_675)))
end else begin
()
end
in (

let _58_1853 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_676 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _153_676))
end else begin
()
end
in ((e), (e'))))))))))))
end))))))
in (FStar_All.pipe_right _153_677 FStar_List.unzip))
in (match (_58_1857) with
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

let _58_1864 = (let _153_678 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _153_678 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_58_1864) with
| (scrutinee_env, _58_1863) -> begin
(

let _58_1870 = (tc_pat true pat_t pattern)
in (match (_58_1870) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let _58_1880 = (match (when_clause) with
| None -> begin
((None), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (e) -> begin
if (FStar_TypeChecker_Env.should_verify env) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("When clauses are not yet supported in --verify mode; they will be some day"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
(

let _58_1877 = (let _153_679 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _153_679 e))
in (match (_58_1877) with
| (e, c, g) -> begin
((Some (e)), (g))
end))
end
end)
in (match (_58_1880) with
| (when_clause, g_when) -> begin
(

let _58_1884 = (tc_term pat_env branch_exp)
in (match (_58_1884) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _153_681 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _153_680 -> Some (_153_680)) _153_681))
end)
in (

let _58_1942 = (

let eqs = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
None
end else begin
(FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _58_1902 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _153_685 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _153_684 -> Some (_153_684)) _153_685))
end))
end))) None))
end
in (

let _58_1910 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_58_1910) with
| (c, g_branch) -> begin
(

let _58_1937 = (match (((eqs), (when_condition))) with
| _58_1912 when (not ((FStar_TypeChecker_Env.should_verify env))) -> begin
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
in (let _153_688 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _153_687 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((_153_688), (_153_687))))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (let _153_689 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_153_689))
in (let _153_692 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _153_691 = (let _153_690 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _153_690 g_when))
in ((_153_692), (_153_691))))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _153_693 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in ((_153_693), (g_when)))))
end)
in (match (_58_1937) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _153_695 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _153_694 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in ((_153_695), (_153_694), (g_branch)))))
end))
end)))
in (match (_58_1942) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
FStar_Syntax_Util.t_true
end else begin
(

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> if ((let _153_705 = (let _153_704 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _153_704))
in (FStar_List.length _153_705)) > (Prims.parse_int "1")) then begin
(

let disc = (let _153_706 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _153_706 FStar_Syntax_Syntax.Delta_equational None))
in (

let disc = (let _153_708 = (let _153_707 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_153_707)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _153_708 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _153_709 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_153_709)::[])))
end else begin
[]
end)
in (

let fail = (fun _58_1952 -> (match (()) with
| () -> begin
(let _153_715 = (let _153_714 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _153_713 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _153_712 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _153_714 _153_713 _153_712))))
in (FStar_All.failwith _153_715))
end))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _58_1959) -> begin
(head_constructor t)
end
| _58_1963 -> begin
(fail ())
end))
in (

let pat_exp = (let _153_718 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _153_718 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_58_1988) -> begin
(let _153_723 = (let _153_722 = (let _153_721 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _153_720 = (let _153_719 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_153_719)::[])
in (_153_721)::_153_720))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _153_722 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_153_723)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _153_724 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _153_724))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(

let sub_term_guards = (let _153_730 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _58_2006 -> (match (_58_2006) with
| (ei, _58_2005) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _58_2010 -> begin
(

let sub_term = (let _153_729 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p) FStar_Syntax_Syntax.Delta_equational None)
in (let _153_728 = (let _153_727 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_153_727)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _153_729 _153_728 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _153_730 FStar_List.flatten))
in (let _153_731 = (discriminate scrutinee_tm f)
in (FStar_List.append _153_731 sub_term_guards)))
end)
end
| _58_2014 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(

let t = (let _153_736 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _153_736))
in (

let _58_2022 = (FStar_Syntax_Util.type_u ())
in (match (_58_2022) with
| (k, _58_2021) -> begin
(

let _58_2028 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_58_2028) with
| (t, _58_2025, _58_2027) -> begin
t
end))
end)))
end)
in (

let branch_guard = (let _153_737 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _153_737 FStar_Syntax_Util.mk_disj_l))
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

let _58_2036 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_738 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _153_738))
end else begin
()
end
in (let _153_739 = (FStar_Syntax_Subst.close_branch ((pattern), (when_clause), (branch_exp)))
in ((_153_739), (branch_guard), (c), (guard))))))
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

let _58_2053 = (check_let_bound_def true env lb)
in (match (_58_2053) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let _58_2065 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
((g1), (e1), (univ_vars), (c1))
end else begin
(

let g1 = (let _153_742 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _153_742 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _58_2060 = (let _153_746 = (let _153_745 = (let _153_744 = (let _153_743 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (_153_743)))
in (_153_744)::[])
in (FStar_TypeChecker_Util.generalize env _153_745))
in (FStar_List.hd _153_746))
in (match (_58_2060) with
| (_58_2056, univs, e1, c1) -> begin
((g1), (e1), (univs), ((FStar_Syntax_Util.lcomp_of_comp c1)))
end)))
end
in (match (_58_2065) with
| (g1, e1, univ_vars, c1) -> begin
(

let _58_2076 = if (FStar_TypeChecker_Env.should_verify env) then begin
(

let _58_2068 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_58_2068) with
| (ok, c1) -> begin
if ok then begin
((e2), (c1))
end else begin
(

let _58_2069 = if (FStar_Options.warn_top_level_effects ()) then begin
(let _153_747 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _153_747 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _153_748 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) None e2.FStar_Syntax_Syntax.pos)
in ((_153_748), (c1))))
end
end))
end else begin
(

let _58_2071 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (

let c = (let _153_749 = (c1.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_right _153_749 (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env)))
in ((e2), (c))))
end
in (match (_58_2076) with
| (e2, c1) -> begin
(

let cres = (let _153_750 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _153_750))
in (

let _58_2078 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _153_751 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((_153_751), (cres), (FStar_TypeChecker_Rel.trivial_guard))))))
end))
end))
end))
end
| _58_2082 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let _58_2093 = env
in {FStar_TypeChecker_Env.solver = _58_2093.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2093.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2093.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2093.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2093.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2093.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2093.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2093.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2093.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2093.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2093.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2093.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2093.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_2093.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2093.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2093.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2093.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2093.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_2093.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_2093.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2093.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2093.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2093.FStar_TypeChecker_Env.qname_and_index})
in (

let _58_2102 = (let _153_755 = (let _153_754 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _153_754 Prims.fst))
in (check_let_bound_def false _153_755 lb))
in (match (_58_2102) with
| (e1, _58_2098, c1, g1, annotated) -> begin
(

let x = (

let _58_2103 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_2103.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2103.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let _58_2108 = (let _153_757 = (let _153_756 = (FStar_Syntax_Syntax.mk_binder x)
in (_153_756)::[])
in (FStar_Syntax_Subst.open_term _153_757 e2))
in (match (_58_2108) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _58_2114 = (let _153_758 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _153_758 e2))
in (match (_58_2114) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (x)), (c2)))
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e2 = (FStar_TypeChecker_Util.maybe_lift env e2 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let e = (let _153_761 = (let _153_760 = (let _153_759 = (FStar_Syntax_Subst.close xb e2)
in ((((false), ((lb)::[]))), (_153_759)))
in FStar_Syntax_Syntax.Tm_let (_153_760))
in (FStar_Syntax_Syntax.mk _153_761 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (let _153_764 = (let _153_763 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _153_763 e1))
in (FStar_All.pipe_left (fun _153_762 -> FStar_TypeChecker_Common.NonTrivial (_153_762)) _153_764))
in (

let g2 = (let _153_766 = (let _153_765 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _153_765 g2))
in (FStar_TypeChecker_Rel.close_guard xb _153_766))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if (let _153_767 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome _153_767)) then begin
(

let tt = (let _153_768 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_All.pipe_right _153_768 FStar_Option.get))
in (

let _58_2125 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Exports"))) then begin
(let _153_770 = (FStar_Syntax_Print.term_to_string tt)
in (let _153_769 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Got expected type from env %s\ncres.res_typ=%s\n" _153_770 _153_769)))
end else begin
()
end
in ((e), (cres), (guard))))
end else begin
(

let t = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (

let _58_2128 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Exports"))) then begin
(let _153_772 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (let _153_771 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checked %s has no escaping types; normalized to %s\n" _153_772 _153_771)))
end else begin
()
end
in ((e), ((

let _58_2130 = cres
in {FStar_Syntax_Syntax.eff_name = _58_2130.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_2130.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_2130.FStar_Syntax_Syntax.comp})), (guard))))
end)))))))))
end))))
end)))
end)))
end
| _58_2133 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _58_2145 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_58_2145) with
| (lbs, e2) -> begin
(

let _58_2148 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2148) with
| (env0, topt) -> begin
(

let _58_2151 = (build_let_rec_env true env0 lbs)
in (match (_58_2151) with
| (lbs, rec_env) -> begin
(

let _58_2154 = (check_let_recs rec_env lbs)
in (match (_58_2154) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (let _153_775 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _153_775 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _153_778 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _153_778 (fun _153_777 -> Some (_153_777))))
in (

let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(

let ecs = (let _153_782 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _153_781 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (_153_781))))))
in (FStar_TypeChecker_Util.generalize env _153_782))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _58_2165 -> (match (_58_2165) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _153_784 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _153_784))
in (

let _58_2168 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _58_2172 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_2172) with
| (lbs, e2) -> begin
(let _153_786 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _153_785 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in ((_153_786), (cres), (_153_785))))
end)))))))
end))
end))
end))
end))
end
| _58_2174 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _58_2186 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_58_2186) with
| (lbs, e2) -> begin
(

let _58_2189 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2189) with
| (env0, topt) -> begin
(

let _58_2192 = (build_let_rec_env false env0 lbs)
in (match (_58_2192) with
| (lbs, rec_env) -> begin
(

let _58_2195 = (check_let_recs rec_env lbs)
in (match (_58_2195) with
| (lbs, g_lbs) -> begin
(

let _58_2207 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let _58_2198 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_2198.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2198.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let _58_2201 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _58_2201.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _58_2201.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _58_2201.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _58_2201.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (lb.FStar_Syntax_Syntax.lbtyp)))
in ((env), (lb)))))) env))
in (match (_58_2207) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let _58_2213 = (tc_term env e2)
in (match (_58_2213) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _58_2217 = cres
in {FStar_Syntax_Syntax.eff_name = _58_2217.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _58_2217.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_2217.FStar_Syntax_Syntax.comp})
in (

let _58_2222 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_2222) with
| (lbs, e2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_58_2225) -> begin
((e), (cres), (guard))
end
| None -> begin
(

let tres = (check_no_escape None env bvs tres)
in (

let cres = (

let _58_2229 = cres
in {FStar_Syntax_Syntax.eff_name = _58_2229.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _58_2229.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_2229.FStar_Syntax_Syntax.comp})
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
| _58_2233 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun t -> (

let _58_2243 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (_58_2243) with
| (_58_2241, c) -> begin
(

let quals = (FStar_TypeChecker_Env.lookup_effect_quals env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
end)))
in (

let _58_2273 = (FStar_List.fold_left (fun _58_2247 lb -> (match (_58_2247) with
| (lbs, env) -> begin
(

let _58_2252 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_58_2252) with
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

let _58_2261 = (let _153_800 = (let _153_799 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _153_799))
in (tc_check_tot_or_gtot_term (

let _58_2255 = env0
in {FStar_TypeChecker_Env.solver = _58_2255.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2255.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2255.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2255.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2255.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2255.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2255.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2255.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2255.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2255.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2255.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2255.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2255.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2255.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _58_2255.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2255.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2255.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2255.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_2255.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_2255.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2255.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2255.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2255.FStar_TypeChecker_Env.qname_and_index}) t _153_800))
in (match (_58_2261) with
| (t, _58_2259, g) -> begin
(

let _58_2262 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (

let env = if ((termination_check_enabled t) && (FStar_TypeChecker_Env.should_verify env)) then begin
(

let _58_2265 = env
in {FStar_TypeChecker_Env.solver = _58_2265.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2265.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2265.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2265.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2265.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2265.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2265.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2265.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2265.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2265.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2265.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2265.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t)))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2265.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_2265.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2265.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2265.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2265.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2265.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_2265.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_2265.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2265.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2265.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2265.FStar_TypeChecker_Env.qname_and_index})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (t)))
end
in (

let lb = (

let _58_2268 = lb
in {FStar_Syntax_Syntax.lbname = _58_2268.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _58_2268.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb)::lbs), (env)))))))
end))
end)) (([]), (env)) lbs)
in (match (_58_2273) with
| (lbs, env) -> begin
(((FStar_List.rev lbs)), (env))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _58_2286 = (let _153_805 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _58_2280 = (let _153_804 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _153_804 lb.FStar_Syntax_Syntax.lbdef))
in (match (_58_2280) with
| (e, c, g) -> begin
(

let _58_2281 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in ((lb), (g))))
end)))))
in (FStar_All.pipe_right _153_805 FStar_List.unzip))
in (match (_58_2286) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _58_2294 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2294) with
| (env1, _58_2293) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _58_2300 = (check_lbtyp top_level env lb)
in (match (_58_2300) with
| (topt, wf_annot, univ_vars, env1) -> begin
(

let _58_2301 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _58_2308 = (tc_maybe_toplevel_term (

let _58_2303 = env1
in {FStar_TypeChecker_Env.solver = _58_2303.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2303.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2303.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2303.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2303.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2303.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2303.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2303.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2303.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2303.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2303.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2303.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2303.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _58_2303.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2303.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2303.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2303.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2303.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_2303.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_2303.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2303.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2303.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2303.FStar_TypeChecker_Env.qname_and_index}) e1)
in (match (_58_2308) with
| (e1, c1, g1) -> begin
(

let _58_2312 = (let _153_812 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_2309 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _153_812 e1 c1 wf_annot))
in (match (_58_2312) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _58_2314 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _153_815 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _153_814 = (FStar_Syntax_Print.term_to_string c1.FStar_Syntax_Syntax.res_typ)
in (let _153_813 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print3 "checked top-level def %s, result type is %s, guard is %s\n" _153_815 _153_814 _153_813))))
end else begin
()
end
in (let _153_816 = (FStar_Option.isSome topt)
in ((e1), (univ_vars), (c1), (g1), (_153_816)))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _58_2321 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in ((None), (FStar_TypeChecker_Rel.trivial_guard), ([]), (env)))
end
| _58_2324 -> begin
(

let _58_2327 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_58_2327) with
| (univ_vars, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _153_820 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars), (_153_820)))
end else begin
(

let _58_2332 = (FStar_Syntax_Util.type_u ())
in (match (_58_2332) with
| (k, _58_2331) -> begin
(

let _58_2337 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_58_2337) with
| (t, _58_2335, g) -> begin
(

let _58_2338 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _153_823 = (let _153_821 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _153_821))
in (let _153_822 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _153_823 _153_822)))
end else begin
()
end
in (

let t = (norm env1 t)
in (let _153_824 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (g), (univ_vars), (_153_824)))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _58_2344 -> (match (_58_2344) with
| (x, imp) -> begin
(

let _58_2347 = (FStar_Syntax_Util.type_u ())
in (match (_58_2347) with
| (tu, u) -> begin
(

let _58_2348 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _153_829 = (FStar_Syntax_Print.bv_to_string x)
in (let _153_828 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _153_827 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binders %s:%s at type %s\n" _153_829 _153_828 _153_827))))
end else begin
()
end
in (

let _58_2354 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_58_2354) with
| (t, _58_2352, g) -> begin
(

let x = (((

let _58_2355 = x
in {FStar_Syntax_Syntax.ppname = _58_2355.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2355.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in (

let _58_2358 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_831 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _153_830 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _153_831 _153_830)))
end else begin
()
end
in (let _153_832 = (push_binding env x)
in ((x), (_153_832), (g), (u)))))
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

let _58_2373 = (tc_binder env b)
in (match (_58_2373) with
| (b, env', g, u) -> begin
(

let _58_2378 = (aux env' bs)
in (match (_58_2378) with
| (bs, env', g', us) -> begin
(let _153_840 = (let _153_839 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _153_839))
in (((b)::bs), (env'), (_153_840), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun _58_2386 _58_2389 -> (match (((_58_2386), (_58_2389))) with
| ((t, imp), (args, g)) -> begin
(

let _58_2394 = (tc_term env t)
in (match (_58_2394) with
| (t, _58_2392, g') -> begin
(let _153_849 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t), (imp)))::args), (_153_849)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p _58_2398 -> (match (_58_2398) with
| (pats, g) -> begin
(

let _58_2401 = (tc_args env p)
in (match (_58_2401) with
| (args, g') -> begin
(let _153_852 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats), (_153_852)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _58_2407 = (tc_maybe_toplevel_term env e)
in (match (_58_2407) with
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

let _58_2413 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _153_855 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in ((_153_855), (false)))
end else begin
(let _153_856 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in ((_153_856), (true)))
end
in (match (_58_2413) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _153_857 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (_153_857)))
end
| _58_2417 -> begin
if allow_ghost then begin
(let _153_860 = (let _153_859 = (let _153_858 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in ((_153_858), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_153_859))
in (Prims.raise _153_860))
end else begin
(let _153_863 = (let _153_862 = (let _153_861 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in ((_153_861), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_153_862))
in (Prims.raise _153_863))
end
end)
end)))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let _58_2427 = (tc_tot_or_gtot_term env t)
in (match (_58_2427) with
| (t, c, g) -> begin
(

let _58_2428 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in ((t), (c)))
end)))


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _58_2432 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _153_873 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _153_873))
end else begin
()
end
in (

let env = (

let _58_2434 = env
in {FStar_TypeChecker_Env.solver = _58_2434.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2434.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2434.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2434.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2434.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2434.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2434.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2434.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2434.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2434.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2434.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2434.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2434.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_2434.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2434.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2434.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2434.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2434.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_2434.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_2434.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2434.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2434.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2434.FStar_TypeChecker_Env.qname_and_index})
in (

let _58_2450 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _58_2442) -> begin
(let _153_878 = (let _153_877 = (let _153_876 = (FStar_TypeChecker_Env.get_range env)
in (((Prims.strcat "Implicit argument: " msg)), (_153_876)))
in FStar_Syntax_Syntax.Error (_153_877))
in (Prims.raise _153_878))
end
in (match (_58_2450) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end else begin
(let _153_883 = (let _153_882 = (let _153_881 = (let _153_879 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _153_879))
in (let _153_880 = (FStar_TypeChecker_Env.get_range env)
in ((_153_881), (_153_880))))
in FStar_Syntax_Syntax.Error (_153_882))
in (Prims.raise _153_883))
end
end)))))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> (

let _58_2453 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _153_888 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "<start> universe_of %s\n" _153_888))
end else begin
()
end
in (

let _58_2458 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2458) with
| (env, _58_2457) -> begin
(

let env = (

let _58_2459 = env
in {FStar_TypeChecker_Env.solver = _58_2459.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2459.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2459.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2459.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2459.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2459.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2459.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2459.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2459.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2459.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2459.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2459.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2459.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_2459.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2459.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2459.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2459.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _58_2459.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_2459.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2459.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _58_2459.FStar_TypeChecker_Env.qname_and_index})
in (

let fail = (fun e t -> (let _153_898 = (let _153_897 = (let _153_896 = (let _153_894 = (FStar_Syntax_Print.term_to_string e)
in (let _153_893 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" _153_894 _153_893)))
in (let _153_895 = (FStar_TypeChecker_Env.get_range env)
in ((_153_896), (_153_895))))
in FStar_Syntax_Syntax.Error (_153_897))
in (Prims.raise _153_898)))
in (

let ok = (fun u -> (

let _58_2467 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _153_903 = (FStar_Syntax_Print.tag_of_term e)
in (let _153_902 = (FStar_Syntax_Print.term_to_string e)
in (let _153_901 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.print3 "<end> universe_of (%s) %s is %s\n" _153_903 _153_902 _153_901))))
end else begin
()
end
in u))
in (

let universe_of_type = (fun e t -> (match ((let _153_908 = (FStar_Syntax_Util.unrefine t)
in _153_908.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(ok u)
end
| _58_2475 -> begin
(fail e t)
end))
in (

let _58_2478 = (FStar_Syntax_Util.head_and_args e)
in (match (_58_2478) with
| (head, args) -> begin
(match ((let _153_909 = (FStar_Syntax_Subst.compress head)
in _153_909.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_58_2480, t) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _153_910 = (FStar_Syntax_Subst.compress t)
in _153_910.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_2486, t) -> begin
(universe_of_type e (FStar_Syntax_Util.comp_result t))
end
| _58_2491 -> begin
(universe_of_type e t)
end))
end
| _58_2493 -> begin
(

let t = (match ((FStar_ST.read e.FStar_Syntax_Syntax.tk)) with
| (None) | (Some (FStar_Syntax_Syntax.Tm_unknown)) -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::[]) env e)
in (

let _58_2509 = (tc_term env e)
in (match (_58_2509) with
| (_58_2499, {FStar_Syntax_Syntax.eff_name = _58_2506; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_2503; FStar_Syntax_Syntax.comp = _58_2501}, g) -> begin
(

let _58_2510 = (let _153_912 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (FStar_All.pipe_right _153_912 Prims.ignore))
in t)
end)))
end
| Some (t) -> begin
(FStar_Syntax_Syntax.mk t None e.FStar_Syntax_Syntax.pos)
end)
in (let _153_913 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (FStar_All.pipe_left (universe_of_type e) _153_913)))
end)
end))))))
end))))




