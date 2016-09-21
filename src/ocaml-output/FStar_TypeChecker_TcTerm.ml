
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
in (let _152_12 = (let _152_11 = (FStar_Syntax_Syntax.as_arg v)
in (let _152_10 = (let _152_9 = (FStar_Syntax_Syntax.as_arg tl)
in (_152_9)::[])
in (_152_11)::_152_10))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _152_12 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _58_1 -> (match (_58_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _58_20 -> begin
false
end))


let steps = (fun env -> (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[])


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
(let _152_43 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _152_43))
end
| Some (head) -> begin
(let _152_45 = (FStar_Syntax_Print.bv_to_string x)
in (let _152_44 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _152_45 _152_44)))
end)
in (let _152_48 = (let _152_47 = (let _152_46 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (_152_46)))
in FStar_Syntax_Syntax.Error (_152_47))
in (Prims.raise _152_48)))
end))
in (

let s = (let _152_50 = (let _152_49 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _152_49))
in (FStar_TypeChecker_Util.new_uvar env _152_50))
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
(let _152_64 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _152_64 t))
end))}))


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let should_return = (fun t -> (match ((let _152_75 = (FStar_Syntax_Subst.compress t)
in _152_75.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_74, c) -> begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(

let t = (FStar_All.pipe_left FStar_Syntax_Util.unrefine (FStar_Syntax_Util.comp_result c))
in (match ((let _152_76 = (FStar_Syntax_Subst.compress t)
in _152_76.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (_58_82) -> begin
false
end
| _58_85 -> begin
true
end))
end else begin
false
end
end
| _58_87 -> begin
true
end))
in (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _152_77 = if ((not ((should_return t))) || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _152_77))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _58_115 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
((e), (lc), (guard))
end
| Some (t') -> begin
(

let _58_97 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_79 = (FStar_Syntax_Print.term_to_string t)
in (let _152_78 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _152_79 _152_78)))
end else begin
()
end
in (

let _58_101 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_58_101) with
| (e, lc) -> begin
(

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _58_105 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_58_105) with
| (e, g) -> begin
(

let _58_106 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_81 = (FStar_Syntax_Print.term_to_string t)
in (let _152_80 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _152_81 _152_80)))
end else begin
()
end
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let _58_111 = (let _152_87 = (FStar_All.pipe_left (fun _152_86 -> Some (_152_86)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _152_87 env e lc g))
in (match (_58_111) with
| (lc, g) -> begin
((e), ((set_lcomp_result lc t')), (g))
end))))
end)))
end)))
end)
in (match (_58_115) with
| (e, lc, g) -> begin
(

let _58_116 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_88 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _152_88))
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

let _58_126 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_58_126) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _58_131 -> (match (_58_131) with
| (e, c) -> begin
(

let expected_c_opt = (match (copt) with
| Some (_58_133) -> begin
copt
end
| None -> begin
if ((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Syntax_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) then begin
(let _152_101 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (_152_101))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
if (FStar_Syntax_Util.is_pure_comp c) then begin
(let _152_102 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (_152_102))
end else begin
if (FStar_Syntax_Util.is_pure_or_ghost_comp c) then begin
(let _152_103 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (_152_103))
end else begin
None
end
end
end
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _152_104 = (norm_c env c)
in ((e), (_152_104), (FStar_TypeChecker_Rel.trivial_guard)))
end
| Some (expected_c) -> begin
(

let _58_140 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_107 = (FStar_Syntax_Print.term_to_string e)
in (let _152_106 = (FStar_Syntax_Print.comp_to_string c)
in (let _152_105 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _152_107 _152_106 _152_105))))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _58_143 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_110 = (FStar_Syntax_Print.term_to_string e)
in (let _152_109 = (FStar_Syntax_Print.comp_to_string c)
in (let _152_108 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _152_110 _152_109 _152_108))))
end else begin
()
end
in (

let _58_149 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_58_149) with
| (e, _58_147, g) -> begin
(

let g = (let _152_111 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _152_111 "could not prove post-condition" g))
in (

let _58_151 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_113 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _152_112 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _152_113 _152_112)))
end else begin
()
end
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e (FStar_Syntax_Util.comp_effect_name c) (FStar_Syntax_Util.comp_effect_name expected_c))
in ((e), (expected_c), (g)))))
end)))))
end))
end))


let no_logical_guard = (fun env _58_158 -> (match (_58_158) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
((te), (kt), (f))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _152_119 = (let _152_118 = (let _152_117 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _152_116 = (FStar_TypeChecker_Env.get_range env)
in ((_152_117), (_152_116))))
in FStar_Syntax_Syntax.Error (_152_118))
in (Prims.raise _152_119))
end)
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _152_122 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _152_122))
end))


let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = _58_184; FStar_Syntax_Syntax.effect_name = _58_182; FStar_Syntax_Syntax.result_typ = _58_180; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, _58_174))::[]; FStar_Syntax_Syntax.flags = _58_171}) -> begin
(

let pat_vars = (let _152_127 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env pats)
in (FStar_Syntax_Free.names _152_127))
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _58_191 -> (match (_58_191) with
| (b, _58_190) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _58_195) -> begin
(let _152_130 = (let _152_129 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" _152_129))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _152_130))
end))
end
| _58_199 -> begin
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

let _58_206 = env
in {FStar_TypeChecker_Env.solver = _58_206.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_206.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_206.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_206.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_206.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_206.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_206.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_206.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_206.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_206.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_206.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_206.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _58_206.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_206.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_206.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_206.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_206.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_206.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_206.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_206.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_206.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_206.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_206.FStar_TypeChecker_Env.qname_and_index})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _58_218 -> (match (_58_218) with
| (b, _58_217) -> begin
(

let t = (let _152_144 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _152_144))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _58_227 -> begin
(let _152_145 = (FStar_Syntax_Syntax.bv_to_name b)
in (_152_145)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let _58_233 = (FStar_Syntax_Util.head_and_args dec)
in (match (_58_233) with
| (head, _58_232) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _58_237 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let cflags = (FStar_Syntax_Util.comp_flags c)
in (match ((FStar_All.pipe_right cflags (FStar_List.tryFind (fun _58_2 -> (match (_58_2) with
| FStar_Syntax_Syntax.DECREASES (_58_241) -> begin
true
end
| _58_244 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _58_249 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| _58_254 -> begin
(mk_lex_list xs)
end))
end)))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun _58_259 -> (match (_58_259) with
| (l, t) -> begin
(match ((let _152_151 = (FStar_Syntax_Subst.compress t)
in _152_151.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _58_266 -> (match (_58_266) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _152_155 = (let _152_154 = (let _152_153 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_152_153))
in (FStar_Syntax_Syntax.new_bv _152_154 x.FStar_Syntax_Syntax.sort))
in ((_152_155), (imp)))
end else begin
((x), (imp))
end
end))))
in (

let _58_270 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_58_270) with
| (formals, c) -> begin
(

let dec = (decreases_clause formals c)
in (

let precedes = (let _152_159 = (let _152_158 = (FStar_Syntax_Syntax.as_arg dec)
in (let _152_157 = (let _152_156 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_152_156)::[])
in (_152_158)::_152_157))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _152_159 None r))
in (

let _58_277 = (FStar_Util.prefix formals)
in (match (_58_277) with
| (bs, (last, imp)) -> begin
(

let last = (

let _58_278 = last
in (let _152_160 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _58_278.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_278.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_160}))
in (

let refined_formals = (FStar_List.append bs ((((last), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (

let _58_283 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_163 = (FStar_Syntax_Print.lbname_to_string l)
in (let _152_162 = (FStar_Syntax_Print.term_to_string t)
in (let _152_161 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _152_163 _152_162 _152_161))))
end else begin
()
end
in ((l), (t'))))))
end))))
end)))
end
| _58_286 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end)
end)


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let _58_289 = env
in {FStar_TypeChecker_Env.solver = _58_289.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_289.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_289.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_289.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_289.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_289.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_289.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_289.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_289.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_289.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_289.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_289.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_289.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_289.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_289.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_289.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_289.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_289.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_289.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_289.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_289.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_289.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_289.FStar_TypeChecker_Env.qname_and_index}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (

let _58_294 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_233 = (let _152_231 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _152_231))
in (let _152_232 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _152_233 _152_232)))
end else begin
()
end
in (

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_58_298) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let _58_339 = (tc_tot_or_gtot_term env e)
in (match (_58_339) with
| (e, c, g) -> begin
(

let g = (

let _58_340 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_340.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_340.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_340.FStar_TypeChecker_Env.implicits})
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let _58_350 = (FStar_Syntax_Util.type_u ())
in (match (_58_350) with
| (t, u) -> begin
(

let _58_354 = (tc_check_tot_or_gtot_term env e t)
in (match (_58_354) with
| (e, c, g) -> begin
(

let _58_361 = (

let _58_358 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_358) with
| (env, _58_357) -> begin
(tc_pats env pats)
end))
in (match (_58_361) with
| (pats, g') -> begin
(

let g' = (

let _58_362 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_362.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_362.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_362.FStar_TypeChecker_Env.implicits})
in (let _152_238 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_pattern (pats))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _152_237 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((_152_238), (c), (_152_237)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _152_239 = (FStar_Syntax_Subst.compress e)
in _152_239.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_58_371, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _58_378; FStar_Syntax_Syntax.lbtyp = _58_376; FStar_Syntax_Syntax.lbeff = _58_374; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _58_389 = (let _152_240 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _152_240 e1))
in (match (_58_389) with
| (e1, c1, g1) -> begin
(

let _58_393 = (tc_term env e2)
in (match (_58_393) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((None), (c2)))
in (

let e = (let _152_245 = (let _152_244 = (let _152_243 = (let _152_242 = (let _152_241 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_TypeChecker_Common.t_unit), (e1)))
in (_152_241)::[])
in ((false), (_152_242)))
in ((_152_243), (e2)))
in FStar_Syntax_Syntax.Tm_let (_152_244))
in (FStar_Syntax_Syntax.mk _152_245 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _152_246 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e), (c), (_152_246))))))
end))
end))
end
| _58_398 -> begin
(

let _58_402 = (tc_term env e)
in (match (_58_402) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (_58_406)) -> begin
(tc_term env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let _58_417 = (tc_term env e)
in (match (_58_417) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (m)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _58_423) -> begin
(

let _58_429 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_429) with
| (env0, _58_428) -> begin
(

let _58_434 = (tc_comp env0 expected_c)
in (match (_58_434) with
| (expected_c, _58_432, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (

let _58_439 = (let _152_247 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term _152_247 e))
in (match (_58_439) with
| (e, c', g') -> begin
(

let _58_443 = (let _152_249 = (let _152_248 = (c'.FStar_Syntax_Syntax.comp ())
in ((e), (_152_248)))
in (check_expected_effect env0 (Some (expected_c)) _152_249))
in (match (_58_443) with
| (e, expected_c, g'') -> begin
(let _152_252 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t_res)), (Some ((FStar_Syntax_Util.comp_effect_name expected_c)))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _152_251 = (let _152_250 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _152_250))
in ((_152_252), ((FStar_Syntax_Util.lcomp_of_comp expected_c)), (_152_251))))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _58_448) -> begin
(

let _58_453 = (FStar_Syntax_Util.type_u ())
in (match (_58_453) with
| (k, u) -> begin
(

let _58_458 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_458) with
| (t, _58_456, f) -> begin
(

let _58_462 = (let _152_253 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _152_253 e))
in (match (_58_462) with
| (e, c, g) -> begin
(

let _58_466 = (let _152_257 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_463 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _152_257 e c f))
in (match (_58_466) with
| (c, f) -> begin
(

let _58_470 = (let _152_258 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t)), (Some (c.FStar_Syntax_Syntax.eff_name))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _152_258 c))
in (match (_58_470) with
| (e, c, f2) -> begin
(let _152_260 = (let _152_259 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _152_259))
in ((e), (c), (_152_260)))
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

let _58_506 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_506) with
| (unary_op, _58_505) -> begin
(

let head = (let _152_261 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (Prims.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) None _152_261))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), (rest)))) None top.FStar_Syntax_Syntax.pos)
in (tc_term env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _58_514; FStar_Syntax_Syntax.pos = _58_512; FStar_Syntax_Syntax.vars = _58_510}, ((e, aqual))::[]) -> begin
(

let _58_524 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end else begin
()
end
in (

let _58_533 = (

let _58_529 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_529) with
| (env0, _58_528) -> begin
(tc_term env0 e)
end))
in (match (_58_533) with
| (e, c, g) -> begin
(

let _58_537 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_537) with
| (reify_op, _58_536) -> begin
(

let u_c = (

let _58_543 = (tc_term env c.FStar_Syntax_Syntax.res_typ)
in (match (_58_543) with
| (_58_539, c, _58_542) -> begin
(match ((let _152_262 = (FStar_Syntax_Subst.compress c.FStar_Syntax_Syntax.res_typ)
in _152_262.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| _58_547 -> begin
(FStar_All.failwith "Unexpected result type of computation")
end)
end))
in (

let repr = (FStar_TypeChecker_Util.reify_comp env c u_c)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e), (aqual)))::[])))) (Some (repr.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let c = (let _152_263 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right _152_263 FStar_Syntax_Util.lcomp_of_comp))
in (

let _58_555 = (comp_check_expected_typ env e c)
in (match (_58_555) with
| (e, c, g') -> begin
(let _152_264 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), (c), (_152_264)))
end))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.tk = _58_561; FStar_Syntax_Syntax.pos = _58_559; FStar_Syntax_Syntax.vars = _58_557}, ((e, aqual))::[]) -> begin
(

let _58_572 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end else begin
()
end
in (

let no_reflect = (fun _58_575 -> (match (()) with
| () -> begin
(let _152_269 = (let _152_268 = (let _152_267 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((_152_267), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_152_268))
in (Prims.raise _152_269))
end))
in (

let _58_579 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_579) with
| (reflect_op, _58_578) -> begin
(match ((FStar_TypeChecker_Env.effect_decl_opt env l)) with
| None -> begin
(no_reflect ())
end
| Some (ed) -> begin
if (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable)))) then begin
(no_reflect ())
end else begin
(

let _58_585 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_585) with
| (env_no_ex, topt) -> begin
(

let _58_613 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (let _152_275 = (let _152_274 = (let _152_273 = (let _152_272 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _152_271 = (let _152_270 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (_152_270)::[])
in (_152_272)::_152_271))
in ((repr), (_152_273)))
in FStar_Syntax_Syntax.Tm_app (_152_274))
in (FStar_Syntax_Syntax.mk _152_275 None top.FStar_Syntax_Syntax.pos))
in (

let _58_593 = (let _152_277 = (let _152_276 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _152_276 Prims.fst))
in (tc_tot_or_gtot_term _152_277 t))
in (match (_58_593) with
| (t, _58_591, g) -> begin
(match ((let _152_278 = (FStar_Syntax_Subst.compress t)
in _152_278.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_58_595, ((res, _58_602))::((wp, _58_598))::[]) -> begin
((t), (res), (wp), (g))
end
| _58_608 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))
in (match (_58_613) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let _58_627 = (

let _58_617 = (tc_tot_or_gtot_term env_no_ex e)
in (match (_58_617) with
| (e, c, g) -> begin
(

let _58_618 = if (let _152_279 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation _152_279)) then begin
(FStar_TypeChecker_Errors.add_errors env (((("Expected Tot, got a GTot computation"), (e.FStar_Syntax_Syntax.pos)))::[]))
end else begin
()
end
in (match ((FStar_TypeChecker_Rel.try_teq env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)) with
| None -> begin
(

let _58_621 = (let _152_284 = (let _152_283 = (let _152_282 = (let _152_281 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _152_280 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" _152_281 _152_280)))
in ((_152_282), (e.FStar_Syntax_Syntax.pos)))
in (_152_283)::[])
in (FStar_TypeChecker_Errors.add_errors env _152_284))
in (let _152_285 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e), (_152_285))))
end
| Some (g') -> begin
(let _152_287 = (let _152_286 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' _152_286))
in ((e), (_152_287)))
end))
end))
in (match (_58_627) with
| (e, g) -> begin
(

let c = (let _152_293 = (let _152_292 = (let _152_291 = (let _152_288 = (env.FStar_TypeChecker_Env.universe_of env res_typ)
in (_152_288)::[])
in (let _152_290 = (let _152_289 = (FStar_Syntax_Syntax.as_arg wp)
in (_152_289)::[])
in {FStar_Syntax_Syntax.comp_univs = _152_291; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = _152_290; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp _152_292))
in (FStar_All.pipe_right _152_293 FStar_Syntax_Util.lcomp_of_comp))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e), (aqual)))::[])))) (Some (res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let _58_633 = (comp_check_expected_typ env e c)
in (match (_58_633) with
| (e, c, g') -> begin
(let _152_294 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e), (c), (_152_294)))
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

let env = (let _152_296 = (let _152_295 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _152_295 Prims.fst))
in (FStar_All.pipe_right _152_296 instantiate_both))
in (

let _58_640 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_298 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _152_297 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _152_298 _152_297)))
end else begin
()
end
in (

let _58_645 = (tc_term (no_inst env) head)
in (match (_58_645) with
| (head, chead, g_head) -> begin
(

let _58_649 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _152_299 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _152_299))
end else begin
(let _152_300 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _152_300))
end
in (match (_58_649) with
| (e, c, g) -> begin
(

let _58_650 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_301 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _152_301))
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

let _58_656 = (comp_check_expected_typ env0 e c)
in (match (_58_656) with
| (e, c, g') -> begin
(

let gimp = (match ((let _152_302 = (FStar_Syntax_Subst.compress head)
in _152_302.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _58_659) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e), (c.FStar_Syntax_Syntax.res_typ), (head.FStar_Syntax_Syntax.pos))
in (

let _58_663 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_663.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_663.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_663.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _58_666 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (

let gres = (let _152_303 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _152_303))
in (

let _58_669 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_305 = (FStar_Syntax_Print.term_to_string e)
in (let _152_304 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" _152_305 _152_304)))
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

let _58_677 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_677) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let _58_682 = (tc_term env1 e1)
in (match (_58_682) with
| (e1, c1, g1) -> begin
(

let _58_693 = (match (topt) with
| Some (t) -> begin
((env), (t))
end
| None -> begin
(

let _58_689 = (FStar_Syntax_Util.type_u ())
in (match (_58_689) with
| (k, _58_688) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _152_306 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in ((_152_306), (res_t))))
end))
end)
in (match (_58_693) with
| (env_branches, res_t) -> begin
(

let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let _58_710 = (

let _58_707 = (FStar_List.fold_right (fun _58_701 _58_704 -> (match (((_58_701), (_58_704))) with
| ((_58_697, f, c, g), (caccum, gaccum)) -> begin
(let _152_309 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (_152_309)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_58_707) with
| (cases, g) -> begin
(let _152_310 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in ((_152_310), (g)))
end))
in (match (_58_710) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (guard_x)), (c_branches)))
in (

let e = (

let mk_match = (fun scrutinee -> (

let branches = (FStar_List.map (fun _58_721 -> (match (_58_721) with
| (f, _58_716, _58_718, _58_720) -> begin
f
end)) t_eqns)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (Some (cres.FStar_Syntax_Syntax.eff_name))))) None e.FStar_Syntax_Syntax.pos))))
in if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c1.FStar_Syntax_Syntax.eff_name) then begin
(mk_match e1)
end else begin
(

let e_match = (let _152_314 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match _152_314))
in (

let lb = (let _152_315 = (FStar_TypeChecker_Env.norm_eff_name env c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = _152_315; FStar_Syntax_Syntax.lbdef = e1})
in (let _152_320 = (let _152_319 = (let _152_318 = (let _152_317 = (let _152_316 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (_152_316)::[])
in (FStar_Syntax_Subst.close _152_317 e_match))
in ((((false), ((lb)::[]))), (_152_318)))
in FStar_Syntax_Syntax.Tm_let (_152_319))
in (FStar_Syntax_Syntax.mk _152_320 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))))
end)
in (

let _58_727 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_323 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _152_322 = (let _152_321 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _152_321))
in (FStar_Util.print2 "(%s) comp type = %s\n" _152_323 _152_322)))
end else begin
()
end
in (let _152_324 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e), (cres), (_152_324))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_739); FStar_Syntax_Syntax.lbunivs = _58_737; FStar_Syntax_Syntax.lbtyp = _58_735; FStar_Syntax_Syntax.lbeff = _58_733; FStar_Syntax_Syntax.lbdef = _58_731})::[]), _58_745) -> begin
(

let _58_748 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_325 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _152_325))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _58_752), _58_755) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_770); FStar_Syntax_Syntax.lbunivs = _58_768; FStar_Syntax_Syntax.lbtyp = _58_766; FStar_Syntax_Syntax.lbeff = _58_764; FStar_Syntax_Syntax.lbdef = _58_762})::_58_760), _58_776) -> begin
(

let _58_779 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_326 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _152_326))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _58_783), _58_786) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let _58_800 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_800) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _152_340 = (let _152_339 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_339))
in FStar_Util.Inr (_152_340))
end
in (

let is_data_ctor = (fun _58_3 -> (match (_58_3) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _58_810 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _152_346 = (let _152_345 = (let _152_344 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _152_343 = (FStar_TypeChecker_Env.get_range env)
in ((_152_344), (_152_343))))
in FStar_Syntax_Syntax.Error (_152_345))
in (Prims.raise _152_346))
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
(let _152_348 = (let _152_347 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" _152_347))
in (FStar_All.failwith _152_348))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (match ((let _152_349 = (FStar_Syntax_Subst.compress t1)
in _152_349.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_821) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _58_824 -> begin
(

let imp = (("uvar in term"), (env), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let _58_826 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_826.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_826.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_826.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _58_841 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(

let _58_834 = (FStar_Syntax_Util.type_u ())
in (match (_58_834) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
end))
end
| Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end)
in (match (_58_841) with
| (t, _58_839, g0) -> begin
(

let _58_846 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (_58_846) with
| (e, _58_844, g1) -> begin
(let _152_352 = (let _152_350 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right _152_350 FStar_Syntax_Util.lcomp_of_comp))
in (let _152_351 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e), (_152_352), (_152_351))))
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

let _58_850 = x
in {FStar_Syntax_Syntax.ppname = _58_850.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_850.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let _58_856 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_856) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _152_354 = (let _152_353 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_353))
in FStar_Util.Inr (_152_354))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _58_863; FStar_Syntax_Syntax.pos = _58_861; FStar_Syntax_Syntax.vars = _58_859}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let _58_873 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_873) with
| (us', t) -> begin
(

let _58_880 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _152_357 = (let _152_356 = (let _152_355 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (_152_355)))
in FStar_Syntax_Syntax.Error (_152_356))
in (Prims.raise _152_357))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _58_879 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (

let fv' = (

let _58_882 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _58_884 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_884.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_884.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_882.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_882.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _152_360 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _152_360 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let _58_892 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_892) with
| (us, t) -> begin
(

let fv' = (

let _58_893 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _58_895 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_895.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_895.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_893.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_893.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _152_361 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _152_361 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t)))
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

let _58_909 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_909) with
| (bs, c) -> begin
(

let env0 = env
in (

let _58_914 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_914) with
| (env, _58_913) -> begin
(

let _58_919 = (tc_binders env bs)
in (match (_58_919) with
| (bs, env, g, us) -> begin
(

let _58_923 = (tc_comp env c)
in (match (_58_923) with
| (c, uc, f) -> begin
(

let e = (

let _58_924 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _58_924.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_924.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_924.FStar_Syntax_Syntax.vars})
in (

let _58_927 = (check_smt_pat env e bs c)
in (

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _152_362 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _152_362))
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

let _58_943 = (let _152_364 = (let _152_363 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_363)::[])
in (FStar_Syntax_Subst.open_term _152_364 phi))
in (match (_58_943) with
| (x, phi) -> begin
(

let env0 = env
in (

let _58_948 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_948) with
| (env, _58_947) -> begin
(

let _58_953 = (let _152_365 = (FStar_List.hd x)
in (tc_binder env _152_365))
in (match (_58_953) with
| (x, env, f1, u) -> begin
(

let _58_954 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_368 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _152_367 = (FStar_Syntax_Print.term_to_string phi)
in (let _152_366 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _152_368 _152_367 _152_366))))
end else begin
()
end
in (

let _58_959 = (FStar_Syntax_Util.type_u ())
in (match (_58_959) with
| (t_phi, _58_958) -> begin
(

let _58_964 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_58_964) with
| (phi, _58_962, f2) -> begin
(

let e = (

let _58_965 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _58_965.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_965.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_965.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _152_369 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _152_369))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _58_973) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (

let _58_979 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_370 = (FStar_Syntax_Print.term_to_string (

let _58_977 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))); FStar_Syntax_Syntax.tk = _58_977.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _58_977.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_977.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _152_370))
end else begin
()
end
in (

let _58_983 = (FStar_Syntax_Subst.open_term bs body)
in (match (_58_983) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _58_985 -> begin
(let _152_373 = (let _152_372 = (FStar_Syntax_Print.term_to_string top)
in (let _152_371 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" _152_372 _152_371)))
in (FStar_All.failwith _152_373))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_58_990) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_58_993, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_58_998, Some (_58_1000)) -> begin
(FStar_All.failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (_58_1005) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_58_1008) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_58_1011) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_58_1015) -> begin
FStar_TypeChecker_Common.t_range
end
| _58_1018 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _58_1024) -> begin
(

let _58_1029 = (FStar_Syntax_Util.type_u ())
in (match (_58_1029) with
| (k, u) -> begin
(

let _58_1034 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_1034) with
| (t, _58_1032, g) -> begin
(let _152_378 = (FStar_Syntax_Syntax.mk_Total' t (Some (u)))
in ((_152_378), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t, _58_1037) -> begin
(

let _58_1042 = (FStar_Syntax_Util.type_u ())
in (match (_58_1042) with
| (k, u) -> begin
(

let _58_1047 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_1047) with
| (t, _58_1045, g) -> begin
(let _152_379 = (FStar_Syntax_Syntax.mk_GTotal' t (Some (u)))
in ((_152_379), (u), (g)))
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

let tc = (let _152_381 = (let _152_380 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_152_380)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _152_381 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let _58_1059 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_58_1059) with
| (tc, _58_1057, f) -> begin
(

let _58_1062 = (FStar_Syntax_Util.head_and_args tc)
in (match (_58_1062) with
| (head, args) -> begin
(

let comp_univs = (match ((let _152_382 = (FStar_Syntax_Subst.compress head)
in _152_382.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (_58_1064, us) -> begin
us
end
| _58_1069 -> begin
[]
end)
in (

let _58_1074 = (FStar_Syntax_Util.head_and_args tc)
in (match (_58_1074) with
| (_58_1072, args) -> begin
(

let _58_1077 = (let _152_384 = (FStar_List.hd args)
in (let _152_383 = (FStar_List.tl args)
in ((_152_384), (_152_383))))
in (match (_58_1077) with
| (res, args) -> begin
(

let _58_1093 = (let _152_386 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _58_4 -> (match (_58_4) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _58_1084 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1084) with
| (env, _58_1083) -> begin
(

let _58_1089 = (tc_tot_or_gtot_term env e)
in (match (_58_1089) with
| (e, _58_1087, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e)), (g))
end))
end))
end
| f -> begin
((f), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right _152_386 FStar_List.unzip))
in (match (_58_1093) with
| (flags, guards) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (Prims.fst res))
in (

let c = (FStar_Syntax_Syntax.mk_Comp (

let _58_1095 = c
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = _58_1095.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _58_1095.FStar_Syntax_Syntax.flags}))
in (

let u_c = (match ((FStar_TypeChecker_Util.effect_repr env c u)) with
| None -> begin
u
end
| Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end)
in (let _152_387 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((c), (u_c), (_152_387))))))
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
| FStar_Syntax_Syntax.U_bvar (_58_1108) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _152_392 = (aux u)
in FStar_Syntax_Syntax.U_succ (_152_392))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _152_393 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_152_393))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _152_397 = (let _152_396 = (let _152_395 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _152_394 = (FStar_TypeChecker_Env.get_range env)
in ((_152_395), (_152_394))))
in FStar_Syntax_Syntax.Error (_152_396))
in (Prims.raise _152_397))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _152_398 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _152_398 Prims.snd))
end
| _58_1123 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _152_407 = (let _152_406 = (let _152_405 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in ((_152_405), (top.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_152_406))
in (Prims.raise _152_407)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun _58_1141 bs bs_expected -> (match (_58_1141) with
| (env, out, g, subst) -> begin
(match (((bs), (bs_expected))) with
| ([], []) -> begin
((env), ((FStar_List.rev out)), (None), (g), (subst))
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
(

let _58_1172 = (match (((imp), (imp'))) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _152_424 = (let _152_423 = (let _152_422 = (let _152_420 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _152_420))
in (let _152_421 = (FStar_Syntax_Syntax.range_of_bv hd)
in ((_152_422), (_152_421))))
in FStar_Syntax_Syntax.Error (_152_423))
in (Prims.raise _152_424))
end
| _58_1171 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _58_1189 = (match ((let _152_425 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _152_425.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| _58_1177 -> begin
(

let _58_1178 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_426 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _152_426))
end else begin
()
end
in (

let _58_1184 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_58_1184) with
| (t, _58_1182, g1) -> begin
(

let g2 = (let _152_428 = (FStar_TypeChecker_Env.get_range env)
in (let _152_427 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _152_428 "Type annotation on parameter incompatible with the expected type" _152_427)))
in (

let g = (let _152_429 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _152_429))
in ((t), (g))))
end)))
end)
in (match (_58_1189) with
| (t, g) -> begin
(

let hd = (

let _58_1190 = hd
in {FStar_Syntax_Syntax.ppname = _58_1190.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1190.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env = (push_binding env b)
in (

let subst = (let _152_430 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _152_430))
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

let _58_1211 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _58_1210 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (

let _58_1218 = (tc_binders env bs)
in (match (_58_1218) with
| (bs, envbody, g, _58_1217) -> begin
(

let _58_1236 = (match ((let _152_437 = (FStar_Syntax_Subst.compress body)
in _152_437.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _58_1223) -> begin
(

let _58_1230 = (tc_comp envbody c)
in (match (_58_1230) with
| (c, _58_1228, g') -> begin
(let _152_438 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((Some (c)), (body), (_152_438)))
end))
end
| _58_1232 -> begin
((None), (body), (g))
end)
in (match (_58_1236) with
| (copt, body, g) -> begin
((None), (bs), ([]), (copt), (envbody), (body), (g))
end))
end)))
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm t -> (match ((let _152_443 = (FStar_Syntax_Subst.compress t)
in _152_443.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let _58_1263 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _58_1262 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _58_1270 = (tc_binders env bs)
in (match (_58_1270) with
| (bs, envbody, g, _58_1269) -> begin
(

let _58_1274 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_58_1274) with
| (envbody, _58_1273) -> begin
((Some (((t), (true)))), (bs), ([]), (None), (envbody), (body), (g))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _58_1277) -> begin
(

let _58_1288 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_58_1288) with
| (_58_1281, bs, bs', copt, env, body, g) -> begin
((Some (((t), (false)))), (bs), (bs'), (copt), (env), (body), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _58_1295 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_58_1295) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun _58_1306 c_expected -> (match (_58_1306) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _152_454 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in ((env), (bs), (guard), (_152_454)))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (let _152_455 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _152_455))
in (let _152_456 = (FStar_Syntax_Subst.subst_comp subst c)
in ((env), (bs), (guard), (_152_456))))
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

let _58_1327 = (check_binders env more_bs bs_expected)
in (match (_58_1327) with
| (env, bs', more, guard', subst) -> begin
(let _152_458 = (let _152_457 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env), ((FStar_List.append bs bs')), (more), (_152_457), (subst)))
in (handle_more _152_458 c_expected))
end))
end
| _58_1329 -> begin
(let _152_460 = (let _152_459 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _152_459))
in (fail _152_460 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _152_461 = (check_binders env bs bs_expected)
in (handle_more _152_461 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let _58_1335 = envbody
in {FStar_TypeChecker_Env.solver = _58_1335.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1335.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1335.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1335.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1335.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1335.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1335.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1335.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1335.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1335.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1335.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1335.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _58_1335.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1335.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1335.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1335.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1335.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1335.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_1335.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_1335.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1335.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1335.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1335.FStar_TypeChecker_Env.qname_and_index})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _58_1340 _58_1343 -> (match (((_58_1340), (_58_1343))) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _58_1349 = (let _152_471 = (let _152_470 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _152_470 Prims.fst))
in (tc_term _152_471 t))
in (match (_58_1349) with
| (t, _58_1346, _58_1348) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l (([]), (t)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _152_472 = (FStar_Syntax_Syntax.mk_binder (

let _58_1353 = x
in {FStar_Syntax_Syntax.ppname = _58_1353.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1353.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_152_472)::letrec_binders)
end
| _58_1356 -> begin
letrec_binders
end)
in ((env), (lb))))
end))
end)) ((envbody), ([])))))))
in (

let _58_1362 = (check_actuals_against_formals env bs bs_expected)
in (match (_58_1362) with
| (envbody, bs, g, c) -> begin
(

let _58_1365 = if (FStar_TypeChecker_Env.should_verify env) then begin
(mk_letrec_env envbody bs c)
end else begin
((envbody), ([]))
end
in (match (_58_1365) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in ((Some (((t), (false)))), (bs), (letrecs), (Some (c)), (envbody), (body), (g)))
end))
end))))
end))
end
| _58_1368 -> begin
if (not (norm)) then begin
(let _152_473 = (unfold_whnf env t)
in (as_function_typ true _152_473))
end else begin
(

let _58_1378 = (expected_function_typ env None body)
in (match (_58_1378) with
| (_58_1370, bs, _58_1373, c_opt, envbody, body, g) -> begin
((Some (((t), (false)))), (bs), ([]), (c_opt), (envbody), (body), (g))
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let _58_1382 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1382) with
| (env, topt) -> begin
(

let _58_1386 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_474 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _152_474 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (

let _58_1395 = (expected_function_typ env topt body)
in (match (_58_1395) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let _58_1401 = (tc_term (

let _58_1396 = envbody
in {FStar_TypeChecker_Env.solver = _58_1396.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1396.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1396.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1396.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1396.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1396.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1396.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1396.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1396.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1396.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1396.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1396.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1396.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_1396.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1396.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1396.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1396.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_1396.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_1396.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1396.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1396.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1396.FStar_TypeChecker_Env.qname_and_index}) body)
in (match (_58_1401) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _58_1403 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _152_477 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _152_476 = (let _152_475 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _152_475))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _152_477 _152_476)))
end else begin
()
end
in (

let _58_1410 = (let _152_479 = (let _152_478 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body), (_152_478)))
in (check_expected_effect (

let _58_1405 = envbody
in {FStar_TypeChecker_Env.solver = _58_1405.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1405.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1405.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1405.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1405.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1405.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1405.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1405.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1405.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1405.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1405.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1405.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1405.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1405.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1405.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1405.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1405.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1405.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_1405.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_1405.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1405.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1405.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1405.FStar_TypeChecker_Env.qname_and_index}) c_opt _152_479))
in (match (_58_1410) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(let _152_480 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _152_480))
end else begin
(

let guard = (let _152_481 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) _152_481))
in guard)
end
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _152_484 = (let _152_483 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _152_482 -> FStar_Util.Inl (_152_482)))
in Some (_152_483))
in (FStar_Syntax_Util.abs bs body _152_484))
in (

let _58_1433 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_58_1422) -> begin
((e), (t), (guard))
end
| _58_1425 -> begin
(

let _58_1428 = if use_teq then begin
(let _152_485 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in ((e), (_152_485)))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_58_1428) with
| (e, guard') -> begin
(let _152_486 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((e), (t), (_152_486)))
end))
end))
end
| None -> begin
((e), (tfun_computed), (guard))
end)
in (match (_58_1433) with
| (e, tfun, guard) -> begin
(

let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (

let _58_1437 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_58_1437) with
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

let _58_1447 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_495 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _152_494 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _152_495 _152_494)))
end else begin
()
end
in (

let monadic_application = (fun _58_1454 subst arg_comps_rev arg_rets guard fvs bs -> (match (_58_1454) with
| (head, chead, ghead, cres) -> begin
(

let rt = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _58_1462 = cres
in {FStar_Syntax_Syntax.eff_name = _58_1462.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = rt; FStar_Syntax_Syntax.cflags = _58_1462.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_1462.FStar_Syntax_Syntax.comp})
in (

let _58_1491 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun _58_5 -> (match (_58_5) with
| (_58_1470, _58_1472, None) -> begin
false
end
| (_58_1476, _58_1478, Some (c)) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _152_511 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _152_511 cres))
end else begin
(

let _58_1483 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_514 = (FStar_Syntax_Print.term_to_string head)
in (let _152_513 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _152_512 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _152_514 _152_513 _152_512))))
end else begin
()
end
in cres)
end
in ((cres), (g))))))
end
| _58_1487 -> begin
(

let g = (let _152_515 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right _152_515 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _152_520 = (let _152_519 = (let _152_518 = (let _152_517 = (let _152_516 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _152_516))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _152_517))
in (FStar_Syntax_Syntax.mk_Total _152_518))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_519))
in ((_152_520), (g))))
end)
in (match (_58_1491) with
| (cres, guard) -> begin
(

let _58_1492 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_521 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _152_521))
end else begin
()
end
in (

let _58_1514 = (FStar_List.fold_left (fun _58_1497 _58_1503 -> (match (((_58_1497), (_58_1503))) with
| ((args, out_c, monadic), ((e, q), x, c)) -> begin
(match (c) with
| None -> begin
(((((e), (q)))::args), (out_c), (monadic))
end
| Some (c) -> begin
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
in (match (_58_1514) with
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

let _58_1520 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (_58_1520) with
| (comp, g) -> begin
((app), (comp), (g))
end)))))
end)))
end))))
end))
in (

let rec tc_args = (fun head_info _58_1528 bs args -> (match (_58_1528) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args))) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (_58_1534))))::rest, ((_58_1542, None))::_58_1540) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let t = (check_no_escape (Some (head)) env fvs t)
in (

let _58_1553 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_58_1553) with
| (varg, _58_1551, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst
in (

let arg = (let _152_533 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (_152_533)))
in (let _152_535 = (let _152_534 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst), ((((arg), (None), (None)))::outargs), ((arg)::arg_rets), (_152_534), (fvs)))
in (tc_args head_info _152_535 rest args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
(

let _58_1585 = (match (((aqual), (aq))) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _58_1584 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifier"), (e.FStar_Syntax_Syntax.pos)))))
end)
in (

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let _58_1588 = x
in {FStar_Syntax_Syntax.ppname = _58_1588.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1588.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (

let _58_1591 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_536 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _152_536))
end else begin
()
end
in (

let targ = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let _58_1595 = env
in {FStar_TypeChecker_Env.solver = _58_1595.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1595.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1595.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1595.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1595.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1595.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1595.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1595.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1595.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1595.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1595.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1595.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1595.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1595.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1595.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _58_1595.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1595.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1595.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_1595.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_1595.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1595.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1595.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1595.FStar_TypeChecker_Env.qname_and_index})
in (

let _58_1598 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_539 = (FStar_Syntax_Print.tag_of_term e)
in (let _152_538 = (FStar_Syntax_Print.term_to_string e)
in (let _152_537 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _152_539 _152_538 _152_537))))
end else begin
()
end
in (

let _58_1603 = (tc_term env e)
in (match (_58_1603) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = ((e), (aq))
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(

let subst = (let _152_540 = (FStar_List.hd bs)
in (maybe_extend_subst subst _152_540 e))
in (tc_args head_info ((subst), ((((arg), (None), (None)))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(

let subst = (let _152_541 = (FStar_List.hd bs)
in (maybe_extend_subst subst _152_541 e))
in (tc_args head_info ((subst), ((((arg), (Some (x)), (Some (c))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (let _152_542 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _152_542)) then begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _152_543 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _152_543))
in (tc_args head_info ((subst), ((((arg), (Some (newx)), (Some (c))))::outargs), ((arg')::arg_rets), (g), (fvs)) rest rest')))
end else begin
(let _152_547 = (let _152_546 = (let _152_545 = (let _152_544 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _152_544))
in (_152_545)::arg_rets)
in ((subst), ((((arg), (Some (x)), (Some (c))))::outargs), (_152_546), (g), ((x)::fvs)))
in (tc_args head_info _152_547 rest rest'))
end
end
end))
end))))))))))
end
| (_58_1611, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::_58_1616) -> begin
(

let _58_1623 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (_58_1623) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _152_552 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _152_552 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let _58_1634 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (_58_1634) with
| (bs, cres') -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp cres')))
in (

let _58_1636 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_553 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _152_553))
end else begin
()
end
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args)))
end))
end
| _58_1639 when (not (norm)) -> begin
(let _152_554 = (unfold_whnf env tres)
in (aux true _152_554))
end
| _58_1641 -> begin
(let _152_560 = (let _152_559 = (let _152_558 = (let _152_556 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (let _152_555 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _152_556 _152_555)))
in (let _152_557 = (FStar_Syntax_Syntax.argpos arg)
in ((_152_558), (_152_557))))
in FStar_Syntax_Syntax.Error (_152_559))
in (Prims.raise _152_560))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (match ((let _152_565 = (FStar_Syntax_Util.unrefine tf)
in _152_565.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl -> begin
(

let _58_1674 = (tc_term env e)
in (match (_58_1674) with
| (e, c, g_e) -> begin
(

let _58_1678 = (tc_args env tl)
in (match (_58_1678) with
| (args, comps, g_rest) -> begin
(let _152_570 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e), (imp)))::args), ((((e.FStar_Syntax_Syntax.pos), (c)))::comps), (_152_570)))
end))
end))
end))
in (

let _58_1682 = (tc_args env args)
in (match (_58_1682) with
| (args, comps, g_args) -> begin
(

let bs = (let _152_572 = (FStar_All.pipe_right comps (FStar_List.map (fun _58_1686 -> (match (_58_1686) with
| (_58_1684, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks _152_572))
in (

let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _58_1692 -> begin
FStar_Syntax_Util.ml_comp
end)
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _152_587 = (FStar_Syntax_Subst.compress t)
in _152_587.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_58_1698) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _58_1703 -> begin
ml_or_tot
end)
end)
in (

let cres = (let _152_592 = (let _152_591 = (let _152_590 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _152_590 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _152_591))
in (ml_or_tot _152_592 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (

let _58_1707 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _152_595 = (FStar_Syntax_Print.term_to_string head)
in (let _152_594 = (FStar_Syntax_Print.term_to_string tf)
in (let _152_593 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _152_595 _152_594 _152_593))))
end else begin
()
end
in (

let _58_1709 = (let _152_596 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _152_596))
in (

let comp = (let _152_599 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _58_1713 out -> (match (_58_1713) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c ((None), (out)))
end)) ((((head.FStar_Syntax_Syntax.pos), (chead)))::comps) _152_599))
in (let _152_601 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _152_600 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((_152_601), (comp), (_152_600))))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _58_1722 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_1722) with
| (bs, c) -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp c)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args))
end))
end
| _58_1725 -> begin
if (not (norm)) then begin
(let _152_602 = (unfold_whnf env tf)
in (check_function_app true _152_602))
end else begin
(let _152_605 = (let _152_604 = (let _152_603 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in ((_152_603), (head.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_152_604))
in (Prims.raise _152_605))
end
end))
in (let _152_607 = (let _152_606 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _152_606))
in (check_function_app false _152_607))))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let _58_1761 = (FStar_List.fold_left2 (fun _58_1742 _58_1745 _58_1748 -> (match (((_58_1742), (_58_1745), (_58_1748))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(

let _58_1749 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifiers"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _58_1754 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_58_1754) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (let _152_617 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _152_617 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _152_621 = (let _152_619 = (let _152_618 = (FStar_Syntax_Syntax.as_arg e)
in (_152_618)::[])
in (FStar_List.append seen _152_619))
in (let _152_620 = (FStar_TypeChecker_Rel.conj_guard guard g)
in ((_152_621), (_152_620), (ghost)))))))
end)))
end)) (([]), (g_head), (false)) args bs)
in (match (_58_1761) with
| (args, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = if ghost then begin
(let _152_622 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _152_622 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (

let _58_1766 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_58_1766) with
| (c, g) -> begin
((e), (c), (g))
end))))
end)))
end
| _58_1768 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let _58_1775 = (FStar_Syntax_Subst.open_branch branch)
in (match (_58_1775) with
| (pattern, when_clause, branch_exp) -> begin
(

let _58_1780 = branch
in (match (_58_1780) with
| (cpat, _58_1778, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _58_1788 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_58_1788) with
| (pat_bvs, exps, p) -> begin
(

let _58_1789 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_634 = (FStar_Syntax_Print.pat_to_string p0)
in (let _152_633 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _152_634 _152_633)))
end else begin
()
end
in (

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let _58_1795 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_58_1795) with
| (env1, _58_1794) -> begin
(

let env1 = (

let _58_1796 = env1
in {FStar_TypeChecker_Env.solver = _58_1796.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1796.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1796.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1796.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1796.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1796.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1796.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1796.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _58_1796.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1796.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1796.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1796.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1796.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1796.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1796.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1796.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1796.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1796.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_1796.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_1796.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1796.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1796.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1796.FStar_TypeChecker_Env.qname_and_index})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _58_1835 = (let _152_657 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _58_1801 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_637 = (FStar_Syntax_Print.term_to_string e)
in (let _152_636 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _152_637 _152_636)))
end else begin
()
end
in (

let _58_1806 = (tc_term env1 e)
in (match (_58_1806) with
| (e, lc, g) -> begin
(

let _58_1807 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_639 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _152_638 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _152_639 _152_638)))
end else begin
()
end
in (

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let _58_1813 = (let _152_640 = (FStar_TypeChecker_Rel.discharge_guard env (

let _58_1811 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_1811.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_1811.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_1811.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _152_640 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _152_645 = (let _152_644 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _152_644 (FStar_List.map (fun _58_1821 -> (match (_58_1821) with
| (u, _58_1820) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _152_645 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _58_1829 = if (let _152_646 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _152_646)) then begin
(

let unresolved = (let _152_647 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _152_647 FStar_Util.set_elements))
in (let _152_655 = (let _152_654 = (let _152_653 = (let _152_652 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _152_651 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _152_650 = (let _152_649 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _58_1828 -> (match (_58_1828) with
| (u, _58_1827) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _152_649 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _152_652 _152_651 _152_650))))
in ((_152_653), (p.FStar_Syntax_Syntax.p)))
in FStar_Syntax_Syntax.Error (_152_654))
in (Prims.raise _152_655)))
end else begin
()
end
in (

let _58_1831 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_656 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _152_656))
end else begin
()
end
in ((e), (e'))))))))))))
end))))))
in (FStar_All.pipe_right _152_657 FStar_List.unzip))
in (match (_58_1835) with
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

let _58_1842 = (let _152_658 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _152_658 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_58_1842) with
| (scrutinee_env, _58_1841) -> begin
(

let _58_1848 = (tc_pat true pat_t pattern)
in (match (_58_1848) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let _58_1858 = (match (when_clause) with
| None -> begin
((None), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (e) -> begin
if (FStar_TypeChecker_Env.should_verify env) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("When clauses are not yet supported in --verify mode; they will be some day"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
(

let _58_1855 = (let _152_659 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _152_659 e))
in (match (_58_1855) with
| (e, c, g) -> begin
((Some (e)), (g))
end))
end
end)
in (match (_58_1858) with
| (when_clause, g_when) -> begin
(

let _58_1862 = (tc_term pat_env branch_exp)
in (match (_58_1862) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _152_661 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _152_660 -> Some (_152_660)) _152_661))
end)
in (

let _58_1920 = (

let eqs = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
None
end else begin
(FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _58_1880 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _152_665 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _152_664 -> Some (_152_664)) _152_665))
end))
end))) None))
end
in (

let _58_1888 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_58_1888) with
| (c, g_branch) -> begin
(

let _58_1915 = (match (((eqs), (when_condition))) with
| _58_1890 when (not ((FStar_TypeChecker_Env.should_verify env))) -> begin
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
in (let _152_668 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _152_667 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((_152_668), (_152_667))))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (let _152_669 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_152_669))
in (let _152_672 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _152_671 = (let _152_670 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _152_670 g_when))
in ((_152_672), (_152_671))))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _152_673 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in ((_152_673), (g_when)))))
end)
in (match (_58_1915) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _152_675 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _152_674 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in ((_152_675), (_152_674), (g_branch)))))
end))
end)))
in (match (_58_1920) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
FStar_Syntax_Util.t_true
end else begin
(

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> if ((let _152_685 = (let _152_684 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _152_684))
in (FStar_List.length _152_685)) > (Prims.parse_int "1")) then begin
(

let disc = (let _152_686 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _152_686 FStar_Syntax_Syntax.Delta_equational None))
in (

let disc = (let _152_688 = (let _152_687 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_152_687)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _152_688 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _152_689 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_152_689)::[])))
end else begin
[]
end)
in (

let fail = (fun _58_1930 -> (match (()) with
| () -> begin
(let _152_695 = (let _152_694 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _152_693 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _152_692 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _152_694 _152_693 _152_692))))
in (FStar_All.failwith _152_695))
end))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _58_1937) -> begin
(head_constructor t)
end
| _58_1941 -> begin
(fail ())
end))
in (

let pat_exp = (let _152_698 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _152_698 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_58_1966) -> begin
(let _152_703 = (let _152_702 = (let _152_701 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _152_700 = (let _152_699 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_152_699)::[])
in (_152_701)::_152_700))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _152_702 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_152_703)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _152_704 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _152_704))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(

let sub_term_guards = (let _152_711 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _58_1984 -> (match (_58_1984) with
| (ei, _58_1983) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _58_1988 -> begin
(

let sub_term = (let _152_710 = (let _152_707 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _152_707 FStar_Syntax_Syntax.Delta_equational None))
in (let _152_709 = (let _152_708 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_152_708)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _152_710 _152_709 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _152_711 FStar_List.flatten))
in (let _152_712 = (discriminate scrutinee_tm f)
in (FStar_List.append _152_712 sub_term_guards)))
end)
end
| _58_1992 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(

let t = (let _152_717 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _152_717))
in (

let _58_2000 = (FStar_Syntax_Util.type_u ())
in (match (_58_2000) with
| (k, _58_1999) -> begin
(

let _58_2006 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_58_2006) with
| (t, _58_2003, _58_2005) -> begin
t
end))
end)))
end)
in (

let branch_guard = (let _152_718 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _152_718 FStar_Syntax_Util.mk_disj_l))
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

let _58_2014 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_719 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _152_719))
end else begin
()
end
in (let _152_720 = (FStar_Syntax_Subst.close_branch ((pattern), (when_clause), (branch_exp)))
in ((_152_720), (branch_guard), (c), (guard))))))
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

let _58_2031 = (check_let_bound_def true env lb)
in (match (_58_2031) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let _58_2043 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
((g1), (e1), (univ_vars), (c1))
end else begin
(

let g1 = (let _152_723 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _152_723 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _58_2038 = (let _152_727 = (let _152_726 = (let _152_725 = (let _152_724 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (_152_724)))
in (_152_725)::[])
in (FStar_TypeChecker_Util.generalize env _152_726))
in (FStar_List.hd _152_727))
in (match (_58_2038) with
| (_58_2034, univs, e1, c1) -> begin
((g1), (e1), (univs), ((FStar_Syntax_Util.lcomp_of_comp c1)))
end)))
end
in (match (_58_2043) with
| (g1, e1, univ_vars, c1) -> begin
(

let _58_2054 = if (FStar_TypeChecker_Env.should_verify env) then begin
(

let _58_2046 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_58_2046) with
| (ok, c1) -> begin
if ok then begin
((e2), (c1))
end else begin
(

let _58_2047 = if (FStar_Options.warn_top_level_effects ()) then begin
(let _152_728 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _152_728 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _152_729 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) None e2.FStar_Syntax_Syntax.pos)
in ((_152_729), (c1))))
end
end))
end else begin
(

let _58_2049 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (

let c = (let _152_730 = (c1.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_right _152_730 (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env)))
in ((e2), (c))))
end
in (match (_58_2054) with
| (e2, c1) -> begin
(

let cres = (let _152_731 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_731))
in (

let _58_2056 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _152_732 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((_152_732), (cres), (FStar_TypeChecker_Rel.trivial_guard))))))
end))
end))
end))
end
| _58_2060 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let _58_2071 = env
in {FStar_TypeChecker_Env.solver = _58_2071.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2071.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2071.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2071.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2071.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2071.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2071.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2071.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2071.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2071.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2071.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2071.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2071.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_2071.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2071.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2071.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2071.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2071.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_2071.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_2071.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2071.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2071.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2071.FStar_TypeChecker_Env.qname_and_index})
in (

let _58_2080 = (let _152_736 = (let _152_735 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _152_735 Prims.fst))
in (check_let_bound_def false _152_736 lb))
in (match (_58_2080) with
| (e1, _58_2076, c1, g1, annotated) -> begin
(

let x = (

let _58_2081 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_2081.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2081.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let _58_2087 = (let _152_738 = (let _152_737 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_737)::[])
in (FStar_Syntax_Subst.open_term _152_738 e2))
in (match (_58_2087) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _58_2093 = (let _152_739 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _152_739 e2))
in (match (_58_2093) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (x)), (c2)))
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e2 = (FStar_TypeChecker_Util.maybe_lift env e2 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e = (let _152_742 = (let _152_741 = (let _152_740 = (FStar_Syntax_Subst.close xb e2)
in ((((false), ((lb)::[]))), (_152_740)))
in FStar_Syntax_Syntax.Tm_let (_152_741))
in (FStar_Syntax_Syntax.mk _152_742 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (let _152_745 = (let _152_744 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _152_744 e1))
in (FStar_All.pipe_left (fun _152_743 -> FStar_TypeChecker_Common.NonTrivial (_152_743)) _152_745))
in (

let g2 = (let _152_747 = (let _152_746 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _152_746 g2))
in (FStar_TypeChecker_Rel.close_guard xb _152_747))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if (let _152_748 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome _152_748)) then begin
(

let tt = (let _152_749 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_All.pipe_right _152_749 FStar_Option.get))
in (

let _58_2103 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Exports"))) then begin
(let _152_751 = (FStar_Syntax_Print.term_to_string tt)
in (let _152_750 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Got expected type from env %s\ncres.res_typ=%s\n" _152_751 _152_750)))
end else begin
()
end
in ((e), (cres), (guard))))
end else begin
(

let t = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (

let _58_2106 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Exports"))) then begin
(let _152_753 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (let _152_752 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checked %s has no escaping types; normalized to %s\n" _152_753 _152_752)))
end else begin
()
end
in ((e), ((

let _58_2108 = cres
in {FStar_Syntax_Syntax.eff_name = _58_2108.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_2108.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_2108.FStar_Syntax_Syntax.comp})), (guard))))
end))))))))
end))))
end))))
end)))
end
| _58_2111 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _58_2123 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_58_2123) with
| (lbs, e2) -> begin
(

let _58_2126 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2126) with
| (env0, topt) -> begin
(

let _58_2129 = (build_let_rec_env true env0 lbs)
in (match (_58_2129) with
| (lbs, rec_env) -> begin
(

let _58_2132 = (check_let_recs rec_env lbs)
in (match (_58_2132) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (let _152_756 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _152_756 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _152_759 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _152_759 (fun _152_758 -> Some (_152_758))))
in (

let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(

let ecs = (let _152_763 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _152_762 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (_152_762))))))
in (FStar_TypeChecker_Util.generalize env _152_763))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _58_2143 -> (match (_58_2143) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _152_765 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_765))
in (

let _58_2146 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _58_2150 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_2150) with
| (lbs, e2) -> begin
(let _152_767 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _152_766 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in ((_152_767), (cres), (_152_766))))
end)))))))
end))
end))
end))
end))
end
| _58_2152 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _58_2164 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_58_2164) with
| (lbs, e2) -> begin
(

let _58_2167 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2167) with
| (env0, topt) -> begin
(

let _58_2170 = (build_let_rec_env false env0 lbs)
in (match (_58_2170) with
| (lbs, rec_env) -> begin
(

let _58_2173 = (check_let_recs rec_env lbs)
in (match (_58_2173) with
| (lbs, g_lbs) -> begin
(

let _58_2185 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let _58_2176 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_2176.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2176.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let _58_2179 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _58_2179.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _58_2179.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _58_2179.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _58_2179.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (lb.FStar_Syntax_Syntax.lbtyp)))
in ((env), (lb)))))) env))
in (match (_58_2185) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let _58_2191 = (tc_term env e2)
in (match (_58_2191) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _58_2195 = cres
in {FStar_Syntax_Syntax.eff_name = _58_2195.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _58_2195.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_2195.FStar_Syntax_Syntax.comp})
in (

let _58_2200 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_2200) with
| (lbs, e2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_58_2203) -> begin
((e), (cres), (guard))
end
| None -> begin
(

let tres = (check_no_escape None env bvs tres)
in (

let cres = (

let _58_2207 = cres
in {FStar_Syntax_Syntax.eff_name = _58_2207.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _58_2207.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_2207.FStar_Syntax_Syntax.comp})
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
| _58_2211 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun t -> (

let _58_2221 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (_58_2221) with
| (_58_2219, c) -> begin
(

let quals = (FStar_TypeChecker_Env.lookup_effect_quals env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
end)))
in (

let _58_2251 = (FStar_List.fold_left (fun _58_2225 lb -> (match (_58_2225) with
| (lbs, env) -> begin
(

let _58_2230 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_58_2230) with
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

let _58_2239 = (let _152_781 = (let _152_780 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _152_780))
in (tc_check_tot_or_gtot_term (

let _58_2233 = env0
in {FStar_TypeChecker_Env.solver = _58_2233.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2233.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2233.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2233.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2233.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2233.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2233.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2233.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2233.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2233.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2233.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2233.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2233.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2233.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _58_2233.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2233.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2233.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2233.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_2233.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_2233.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2233.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2233.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2233.FStar_TypeChecker_Env.qname_and_index}) t _152_781))
in (match (_58_2239) with
| (t, _58_2237, g) -> begin
(

let _58_2240 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (

let env = if ((termination_check_enabled t) && (FStar_TypeChecker_Env.should_verify env)) then begin
(

let _58_2243 = env
in {FStar_TypeChecker_Env.solver = _58_2243.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2243.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2243.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2243.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2243.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2243.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2243.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2243.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2243.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2243.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2243.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2243.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t)))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2243.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_2243.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2243.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2243.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2243.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2243.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_2243.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_2243.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2243.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2243.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2243.FStar_TypeChecker_Env.qname_and_index})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (t)))
end
in (

let lb = (

let _58_2246 = lb
in {FStar_Syntax_Syntax.lbname = _58_2246.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _58_2246.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb)::lbs), (env)))))))
end))
end)) (([]), (env)) lbs)
in (match (_58_2251) with
| (lbs, env) -> begin
(((FStar_List.rev lbs)), (env))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _58_2264 = (let _152_786 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _58_2258 = (let _152_785 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _152_785 lb.FStar_Syntax_Syntax.lbdef))
in (match (_58_2258) with
| (e, c, g) -> begin
(

let _58_2259 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in ((lb), (g))))
end)))))
in (FStar_All.pipe_right _152_786 FStar_List.unzip))
in (match (_58_2264) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _58_2272 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2272) with
| (env1, _58_2271) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _58_2278 = (check_lbtyp top_level env lb)
in (match (_58_2278) with
| (topt, wf_annot, univ_vars, env1) -> begin
(

let _58_2279 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _58_2286 = (tc_maybe_toplevel_term (

let _58_2281 = env1
in {FStar_TypeChecker_Env.solver = _58_2281.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2281.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2281.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2281.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2281.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2281.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2281.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2281.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2281.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2281.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2281.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2281.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2281.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _58_2281.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2281.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2281.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2281.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2281.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_2281.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_2281.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2281.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2281.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2281.FStar_TypeChecker_Env.qname_and_index}) e1)
in (match (_58_2286) with
| (e1, c1, g1) -> begin
(

let _58_2290 = (let _152_793 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_2287 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _152_793 e1 c1 wf_annot))
in (match (_58_2290) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _58_2292 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_796 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _152_795 = (FStar_Syntax_Print.term_to_string c1.FStar_Syntax_Syntax.res_typ)
in (let _152_794 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print3 "checked top-level def %s, result type is %s, guard is %s\n" _152_796 _152_795 _152_794))))
end else begin
()
end
in (let _152_797 = (FStar_Option.isSome topt)
in ((e1), (univ_vars), (c1), (g1), (_152_797)))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _58_2299 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in ((None), (FStar_TypeChecker_Rel.trivial_guard), ([]), (env)))
end
| _58_2302 -> begin
(

let _58_2305 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_58_2305) with
| (univ_vars, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _152_801 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars), (_152_801)))
end else begin
(

let _58_2310 = (FStar_Syntax_Util.type_u ())
in (match (_58_2310) with
| (k, _58_2309) -> begin
(

let _58_2315 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_58_2315) with
| (t, _58_2313, g) -> begin
(

let _58_2316 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _152_804 = (let _152_802 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _152_802))
in (let _152_803 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _152_804 _152_803)))
end else begin
()
end
in (

let t = (norm env1 t)
in (let _152_805 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (g), (univ_vars), (_152_805)))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _58_2322 -> (match (_58_2322) with
| (x, imp) -> begin
(

let _58_2325 = (FStar_Syntax_Util.type_u ())
in (match (_58_2325) with
| (tu, u) -> begin
(

let _58_2326 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_810 = (FStar_Syntax_Print.bv_to_string x)
in (let _152_809 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _152_808 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binders %s:%s at type %s\n" _152_810 _152_809 _152_808))))
end else begin
()
end
in (

let _58_2332 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_58_2332) with
| (t, _58_2330, g) -> begin
(

let x = (((

let _58_2333 = x
in {FStar_Syntax_Syntax.ppname = _58_2333.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2333.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in (

let _58_2336 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_812 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _152_811 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _152_812 _152_811)))
end else begin
()
end
in (let _152_813 = (push_binding env x)
in ((x), (_152_813), (g), (u)))))
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

let _58_2351 = (tc_binder env b)
in (match (_58_2351) with
| (b, env', g, u) -> begin
(

let _58_2356 = (aux env' bs)
in (match (_58_2356) with
| (bs, env', g', us) -> begin
(let _152_821 = (let _152_820 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _152_820))
in (((b)::bs), (env'), (_152_821), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun _58_2364 _58_2367 -> (match (((_58_2364), (_58_2367))) with
| ((t, imp), (args, g)) -> begin
(

let _58_2372 = (tc_term env t)
in (match (_58_2372) with
| (t, _58_2370, g') -> begin
(let _152_830 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t), (imp)))::args), (_152_830)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p _58_2376 -> (match (_58_2376) with
| (pats, g) -> begin
(

let _58_2379 = (tc_args env p)
in (match (_58_2379) with
| (args, g') -> begin
(let _152_833 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats), (_152_833)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _58_2385 = (tc_maybe_toplevel_term env e)
in (match (_58_2385) with
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

let _58_2391 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _152_836 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in ((_152_836), (false)))
end else begin
(let _152_837 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in ((_152_837), (true)))
end
in (match (_58_2391) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _152_838 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (_152_838)))
end
| _58_2395 -> begin
if allow_ghost then begin
(let _152_841 = (let _152_840 = (let _152_839 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in ((_152_839), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_152_840))
in (Prims.raise _152_841))
end else begin
(let _152_844 = (let _152_843 = (let _152_842 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in ((_152_842), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_152_843))
in (Prims.raise _152_844))
end
end)
end)))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let _58_2405 = (tc_tot_or_gtot_term env t)
in (match (_58_2405) with
| (t, c, g) -> begin
(

let _58_2406 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in ((t), (c)))
end)))


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _58_2410 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _152_854 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _152_854))
end else begin
()
end
in (

let env = (

let _58_2412 = env
in {FStar_TypeChecker_Env.solver = _58_2412.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2412.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2412.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2412.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2412.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2412.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2412.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2412.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2412.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2412.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2412.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2412.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2412.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_2412.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2412.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2412.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2412.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2412.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_2412.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_2412.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2412.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2412.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2412.FStar_TypeChecker_Env.qname_and_index})
in (

let _58_2428 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _58_2420) -> begin
(let _152_859 = (let _152_858 = (let _152_857 = (FStar_TypeChecker_Env.get_range env)
in (((Prims.strcat "Implicit argument: " msg)), (_152_857)))
in FStar_Syntax_Syntax.Error (_152_858))
in (Prims.raise _152_859))
end
in (match (_58_2428) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end else begin
(let _152_864 = (let _152_863 = (let _152_862 = (let _152_860 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _152_860))
in (let _152_861 = (FStar_TypeChecker_Env.get_range env)
in ((_152_862), (_152_861))))
in FStar_Syntax_Syntax.Error (_152_863))
in (Prims.raise _152_864))
end
end)))))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> (

let _58_2431 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_869 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "<start> universe_of %s\n" _152_869))
end else begin
()
end
in (

let _58_2436 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2436) with
| (env, _58_2435) -> begin
(

let env = (

let _58_2437 = env
in {FStar_TypeChecker_Env.solver = _58_2437.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2437.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2437.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2437.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2437.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2437.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2437.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2437.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2437.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2437.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2437.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2437.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2437.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_2437.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2437.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2437.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2437.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _58_2437.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_2437.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2437.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _58_2437.FStar_TypeChecker_Env.qname_and_index})
in (

let fail = (fun e t -> (let _152_879 = (let _152_878 = (let _152_877 = (let _152_875 = (FStar_Syntax_Print.term_to_string e)
in (let _152_874 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" _152_875 _152_874)))
in (let _152_876 = (FStar_TypeChecker_Env.get_range env)
in ((_152_877), (_152_876))))
in FStar_Syntax_Syntax.Error (_152_878))
in (Prims.raise _152_879)))
in (

let ok = (fun u -> (

let _58_2445 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_884 = (FStar_Syntax_Print.tag_of_term e)
in (let _152_883 = (FStar_Syntax_Print.term_to_string e)
in (let _152_882 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.print3 "<end> universe_of (%s) %s is %s\n" _152_884 _152_883 _152_882))))
end else begin
()
end
in u))
in (

let universe_of_type = (fun e t -> (match ((let _152_889 = (FStar_Syntax_Util.unrefine t)
in _152_889.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(ok u)
end
| _58_2453 -> begin
(fail e t)
end))
in (

let _58_2456 = (FStar_Syntax_Util.head_and_args e)
in (match (_58_2456) with
| (head, args) -> begin
(match ((let _152_890 = (FStar_Syntax_Subst.compress head)
in _152_890.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_58_2458, t) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _152_891 = (FStar_Syntax_Subst.compress t)
in _152_891.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_2464, t) -> begin
(universe_of_type e (FStar_Syntax_Util.comp_result t))
end
| _58_2469 -> begin
(universe_of_type e t)
end))
end
| _58_2471 -> begin
(

let t = (match ((FStar_ST.read e.FStar_Syntax_Syntax.tk)) with
| (None) | (Some (FStar_Syntax_Syntax.Tm_unknown)) -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoInline)::[]) env e)
in (

let _58_2487 = (tc_term env e)
in (match (_58_2487) with
| (_58_2477, {FStar_Syntax_Syntax.eff_name = _58_2484; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_2481; FStar_Syntax_Syntax.comp = _58_2479}, g) -> begin
(

let _58_2488 = (let _152_893 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (FStar_All.pipe_right _152_893 Prims.ignore))
in t)
end)))
end
| Some (t) -> begin
(FStar_Syntax_Syntax.mk t None e.FStar_Syntax_Syntax.pos)
end)
in (let _152_894 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (FStar_All.pipe_left (universe_of_type e) _152_894)))
end)
end))))))
end))))




