
open Prims

let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (not ((let _150_3 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _150_3))))))


let rng : FStar_TypeChecker_Env.env  ->  FStar_Range.range = (fun env -> (FStar_TypeChecker_Env.get_range env))


let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _58_19 = env
in {FStar_TypeChecker_Env.solver = _58_19.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_19.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_19.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_19.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_19.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_19.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_19.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_19.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_19.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _58_19.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_19.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_19.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_19.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_19.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_19.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_19.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_19.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_19.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_19.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_19.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_19.FStar_TypeChecker_Env.use_bv_sorts}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _58_22 = env
in {FStar_TypeChecker_Env.solver = _58_22.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_22.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_22.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_22.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_22.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_22.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_22.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_22.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_22.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _58_22.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_22.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_22.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_22.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_22.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_22.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_22.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_22.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_22.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_22.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_22.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_22.FStar_TypeChecker_Env.use_bv_sorts}))


let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (

let r = if (tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
v.FStar_Syntax_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos tl.FStar_Syntax_Syntax.pos)
end
in (let _150_17 = (let _150_16 = (FStar_Syntax_Syntax.as_arg v)
in (let _150_15 = (let _150_14 = (FStar_Syntax_Syntax.as_arg tl)
in (_150_14)::[])
in (_150_16)::_150_15))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _150_17 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _58_1 -> (match (_58_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _58_32 -> begin
false
end))


let steps = (fun env -> (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[])


let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Beta)::[]) env t))


let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize (steps env) env t))


let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (FStar_TypeChecker_Normalize.normalize_comp (steps env) env c))


let check_no_escape : FStar_Syntax_Syntax.term Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun head_opt env fvs kt -> (

let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
()
end
| _58_49 -> begin
(

let fvs' = (let _150_45 = if try_norm then begin
(norm env t)
end else begin
t
end
in (FStar_Syntax_Free.names _150_45))
in (match ((FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)) with
| None -> begin
()
end
| Some (x) -> begin
if (not (try_norm)) then begin
(aux true t)
end else begin
(

let fail = (fun _58_56 -> (match (()) with
| () -> begin
(

let msg = (match (head_opt) with
| None -> begin
(let _150_49 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _150_49))
end
| Some (head) -> begin
(let _150_51 = (FStar_Syntax_Print.bv_to_string x)
in (let _150_50 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _150_51 _150_50)))
end)
in (let _150_54 = (let _150_53 = (let _150_52 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (_150_52)))
in FStar_Syntax_Syntax.Error (_150_53))
in (Prims.raise _150_54)))
end))
in (

let s = (let _150_56 = (let _150_55 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _150_55))
in (FStar_TypeChecker_Util.new_uvar env _150_56))
in (match ((FStar_TypeChecker_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g)
end
| _58_65 -> begin
(fail ())
end)))
end
end))
end))
in (aux false kt)))


let push_binding = (fun env b -> (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))


let maybe_make_subst = (fun _58_2 -> (match (_58_2) with
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Syntax_Syntax.NT (((x), (e))))::[]
end
| _58_75 -> begin
[]
end))


let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.subst_t = (fun s b v -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
s
end else begin
(FStar_Syntax_Syntax.NT ((((Prims.fst b)), (v))))::s
end)


let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (

let _58_81 = lc
in {FStar_Syntax_Syntax.eff_name = _58_81.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_81.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _58_83 -> (match (()) with
| () -> begin
(let _150_71 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _150_71 t))
end))}))


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let should_return = (fun t -> (match ((let _150_82 = (FStar_Syntax_Subst.compress t)
in _150_82.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_91, c) -> begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(

let t = (FStar_All.pipe_left FStar_Syntax_Util.unrefine (FStar_Syntax_Util.comp_result c))
in (match ((let _150_83 = (FStar_Syntax_Subst.compress t)
in _150_83.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (_58_99) -> begin
false
end
| _58_102 -> begin
true
end))
end else begin
false
end
end
| _58_104 -> begin
true
end))
in (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _150_84 = if ((not ((should_return t))) || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _150_84))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _58_132 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
((e), (lc), (guard))
end
| Some (t') -> begin
(

let _58_114 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_86 = (FStar_Syntax_Print.term_to_string t)
in (let _150_85 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _150_86 _150_85)))
end else begin
()
end
in (

let _58_118 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_58_118) with
| (e, lc) -> begin
(

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _58_122 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_58_122) with
| (e, g) -> begin
(

let _58_123 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_88 = (FStar_Syntax_Print.term_to_string t)
in (let _150_87 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _150_88 _150_87)))
end else begin
()
end
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let _58_128 = (let _150_94 = (FStar_All.pipe_left (fun _150_93 -> Some (_150_93)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _150_94 env e lc g))
in (match (_58_128) with
| (lc, g) -> begin
((e), ((set_lcomp_result lc t')), (g))
end))))
end)))
end)))
end)
in (match (_58_132) with
| (e, lc, g) -> begin
(

let _58_133 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_95 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _150_95))
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

let _58_143 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_58_143) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _58_148 -> (match (_58_148) with
| (e, c) -> begin
(

let expected_c_opt = (match (copt) with
| Some (_58_150) -> begin
copt
end
| None -> begin
if ((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Syntax_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) then begin
(let _150_108 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (_150_108))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
if (FStar_Syntax_Util.is_pure_comp c) then begin
(let _150_109 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (_150_109))
end else begin
if (FStar_Syntax_Util.is_pure_or_ghost_comp c) then begin
(let _150_110 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (_150_110))
end else begin
None
end
end
end
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _150_111 = (norm_c env c)
in ((e), (_150_111), (FStar_TypeChecker_Rel.trivial_guard)))
end
| Some (expected_c) -> begin
(

let _58_157 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_114 = (FStar_Syntax_Print.term_to_string e)
in (let _150_113 = (FStar_Syntax_Print.comp_to_string c)
in (let _150_112 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _150_114 _150_113 _150_112))))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _58_160 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_117 = (FStar_Syntax_Print.term_to_string e)
in (let _150_116 = (FStar_Syntax_Print.comp_to_string c)
in (let _150_115 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _150_117 _150_116 _150_115))))
end else begin
()
end
in (

let _58_166 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_58_166) with
| (e, _58_164, g) -> begin
(

let g = (let _150_118 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _150_118 "could not prove post-condition" g))
in (

let _58_168 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_120 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _150_119 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _150_120 _150_119)))
end else begin
()
end
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e (FStar_Syntax_Util.comp_effect_name c) (FStar_Syntax_Util.comp_effect_name expected_c))
in ((e), (expected_c), (g)))))
end)))))
end))
end))


let no_logical_guard = (fun env _58_175 -> (match (_58_175) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
((te), (kt), (f))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _150_126 = (let _150_125 = (let _150_124 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _150_123 = (FStar_TypeChecker_Env.get_range env)
in ((_150_124), (_150_123))))
in FStar_Syntax_Syntax.Error (_150_125))
in (Prims.raise _150_126))
end)
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _150_129 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _150_129))
end))


let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _58_199; FStar_Syntax_Syntax.result_typ = _58_197; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, _58_191))::[]; FStar_Syntax_Syntax.flags = _58_188}) -> begin
(

let pat_vars = (FStar_Syntax_Free.names pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _58_206 -> (match (_58_206) with
| (b, _58_205) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _58_210) -> begin
(let _150_136 = (let _150_135 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _150_135))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _150_136))
end))
end
| _58_214 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end)


let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun env actuals expected_c -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
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

let _58_221 = env
in {FStar_TypeChecker_Env.solver = _58_221.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_221.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_221.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_221.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_221.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_221.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_221.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_221.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_221.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_221.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_221.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_221.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _58_221.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_221.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_221.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_221.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_221.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_221.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_221.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_221.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_221.FStar_TypeChecker_Env.use_bv_sorts})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _58_233 -> (match (_58_233) with
| (b, _58_232) -> begin
(

let t = (let _150_150 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _150_150))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _58_242 -> begin
(let _150_151 = (FStar_Syntax_Syntax.bv_to_name b)
in (_150_151)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let _58_248 = (FStar_Syntax_Util.head_and_args dec)
in (match (_58_248) with
| (head, _58_247) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _58_252 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _58_3 -> (match (_58_3) with
| FStar_Syntax_Syntax.DECREASES (_58_256) -> begin
true
end
| _58_259 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _58_264 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| _58_269 -> begin
(mk_lex_list xs)
end))
end)))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun _58_274 -> (match (_58_274) with
| (l, t) -> begin
(match ((let _150_157 = (FStar_Syntax_Subst.compress t)
in _150_157.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _58_281 -> (match (_58_281) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _150_161 = (let _150_160 = (let _150_159 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_150_159))
in (FStar_Syntax_Syntax.new_bv _150_160 x.FStar_Syntax_Syntax.sort))
in ((_150_161), (imp)))
end else begin
((x), (imp))
end
end))))
in (

let _58_285 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_58_285) with
| (formals, c) -> begin
(

let dec = (decreases_clause formals c)
in (

let precedes = (let _150_165 = (let _150_164 = (FStar_Syntax_Syntax.as_arg dec)
in (let _150_163 = (let _150_162 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_150_162)::[])
in (_150_164)::_150_163))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _150_165 None r))
in (

let _58_292 = (FStar_Util.prefix formals)
in (match (_58_292) with
| (bs, (last, imp)) -> begin
(

let last = (

let _58_293 = last
in (let _150_166 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _58_293.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_293.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_166}))
in (

let refined_formals = (FStar_List.append bs ((((last), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (

let _58_298 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_169 = (FStar_Syntax_Print.lbname_to_string l)
in (let _150_168 = (FStar_Syntax_Print.term_to_string t)
in (let _150_167 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _150_169 _150_168 _150_167))))
end else begin
()
end
in ((l), (t'))))))
end))))
end)))
end
| _58_301 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end)
end)


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let _58_304 = env
in {FStar_TypeChecker_Env.solver = _58_304.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_304.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_304.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_304.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_304.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_304.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_304.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_304.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_304.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_304.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_304.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_304.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_304.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_304.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_304.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_304.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_304.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_304.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_304.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_304.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_304.FStar_TypeChecker_Env.use_bv_sorts}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (

let _58_309 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_239 = (let _150_237 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _150_237))
in (let _150_238 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _150_239 _150_238)))
end else begin
()
end
in (

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_58_313) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let _58_354 = (tc_tot_or_gtot_term env e)
in (match (_58_354) with
| (e, c, g) -> begin
(

let g = (

let _58_355 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_355.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_355.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_355.FStar_TypeChecker_Env.implicits})
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let _58_365 = (FStar_Syntax_Util.type_u ())
in (match (_58_365) with
| (t, u) -> begin
(

let _58_369 = (tc_check_tot_or_gtot_term env e t)
in (match (_58_369) with
| (e, c, g) -> begin
(

let _58_376 = (

let _58_373 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_373) with
| (env, _58_372) -> begin
(tc_pats env pats)
end))
in (match (_58_376) with
| (pats, g') -> begin
(

let g' = (

let _58_377 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_377.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_377.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_377.FStar_TypeChecker_Env.implicits})
in (let _150_244 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_pattern (pats))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _150_243 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((_150_244), (c), (_150_243)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _150_245 = (FStar_Syntax_Subst.compress e)
in _150_245.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_58_386, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _58_393; FStar_Syntax_Syntax.lbtyp = _58_391; FStar_Syntax_Syntax.lbeff = _58_389; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _58_404 = (let _150_246 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _150_246 e1))
in (match (_58_404) with
| (e1, c1, g1) -> begin
(

let _58_408 = (tc_term env e2)
in (match (_58_408) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((None), (c2)))
in (

let e = (let _150_251 = (let _150_250 = (let _150_249 = (let _150_248 = (let _150_247 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_TypeChecker_Common.t_unit), (e1)))
in (_150_247)::[])
in ((false), (_150_248)))
in ((_150_249), (e2)))
in FStar_Syntax_Syntax.Tm_let (_150_250))
in (FStar_Syntax_Syntax.mk _150_251 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _150_252 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e), (c), (_150_252))))))
end))
end))
end
| _58_413 -> begin
(

let _58_417 = (tc_term env e)
in (match (_58_417) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (_58_421)) -> begin
(tc_term env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let _58_432 = (tc_term env e)
in (match (_58_432) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (m)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _58_438) -> begin
(

let _58_444 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_444) with
| (env0, _58_443) -> begin
(

let _58_449 = (tc_comp env0 expected_c)
in (match (_58_449) with
| (expected_c, _58_447, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (

let _58_454 = (let _150_253 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term _150_253 e))
in (match (_58_454) with
| (e, c', g') -> begin
(

let _58_458 = (let _150_255 = (let _150_254 = (c'.FStar_Syntax_Syntax.comp ())
in ((e), (_150_254)))
in (check_expected_effect env0 (Some (expected_c)) _150_255))
in (match (_58_458) with
| (e, expected_c, g'') -> begin
(let _150_258 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t_res)), (Some ((FStar_Syntax_Util.comp_effect_name expected_c)))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _150_257 = (let _150_256 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _150_256))
in ((_150_258), ((FStar_Syntax_Util.lcomp_of_comp expected_c)), (_150_257))))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _58_463) -> begin
(

let _58_468 = (FStar_Syntax_Util.type_u ())
in (match (_58_468) with
| (k, u) -> begin
(

let _58_473 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_473) with
| (t, _58_471, f) -> begin
(

let _58_477 = (let _150_259 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _150_259 e))
in (match (_58_477) with
| (e, c, g) -> begin
(

let _58_481 = (let _150_263 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_478 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _150_263 e c f))
in (match (_58_481) with
| (c, f) -> begin
(

let _58_485 = (let _150_264 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t)), (Some (c.FStar_Syntax_Syntax.eff_name))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _150_264 c))
in (match (_58_485) with
| (e, c, f2) -> begin
(let _150_266 = (let _150_265 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _150_265))
in ((e), (c), (_150_266)))
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

let _58_521 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_521) with
| (unary_op, _58_520) -> begin
(

let head = (let _150_267 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (Prims.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) None _150_267))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), (rest)))) None top.FStar_Syntax_Syntax.pos)
in (tc_term env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _58_529; FStar_Syntax_Syntax.pos = _58_527; FStar_Syntax_Syntax.vars = _58_525}, ((e, aqual))::[]) -> begin
(

let _58_539 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end else begin
()
end
in (

let _58_548 = (

let _58_544 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_544) with
| (env0, _58_543) -> begin
(tc_term env0 e)
end))
in (match (_58_548) with
| (e, c, g) -> begin
(

let _58_552 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_552) with
| (reify_op, _58_551) -> begin
(

let u_c = (

let _58_558 = (tc_term env c.FStar_Syntax_Syntax.res_typ)
in (match (_58_558) with
| (_58_554, c, _58_557) -> begin
(match ((let _150_268 = (FStar_Syntax_Subst.compress c.FStar_Syntax_Syntax.res_typ)
in _150_268.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| _58_562 -> begin
(FStar_All.failwith "Unexpected result type of computation")
end)
end))
in (

let repr = (FStar_TypeChecker_Util.reify_comp env c u_c)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e), (aqual)))::[])))) (Some (repr.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let c = (let _150_269 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right _150_269 FStar_Syntax_Util.lcomp_of_comp))
in (

let _58_570 = (comp_check_expected_typ env e c)
in (match (_58_570) with
| (e, c, g') -> begin
(let _150_270 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), (c), (_150_270)))
end))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.tk = _58_576; FStar_Syntax_Syntax.pos = _58_574; FStar_Syntax_Syntax.vars = _58_572}, ((e, aqual))::[]) -> begin
(

let _58_587 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end else begin
()
end
in (

let no_reflect = (fun _58_590 -> (match (()) with
| () -> begin
(let _150_275 = (let _150_274 = (let _150_273 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((_150_273), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_274))
in (Prims.raise _150_275))
end))
in (

let _58_594 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_594) with
| (reflect_op, _58_593) -> begin
(match ((FStar_TypeChecker_Env.effect_decl_opt env l)) with
| None -> begin
(no_reflect ())
end
| Some (ed) -> begin
if (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable)))) then begin
(no_reflect ())
end else begin
(

let _58_600 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_600) with
| (env_no_ex, topt) -> begin
(

let _58_628 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (let _150_281 = (let _150_280 = (let _150_279 = (let _150_278 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _150_277 = (let _150_276 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (_150_276)::[])
in (_150_278)::_150_277))
in ((repr), (_150_279)))
in FStar_Syntax_Syntax.Tm_app (_150_280))
in (FStar_Syntax_Syntax.mk _150_281 None top.FStar_Syntax_Syntax.pos))
in (

let _58_608 = (let _150_283 = (let _150_282 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _150_282 Prims.fst))
in (tc_tot_or_gtot_term _150_283 t))
in (match (_58_608) with
| (t, _58_606, g) -> begin
(match ((let _150_284 = (FStar_Syntax_Subst.compress t)
in _150_284.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_58_610, ((res, _58_617))::((wp, _58_613))::[]) -> begin
((t), (res), (wp), (g))
end
| _58_623 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))
in (match (_58_628) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let _58_642 = (

let _58_632 = (tc_tot_or_gtot_term env_no_ex e)
in (match (_58_632) with
| (e, c, g) -> begin
(

let _58_633 = if (let _150_285 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation _150_285)) then begin
(FStar_TypeChecker_Errors.add_errors env (((("Expected Tot, got a GTot computation"), (e.FStar_Syntax_Syntax.pos)))::[]))
end else begin
()
end
in (match ((FStar_TypeChecker_Rel.try_teq env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)) with
| None -> begin
(

let _58_636 = (let _150_290 = (let _150_289 = (let _150_288 = (let _150_287 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _150_286 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" _150_287 _150_286)))
in ((_150_288), (e.FStar_Syntax_Syntax.pos)))
in (_150_289)::[])
in (FStar_TypeChecker_Errors.add_errors env _150_290))
in (let _150_291 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e), (_150_291))))
end
| Some (g') -> begin
(let _150_293 = (let _150_292 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' _150_292))
in ((e), (_150_293)))
end))
end))
in (match (_58_642) with
| (e, g) -> begin
(

let c = (let _150_297 = (let _150_296 = (let _150_295 = (let _150_294 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_294)::[])
in {FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = _150_295; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp _150_296))
in (FStar_All.pipe_right _150_297 FStar_Syntax_Util.lcomp_of_comp))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e), (aqual)))::[])))) (Some (res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let _58_648 = (comp_check_expected_typ env e c)
in (match (_58_648) with
| (e, c, g') -> begin
(let _150_298 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e), (c), (_150_298)))
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

let env = (let _150_300 = (let _150_299 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _150_299 Prims.fst))
in (FStar_All.pipe_right _150_300 instantiate_both))
in (

let _58_655 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_302 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _150_301 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _150_302 _150_301)))
end else begin
()
end
in (

let _58_660 = (tc_term (no_inst env) head)
in (match (_58_660) with
| (head, chead, g_head) -> begin
(

let _58_664 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _150_303 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _150_303))
end else begin
(let _150_304 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _150_304))
end
in (match (_58_664) with
| (e, c, g) -> begin
(

let _58_665 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_305 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _150_305))
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

let _58_671 = (comp_check_expected_typ env0 e c)
in (match (_58_671) with
| (e, c, g') -> begin
(

let gimp = (match ((let _150_306 = (FStar_Syntax_Subst.compress head)
in _150_306.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _58_674) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e), (c.FStar_Syntax_Syntax.res_typ), (head.FStar_Syntax_Syntax.pos))
in (

let _58_678 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_678.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_678.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_678.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _58_681 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (

let gres = (let _150_307 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _150_307))
in (

let _58_684 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_309 = (FStar_Syntax_Print.term_to_string e)
in (let _150_308 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" _150_309 _150_308)))
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

let _58_692 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_692) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let _58_697 = (tc_term env1 e1)
in (match (_58_697) with
| (e1, c1, g1) -> begin
(

let _58_708 = (match (topt) with
| Some (t) -> begin
((env), (t))
end
| None -> begin
(

let _58_704 = (FStar_Syntax_Util.type_u ())
in (match (_58_704) with
| (k, _58_703) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _150_310 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in ((_150_310), (res_t))))
end))
end)
in (match (_58_708) with
| (env_branches, res_t) -> begin
(

let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let _58_725 = (

let _58_722 = (FStar_List.fold_right (fun _58_716 _58_719 -> (match (((_58_716), (_58_719))) with
| ((_58_712, f, c, g), (caccum, gaccum)) -> begin
(let _150_313 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (_150_313)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_58_722) with
| (cases, g) -> begin
(let _150_314 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in ((_150_314), (g)))
end))
in (match (_58_725) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (guard_x)), (c_branches)))
in (

let e = (

let mk_match = (fun scrutinee -> (

let branches = (FStar_List.map (fun _58_736 -> (match (_58_736) with
| (f, _58_731, _58_733, _58_735) -> begin
f
end)) t_eqns)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (Some (cres.FStar_Syntax_Syntax.eff_name))))) None e.FStar_Syntax_Syntax.pos))))
in if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c1.FStar_Syntax_Syntax.eff_name) then begin
(mk_match e1)
end else begin
(

let e_match = (let _150_318 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match _150_318))
in (

let lb = (let _150_319 = (FStar_TypeChecker_Env.norm_eff_name env c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = _150_319; FStar_Syntax_Syntax.lbdef = e1})
in (let _150_324 = (let _150_323 = (let _150_322 = (let _150_321 = (let _150_320 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (_150_320)::[])
in (FStar_Syntax_Subst.close _150_321 e_match))
in ((((false), ((lb)::[]))), (_150_322)))
in FStar_Syntax_Syntax.Tm_let (_150_323))
in (FStar_Syntax_Syntax.mk _150_324 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))))
end)
in (

let _58_742 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_327 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _150_326 = (let _150_325 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _150_325))
in (FStar_Util.print2 "(%s) comp type = %s\n" _150_327 _150_326)))
end else begin
()
end
in (let _150_328 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e), (cres), (_150_328))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_754); FStar_Syntax_Syntax.lbunivs = _58_752; FStar_Syntax_Syntax.lbtyp = _58_750; FStar_Syntax_Syntax.lbeff = _58_748; FStar_Syntax_Syntax.lbdef = _58_746})::[]), _58_760) -> begin
(

let _58_763 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_329 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _150_329))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _58_767), _58_770) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_785); FStar_Syntax_Syntax.lbunivs = _58_783; FStar_Syntax_Syntax.lbtyp = _58_781; FStar_Syntax_Syntax.lbeff = _58_779; FStar_Syntax_Syntax.lbdef = _58_777})::_58_775), _58_791) -> begin
(

let _58_794 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_330 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _150_330))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _58_798), _58_801) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let _58_815 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_815) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _150_344 = (let _150_343 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_343))
in FStar_Util.Inr (_150_344))
end
in (

let is_data_ctor = (fun _58_4 -> (match (_58_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _58_825 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _150_350 = (let _150_349 = (let _150_348 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _150_347 = (FStar_TypeChecker_Env.get_range env)
in ((_150_348), (_150_347))))
in FStar_Syntax_Syntax.Error (_150_349))
in (Prims.raise _150_350))
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
(FStar_All.failwith "Impossible: Violation of locally nameless convention")
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (match ((let _150_351 = (FStar_Syntax_Subst.compress t1)
in _150_351.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_836) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _58_839 -> begin
(

let imp = (("uvar in term"), (env), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let _58_841 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_841.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_841.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_841.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _58_856 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(

let _58_849 = (FStar_Syntax_Util.type_u ())
in (match (_58_849) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
end))
end
| Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end)
in (match (_58_856) with
| (t, _58_854, g0) -> begin
(

let _58_861 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (_58_861) with
| (e, _58_859, g1) -> begin
(let _150_354 = (let _150_352 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right _150_352 FStar_Syntax_Util.lcomp_of_comp))
in (let _150_353 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e), (_150_354), (_150_353))))
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

let _58_865 = x
in {FStar_Syntax_Syntax.ppname = _58_865.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_865.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let _58_871 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_871) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _150_356 = (let _150_355 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_355))
in FStar_Util.Inr (_150_356))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _58_878; FStar_Syntax_Syntax.pos = _58_876; FStar_Syntax_Syntax.vars = _58_874}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let _58_888 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_888) with
| (us', t) -> begin
(

let _58_895 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _150_359 = (let _150_358 = (let _150_357 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (_150_357)))
in FStar_Syntax_Syntax.Error (_150_358))
in (Prims.raise _150_359))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _58_894 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (

let fv' = (

let _58_897 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _58_899 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_899.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_899.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_897.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_897.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _150_362 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_362 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let _58_907 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_907) with
| (us, t) -> begin
(

let fv' = (

let _58_908 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _58_910 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_910.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_910.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_908.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_908.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _150_363 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_363 us))
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

let _58_924 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_924) with
| (bs, c) -> begin
(

let env0 = env
in (

let _58_929 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_929) with
| (env, _58_928) -> begin
(

let _58_934 = (tc_binders env bs)
in (match (_58_934) with
| (bs, env, g, us) -> begin
(

let _58_938 = (tc_comp env c)
in (match (_58_938) with
| (c, uc, f) -> begin
(

let e = (

let _58_939 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _58_939.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_939.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_939.FStar_Syntax_Syntax.vars})
in (

let _58_942 = (check_smt_pat env e bs c)
in (

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _150_364 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _150_364))
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

let _58_958 = (let _150_366 = (let _150_365 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_365)::[])
in (FStar_Syntax_Subst.open_term _150_366 phi))
in (match (_58_958) with
| (x, phi) -> begin
(

let env0 = env
in (

let _58_963 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_963) with
| (env, _58_962) -> begin
(

let _58_968 = (let _150_367 = (FStar_List.hd x)
in (tc_binder env _150_367))
in (match (_58_968) with
| (x, env, f1, u) -> begin
(

let _58_969 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_370 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _150_369 = (FStar_Syntax_Print.term_to_string phi)
in (let _150_368 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _150_370 _150_369 _150_368))))
end else begin
()
end
in (

let _58_974 = (FStar_Syntax_Util.type_u ())
in (match (_58_974) with
| (t_phi, _58_973) -> begin
(

let _58_979 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_58_979) with
| (phi, _58_977, f2) -> begin
(

let e = (

let _58_980 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _58_980.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_980.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_980.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _150_371 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _150_371))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _58_988) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (

let _58_994 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_372 = (FStar_Syntax_Print.term_to_string (

let _58_992 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))); FStar_Syntax_Syntax.tk = _58_992.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _58_992.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_992.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _150_372))
end else begin
()
end
in (

let _58_998 = (FStar_Syntax_Subst.open_term bs body)
in (match (_58_998) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _58_1000 -> begin
(let _150_375 = (let _150_374 = (FStar_Syntax_Print.term_to_string top)
in (let _150_373 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" _150_374 _150_373)))
in (FStar_All.failwith _150_375))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_58_1005) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_58_1008, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_58_1013, Some (_58_1015)) -> begin
(FStar_All.failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (_58_1020) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_58_1023) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_58_1026) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_58_1030) -> begin
FStar_TypeChecker_Common.t_range
end
| _58_1033 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(

let _58_1041 = (FStar_Syntax_Util.type_u ())
in (match (_58_1041) with
| (k, u) -> begin
(

let _58_1046 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_1046) with
| (t, _58_1044, g) -> begin
(let _150_380 = (FStar_Syntax_Syntax.mk_Total t)
in ((_150_380), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(

let _58_1051 = (FStar_Syntax_Util.type_u ())
in (match (_58_1051) with
| (k, u) -> begin
(

let _58_1056 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_1056) with
| (t, _58_1054, g) -> begin
(let _150_381 = (FStar_Syntax_Syntax.mk_GTotal t)
in ((_150_381), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (

let tc = (let _150_383 = (let _150_382 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_150_382)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _150_383 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let _58_1065 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_58_1065) with
| (tc, _58_1063, f) -> begin
(

let _58_1069 = (FStar_Syntax_Util.head_and_args tc)
in (match (_58_1069) with
| (_58_1067, args) -> begin
(

let _58_1072 = (let _150_385 = (FStar_List.hd args)
in (let _150_384 = (FStar_List.tl args)
in ((_150_385), (_150_384))))
in (match (_58_1072) with
| (res, args) -> begin
(

let _58_1088 = (let _150_387 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _58_5 -> (match (_58_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _58_1079 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1079) with
| (env, _58_1078) -> begin
(

let _58_1084 = (tc_tot_or_gtot_term env e)
in (match (_58_1084) with
| (e, _58_1082, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e)), (g))
end))
end))
end
| f -> begin
((f), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right _150_387 FStar_List.unzip))
in (match (_58_1088) with
| (flags, guards) -> begin
(

let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Syntax.mk t None FStar_Range.dummyRange)
in (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| _58_1099 -> begin
(FStar_All.failwith "Impossible:Unexpected sort for computation")
end)))
end
| _58_1101 -> begin
(FStar_All.failwith "Impossible:Unexpected sort for computation")
end)
in (let _150_389 = (FStar_Syntax_Syntax.mk_Comp (

let _58_1103 = c
in {FStar_Syntax_Syntax.effect_name = _58_1103.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _58_1103.FStar_Syntax_Syntax.flags}))
in (let _150_388 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((_150_389), (u), (_150_388)))))
end))
end))
end))
end))))
end)))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_58_1111) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _150_394 = (aux u)
in FStar_Syntax_Syntax.U_succ (_150_394))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _150_395 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_150_395))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _150_399 = (let _150_398 = (let _150_397 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _150_396 = (FStar_TypeChecker_Env.get_range env)
in ((_150_397), (_150_396))))
in FStar_Syntax_Syntax.Error (_150_398))
in (Prims.raise _150_399))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _150_400 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_400 Prims.snd))
end
| _58_1126 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _150_409 = (let _150_408 = (let _150_407 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in ((_150_407), (top.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_408))
in (Prims.raise _150_409)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun _58_1144 bs bs_expected -> (match (_58_1144) with
| (env, out, g, subst) -> begin
(match (((bs), (bs_expected))) with
| ([], []) -> begin
((env), ((FStar_List.rev out)), (None), (g), (subst))
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
(

let _58_1175 = (match (((imp), (imp'))) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _150_426 = (let _150_425 = (let _150_424 = (let _150_422 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _150_422))
in (let _150_423 = (FStar_Syntax_Syntax.range_of_bv hd)
in ((_150_424), (_150_423))))
in FStar_Syntax_Syntax.Error (_150_425))
in (Prims.raise _150_426))
end
| _58_1174 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _58_1192 = (match ((let _150_427 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _150_427.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| _58_1180 -> begin
(

let _58_1181 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_428 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _150_428))
end else begin
()
end
in (

let _58_1187 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_58_1187) with
| (t, _58_1185, g1) -> begin
(

let g2 = (let _150_430 = (FStar_TypeChecker_Env.get_range env)
in (let _150_429 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _150_430 "Type annotation on parameter incompatible with the expected type" _150_429)))
in (

let g = (let _150_431 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _150_431))
in ((t), (g))))
end)))
end)
in (match (_58_1192) with
| (t, g) -> begin
(

let hd = (

let _58_1193 = hd
in {FStar_Syntax_Syntax.ppname = _58_1193.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1193.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env = (push_binding env b)
in (

let subst = (let _150_432 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _150_432))
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

let _58_1214 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _58_1213 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (

let _58_1221 = (tc_binders env bs)
in (match (_58_1221) with
| (bs, envbody, g, _58_1220) -> begin
(

let _58_1239 = (match ((let _150_439 = (FStar_Syntax_Subst.compress body)
in _150_439.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _58_1226) -> begin
(

let _58_1233 = (tc_comp envbody c)
in (match (_58_1233) with
| (c, _58_1231, g') -> begin
(let _150_440 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((Some (c)), (body), (_150_440)))
end))
end
| _58_1235 -> begin
((None), (body), (g))
end)
in (match (_58_1239) with
| (copt, body, g) -> begin
((None), (bs), ([]), (copt), (envbody), (body), (g))
end))
end)))
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm t -> (match ((let _150_445 = (FStar_Syntax_Subst.compress t)
in _150_445.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let _58_1266 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _58_1265 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _58_1273 = (tc_binders env bs)
in (match (_58_1273) with
| (bs, envbody, g, _58_1272) -> begin
(

let _58_1277 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_58_1277) with
| (envbody, _58_1276) -> begin
((Some (((t), (true)))), (bs), ([]), (None), (envbody), (body), (g))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _58_1280) -> begin
(

let _58_1291 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_58_1291) with
| (_58_1284, bs, bs', copt, env, body, g) -> begin
((Some (((t), (false)))), (bs), (bs'), (copt), (env), (body), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _58_1298 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_58_1298) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun _58_1309 c_expected -> (match (_58_1309) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _150_456 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in ((env), (bs), (guard), (_150_456)))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (let _150_457 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _150_457))
in (let _150_458 = (FStar_Syntax_Subst.subst_comp subst c)
in ((env), (bs), (guard), (_150_458))))
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

let _58_1330 = (check_binders env more_bs bs_expected)
in (match (_58_1330) with
| (env, bs', more, guard', subst) -> begin
(let _150_460 = (let _150_459 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env), ((FStar_List.append bs bs')), (more), (_150_459), (subst)))
in (handle_more _150_460 c_expected))
end))
end
| _58_1332 -> begin
(let _150_462 = (let _150_461 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _150_461))
in (fail _150_462 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _150_463 = (check_binders env bs bs_expected)
in (handle_more _150_463 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let _58_1338 = envbody
in {FStar_TypeChecker_Env.solver = _58_1338.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1338.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1338.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1338.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1338.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1338.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1338.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1338.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1338.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1338.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1338.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1338.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _58_1338.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1338.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1338.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1338.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1338.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1338.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1338.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1338.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1338.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _58_1343 _58_1346 -> (match (((_58_1343), (_58_1346))) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _58_1352 = (let _150_473 = (let _150_472 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _150_472 Prims.fst))
in (tc_term _150_473 t))
in (match (_58_1352) with
| (t, _58_1349, _58_1351) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l (([]), (t)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _150_474 = (FStar_Syntax_Syntax.mk_binder (

let _58_1356 = x
in {FStar_Syntax_Syntax.ppname = _58_1356.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1356.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_150_474)::letrec_binders)
end
| _58_1359 -> begin
letrec_binders
end)
in ((env), (lb))))
end))
end)) ((envbody), ([])))))))
in (

let _58_1365 = (check_actuals_against_formals env bs bs_expected)
in (match (_58_1365) with
| (envbody, bs, g, c) -> begin
(

let _58_1368 = if (FStar_TypeChecker_Env.should_verify env) then begin
(mk_letrec_env envbody bs c)
end else begin
((envbody), ([]))
end
in (match (_58_1368) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in ((Some (((t), (false)))), (bs), (letrecs), (Some (c)), (envbody), (body), (g)))
end))
end))))
end))
end
| _58_1371 -> begin
if (not (norm)) then begin
(let _150_475 = (unfold_whnf env t)
in (as_function_typ true _150_475))
end else begin
(

let _58_1381 = (expected_function_typ env None body)
in (match (_58_1381) with
| (_58_1373, bs, _58_1376, c_opt, envbody, body, g) -> begin
((Some (((t), (false)))), (bs), ([]), (c_opt), (envbody), (body), (g))
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let _58_1385 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1385) with
| (env, topt) -> begin
(

let _58_1389 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_476 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _150_476 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (

let _58_1398 = (expected_function_typ env topt body)
in (match (_58_1398) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let _58_1404 = (tc_term (

let _58_1399 = envbody
in {FStar_TypeChecker_Env.solver = _58_1399.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1399.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1399.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1399.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1399.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1399.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1399.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1399.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1399.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1399.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1399.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1399.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1399.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_1399.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1399.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1399.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1399.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1399.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1399.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1399.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_58_1404) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _58_1406 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _150_479 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _150_478 = (let _150_477 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _150_477))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _150_479 _150_478)))
end else begin
()
end
in (

let _58_1413 = (let _150_481 = (let _150_480 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body), (_150_480)))
in (check_expected_effect (

let _58_1408 = envbody
in {FStar_TypeChecker_Env.solver = _58_1408.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1408.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1408.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1408.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1408.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1408.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1408.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1408.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1408.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1408.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1408.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1408.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1408.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1408.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1408.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1408.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1408.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1408.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1408.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1408.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1408.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _150_481))
in (match (_58_1413) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(let _150_482 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _150_482))
end else begin
(

let guard = (let _150_483 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) _150_483))
in guard)
end
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _150_486 = (let _150_485 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _150_484 -> FStar_Util.Inl (_150_484)))
in Some (_150_485))
in (FStar_Syntax_Util.abs bs body _150_486))
in (

let _58_1436 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_58_1425) -> begin
((e), (t), (guard))
end
| _58_1428 -> begin
(

let _58_1431 = if use_teq then begin
(let _150_487 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in ((e), (_150_487)))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_58_1431) with
| (e, guard') -> begin
(let _150_488 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((e), (t), (_150_488)))
end))
end))
end
| None -> begin
((e), (tfun_computed), (guard))
end)
in (match (_58_1436) with
| (e, tfun, guard) -> begin
(

let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (

let _58_1440 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_58_1440) with
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

let _58_1450 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_497 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _150_496 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _150_497 _150_496)))
end else begin
()
end
in (

let monadic_application = (fun _58_1457 subst arg_comps_rev arg_rets guard fvs bs -> (match (_58_1457) with
| (head, chead, ghead, cres) -> begin
(

let _58_1464 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let _58_1492 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun _58_6 -> (match (_58_6) with
| (_58_1471, _58_1473, None) -> begin
false
end
| (_58_1477, _58_1479, Some (c)) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _150_513 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _150_513 cres))
end else begin
(

let _58_1484 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_516 = (FStar_Syntax_Print.term_to_string head)
in (let _150_515 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _150_514 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _150_516 _150_515 _150_514))))
end else begin
()
end
in cres)
end
in ((cres), (g))))))
end
| _58_1488 -> begin
(

let g = (let _150_517 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right _150_517 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _150_522 = (let _150_521 = (let _150_520 = (let _150_519 = (let _150_518 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _150_518))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _150_519))
in (FStar_Syntax_Syntax.mk_Total _150_520))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_521))
in ((_150_522), (g))))
end)
in (match (_58_1492) with
| (cres, guard) -> begin
(

let _58_1493 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_523 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _150_523))
end else begin
()
end
in (

let _58_1515 = (FStar_List.fold_left (fun _58_1498 _58_1504 -> (match (((_58_1498), (_58_1504))) with
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
in (match (_58_1515) with
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

let _58_1521 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (_58_1521) with
| (comp, g) -> begin
((app), (comp), (g))
end)))))
end)))
end)))
end))
in (

let rec tc_args = (fun head_info _58_1529 bs args -> (match (_58_1529) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args))) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (_58_1535))))::rest, ((_58_1543, None))::_58_1541) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _58_1549 = (check_no_escape (Some (head)) env fvs t)
in (

let _58_1555 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_58_1555) with
| (varg, _58_1553, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst
in (

let arg = (let _150_535 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (_150_535)))
in (let _150_537 = (let _150_536 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst), ((((arg), (None), (None)))::outargs), ((arg)::arg_rets), (_150_536), (fvs)))
in (tc_args head_info _150_537 rest args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
(

let _58_1587 = (match (((aqual), (aq))) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _58_1586 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifier"), (e.FStar_Syntax_Syntax.pos)))))
end)
in (

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let _58_1590 = x
in {FStar_Syntax_Syntax.ppname = _58_1590.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1590.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (

let _58_1593 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_538 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _150_538))
end else begin
()
end
in (

let _58_1595 = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let _58_1598 = env
in {FStar_TypeChecker_Env.solver = _58_1598.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1598.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1598.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1598.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1598.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1598.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1598.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1598.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1598.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1598.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1598.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1598.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1598.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1598.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1598.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _58_1598.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1598.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1598.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1598.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1598.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1598.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _58_1601 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_541 = (FStar_Syntax_Print.tag_of_term e)
in (let _150_540 = (FStar_Syntax_Print.term_to_string e)
in (let _150_539 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _150_541 _150_540 _150_539))))
end else begin
()
end
in (

let _58_1606 = (tc_term env e)
in (match (_58_1606) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = ((e), (aq))
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(

let subst = (let _150_542 = (FStar_List.hd bs)
in (maybe_extend_subst subst _150_542 e))
in (tc_args head_info ((subst), ((((arg), (None), (None)))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(

let subst = (let _150_543 = (FStar_List.hd bs)
in (maybe_extend_subst subst _150_543 e))
in (tc_args head_info ((subst), ((((arg), (Some (x)), (Some (c))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (let _150_544 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _150_544)) then begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _150_545 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_545))
in (tc_args head_info ((subst), ((((arg), (Some (newx)), (Some (c))))::outargs), ((arg')::arg_rets), (g), (fvs)) rest rest')))
end else begin
(let _150_549 = (let _150_548 = (let _150_547 = (let _150_546 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _150_546))
in (_150_547)::arg_rets)
in ((subst), ((((arg), (Some (x)), (Some (c))))::outargs), (_150_548), (g), ((x)::fvs)))
in (tc_args head_info _150_549 rest rest'))
end
end
end))
end))))))))))
end
| (_58_1614, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::_58_1619) -> begin
(

let _58_1626 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (_58_1626) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _150_554 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _150_554 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let _58_1637 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (_58_1637) with
| (bs, cres') -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp cres')))
in (

let _58_1639 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_555 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _150_555))
end else begin
()
end
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args)))
end))
end
| _58_1642 when (not (norm)) -> begin
(let _150_556 = (unfold_whnf env tres)
in (aux true _150_556))
end
| _58_1644 -> begin
(let _150_562 = (let _150_561 = (let _150_560 = (let _150_558 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (let _150_557 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _150_558 _150_557)))
in (let _150_559 = (FStar_Syntax_Syntax.argpos arg)
in ((_150_560), (_150_559))))
in FStar_Syntax_Syntax.Error (_150_561))
in (Prims.raise _150_562))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (match ((let _150_567 = (FStar_Syntax_Util.unrefine tf)
in _150_567.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl -> begin
(

let _58_1677 = (tc_term env e)
in (match (_58_1677) with
| (e, c, g_e) -> begin
(

let _58_1681 = (tc_args env tl)
in (match (_58_1681) with
| (args, comps, g_rest) -> begin
(let _150_572 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e), (imp)))::args), ((((e.FStar_Syntax_Syntax.pos), (c)))::comps), (_150_572)))
end))
end))
end))
in (

let _58_1685 = (tc_args env args)
in (match (_58_1685) with
| (args, comps, g_args) -> begin
(

let bs = (let _150_574 = (FStar_All.pipe_right comps (FStar_List.map (fun _58_1689 -> (match (_58_1689) with
| (_58_1687, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks _150_574))
in (

let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _58_1695 -> begin
FStar_Syntax_Util.ml_comp
end)
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _150_589 = (FStar_Syntax_Subst.compress t)
in _150_589.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_58_1701) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _58_1706 -> begin
ml_or_tot
end)
end)
in (

let cres = (let _150_594 = (let _150_593 = (let _150_592 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_592 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _150_593))
in (ml_or_tot _150_594 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (

let _58_1710 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_597 = (FStar_Syntax_Print.term_to_string head)
in (let _150_596 = (FStar_Syntax_Print.term_to_string tf)
in (let _150_595 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _150_597 _150_596 _150_595))))
end else begin
()
end
in (

let _58_1712 = (let _150_598 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _150_598))
in (

let comp = (let _150_601 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _58_1716 out -> (match (_58_1716) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c ((None), (out)))
end)) ((((head.FStar_Syntax_Syntax.pos), (chead)))::comps) _150_601))
in (let _150_603 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _150_602 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((_150_603), (comp), (_150_602))))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _58_1725 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_1725) with
| (bs, c) -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp c)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args))
end))
end
| _58_1728 -> begin
if (not (norm)) then begin
(let _150_604 = (unfold_whnf env tf)
in (check_function_app true _150_604))
end else begin
(let _150_607 = (let _150_606 = (let _150_605 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in ((_150_605), (head.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_606))
in (Prims.raise _150_607))
end
end))
in (let _150_609 = (let _150_608 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _150_608))
in (check_function_app false _150_609))))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let _58_1764 = (FStar_List.fold_left2 (fun _58_1745 _58_1748 _58_1751 -> (match (((_58_1745), (_58_1748), (_58_1751))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(

let _58_1752 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifiers"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _58_1757 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_58_1757) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (let _150_619 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _150_619 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _150_623 = (let _150_621 = (let _150_620 = (FStar_Syntax_Syntax.as_arg e)
in (_150_620)::[])
in (FStar_List.append seen _150_621))
in (let _150_622 = (FStar_TypeChecker_Rel.conj_guard guard g)
in ((_150_623), (_150_622), (ghost)))))))
end)))
end)) (([]), (g_head), (false)) args bs)
in (match (_58_1764) with
| (args, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = if ghost then begin
(let _150_624 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _150_624 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (

let _58_1769 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_58_1769) with
| (c, g) -> begin
((e), (c), (g))
end))))
end)))
end
| _58_1771 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let _58_1778 = (FStar_Syntax_Subst.open_branch branch)
in (match (_58_1778) with
| (pattern, when_clause, branch_exp) -> begin
(

let _58_1783 = branch
in (match (_58_1783) with
| (cpat, _58_1781, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _58_1791 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_58_1791) with
| (pat_bvs, exps, p) -> begin
(

let _58_1792 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_636 = (FStar_Syntax_Print.pat_to_string p0)
in (let _150_635 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _150_636 _150_635)))
end else begin
()
end
in (

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let _58_1798 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_58_1798) with
| (env1, _58_1797) -> begin
(

let env1 = (

let _58_1799 = env1
in {FStar_TypeChecker_Env.solver = _58_1799.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1799.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1799.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1799.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1799.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1799.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1799.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1799.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _58_1799.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1799.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1799.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1799.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1799.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1799.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1799.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1799.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1799.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1799.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1799.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1799.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1799.FStar_TypeChecker_Env.use_bv_sorts})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _58_1838 = (let _150_659 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _58_1804 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_639 = (FStar_Syntax_Print.term_to_string e)
in (let _150_638 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _150_639 _150_638)))
end else begin
()
end
in (

let _58_1809 = (tc_term env1 e)
in (match (_58_1809) with
| (e, lc, g) -> begin
(

let _58_1810 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_641 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _150_640 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _150_641 _150_640)))
end else begin
()
end
in (

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let _58_1816 = (let _150_642 = (FStar_TypeChecker_Rel.discharge_guard env (

let _58_1814 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_1814.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_1814.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_1814.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _150_642 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _150_647 = (let _150_646 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _150_646 (FStar_List.map (fun _58_1824 -> (match (_58_1824) with
| (u, _58_1823) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _150_647 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _58_1832 = if (let _150_648 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _150_648)) then begin
(

let unresolved = (let _150_649 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _150_649 FStar_Util.set_elements))
in (let _150_657 = (let _150_656 = (let _150_655 = (let _150_654 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _150_653 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _150_652 = (let _150_651 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _58_1831 -> (match (_58_1831) with
| (u, _58_1830) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _150_651 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _150_654 _150_653 _150_652))))
in ((_150_655), (p.FStar_Syntax_Syntax.p)))
in FStar_Syntax_Syntax.Error (_150_656))
in (Prims.raise _150_657)))
end else begin
()
end
in (

let _58_1834 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_658 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _150_658))
end else begin
()
end
in ((e), (e'))))))))))))
end))))))
in (FStar_All.pipe_right _150_659 FStar_List.unzip))
in (match (_58_1838) with
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

let _58_1845 = (let _150_660 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _150_660 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_58_1845) with
| (scrutinee_env, _58_1844) -> begin
(

let _58_1851 = (tc_pat true pat_t pattern)
in (match (_58_1851) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let _58_1861 = (match (when_clause) with
| None -> begin
((None), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (e) -> begin
if (FStar_TypeChecker_Env.should_verify env) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("When clauses are not yet supported in --verify mode; they will be some day"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
(

let _58_1858 = (let _150_661 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _150_661 e))
in (match (_58_1858) with
| (e, c, g) -> begin
((Some (e)), (g))
end))
end
end)
in (match (_58_1861) with
| (when_clause, g_when) -> begin
(

let _58_1865 = (tc_term pat_env branch_exp)
in (match (_58_1865) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _150_663 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _150_662 -> Some (_150_662)) _150_663))
end)
in (

let _58_1923 = (

let eqs = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
None
end else begin
(FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _58_1883 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _150_667 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _150_666 -> Some (_150_666)) _150_667))
end))
end))) None))
end
in (

let _58_1891 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_58_1891) with
| (c, g_branch) -> begin
(

let _58_1918 = (match (((eqs), (when_condition))) with
| _58_1893 when (not ((FStar_TypeChecker_Env.should_verify env))) -> begin
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
in (let _150_670 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _150_669 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((_150_670), (_150_669))))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (let _150_671 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_150_671))
in (let _150_674 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _150_673 = (let _150_672 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _150_672 g_when))
in ((_150_674), (_150_673))))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _150_675 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in ((_150_675), (g_when)))))
end)
in (match (_58_1918) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _150_677 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _150_676 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in ((_150_677), (_150_676), (g_branch)))))
end))
end)))
in (match (_58_1923) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
FStar_Syntax_Util.t_true
end else begin
(

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> if ((let _150_687 = (let _150_686 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _150_686))
in (FStar_List.length _150_687)) > 1) then begin
(

let disc = (let _150_688 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _150_688 FStar_Syntax_Syntax.Delta_equational None))
in (

let disc = (let _150_690 = (let _150_689 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_150_689)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _150_690 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _150_691 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_150_691)::[])))
end else begin
[]
end)
in (

let fail = (fun _58_1933 -> (match (()) with
| () -> begin
(let _150_697 = (let _150_696 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _150_695 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _150_694 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _150_696 _150_695 _150_694))))
in (FStar_All.failwith _150_697))
end))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _58_1940) -> begin
(head_constructor t)
end
| _58_1944 -> begin
(fail ())
end))
in (

let pat_exp = (let _150_700 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _150_700 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_58_1969) -> begin
(let _150_705 = (let _150_704 = (let _150_703 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _150_702 = (let _150_701 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_150_701)::[])
in (_150_703)::_150_702))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _150_704 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_150_705)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _150_706 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _150_706))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(

let sub_term_guards = (let _150_713 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _58_1987 -> (match (_58_1987) with
| (ei, _58_1986) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _58_1991 -> begin
(

let sub_term = (let _150_712 = (let _150_709 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _150_709 FStar_Syntax_Syntax.Delta_equational None))
in (let _150_711 = (let _150_710 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_150_710)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _150_712 _150_711 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _150_713 FStar_List.flatten))
in (let _150_714 = (discriminate scrutinee_tm f)
in (FStar_List.append _150_714 sub_term_guards)))
end)
end
| _58_1995 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(

let t = (let _150_719 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _150_719))
in (

let _58_2003 = (FStar_Syntax_Util.type_u ())
in (match (_58_2003) with
| (k, _58_2002) -> begin
(

let _58_2009 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_58_2009) with
| (t, _58_2006, _58_2008) -> begin
t
end))
end)))
end)
in (

let branch_guard = (let _150_720 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _150_720 FStar_Syntax_Util.mk_disj_l))
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

let _58_2017 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_721 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _150_721))
end else begin
()
end
in (let _150_722 = (FStar_Syntax_Subst.close_branch ((pattern), (when_clause), (branch_exp)))
in ((_150_722), (branch_guard), (c), (guard))))))
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

let _58_2034 = (check_let_bound_def true env lb)
in (match (_58_2034) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let _58_2046 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
((g1), (e1), (univ_vars), (c1))
end else begin
(

let g1 = (let _150_725 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _150_725 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _58_2041 = (let _150_729 = (let _150_728 = (let _150_727 = (let _150_726 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (_150_726)))
in (_150_727)::[])
in (FStar_TypeChecker_Util.generalize env _150_728))
in (FStar_List.hd _150_729))
in (match (_58_2041) with
| (_58_2037, univs, e1, c1) -> begin
((g1), (e1), (univs), ((FStar_Syntax_Util.lcomp_of_comp c1)))
end)))
end
in (match (_58_2046) with
| (g1, e1, univ_vars, c1) -> begin
(

let _58_2056 = if (FStar_TypeChecker_Env.should_verify env) then begin
(

let _58_2049 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_58_2049) with
| (ok, c1) -> begin
if ok then begin
((e2), (c1))
end else begin
(

let _58_2050 = if (FStar_Options.warn_top_level_effects ()) then begin
(let _150_730 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _150_730 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _150_731 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) None e2.FStar_Syntax_Syntax.pos)
in ((_150_731), (c1))))
end
end))
end else begin
(

let _58_2052 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _150_732 = (c1.FStar_Syntax_Syntax.comp ())
in ((e2), (_150_732))))
end
in (match (_58_2056) with
| (e2, c1) -> begin
(

let cres = (let _150_733 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_733))
in (

let _58_2058 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _150_734 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((_150_734), (cres), (FStar_TypeChecker_Rel.trivial_guard))))))
end))
end))
end))
end
| _58_2062 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let _58_2073 = env
in {FStar_TypeChecker_Env.solver = _58_2073.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2073.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2073.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2073.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2073.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2073.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2073.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2073.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2073.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2073.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2073.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2073.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2073.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_2073.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2073.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2073.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2073.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2073.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2073.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2073.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2073.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _58_2082 = (let _150_738 = (let _150_737 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _150_737 Prims.fst))
in (check_let_bound_def false _150_738 lb))
in (match (_58_2082) with
| (e1, _58_2078, c1, g1, annotated) -> begin
(

let x = (

let _58_2083 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_2083.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2083.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let _58_2089 = (let _150_740 = (let _150_739 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_739)::[])
in (FStar_Syntax_Subst.open_term _150_740 e2))
in (match (_58_2089) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _58_2095 = (let _150_741 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _150_741 e2))
in (match (_58_2095) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (x)), (c2)))
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e2 = (FStar_TypeChecker_Util.maybe_lift env e2 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e = (let _150_744 = (let _150_743 = (let _150_742 = (FStar_Syntax_Subst.close xb e2)
in ((((false), ((lb)::[]))), (_150_742)))
in FStar_Syntax_Syntax.Tm_let (_150_743))
in (FStar_Syntax_Syntax.mk _150_744 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (let _150_747 = (let _150_746 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _150_746 e1))
in (FStar_All.pipe_left (fun _150_745 -> FStar_TypeChecker_Common.NonTrivial (_150_745)) _150_747))
in (

let g2 = (let _150_749 = (let _150_748 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _150_748 g2))
in (FStar_TypeChecker_Rel.close_guard xb _150_749))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if (let _150_750 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome _150_750)) then begin
((e), (cres), (guard))
end else begin
(

let _58_2104 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in ((e), (cres), (guard)))
end))))))))
end))))
end))))
end)))
end
| _58_2107 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _58_2119 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_58_2119) with
| (lbs, e2) -> begin
(

let _58_2122 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2122) with
| (env0, topt) -> begin
(

let _58_2125 = (build_let_rec_env true env0 lbs)
in (match (_58_2125) with
| (lbs, rec_env) -> begin
(

let _58_2128 = (check_let_recs rec_env lbs)
in (match (_58_2128) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (let _150_753 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _150_753 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _150_756 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _150_756 (fun _150_755 -> Some (_150_755))))
in (

let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(

let ecs = (let _150_760 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _150_759 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (_150_759))))))
in (FStar_TypeChecker_Util.generalize env _150_760))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _58_2139 -> (match (_58_2139) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _150_762 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_762))
in (

let _58_2142 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _58_2146 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_2146) with
| (lbs, e2) -> begin
(let _150_764 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _150_763 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in ((_150_764), (cres), (_150_763))))
end)))))))
end))
end))
end))
end))
end
| _58_2148 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _58_2160 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_58_2160) with
| (lbs, e2) -> begin
(

let _58_2163 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2163) with
| (env0, topt) -> begin
(

let _58_2166 = (build_let_rec_env false env0 lbs)
in (match (_58_2166) with
| (lbs, rec_env) -> begin
(

let _58_2169 = (check_let_recs rec_env lbs)
in (match (_58_2169) with
| (lbs, g_lbs) -> begin
(

let _58_2181 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let _58_2172 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_2172.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2172.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let _58_2175 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _58_2175.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _58_2175.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _58_2175.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _58_2175.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (lb.FStar_Syntax_Syntax.lbtyp)))
in ((env), (lb)))))) env))
in (match (_58_2181) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let _58_2187 = (tc_term env e2)
in (match (_58_2187) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _58_2191 = cres
in {FStar_Syntax_Syntax.eff_name = _58_2191.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _58_2191.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_2191.FStar_Syntax_Syntax.comp})
in (

let _58_2196 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_2196) with
| (lbs, e2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_58_2199) -> begin
((e), (cres), (guard))
end
| None -> begin
(

let _58_2202 = (check_no_escape None env bvs tres)
in ((e), (cres), (guard)))
end))
end))))))
end)))
end))
end))
end))
end))
end))
end
| _58_2205 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let _58_2238 = (FStar_List.fold_left (fun _58_2212 lb -> (match (_58_2212) with
| (lbs, env) -> begin
(

let _58_2217 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_58_2217) with
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

let _58_2226 = (let _150_776 = (let _150_775 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _150_775))
in (tc_check_tot_or_gtot_term (

let _58_2220 = env0
in {FStar_TypeChecker_Env.solver = _58_2220.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2220.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2220.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2220.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2220.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2220.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2220.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2220.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2220.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2220.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2220.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2220.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2220.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2220.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _58_2220.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2220.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2220.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2220.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2220.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2220.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2220.FStar_TypeChecker_Env.use_bv_sorts}) t _150_776))
in (match (_58_2226) with
| (t, _58_2224, g) -> begin
(

let _58_2227 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (

let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_TypeChecker_Env.should_verify env)) then begin
(

let _58_2230 = env
in {FStar_TypeChecker_Env.solver = _58_2230.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2230.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2230.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2230.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2230.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2230.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2230.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2230.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2230.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2230.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2230.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2230.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t)))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2230.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_2230.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2230.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2230.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2230.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2230.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2230.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2230.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2230.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (t)))
end
in (

let lb = (

let _58_2233 = lb
in {FStar_Syntax_Syntax.lbname = _58_2233.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _58_2233.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb)::lbs), (env)))))))
end))
end)) (([]), (env)) lbs)
in (match (_58_2238) with
| (lbs, env) -> begin
(((FStar_List.rev lbs)), (env))
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _58_2251 = (let _150_781 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _58_2245 = (let _150_780 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _150_780 lb.FStar_Syntax_Syntax.lbdef))
in (match (_58_2245) with
| (e, c, g) -> begin
(

let _58_2246 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in ((lb), (g))))
end)))))
in (FStar_All.pipe_right _150_781 FStar_List.unzip))
in (match (_58_2251) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _58_2259 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2259) with
| (env1, _58_2258) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _58_2265 = (check_lbtyp top_level env lb)
in (match (_58_2265) with
| (topt, wf_annot, univ_vars, env1) -> begin
(

let _58_2266 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _58_2273 = (tc_maybe_toplevel_term (

let _58_2268 = env1
in {FStar_TypeChecker_Env.solver = _58_2268.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2268.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2268.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2268.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2268.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2268.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2268.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2268.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2268.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2268.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2268.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2268.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2268.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _58_2268.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2268.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2268.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2268.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2268.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2268.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2268.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2268.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_58_2273) with
| (e1, c1, g1) -> begin
(

let _58_2277 = (let _150_788 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_2274 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _150_788 e1 c1 wf_annot))
in (match (_58_2277) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _58_2279 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_789 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _150_789))
end else begin
()
end
in (let _150_790 = (FStar_Option.isSome topt)
in ((e1), (univ_vars), (c1), (g1), (_150_790)))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _58_2286 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in ((None), (FStar_TypeChecker_Rel.trivial_guard), ([]), (env)))
end
| _58_2289 -> begin
(

let _58_2292 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_58_2292) with
| (univ_vars, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _150_794 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars), (_150_794)))
end else begin
(

let _58_2297 = (FStar_Syntax_Util.type_u ())
in (match (_58_2297) with
| (k, _58_2296) -> begin
(

let _58_2302 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_58_2302) with
| (t, _58_2300, g) -> begin
(

let _58_2303 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_797 = (let _150_795 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _150_795))
in (let _150_796 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _150_797 _150_796)))
end else begin
()
end
in (

let t = (norm env1 t)
in (let _150_798 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (g), (univ_vars), (_150_798)))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _58_2309 -> (match (_58_2309) with
| (x, imp) -> begin
(

let _58_2312 = (FStar_Syntax_Util.type_u ())
in (match (_58_2312) with
| (tu, u) -> begin
(

let _58_2317 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_58_2317) with
| (t, _58_2315, g) -> begin
(

let x = (((

let _58_2318 = x
in {FStar_Syntax_Syntax.ppname = _58_2318.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2318.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in (

let _58_2321 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_802 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _150_801 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _150_802 _150_801)))
end else begin
()
end
in (let _150_803 = (push_binding env x)
in ((x), (_150_803), (g), (u)))))
end))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe Prims.list) = (fun env bs -> (

let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
(([]), (env), (FStar_TypeChecker_Rel.trivial_guard), ([]))
end
| (b)::bs -> begin
(

let _58_2336 = (tc_binder env b)
in (match (_58_2336) with
| (b, env', g, u) -> begin
(

let _58_2341 = (aux env' bs)
in (match (_58_2341) with
| (bs, env', g', us) -> begin
(let _150_811 = (let _150_810 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _150_810))
in (((b)::bs), (env'), (_150_811), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun _58_2349 _58_2352 -> (match (((_58_2349), (_58_2352))) with
| ((t, imp), (args, g)) -> begin
(

let _58_2357 = (tc_term env t)
in (match (_58_2357) with
| (t, _58_2355, g') -> begin
(let _150_820 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t), (imp)))::args), (_150_820)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p _58_2361 -> (match (_58_2361) with
| (pats, g) -> begin
(

let _58_2364 = (tc_args env p)
in (match (_58_2364) with
| (args, g') -> begin
(let _150_823 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats), (_150_823)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _58_2370 = (tc_maybe_toplevel_term env e)
in (match (_58_2370) with
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

let _58_2376 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _150_826 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in ((_150_826), (false)))
end else begin
(let _150_827 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in ((_150_827), (true)))
end
in (match (_58_2376) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _150_828 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (_150_828)))
end
| _58_2380 -> begin
if allow_ghost then begin
(let _150_831 = (let _150_830 = (let _150_829 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in ((_150_829), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_830))
in (Prims.raise _150_831))
end else begin
(let _150_834 = (let _150_833 = (let _150_832 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in ((_150_832), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_833))
in (Prims.raise _150_834))
end
end)
end)))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let _58_2390 = (tc_tot_or_gtot_term env t)
in (match (_58_2390) with
| (t, c, g) -> begin
(

let _58_2391 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in ((t), (c)))
end)))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let _58_2399 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_2399) with
| (t, c, g) -> begin
(

let _58_2400 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _150_852 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _150_852)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _150_856 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (([]), (_150_856)))))


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let _58_2415 = (tc_binders env tps)
in (match (_58_2415) with
| (tps, env, g, us) -> begin
(

let _58_2416 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in ((tps), (env), (us)))
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (

let fail = (fun _58_2422 -> (match (()) with
| () -> begin
(let _150_871 = (let _150_870 = (let _150_869 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in ((_150_869), ((FStar_Ident.range_of_lid m))))
in FStar_Syntax_Syntax.Error (_150_870))
in (Prims.raise _150_871))
end))
in (

let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _58_2435))::((wp, _58_2431))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _58_2439 -> begin
(fail ())
end))
end
| _58_2441 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let _58_2448 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_58_2448) with
| (uvs, c) -> begin
((uvs), ([]), (c))
end))
end
| _58_2450 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let _58_2454 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_58_2454) with
| (uvs, t') -> begin
(match ((let _150_878 = (FStar_Syntax_Subst.compress t')
in _150_878.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
((uvs), (binders), (c))
end
| _58_2460 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))


let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (

let fail = (fun t -> (let _150_889 = (let _150_888 = (let _150_887 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in ((_150_887), ((FStar_Ident.range_of_lid mname))))
in FStar_Syntax_Syntax.Error (_150_888))
in (Prims.raise _150_889)))
in (match ((let _150_890 = (FStar_Syntax_Subst.compress signature)
in _150_890.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _58_2477))::((wp, _58_2473))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _58_2481 -> begin
(fail signature)
end))
end
| _58_2483 -> begin
(fail signature)
end)))


let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (

let _58_2488 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_58_2488) with
| (a, wp) -> begin
(

let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _58_2491 -> begin
(

let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (

let op = (fun ts -> (

let _58_2495 = ()
in (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in (([]), (t1)))))
in (

let _58_2498 = ed
in (let _150_906 = (op ed.FStar_Syntax_Syntax.ret_wp)
in (let _150_905 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _150_904 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _150_903 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _150_902 = (op ed.FStar_Syntax_Syntax.stronger)
in (let _150_901 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _150_900 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _150_899 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _150_898 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _150_897 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _58_2498.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2498.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _58_2498.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _58_2498.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _58_2498.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _150_906; FStar_Syntax_Syntax.bind_wp = _150_905; FStar_Syntax_Syntax.if_then_else = _150_904; FStar_Syntax_Syntax.ite_wp = _150_903; FStar_Syntax_Syntax.stronger = _150_902; FStar_Syntax_Syntax.close_wp = _150_901; FStar_Syntax_Syntax.assert_p = _150_900; FStar_Syntax_Syntax.assume_p = _150_899; FStar_Syntax_Syntax.null_wp = _150_898; FStar_Syntax_Syntax.trivial = _150_897; FStar_Syntax_Syntax.repr = _58_2498.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _58_2498.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _58_2498.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _58_2498.FStar_Syntax_Syntax.actions})))))))))))))
end)
in ((ed), (a), (wp)))
end)))


let rec tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (

let _58_2503 = ()
in (

let _58_2507 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_58_2507) with
| (binders_un, signature_un) -> begin
(

let _58_2512 = (tc_tparams env0 binders_un)
in (match (_58_2512) with
| (binders, env, _58_2511) -> begin
(

let _58_2516 = (tc_trivial_guard env signature_un)
in (match (_58_2516) with
| (signature, _58_2515) -> begin
(

let ed = (

let _58_2517 = ed
in {FStar_Syntax_Syntax.qualifiers = _58_2517.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2517.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _58_2517.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _58_2517.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _58_2517.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _58_2517.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _58_2517.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _58_2517.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _58_2517.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _58_2517.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _58_2517.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _58_2517.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _58_2517.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _58_2517.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _58_2517.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _58_2517.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _58_2517.FStar_Syntax_Syntax.actions})
in (

let _58_2523 = (open_effect_decl env ed)
in (match (_58_2523) with
| (ed, a, wp_a) -> begin
(

let get_effect_signature = (fun _58_2525 -> (match (()) with
| () -> begin
(

let _58_2529 = (tc_trivial_guard env signature_un)
in (match (_58_2529) with
| (signature, _58_2528) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (

let env = (let _150_930 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _150_930))
in (

let _58_2531 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _150_936 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _150_935 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _150_934 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _150_933 = (let _150_931 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Print.term_to_string _150_931))
in (let _150_932 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort)
in (FStar_Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n" _150_936 _150_935 _150_934 _150_933 _150_932))))))
end else begin
()
end
in (

let check_and_gen' = (fun env _58_2538 k -> (match (_58_2538) with
| (_58_2536, t) -> begin
(check_and_gen env t k)
end))
in (

let return_wp = (

let expected_k = (let _150_948 = (let _150_946 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_945 = (let _150_944 = (let _150_943 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _150_943))
in (_150_944)::[])
in (_150_946)::_150_945))
in (let _150_947 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _150_948 _150_947)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let _58_2544 = (get_effect_signature ())
in (match (_58_2544) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _150_952 = (let _150_950 = (let _150_949 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _150_949))
in (_150_950)::[])
in (let _150_951 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _150_952 _150_951)))
in (

let expected_k = (let _150_963 = (let _150_961 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _150_960 = (let _150_959 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_958 = (let _150_957 = (FStar_Syntax_Syntax.mk_binder b)
in (let _150_956 = (let _150_955 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _150_954 = (let _150_953 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (_150_953)::[])
in (_150_955)::_150_954))
in (_150_957)::_150_956))
in (_150_959)::_150_958))
in (_150_961)::_150_960))
in (let _150_962 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _150_963 _150_962)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (let _150_965 = (let _150_964 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_964 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _150_965))
in (

let expected_k = (let _150_974 = (let _150_972 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_971 = (let _150_970 = (FStar_Syntax_Syntax.mk_binder p)
in (let _150_969 = (let _150_968 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _150_967 = (let _150_966 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_966)::[])
in (_150_968)::_150_967))
in (_150_970)::_150_969))
in (_150_972)::_150_971))
in (let _150_973 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_974 _150_973)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (let _150_979 = (let _150_977 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_976 = (let _150_975 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_975)::[])
in (_150_977)::_150_976))
in (let _150_978 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_979 _150_978)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let _58_2556 = (FStar_Syntax_Util.type_u ())
in (match (_58_2556) with
| (t, _58_2555) -> begin
(

let expected_k = (let _150_986 = (let _150_984 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_983 = (let _150_982 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _150_981 = (let _150_980 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_980)::[])
in (_150_982)::_150_981))
in (_150_984)::_150_983))
in (let _150_985 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _150_986 _150_985)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (let _150_988 = (let _150_987 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_987 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _150_988))
in (

let b_wp_a = (let _150_992 = (let _150_990 = (let _150_989 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _150_989))
in (_150_990)::[])
in (let _150_991 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_992 _150_991)))
in (

let expected_k = (let _150_999 = (let _150_997 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_996 = (let _150_995 = (FStar_Syntax_Syntax.mk_binder b)
in (let _150_994 = (let _150_993 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_150_993)::[])
in (_150_995)::_150_994))
in (_150_997)::_150_996))
in (let _150_998 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_999 _150_998)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (let _150_1008 = (let _150_1006 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1005 = (let _150_1004 = (let _150_1001 = (let _150_1000 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_1000 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _150_1001))
in (let _150_1003 = (let _150_1002 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_1002)::[])
in (_150_1004)::_150_1003))
in (_150_1006)::_150_1005))
in (let _150_1007 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_1008 _150_1007)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _150_1017 = (let _150_1015 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1014 = (let _150_1013 = (let _150_1010 = (let _150_1009 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_1009 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _150_1010))
in (let _150_1012 = (let _150_1011 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_1011)::[])
in (_150_1013)::_150_1012))
in (_150_1015)::_150_1014))
in (let _150_1016 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_1017 _150_1016)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _150_1020 = (let _150_1018 = (FStar_Syntax_Syntax.mk_binder a)
in (_150_1018)::[])
in (let _150_1019 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_1020 _150_1019)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let _58_2572 = (FStar_Syntax_Util.type_u ())
in (match (_58_2572) with
| (t, _58_2571) -> begin
(

let expected_k = (let _150_1025 = (let _150_1023 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1022 = (let _150_1021 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_1021)::[])
in (_150_1023)::_150_1022))
in (let _150_1024 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _150_1025 _150_1024)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let _58_2710 = if ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) || (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable))) then begin
(

let repr = (

let _58_2578 = (FStar_Syntax_Util.type_u ())
in (match (_58_2578) with
| (t, _58_2577) -> begin
(

let expected_k = (let _150_1030 = (let _150_1028 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1027 = (let _150_1026 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_1026)::[])
in (_150_1028)::_150_1027))
in (let _150_1029 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _150_1030 _150_1029)))
in (tc_check_trivial_guard env ed.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (let _150_1041 = (let _150_1040 = (let _150_1039 = (FStar_Syntax_Util.un_uinst repr)
in (let _150_1038 = (let _150_1037 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_1036 = (let _150_1035 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_1035)::[])
in (_150_1037)::_150_1036))
in ((_150_1039), (_150_1038))))
in FStar_Syntax_Syntax.Tm_app (_150_1040))
in (FStar_Syntax_Syntax.mk _150_1041 None FStar_Range.dummyRange)))
in (

let mk_repr = (fun a wp -> (let _150_1046 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_repr' _150_1046 wp)))
in (

let destruct_repr = (fun t -> (match ((let _150_1049 = (FStar_Syntax_Subst.compress t)
in _150_1049.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_58_2590, ((t, _58_2597))::((wp, _58_2593))::[]) -> begin
((t), (wp))
end
| _58_2603 -> begin
(FStar_All.failwith "Unexpected repr type")
end))
in (

let bind_repr = (

let r = (let _150_1050 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_0 FStar_Syntax_Syntax.Delta_constant None)
in (FStar_All.pipe_right _150_1050 FStar_Syntax_Syntax.fv_to_tm))
in (

let _58_2607 = (get_effect_signature ())
in (match (_58_2607) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _150_1054 = (let _150_1052 = (let _150_1051 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _150_1051))
in (_150_1052)::[])
in (let _150_1053 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _150_1054 _150_1053)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" None a_wp_b)
in (

let x_a = (let _150_1055 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _150_1055))
in (

let wp_g_x = (let _150_1059 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (let _150_1058 = (let _150_1057 = (let _150_1056 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_1056))
in (_150_1057)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _150_1059 _150_1058 None FStar_Range.dummyRange)))
in (

let res = (

let wp = (let _150_1071 = (let _150_1060 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right _150_1060 Prims.snd))
in (let _150_1070 = (let _150_1069 = (let _150_1068 = (let _150_1067 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_1066 = (let _150_1065 = (FStar_Syntax_Syntax.bv_to_name b)
in (let _150_1064 = (let _150_1063 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (let _150_1062 = (let _150_1061 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (_150_1061)::[])
in (_150_1063)::_150_1062))
in (_150_1065)::_150_1064))
in (_150_1067)::_150_1066))
in (r)::_150_1068)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _150_1069))
in (FStar_Syntax_Syntax.mk_Tm_app _150_1071 _150_1070 None FStar_Range.dummyRange)))
in (mk_repr b wp))
in (

let expected_k = (let _150_1091 = (let _150_1089 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1088 = (let _150_1087 = (FStar_Syntax_Syntax.mk_binder b)
in (let _150_1086 = (let _150_1085 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (let _150_1084 = (let _150_1083 = (let _150_1073 = (let _150_1072 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a _150_1072))
in (FStar_Syntax_Syntax.null_binder _150_1073))
in (let _150_1082 = (let _150_1081 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (let _150_1080 = (let _150_1079 = (let _150_1078 = (let _150_1077 = (let _150_1074 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_150_1074)::[])
in (let _150_1076 = (let _150_1075 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _150_1075))
in (FStar_Syntax_Util.arrow _150_1077 _150_1076)))
in (FStar_Syntax_Syntax.null_binder _150_1078))
in (_150_1079)::[])
in (_150_1081)::_150_1080))
in (_150_1083)::_150_1082))
in (_150_1085)::_150_1084))
in (_150_1087)::_150_1086))
in (_150_1089)::_150_1088))
in (let _150_1090 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _150_1091 _150_1090)))
in (

let _58_2621 = (tc_tot_or_gtot_term env expected_k)
in (match (_58_2621) with
| (expected_k, _58_2618, _58_2620) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (

let env = (

let _58_2623 = env
in {FStar_TypeChecker_Env.solver = _58_2623.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2623.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2623.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2623.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2623.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2623.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2623.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2623.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2623.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2623.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2623.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2623.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2623.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2623.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_2623.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2623.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2623.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2623.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _58_2623.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2623.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2623.FStar_TypeChecker_Env.use_bv_sorts})
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_repr expected_k)))
end)))))))))
end)))
in (

let return_repr = (

let x_a = (let _150_1092 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _150_1092))
in (

let res = (

let wp = (let _150_1099 = (let _150_1093 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right _150_1093 Prims.snd))
in (let _150_1098 = (let _150_1097 = (let _150_1096 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_1095 = (let _150_1094 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (_150_1094)::[])
in (_150_1096)::_150_1095))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _150_1097))
in (FStar_Syntax_Syntax.mk_Tm_app _150_1099 _150_1098 None FStar_Range.dummyRange)))
in (mk_repr a wp))
in (

let expected_k = (let _150_1104 = (let _150_1102 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1101 = (let _150_1100 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_150_1100)::[])
in (_150_1102)::_150_1101))
in (let _150_1103 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _150_1104 _150_1103)))
in (

let _58_2636 = (tc_tot_or_gtot_term env expected_k)
in (match (_58_2636) with
| (expected_k, _58_2633, _58_2635) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let _58_2640 = (check_and_gen' env ed.FStar_Syntax_Syntax.return_repr expected_k)
in (match (_58_2640) with
| (univs, repr) -> begin
(match (univs) with
| [] -> begin
(([]), (repr))
end
| _58_2643 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected universe-polymorphic return for effect"), (repr.FStar_Syntax_Syntax.pos)))))
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let _58_2651 = (tc_tot_or_gtot_term env act.FStar_Syntax_Syntax.action_typ)
in (match (_58_2651) with
| (act_typ, _58_2649, g_t) -> begin
(

let env' = (FStar_TypeChecker_Env.set_expected_typ env act_typ)
in (

let act_defn = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env act.FStar_Syntax_Syntax.action_defn)
in (

let _58_2654 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _150_1108 = (FStar_Syntax_Print.term_to_string act_defn)
in (let _150_1107 = (FStar_Syntax_Print.term_to_string act_typ)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" (FStar_Ident.text_of_lid act.FStar_Syntax_Syntax.action_name) _150_1108 _150_1107)))
end else begin
()
end
in (

let _58_2659 = (tc_tot_or_gtot_term env' act_defn)
in (match (_58_2659) with
| (act_defn, c, g_a) -> begin
(

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let _58_2681 = (

let act_typ = (FStar_Syntax_Subst.compress act_typ)
in (match (act_typ.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _58_2669 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_2669) with
| (bs, _58_2668) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (let _150_1109 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs _150_1109))
in (

let _58_2676 = (tc_tot_or_gtot_term env k)
in (match (_58_2676) with
| (k, _58_2674, g) -> begin
((k), (g))
end))))
end))
end
| _58_2678 -> begin
(let _150_1114 = (let _150_1113 = (let _150_1112 = (let _150_1111 = (FStar_Syntax_Print.term_to_string act_typ)
in (let _150_1110 = (FStar_Syntax_Print.tag_of_term act_typ)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" _150_1111 _150_1110)))
in ((_150_1112), (act_defn.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_1113))
in (Prims.raise _150_1114))
end))
in (match (_58_2681) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env act_typ expected_k)
in (

let _58_2683 = (let _150_1117 = (let _150_1116 = (let _150_1115 = (FStar_TypeChecker_Rel.conj_guard g_t g)
in (FStar_TypeChecker_Rel.conj_guard g_k _150_1115))
in (FStar_TypeChecker_Rel.conj_guard g_a _150_1116))
in (FStar_TypeChecker_Rel.force_trivial_guard env _150_1117))
in (

let act_typ = (match ((let _150_1118 = (FStar_Syntax_Subst.compress expected_k)
in _150_1118.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _58_2691 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_2691) with
| (bs, c) -> begin
(

let _58_2694 = (destruct_repr (FStar_Syntax_Util.comp_result c))
in (match (_58_2694) with
| (a, wp) -> begin
(

let c = (let _150_1120 = (let _150_1119 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_1119)::[])
in {FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a; FStar_Syntax_Syntax.effect_args = _150_1120; FStar_Syntax_Syntax.flags = []})
in (let _150_1121 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Util.arrow bs _150_1121)))
end))
end))
end
| _58_2697 -> begin
(FStar_All.failwith "")
end)
in (

let _58_2701 = (FStar_TypeChecker_Util.generalize_universes env act_defn)
in (match (_58_2701) with
| (univs, act_defn) -> begin
(

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let _58_2703 = act
in {FStar_Syntax_Syntax.action_name = _58_2703.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = act_defn; FStar_Syntax_Syntax.action_typ = act_typ}))
end)))))
end)))
end)))))
end)))
in (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.map check_action)))
in ((repr), (bind_repr), (return_repr), (actions)))))))))
end else begin
((ed.FStar_Syntax_Syntax.repr), (ed.FStar_Syntax_Syntax.bind_repr), (ed.FStar_Syntax_Syntax.return_repr), (ed.FStar_Syntax_Syntax.actions))
end
in (match (_58_2710) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t = (let _150_1122 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _150_1122))
in (

let _58_2714 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_58_2714) with
| (univs, t) -> begin
(

let _58_2730 = (match ((let _150_1124 = (let _150_1123 = (FStar_Syntax_Subst.compress t)
in _150_1123.FStar_Syntax_Syntax.n)
in ((binders), (_150_1124)))) with
| ([], _58_2717) -> begin
(([]), (t))
end
| (_58_2720, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
((binders), ((FStar_Syntax_Util.comp_result c)))
end
| _58_2727 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_58_2730) with
| (binders, signature) -> begin
(

let close = (fun n ts -> (

let ts = (let _150_1129 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _150_1129))
in (

let _58_2735 = if (((n > 0) && (not ((FStar_Syntax_Util.is_unknown (Prims.snd ts))))) && ((FStar_List.length (Prims.fst ts)) <> n)) then begin
(let _150_1132 = (let _150_1131 = (FStar_Util.string_of_int n)
in (let _150_1130 = (FStar_Syntax_Print.tscheme_to_string ts)
in (FStar_Util.format2 "The effect combinator is not universe-polymorphic enough (n=%s) (%s)" _150_1131 _150_1130)))
in (FStar_All.failwith _150_1132))
end else begin
()
end
in ts)))
in (

let close_action = (fun act -> (

let _58_2741 = (close (- (1)) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (_58_2741) with
| (univs, defn) -> begin
(

let _58_2744 = (close (- (1)) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (_58_2744) with
| (univs', typ) -> begin
(

let _58_2745 = ()
in (

let _58_2747 = act
in {FStar_Syntax_Syntax.action_name = _58_2747.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ}))
end))
end)))
in (

let _58_2749 = ()
in (

let ed = (

let _58_2751 = ed
in (let _150_1149 = (close 0 return_wp)
in (let _150_1148 = (close 1 bind_wp)
in (let _150_1147 = (close 0 if_then_else)
in (let _150_1146 = (close 0 ite_wp)
in (let _150_1145 = (close 0 stronger)
in (let _150_1144 = (close 1 close_wp)
in (let _150_1143 = (close 0 assert_p)
in (let _150_1142 = (close 0 assume_p)
in (let _150_1141 = (close 0 null_wp)
in (let _150_1140 = (close 0 trivial_wp)
in (let _150_1139 = (let _150_1135 = (close 0 (([]), (repr)))
in (Prims.snd _150_1135))
in (let _150_1138 = (close 0 return_repr)
in (let _150_1137 = (close 1 bind_repr)
in (let _150_1136 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.qualifiers = _58_2751.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2751.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _150_1149; FStar_Syntax_Syntax.bind_wp = _150_1148; FStar_Syntax_Syntax.if_then_else = _150_1147; FStar_Syntax_Syntax.ite_wp = _150_1146; FStar_Syntax_Syntax.stronger = _150_1145; FStar_Syntax_Syntax.close_wp = _150_1144; FStar_Syntax_Syntax.assert_p = _150_1143; FStar_Syntax_Syntax.assume_p = _150_1142; FStar_Syntax_Syntax.null_wp = _150_1141; FStar_Syntax_Syntax.trivial = _150_1140; FStar_Syntax_Syntax.repr = _150_1139; FStar_Syntax_Syntax.return_repr = _150_1138; FStar_Syntax_Syntax.bind_repr = _150_1137; FStar_Syntax_Syntax.actions = _150_1136})))))))))))))))
in (

let _58_2754 = if ((FStar_TypeChecker_Env.debug env FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EffDecl")))) then begin
(let _150_1150 = (FStar_Syntax_Print.eff_decl_to_string false ed)
in (FStar_Util.print_string _150_1150))
end else begin
()
end
in ed)))))
end))
end)))
end))))))))))))))))
end)))
end))
end))
end))))
and cps_and_elaborate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl) = (fun env ed -> (

let _58_2760 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_58_2760) with
| (binders_un, signature_un) -> begin
(

let _58_2765 = (tc_tparams env binders_un)
in (match (_58_2765) with
| (binders, env, _58_2764) -> begin
(

let _58_2769 = (tc_trivial_guard env signature_un)
in (match (_58_2769) with
| (signature, _58_2768) -> begin
(

let _58_2782 = (match ((let _150_1153 = (FStar_Syntax_Subst.compress signature_un)
in _150_1153.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (((a, _58_2772))::[], effect_marker) -> begin
((a), (effect_marker))
end
| _58_2779 -> begin
(FStar_All.failwith "bad shape for effect-for-free signature")
end)
in (match (_58_2782) with
| (a, effect_marker) -> begin
(

let open_and_check = (fun t -> (

let subst = (FStar_Syntax_Subst.opening_of_binders binders)
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (

let _58_2791 = (tc_term env t)
in (match (_58_2791) with
| (t, comp, _58_2790) -> begin
((t), (comp))
end)))))
in (

let recheck_debug = (fun s env t -> (

let _58_2796 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _150_1162 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Term has been %s-transformed to:\n%s\n----------\n" s _150_1162))
end else begin
()
end
in (

let _58_2803 = (tc_term env t)
in (match (_58_2803) with
| (t', _58_2800, _58_2802) -> begin
(

let _58_2804 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _150_1163 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print1 "Re-checked; got:\n%s\n----------\n" _150_1163))
end else begin
()
end
in t)
end))))
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None signature.FStar_Syntax_Syntax.pos))
in (

let _58_2810 = (open_and_check ed.FStar_Syntax_Syntax.repr)
in (match (_58_2810) with
| (repr, _comp) -> begin
(

let _58_2811 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _150_1166 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" _150_1166))
end else begin
()
end
in (

let dmff_env = (FStar_TypeChecker_DMFF.empty env (tc_constant FStar_Range.dummyRange))
in (

let _58_2816 = (FStar_TypeChecker_DMFF.star_type_definition dmff_env repr)
in (match (_58_2816) with
| (dmff_env, wp_type) -> begin
(

let wp_type = (recheck_debug "*" env wp_type)
in (

let wp_a = (let _150_1172 = (let _150_1171 = (let _150_1170 = (let _150_1169 = (let _150_1168 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_1167 = (FStar_Syntax_Syntax.as_implicit false)
in ((_150_1168), (_150_1167))))
in (_150_1169)::[])
in ((wp_type), (_150_1170)))
in FStar_Syntax_Syntax.Tm_app (_150_1171))
in (mk _150_1172))
in (

let effect_signature = (

let binders = (let _150_1177 = (let _150_1173 = (FStar_Syntax_Syntax.as_implicit false)
in ((a), (_150_1173)))
in (let _150_1176 = (let _150_1175 = (let _150_1174 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" None wp_a)
in (FStar_All.pipe_right _150_1174 FStar_Syntax_Syntax.mk_binder))
in (_150_1175)::[])
in (_150_1177)::_150_1176))
in (

let binders = (FStar_Syntax_Subst.close_binders binders)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (effect_marker)))))))
in (

let effect_signature = (recheck_debug "turned into the effect signature" env effect_signature)
in (

let sigelts = (FStar_ST.alloc [])
in (

let mk_lid = (fun name -> (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" name))) FStar_Range.dummyRange))
in (

let elaborate_and_star = (fun dmff_env item -> (

let _58_2831 = item
in (match (_58_2831) with
| (u_item, item) -> begin
(

let _58_2834 = (open_and_check item)
in (match (_58_2834) with
| (item, item_comp) -> begin
(

let _58_2835 = if (not ((FStar_Syntax_Util.is_total_lcomp item_comp))) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Computation for [item] is not total!")))
end else begin
()
end
in (

let _58_2842 = (FStar_TypeChecker_DMFF.star_expr_definition dmff_env item)
in (match (_58_2842) with
| (dmff_env, (item_t, item_wp, item_elab)) -> begin
(

let item_wp = (recheck_debug "*" env item_wp)
in (

let item_elab = (recheck_debug "_" env item_elab)
in ((dmff_env), (item_t), (item_wp), (item_elab))))
end)))
end))
end)))
in (

let _58_2850 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.bind_repr)
in (match (_58_2850) with
| (dmff_env, _58_2847, bind_wp, bind_elab) -> begin
(

let _58_2856 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.return_repr)
in (match (_58_2856) with
| (dmff_env, _58_2853, return_wp, return_elab) -> begin
(

let return_wp = (match ((let _150_1184 = (FStar_Syntax_Subst.compress return_wp)
in _150_1184.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(let _150_1185 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) _150_1185 (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_GTot_lid)))))
end
| _58_2867 -> begin
(FStar_All.failwith "unexpected shape for return")
end)
in (

let bind_wp = (match ((let _150_1186 = (FStar_Syntax_Subst.compress bind_wp)
in _150_1186.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (let _150_1189 = (let _150_1188 = (let _150_1187 = (mk (FStar_Syntax_Syntax.Tm_fvar (r)))
in (FStar_Syntax_Syntax.null_binder _150_1187))
in (_150_1188)::binders)
in (FStar_Syntax_Util.abs _150_1189 body what)))
end
| _58_2876 -> begin
(FStar_All.failwith "unexpected shape for bind")
end)
in (

let register = (fun name item -> (

let _58_2883 = (let _150_1194 = (mk_lid name)
in (FStar_TypeChecker_Util.mk_toplevel_definition env _150_1194 item))
in (match (_58_2883) with
| (sigelt, fv) -> begin
(

let _58_2884 = (let _150_1196 = (let _150_1195 = (FStar_ST.read sigelts)
in (sigelt)::_150_1195)
in (FStar_ST.op_Colon_Equals sigelts _150_1196))
in fv)
end)))
in (

let return_wp = (register "return_wp" return_wp)
in (

let return_elab = (register "return_elab" return_elab)
in (

let bind_wp = (register "bind_wp" bind_wp)
in (

let _58_2889 = (let _150_1198 = (let _150_1197 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::_150_1197)
in (FStar_ST.op_Colon_Equals sigelts _150_1198))
in (

let bind_elab = (register "bind_elab" bind_elab)
in (

let _58_2892 = (let _150_1200 = (let _150_1199 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::_150_1199)
in (FStar_ST.op_Colon_Equals sigelts _150_1200))
in (

let _58_2911 = (FStar_List.fold_left (fun _58_2896 action -> (match (_58_2896) with
| (dmff_env, actions) -> begin
(

let _58_2902 = (elaborate_and_star dmff_env ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (_58_2902) with
| (dmff_env, action_t, action_wp, action_elab) -> begin
(

let name = action.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText
in (

let action_elab = (register (Prims.strcat name "_elab") action_elab)
in (

let action_typ_with_wp = (FStar_TypeChecker_DMFF.trans_F dmff_env action_t action_wp)
in (

let action_wp = (register (Prims.strcat name "_wp") action_wp)
in ((dmff_env), (((

let _58_2907 = action
in {FStar_Syntax_Syntax.action_name = _58_2907.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = _58_2907.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = action_elab; FStar_Syntax_Syntax.action_typ = action_typ_with_wp}))::actions))))))
end))
end)) ((dmff_env), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (_58_2911) with
| (dmff_env, actions) -> begin
(

let actions = (FStar_List.rev actions)
in (

let repr = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" None wp_a)
in (

let binders = (let _150_1205 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1204 = (let _150_1203 = (FStar_Syntax_Syntax.mk_binder wp)
in (_150_1203)::[])
in (_150_1205)::_150_1204))
in (let _150_1214 = (let _150_1213 = (let _150_1211 = (let _150_1210 = (let _150_1209 = (let _150_1208 = (let _150_1207 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_1206 = (FStar_Syntax_Syntax.as_implicit false)
in ((_150_1207), (_150_1206))))
in (_150_1208)::[])
in ((ed.FStar_Syntax_Syntax.repr), (_150_1209)))
in FStar_Syntax_Syntax.Tm_app (_150_1210))
in (mk _150_1211))
in (let _150_1212 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env _150_1213 _150_1212)))
in (FStar_Syntax_Util.abs binders _150_1214 None))))
in (

let repr = (recheck_debug "FC" env repr)
in (

let repr = (register "repr (applied to binders)" repr)
in (

let _58_2947 = (

let _58_2918 = (let _150_1215 = (FStar_Syntax_Print.term_to_string wp_type)
in (FStar_Util.print1 "wp_type is: %s\n" _150_1215))
in (match ((let _150_1216 = (FStar_Syntax_Subst.compress wp_type)
in _150_1216.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (effect_param, arrow, _58_2923) -> begin
(

let _58_2926 = (let _150_1217 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.print1 "arrow is: %s\n" _150_1217))
in (

let _58_2930 = (FStar_Syntax_Subst.open_term effect_param arrow)
in (match (_58_2930) with
| (effect_param, arrow) -> begin
(match ((let _150_1218 = (FStar_Syntax_Subst.compress arrow)
in _150_1218.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let _58_2937 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (_58_2937) with
| (wp_binders, c) -> begin
(

let _58_2940 = (FStar_Util.prefix wp_binders)
in (match (_58_2940) with
| (pre_args, post) -> begin
(let _150_1220 = (FStar_Syntax_Util.arrow pre_args c)
in (let _150_1219 = (FStar_Syntax_Util.abs (FStar_List.append binders effect_param) (Prims.fst post).FStar_Syntax_Syntax.sort None)
in ((_150_1220), (_150_1219))))
end))
end))
end
| _58_2942 -> begin
(let _150_1222 = (let _150_1221 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" _150_1221))
in (FStar_All.failwith _150_1222))
end)
end)))
end
| _58_2944 -> begin
(let _150_1224 = (let _150_1223 = (FStar_Syntax_Print.term_to_string wp_type)
in (FStar_Util.format1 "Impossible: pre/post abs %s" _150_1223))
in (FStar_All.failwith _150_1224))
end))
in (match (_58_2947) with
| (pre, post) -> begin
(

let _58_2948 = (let _150_1225 = (register "pre" pre)
in (Prims.ignore _150_1225))
in (

let _58_2950 = (let _150_1226 = (register "post" post)
in (Prims.ignore _150_1226))
in (

let _58_2952 = (let _150_1228 = (let _150_1227 = (FStar_Syntax_Util.abs binders repr None)
in (register "repr" _150_1227))
in (Prims.ignore _150_1228))
in (

let _58_2954 = (let _150_1230 = (let _150_1229 = (FStar_Syntax_Util.abs binders wp_type None)
in (register "wp" _150_1229))
in (Prims.ignore _150_1230))
in (

let c = (FStar_Syntax_Subst.close binders)
in (

let ed = (

let _58_2957 = ed
in (let _150_1244 = (FStar_Syntax_Subst.close_binders binders)
in (let _150_1243 = (let _150_1232 = (c return_wp)
in (([]), (_150_1232)))
in (let _150_1242 = (let _150_1233 = (c bind_wp)
in (([]), (_150_1233)))
in (let _150_1241 = (c repr)
in (let _150_1240 = (let _150_1234 = (c return_elab)
in (([]), (_150_1234)))
in (let _150_1239 = (let _150_1235 = (c bind_elab)
in (([]), (_150_1235)))
in (let _150_1238 = (FStar_List.map (fun action -> (

let _58_2960 = action
in (let _150_1237 = (c action.FStar_Syntax_Syntax.action_defn)
in {FStar_Syntax_Syntax.action_name = _58_2960.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = _58_2960.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _150_1237; FStar_Syntax_Syntax.action_typ = _58_2960.FStar_Syntax_Syntax.action_typ}))) actions)
in {FStar_Syntax_Syntax.qualifiers = _58_2957.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2957.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _58_2957.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _150_1244; FStar_Syntax_Syntax.signature = effect_signature; FStar_Syntax_Syntax.ret_wp = _150_1243; FStar_Syntax_Syntax.bind_wp = _150_1242; FStar_Syntax_Syntax.if_then_else = _58_2957.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _58_2957.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _58_2957.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _58_2957.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _58_2957.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _58_2957.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _58_2957.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _58_2957.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _150_1241; FStar_Syntax_Syntax.return_repr = _150_1240; FStar_Syntax_Syntax.bind_repr = _150_1239; FStar_Syntax_Syntax.actions = _150_1238}))))))))
in (

let _58_2963 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _150_1245 = (FStar_Syntax_Print.eff_decl_to_string true ed)
in (FStar_Util.print_string _150_1245))
end else begin
()
end
in (

let _58_2967 = (FStar_TypeChecker_DMFF.gen_wps_for_free env binders a wp_a ed)
in (match (_58_2967) with
| (sigelts', ed) -> begin
(let _150_1248 = (let _150_1247 = (let _150_1246 = (FStar_ST.read sigelts)
in (FStar_List.rev _150_1246))
in (FStar_List.append _150_1247 sigelts'))
in ((_150_1248), (ed)))
end)))))))))
end))))))
end)))))))))))
end))
end)))))))))
end))))
end)))))
end))
end))
end))
end)))
and tc_lex_t : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (

let _58_2972 = ()
in (

let _58_2980 = ()
in (match (ses) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _58_3009, _58_3011, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _58_3000, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _58_2989, r2))::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(

let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (

let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (

let tc = FStar_Syntax_Syntax.Sig_inductive_typ (((lex_t), ((u)::[]), ([]), (t), ([]), ((FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[]), ([]), (r)))
in (

let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (

let lex_top_t = (let _150_1256 = (let _150_1255 = (let _150_1254 = (let _150_1253 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _150_1253 FStar_Syntax_Syntax.Delta_constant None))
in ((_150_1254), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_150_1255))
in (FStar_Syntax_Syntax.mk _150_1256 None r1))
in (

let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (

let dc_lextop = FStar_Syntax_Syntax.Sig_datacon (((lex_top), ((utop)::[]), (lex_top_t), (FStar_Syntax_Const.lex_t_lid), (0), ([]), ([]), (r1)))
in (

let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (

let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (

let lex_cons_t = (

let a = (let _150_1257 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _150_1257))
in (

let hd = (let _150_1258 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _150_1258))
in (

let tl = (let _150_1263 = (let _150_1262 = (let _150_1261 = (let _150_1260 = (let _150_1259 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _150_1259 FStar_Syntax_Syntax.Delta_constant None))
in ((_150_1260), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_150_1261))
in (FStar_Syntax_Syntax.mk _150_1262 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _150_1263))
in (

let res = (let _150_1267 = (let _150_1266 = (let _150_1265 = (let _150_1264 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _150_1264 FStar_Syntax_Syntax.Delta_constant None))
in ((_150_1265), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_150_1266))
in (FStar_Syntax_Syntax.mk _150_1267 None r2))
in (let _150_1268 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (Some (FStar_Syntax_Syntax.imp_tag))))::(((hd), (None)))::(((tl), (None)))::[]) _150_1268))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t), (FStar_Syntax_Const.lex_t_lid), (0), ([]), ([]), (r2)))
in (let _150_1270 = (let _150_1269 = (FStar_TypeChecker_Env.get_range env)
in (((tc)::(dc_lextop)::(dc_lexcons)::[]), ([]), (lids), (_150_1269)))
in FStar_Syntax_Syntax.Sig_bundle (_150_1270)))))))))))))))
end
| _58_3035 -> begin
(let _150_1272 = (let _150_1271 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle (((ses), ([]), (lids), (FStar_Range.dummyRange)))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _150_1271))
in (FStar_All.failwith _150_1272))
end))))
and tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _58_3045 = (FStar_Syntax_Util.type_u ())
in (match (_58_3045) with
| (k, _58_3044) -> begin
(

let phi = (let _150_1278 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _150_1278 (norm env)))
in (

let _58_3047 = (FStar_TypeChecker_Util.check_uvars r phi)
in FStar_Syntax_Syntax.Sig_assume (((lid), (phi), (quals), (r)))))
end))))
and tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _150_1288 = (let _150_1287 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _150_1287))
in (FStar_TypeChecker_Errors.diag r _150_1288)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let _58_3070 = ()
in (

let _58_3072 = (warn_positivity tc r)
in (

let _58_3076 = (FStar_Syntax_Subst.open_term tps k)
in (match (_58_3076) with
| (tps, k) -> begin
(

let _58_3081 = (tc_binders env tps)
in (match (_58_3081) with
| (tps, env_tps, guard_params, us) -> begin
(

let _58_3084 = (FStar_Syntax_Util.arrow_formals k)
in (match (_58_3084) with
| (indices, t) -> begin
(

let _58_3089 = (tc_binders env_tps indices)
in (match (_58_3089) with
| (indices, env', guard_indices, us') -> begin
(

let _58_3097 = (

let _58_3094 = (tc_tot_or_gtot_term env' t)
in (match (_58_3094) with
| (t, _58_3092, g) -> begin
(let _150_1295 = (let _150_1294 = (let _150_1293 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params _150_1293))
in (FStar_TypeChecker_Rel.discharge_guard env' _150_1294))
in ((t), (_150_1295)))
end))
in (match (_58_3097) with
| (t, guard) -> begin
(

let k = (let _150_1296 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _150_1296))
in (

let _58_3101 = (FStar_Syntax_Util.type_u ())
in (match (_58_3101) with
| (t_type, u) -> begin
(

let _58_3102 = (let _150_1297 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _150_1297))
in (

let t_tc = (let _150_1298 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _150_1298))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _150_1299 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((_150_1299), (FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps), (k), (mutuals), (data), (quals), (r)))), (u), (guard))))))))
end)))
end))
end))
end))
end))
end))))
end
| _58_3109 -> begin
(FStar_All.failwith "impossible")
end))
in (

let positive_if_pure = (fun _58_3111 l -> ())
in (

let tc_data = (fun env tcs _58_7 -> (match (_58_7) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let _58_3128 = ()
in (

let _58_3163 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _58_3132 -> (match (_58_3132) with
| (se, u_tc) -> begin
if (let _150_1312 = (let _150_1311 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _150_1311))
in (FStar_Ident.lid_equals tc_lid _150_1312)) then begin
(

let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_3134, _58_3136, tps, _58_3139, _58_3141, _58_3143, _58_3145, _58_3147) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _58_3153 -> (match (_58_3153) with
| (x, _58_3152) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
end
| _58_3155 -> begin
(FStar_All.failwith "Impossible")
end)
in Some (((tps), (u_tc))))
end else begin
None
end
end)))
in (match (tps_u_opt) with
| Some (x) -> begin
x
end
| None -> begin
if (FStar_Ident.lid_equals tc_lid FStar_Syntax_Const.exn_lid) then begin
(([]), (FStar_Syntax_Syntax.U_zero))
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected data constructor"), (r)))))
end
end))
in (match (_58_3163) with
| (tps, u_tc) -> begin
(

let _58_3183 = (match ((let _150_1314 = (FStar_Syntax_Subst.compress t)
in _150_1314.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _58_3171 = (FStar_Util.first_N ntps bs)
in (match (_58_3171) with
| (_58_3169, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res)))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _58_3177 -> (match (_58_3177) with
| (x, _58_3176) -> begin
FStar_Syntax_Syntax.DB ((((ntps - (1 + i))), (x)))
end))))
in (let _150_1317 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _150_1317))))
end))
end
| _58_3180 -> begin
(([]), (t))
end)
in (match (_58_3183) with
| (arguments, result) -> begin
(

let _58_3184 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1320 = (FStar_Syntax_Print.lid_to_string c)
in (let _150_1319 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _150_1318 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _150_1320 _150_1319 _150_1318))))
end else begin
()
end
in (

let _58_3189 = (tc_tparams env arguments)
in (match (_58_3189) with
| (arguments, env', us) -> begin
(

let _58_3193 = (tc_trivial_guard env' result)
in (match (_58_3193) with
| (result, _58_3192) -> begin
(

let _58_3197 = (FStar_Syntax_Util.head_and_args result)
in (match (_58_3197) with
| (head, _58_3196) -> begin
(

let _58_3202 = (match ((let _150_1321 = (FStar_Syntax_Subst.compress head)
in _150_1321.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _58_3201 -> begin
(let _150_1326 = (let _150_1325 = (let _150_1324 = (let _150_1323 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _150_1322 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _150_1323 _150_1322)))
in ((_150_1324), (r)))
in FStar_Syntax_Syntax.Error (_150_1325))
in (Prims.raise _150_1326))
end)
in (

let g = (FStar_List.fold_left2 (fun g _58_3208 u_x -> (match (_58_3208) with
| (x, _58_3207) -> begin
(

let _58_3210 = ()
in (let _150_1330 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _150_1330)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _150_1334 = (let _150_1332 = (FStar_All.pipe_right tps (FStar_List.map (fun _58_3216 -> (match (_58_3216) with
| (x, _58_3215) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append _150_1332 arguments))
in (let _150_1333 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _150_1334 _150_1333)))
in ((FStar_Syntax_Syntax.Sig_datacon (((c), ([]), (t), (tc_lid), (ntps), (quals), ([]), (r)))), (g)))))
end))
end))
end)))
end))
end)))
end
| _58_3219 -> begin
(FStar_All.failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let _58_3225 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _58_8 -> (match (_58_8) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_3229, _58_3231, tps, k, _58_3235, _58_3237, _58_3239, _58_3241) -> begin
(let _150_1345 = (let _150_1344 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _150_1344))
in (FStar_Syntax_Syntax.null_binder _150_1345))
end
| _58_3245 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _58_9 -> (match (_58_9) with
| FStar_Syntax_Syntax.Sig_datacon (_58_3249, _58_3251, t, _58_3254, _58_3256, _58_3258, _58_3260, _58_3262) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _58_3266 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let t = (let _150_1347 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _150_1347))
in (

let _58_3269 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1348 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _150_1348))
end else begin
()
end
in (

let _58_3273 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_58_3273) with
| (uvs, t) -> begin
(

let _58_3275 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1352 = (let _150_1350 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _150_1350 (FStar_String.concat ", ")))
in (let _150_1351 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _150_1352 _150_1351)))
end else begin
()
end
in (

let _58_3279 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_58_3279) with
| (uvs, t) -> begin
(

let _58_3283 = (FStar_Syntax_Util.arrow_formals t)
in (match (_58_3283) with
| (args, _58_3282) -> begin
(

let _58_3286 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_58_3286) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _58_3290 se -> (match (_58_3290) with
| (x, _58_3289) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _58_3294, tps, _58_3297, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let _58_3320 = (match ((let _150_1355 = (FStar_Syntax_Subst.compress ty)
in _150_1355.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _58_3311 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_58_3311) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _58_3314 -> begin
(let _150_1356 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) _150_1356 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps), (t)))
end))
end
| _58_3317 -> begin
(([]), (ty))
end)
in (match (_58_3320) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs), (tps), (t), (mutuals), (datas), (quals), (r)))
end)))
end
| _58_3322 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| _58_3326 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _150_1357 -> FStar_Syntax_Syntax.U_name (_150_1357))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _58_10 -> (match (_58_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _58_3331, _58_3333, _58_3335, _58_3337, _58_3339, _58_3341, _58_3343) -> begin
((tc), (uvs_universes))
end
| _58_3347 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _58_3352 d -> (match (_58_3352) with
| (t, _58_3351) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _58_3356, _58_3358, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _150_1361 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _150_1361 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon (((l), (uvs), (ty), (tc), (ntps), (quals), (mutuals), (r))))
end
| _58_3368 -> begin
(FStar_All.failwith "Impossible")
end)
end)) data_types datas)))
end)
in ((tcs), (datas))))
end))
end))
end)))
end))))))))
in (

let _58_3378 = (FStar_All.pipe_right ses (FStar_List.partition (fun _58_11 -> (match (_58_11) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_3372) -> begin
true
end
| _58_3375 -> begin
false
end))))
in (match (_58_3378) with
| (tys, datas) -> begin
(

let _58_3385 = if (FStar_All.pipe_right datas (FStar_Util.for_some (fun _58_12 -> (match (_58_12) with
| FStar_Syntax_Syntax.Sig_datacon (_58_3381) -> begin
false
end
| _58_3384 -> begin
true
end)))) then begin
(let _150_1366 = (let _150_1365 = (let _150_1364 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (_150_1364)))
in FStar_Syntax_Syntax.Error (_150_1365))
in (Prims.raise _150_1366))
end else begin
()
end
in (

let env0 = env
in (

let _58_3404 = (FStar_List.fold_right (fun tc _58_3392 -> (match (_58_3392) with
| (env, all_tcs, g) -> begin
(

let _58_3397 = (tc_tycon env tc)
in (match (_58_3397) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (

let _58_3399 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1369 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _150_1369))
end else begin
()
end
in (let _150_1371 = (let _150_1370 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g _150_1370))
in ((env), ((((tc), (tc_u)))::all_tcs), (_150_1371)))))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_58_3404) with
| (env, tcs, g) -> begin
(

let _58_3414 = (FStar_List.fold_right (fun se _58_3408 -> (match (_58_3408) with
| (datas, g) -> begin
(

let _58_3411 = (tc_data env tcs se)
in (match (_58_3411) with
| (data, g') -> begin
(let _150_1374 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((data)::datas), (_150_1374)))
end))
end)) datas (([]), (g)))
in (match (_58_3414) with
| (datas, g) -> begin
(

let _58_3417 = (let _150_1375 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _150_1375 datas))
in (match (_58_3417) with
| (tcs, datas) -> begin
(

let sig_bndle = (let _150_1377 = (let _150_1376 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_150_1376)))
in FStar_Syntax_Syntax.Sig_bundle (_150_1377))
in (

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (_58_3422, _58_3424, t, _58_3427, _58_3429, _58_3431, _58_3433, _58_3435) -> begin
t
end
| _58_3439 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let dr = FStar_Range.dummyRange
in (

let haseq_ty = (fun usubst us acc ty -> (

let _58_3466 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _58_3448, bs, t, _58_3452, d_lids, _58_3455, _58_3457) -> begin
((lid), (bs), (t), (d_lids))
end
| _58_3461 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_58_3466) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _150_1388 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _150_1388 t))
in (

let _58_3471 = (FStar_Syntax_Subst.open_term bs t)
in (match (_58_3471) with
| (bs, t) -> begin
(

let ibs = (match ((let _150_1389 = (FStar_Syntax_Subst.compress t)
in _150_1389.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _58_3474) -> begin
ibs
end
| _58_3478 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _150_1392 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _150_1391 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_1392 _150_1391)))
in (

let ind = (let _150_1395 = (FStar_List.map (fun _58_3485 -> (match (_58_3485) with
| (bv, aq) -> begin
(let _150_1394 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_150_1394), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _150_1395 None dr))
in (

let ind = (let _150_1398 = (FStar_List.map (fun _58_3489 -> (match (_58_3489) with
| (bv, aq) -> begin
(let _150_1397 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_150_1397), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _150_1398 None dr))
in (

let haseq_ind = (let _150_1400 = (let _150_1399 = (FStar_Syntax_Syntax.as_arg ind)
in (_150_1399)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _150_1400 None dr))
in (

let bs' = (FStar_List.filter (fun b -> (

let _58_3500 = acc
in (match (_58_3500) with
| (_58_3494, en, _58_3497, _58_3499) -> begin
(

let opt = (let _150_1403 = (let _150_1402 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _150_1402))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort _150_1403 false))
in (match (opt) with
| None -> begin
false
end
| Some (_58_3504) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (let _150_1409 = (let _150_1408 = (let _150_1407 = (let _150_1406 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg _150_1406))
in (_150_1407)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _150_1408 None dr))
in (FStar_Syntax_Util.mk_conj t _150_1409))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let _58_3511 = fml
in (let _150_1415 = (let _150_1414 = (let _150_1413 = (let _150_1412 = (let _150_1411 = (let _150_1410 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_150_1410)::[])
in (_150_1411)::[])
in FStar_Syntax_Syntax.Meta_pattern (_150_1412))
in ((fml), (_150_1413)))
in FStar_Syntax_Syntax.Tm_meta (_150_1414))
in {FStar_Syntax_Syntax.n = _150_1415; FStar_Syntax_Syntax.tk = _58_3511.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _58_3511.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_3511.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _150_1421 = (let _150_1420 = (let _150_1419 = (let _150_1418 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _150_1418 None))
in (FStar_Syntax_Syntax.as_arg _150_1419))
in (_150_1420)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _150_1421 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _150_1427 = (let _150_1426 = (let _150_1425 = (let _150_1424 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _150_1424 None))
in (FStar_Syntax_Syntax.as_arg _150_1425))
in (_150_1426)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _150_1427 None dr))) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let _58_3525 = acc
in (match (_58_3525) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_58_3530, _58_3532, _58_3534, t_lid, _58_3537, _58_3539, _58_3541, _58_3543) -> begin
(t_lid = lid)
end
| _58_3547 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let haseq_data = (fun acc data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (match ((let _150_1433 = (FStar_Syntax_Subst.compress dt)
in _150_1433.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _58_3556) -> begin
(

let dbs = (let _150_1434 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _150_1434))
in (

let dbs = (let _150_1435 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _150_1435 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (let _150_1440 = (let _150_1439 = (let _150_1438 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_150_1438)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _150_1439 None dr))
in (FStar_Syntax_Util.mk_conj t _150_1440))) FStar_Syntax_Util.t_true dbs)
in (

let _58_3567 = acc
in (match (_58_3567) with
| (env, cond') -> begin
(let _150_1442 = (FStar_TypeChecker_Env.push_binders env dbs)
in (let _150_1441 = (FStar_Syntax_Util.mk_conj cond' cond)
in ((_150_1442), (_150_1441))))
end))))))
end
| _58_3569 -> begin
acc
end))))
in (

let _58_3572 = (FStar_List.fold_left haseq_data ((env), (FStar_Syntax_Util.t_true)) t_datas)
in (match (_58_3572) with
| (env, cond) -> begin
(

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (let _150_1444 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _150_1443 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env), (_150_1444), (_150_1443)))))
end))))))
end)))))))))))))))
end))))
end)))
in (

let is_noeq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Noeq)) quals)
in if (((not ((FStar_Ident.lid_equals env.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid))) && (not (is_noeq))) && ((FStar_List.length tcs) > 0)) then begin
(

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_3578, us, _58_3581, _58_3583, _58_3585, _58_3587, _58_3589, _58_3591) -> begin
us
end
| _58_3595 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let _58_3599 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_58_3599) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _58_3601 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _58_3603 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let _58_3610 = (FStar_List.fold_left (haseq_ty usubst us) (([]), (env), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (_58_3610) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let _58_3615 = (tc_trivial_guard env phi)
in (match (_58_3615) with
| (phi, _58_3614) -> begin
(

let _58_3616 = if (FStar_TypeChecker_Env.should_verify env) then begin
(let _150_1446 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _150_1446))
end else begin
()
end
in (

let _58_3618 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env0 us)
in (

let ses = (FStar_List.fold_left (fun l _58_3624 -> (match (_58_3624) with
| (lid, fml) -> begin
(

let se = (tc_assume env lid fml [] dr)
in (FStar_List.append l ((se)::[])))
end)) [] axioms)
in (let _150_1451 = (let _150_1450 = (let _150_1449 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_150_1449)))
in FStar_Syntax_Syntax.Sig_bundle (_150_1450))
in (_150_1451)::ses)))))
end)))
end))))))
end)))
end else begin
(sig_bndle)::[]
end)))))
end))
end))
end))))
end)))))))))
and tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let se = (tc_lex_t env ses quals lids)
in (let _150_1454 = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (_150_1454)))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let ses = (tc_inductive env ses quals lids)
in (

let env = (FStar_List.fold_left (fun env' se -> (FStar_TypeChecker_Env.push_sigelt env' se)) env ses)
in ((ses), (env)))))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(

let set_options = (fun t s -> (match ((FStar_Options.set_options t s)) with
| FStar_Getopt.Success -> begin
()
end
| FStar_Getopt.Help -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Failed to process pragma: use \'fstar --help\' to see which options are available"), (r)))))
end
| FStar_Getopt.Error (s) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Failed to process pragma: " s)), (r)))))
end))
in (match (p) with
| FStar_Syntax_Syntax.SetOptions (o) -> begin
(

let _58_3667 = (set_options FStar_Options.Set o)
in (((se)::[]), (env)))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(

let _58_3671 = (let _150_1461 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _150_1461 Prims.ignore))
in (

let _58_3676 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _58_3678 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (((se)::[]), (env)))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_58_3681) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(

let ne = (tc_eff_decl env ne)
in (

let se = FStar_Syntax_Syntax.Sig_new_effect (((ne), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (

let _58_3697 = (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun _58_3692 a -> (match (_58_3692) with
| (env, ses) -> begin
(

let se_let = (FStar_Syntax_Util.action_as_lb a)
in (let _150_1464 = (FStar_TypeChecker_Env.push_sigelt env se_let)
in ((_150_1464), ((se_let)::ses))))
end)) ((env), ((se)::[]))))
in (match (_58_3697) with
| (env, ses) -> begin
(((se)::[]), (env))
end)))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(

let ed_src = (FStar_TypeChecker_Env.get_effect_decl env sub.FStar_Syntax_Syntax.source)
in (

let ed_tgt = (FStar_TypeChecker_Env.get_effect_decl env sub.FStar_Syntax_Syntax.target)
in (

let _58_3706 = (let _150_1465 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _150_1465))
in (match (_58_3706) with
| (a, wp_a_src) -> begin
(

let _58_3709 = (let _150_1466 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _150_1466))
in (match (_58_3709) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _150_1470 = (let _150_1469 = (let _150_1468 = (let _150_1467 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (_150_1467)))
in FStar_Syntax_Syntax.NT (_150_1468))
in (_150_1469)::[])
in (FStar_Syntax_Subst.subst _150_1470 wp_b_tgt))
in (

let expected_k = (let _150_1475 = (let _150_1473 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1472 = (let _150_1471 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_150_1471)::[])
in (_150_1473)::_150_1472))
in (let _150_1474 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _150_1475 _150_1474)))
in (

let lift_wp = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift_wp) expected_k)
in (

let repr_type = (fun eff_name a wp -> (

let no_reify = (fun l -> (let _150_1487 = (let _150_1486 = (let _150_1485 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _150_1484 = (FStar_TypeChecker_Env.get_range env)
in ((_150_1485), (_150_1484))))
in FStar_Syntax_Syntax.Error (_150_1486))
in (Prims.raise _150_1487)))
in (match ((FStar_TypeChecker_Env.effect_decl_opt env eff_name)) with
| None -> begin
(no_reify eff_name)
end
| Some (ed) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((FStar_Syntax_Syntax.U_unknown)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in if (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)))) then begin
(no_reify eff_name)
end else begin
(let _150_1494 = (let _150_1492 = (let _150_1491 = (let _150_1490 = (FStar_Syntax_Syntax.as_arg a)
in (let _150_1489 = (let _150_1488 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_1488)::[])
in (_150_1490)::_150_1489))
in ((repr), (_150_1491)))
in FStar_Syntax_Syntax.Tm_app (_150_1492))
in (let _150_1493 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _150_1494 None _150_1493)))
end)
end)))
in (

let lift = (match (sub.FStar_Syntax_Syntax.lift) with
| None -> begin
None
end
| Some (_58_3725, lift) -> begin
(

let _58_3731 = (let _150_1495 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _150_1495))
in (match (_58_3731) with
| (a, wp_a_src) -> begin
(

let wp_a = (FStar_Syntax_Syntax.new_bv None wp_a_src)
in (

let a_typ = (FStar_Syntax_Syntax.bv_to_name a)
in (

let wp_a_typ = (FStar_Syntax_Syntax.bv_to_name wp_a)
in (

let repr_f = (repr_type sub.FStar_Syntax_Syntax.source a_typ wp_a_typ)
in (

let repr_result = (

let lift_wp_a = (let _150_1502 = (let _150_1500 = (let _150_1499 = (let _150_1498 = (FStar_Syntax_Syntax.as_arg a_typ)
in (let _150_1497 = (let _150_1496 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (_150_1496)::[])
in (_150_1498)::_150_1497))
in (((Prims.snd sub.FStar_Syntax_Syntax.lift_wp)), (_150_1499)))
in FStar_Syntax_Syntax.Tm_app (_150_1500))
in (let _150_1501 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _150_1502 None _150_1501)))
in (repr_type sub.FStar_Syntax_Syntax.target a_typ lift_wp_a))
in (

let expected_k = (let _150_1509 = (let _150_1507 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1506 = (let _150_1505 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (let _150_1504 = (let _150_1503 = (FStar_Syntax_Syntax.null_binder repr_f)
in (_150_1503)::[])
in (_150_1505)::_150_1504))
in (_150_1507)::_150_1506))
in (let _150_1508 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow _150_1509 _150_1508)))
in (

let _58_3744 = (tc_tot_or_gtot_term env expected_k)
in (match (_58_3744) with
| (expected_k, _58_3741, _58_3743) -> begin
(

let lift = (check_and_gen env lift expected_k)
in Some (lift))
end))))))))
end))
end)
in (

let sub = (

let _58_3747 = sub
in {FStar_Syntax_Syntax.source = _58_3747.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _58_3747.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift})
in (

let se = FStar_Syntax_Syntax.Sig_sub_effect (((sub), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env))))))))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(

let _58_3760 = ()
in (

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _58_3766 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_58_3766) with
| (tps, c) -> begin
(

let _58_3770 = (tc_tparams env tps)
in (match (_58_3770) with
| (tps, env, us) -> begin
(

let _58_3774 = (tc_comp env c)
in (match (_58_3774) with
| (c, u, g) -> begin
(

let _58_3775 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let _58_3781 = (let _150_1510 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _150_1510))
in (match (_58_3781) with
| (uvs, t) -> begin
(

let _58_3800 = (match ((let _150_1512 = (let _150_1511 = (FStar_Syntax_Subst.compress t)
in _150_1511.FStar_Syntax_Syntax.n)
in ((tps), (_150_1512)))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_58_3784, c)) -> begin
(([]), (c))
end
| (_58_3790, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
((tps), (c))
end
| _58_3797 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_58_3800) with
| (tps, c) -> begin
(

let se = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (uvs), (tps), (c), (tags), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 se)
in (((se)::[]), (env))))
end))
end)))))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t, quals, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _58_3811 = ()
in (

let _58_3815 = (let _150_1514 = (let _150_1513 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _150_1513))
in (check_and_gen env t _150_1514))
in (match (_58_3815) with
| (uvs, t) -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (uvs), (t), (quals), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env))))
end))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(

let se = (tc_assume env lid phi quals r)
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env))))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (

let _58_3835 = (tc_term env e)
in (match (_58_3835) with
| (e, c, g1) -> begin
(

let _58_3840 = (let _150_1518 = (let _150_1515 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_150_1515))
in (let _150_1517 = (let _150_1516 = (c.FStar_Syntax_Syntax.comp ())
in ((e), (_150_1516)))
in (check_expected_effect env _150_1518 _150_1517)))
in (match (_58_3840) with
| (e, _58_3838, g) -> begin
(

let _58_3841 = (let _150_1519 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _150_1519))
in (

let se = FStar_Syntax_Syntax.Sig_main (((e), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env)))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
if (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q')) then begin
Some (q)
end else begin
(let _150_1531 = (let _150_1530 = (let _150_1529 = (let _150_1528 = (FStar_Syntax_Print.lid_to_string l)
in (let _150_1527 = (FStar_Syntax_Print.quals_to_string q)
in (let _150_1526 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _150_1528 _150_1527 _150_1526))))
in ((_150_1529), (r)))
in FStar_Syntax_Syntax.Error (_150_1530))
in (Prims.raise _150_1531))
end
end))
in (

let _58_3885 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _58_3862 lb -> (match (_58_3862) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _58_3881 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
((gen), (lb), (quals_opt))
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (

let _58_3876 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _58_3875 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _150_1534 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Syntax_Const.effect_ALL_lid), (tval), (lb.FStar_Syntax_Syntax.lbdef)))
in ((false), (_150_1534), (quals_opt)))))
end)
in (match (_58_3881) with
| (gen, lb, quals_opt) -> begin
((gen), ((lb)::lbs), (quals_opt))
end)))
end)) ((true), ([]), (if (quals = []) then begin
None
end else begin
Some (quals)
end))))
in (match (_58_3885) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _58_13 -> (match (_58_13) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _58_3894 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (

let lbs' = (FStar_List.rev lbs')
in (

let e = (let _150_1538 = (let _150_1537 = (let _150_1536 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((((Prims.fst lbs)), (lbs'))), (_150_1536)))
in FStar_Syntax_Syntax.Tm_let (_150_1537))
in (FStar_Syntax_Syntax.mk _150_1538 None r))
in (

let _58_3928 = (match ((tc_maybe_toplevel_term (

let _58_3898 = env
in {FStar_TypeChecker_Env.solver = _58_3898.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_3898.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_3898.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_3898.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_3898.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_3898.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_3898.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_3898.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_3898.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_3898.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_3898.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _58_3898.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _58_3898.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_3898.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_3898.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_3898.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_3898.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_3898.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_3898.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_3898.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _58_3905; FStar_Syntax_Syntax.pos = _58_3903; FStar_Syntax_Syntax.vars = _58_3901}, _58_3912, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_58_3916, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _58_3922 -> begin
quals
end)
in ((FStar_Syntax_Syntax.Sig_let (((lbs), (r), (lids), (quals)))), (lbs)))
end
| _58_3925 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_58_3928) with
| (se, lbs) -> begin
(

let _58_3934 = if (log env) then begin
(let _150_1546 = (let _150_1545 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _150_1542 = (let _150_1541 = (let _150_1540 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _150_1540.FStar_Syntax_Syntax.fv_name)
in _150_1541.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _150_1542))) with
| None -> begin
true
end
| _58_3932 -> begin
false
end)
in if should_log then begin
(let _150_1544 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _150_1543 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _150_1544 _150_1543)))
end else begin
""
end))))
in (FStar_All.pipe_right _150_1545 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _150_1546))
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env))))
end)))))
end))))
end))


let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _58_14 -> (match (_58_14) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _58_3944 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _58_3954 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_58_3956) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _58_3967, _58_3969) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _58_3975 -> (match (_58_3975) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _58_3981, _58_3983, quals, r) -> begin
(

let dec = (let _150_1562 = (let _150_1561 = (let _150_1560 = (let _150_1559 = (let _150_1558 = (FStar_Syntax_Syntax.mk_Total t)
in ((bs), (_150_1558)))
in FStar_Syntax_Syntax.Tm_arrow (_150_1559))
in (FStar_Syntax_Syntax.mk _150_1560 None r))
in ((l), (us), (_150_1561), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_150_1562))
in (((dec)::out), (hidden)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _58_3993, _58_3995, _58_3997, _58_3999, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r)))
in (((dec)::out), ((l)::hidden)))
end
| _58_4005 -> begin
((out), (hidden))
end)
end)) ses (([]), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end
| FStar_Syntax_Syntax.Sig_assume (_58_4007, _58_4009, quals, _58_4012) -> begin
if (is_abstract quals) then begin
(([]), (hidden))
end else begin
(((se)::[]), (hidden))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, us, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) then begin
(((FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r))))::[]), ((l)::hidden))
end else begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _58_15 -> (match (_58_15) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _58_4031 -> begin
false
end)))) then begin
(((se)::[]), (hidden))
end else begin
(([]), (hidden))
end
end
end
| FStar_Syntax_Syntax.Sig_main (_58_4033) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _58_4052, _58_4054, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))) then begin
(([]), (hidden))
end else begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::[]), ((FStar_Ident.range_of_lid lid))))
in (((dec)::[]), ((lid)::hidden)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (is_abstract quals) then begin
(let _150_1569 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _150_1568 = (let _150_1567 = (let _150_1566 = (let _150_1565 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _150_1565.FStar_Syntax_Syntax.fv_name)
in _150_1566.FStar_Syntax_Syntax.v)
in ((_150_1567), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_150_1568)))))
in ((_150_1569), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let process_one_decl = (fun _58_4075 se -> (match (_58_4075) with
| (ses, exports, env, hidden) -> begin
(

let _58_4077 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1578 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _150_1578))
end else begin
()
end
in (

let _58_4081 = (tc_decl env se)
in (match (_58_4081) with
| (ses', env) -> begin
(

let _58_4084 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _150_1583 = (FStar_List.fold_left (fun s se -> (let _150_1582 = (let _150_1581 = (FStar_Syntax_Print.sigelt_to_string se)
in (Prims.strcat _150_1581 "\n"))
in (Prims.strcat s _150_1582))) "" ses')
in (FStar_Util.print1 "Checked: %s\n" _150_1583))
end else begin
()
end
in (

let _58_4087 = (FStar_List.iter (fun se -> (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)) ses')
in (

let _58_4096 = (FStar_List.fold_left (fun _58_4091 se -> (match (_58_4091) with
| (le, lh) -> begin
(

let tup = (for_export hidden se)
in (((FStar_List.rev_append (Prims.fst tup) le)), ((FStar_List.rev_append (Prims.snd tup) lh))))
end)) (([]), ([])) ses')
in (match (_58_4096) with
| (exported, hidden) -> begin
(((FStar_List.rev_append ses' ses)), (((FStar_List.rev_append exported []))::exports), (env), (hidden))
end))))
end)))
end))
in (

let _58_4122 = (FStar_List.fold_left (fun acc se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(

let _58_4110 = acc
in (match (_58_4110) with
| (_58_4104, _58_4106, env, _58_4109) -> begin
(

let _58_4113 = (cps_and_elaborate env ne)
in (match (_58_4113) with
| (ses, ne) -> begin
(

let ses = (FStar_List.append ses ((FStar_Syntax_Syntax.Sig_new_effect (((ne), (r))))::[]))
in (FStar_List.fold_left process_one_decl acc ses))
end))
end))
end
| _58_4116 -> begin
(process_one_decl acc se)
end)) (([]), ([]), (env), ([])) ses)
in (match (_58_4122) with
| (ses, exports, env, _58_4121) -> begin
(let _150_1589 = (FStar_All.pipe_right (FStar_List.rev_append exports []) FStar_List.flatten)
in (((FStar_List.rev_append ses [])), (_150_1589), (env)))
end))))


let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let msg = (Prims.strcat "Internals for " name)
in (

let env = (

let _58_4127 = env
in (let _150_1594 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _58_4127.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_4127.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_4127.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_4127.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_4127.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_4127.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_4127.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_4127.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_4127.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_4127.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_4127.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_4127.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_4127.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_4127.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_4127.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_4127.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _150_1594; FStar_TypeChecker_Env.lax = _58_4127.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_4127.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_4127.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_4127.FStar_TypeChecker_Env.use_bv_sorts}))
in (

let _58_4130 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let _58_4136 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_58_4136) with
| (ses, exports, env) -> begin
(((

let _58_4137 = modul
in {FStar_Syntax_Syntax.name = _58_4137.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _58_4137.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _58_4137.FStar_Syntax_Syntax.is_interface})), (exports), (env))
end))))))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let _58_4145 = (tc_decls env decls)
in (match (_58_4145) with
| (ses, exports, env) -> begin
(

let modul = (

let _58_4146 = modul
in {FStar_Syntax_Syntax.name = _58_4146.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _58_4146.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _58_4146.FStar_Syntax_Syntax.is_interface})
in ((modul), (exports), (env)))
end)))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul = (

let _58_4152 = modul
in {FStar_Syntax_Syntax.name = _58_4152.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _58_4152.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in (

let _58_4162 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(

let _58_4156 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let _58_4158 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (

let _58_4160 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _150_1607 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _150_1607 Prims.ignore)))))
end else begin
()
end
in ((modul), (env))))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let _58_4169 = (tc_partial_modul env modul)
in (match (_58_4169) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _58_4172 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _150_1616 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _150_1616))
end else begin
()
end
in (

let env = (

let _58_4174 = env
in {FStar_TypeChecker_Env.solver = _58_4174.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_4174.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_4174.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_4174.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_4174.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_4174.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_4174.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_4174.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_4174.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_4174.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_4174.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_4174.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_4174.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_4174.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_4174.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_4174.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_4174.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_4174.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_4174.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_4174.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_4174.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _58_4190 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _58_4182) -> begin
(let _150_1621 = (let _150_1620 = (let _150_1619 = (FStar_TypeChecker_Env.get_range env)
in (((Prims.strcat "Implicit argument: " msg)), (_150_1619)))
in FStar_Syntax_Syntax.Error (_150_1620))
in (Prims.raise _150_1621))
end
in (match (_58_4190) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end else begin
(let _150_1626 = (let _150_1625 = (let _150_1624 = (let _150_1622 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _150_1622))
in (let _150_1623 = (FStar_TypeChecker_Env.get_range env)
in ((_150_1624), (_150_1623))))
in FStar_Syntax_Syntax.Error (_150_1625))
in (Prims.raise _150_1626))
end
end)))))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
FStar_Syntax_Syntax.U_zero
end else begin
(

let _58_4193 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_1631 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print1 "universe_of %s\n" _150_1631))
end else begin
()
end
in (

let _58_4198 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_4198) with
| (env, _58_4197) -> begin
(

let env = (

let _58_4199 = env
in {FStar_TypeChecker_Env.solver = _58_4199.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_4199.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_4199.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_4199.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_4199.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_4199.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_4199.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_4199.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_4199.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_4199.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_4199.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_4199.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_4199.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_4199.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_4199.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_4199.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_4199.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _58_4199.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_4199.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true})
in (

let fail = (fun e t -> (let _150_1641 = (let _150_1640 = (let _150_1639 = (let _150_1637 = (FStar_Syntax_Print.term_to_string e)
in (let _150_1636 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" _150_1637 _150_1636)))
in (let _150_1638 = (FStar_TypeChecker_Env.get_range env)
in ((_150_1639), (_150_1638))))
in FStar_Syntax_Syntax.Error (_150_1640))
in (Prims.raise _150_1641)))
in (

let ok = (fun u -> (

let _58_4207 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_1645 = (FStar_Syntax_Print.tag_of_term e)
in (let _150_1644 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.print2 "<end> universe_of %s is %s\n" _150_1645 _150_1644)))
end else begin
()
end
in u))
in (

let universe_of_type = (fun e t -> (match ((let _150_1650 = (FStar_Syntax_Util.unrefine t)
in _150_1650.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(ok u)
end
| _58_4215 -> begin
(fail e t)
end))
in (

let _58_4218 = (FStar_Syntax_Util.head_and_args e)
in (match (_58_4218) with
| (head, args) -> begin
(match ((let _150_1651 = (FStar_Syntax_Subst.compress head)
in _150_1651.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_58_4220, t) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _150_1652 = (FStar_Syntax_Subst.compress t)
in _150_1652.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_4226, t) -> begin
(universe_of_type e (FStar_Syntax_Util.comp_result t))
end
| _58_4231 -> begin
(universe_of_type e t)
end))
end
| _58_4233 -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoInline)::[]) env e)
in (

let _58_4246 = (tc_term env e)
in (match (_58_4246) with
| (_58_4236, {FStar_Syntax_Syntax.eff_name = _58_4243; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_4240; FStar_Syntax_Syntax.comp = _58_4238}, g) -> begin
(

let _58_4247 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (let _150_1654 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (FStar_All.pipe_left (universe_of_type e) _150_1654)))
end)))
end)
end))))))
end)))
end)


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

let _58_4251 = if (FStar_Options.debug_any ()) then begin
(let _150_1659 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _150_1659))
end else begin
()
end
in (

let _58_4255 = (tc_modul env m)
in (match (_58_4255) with
| (m, env) -> begin
(

let _58_4256 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _150_1660 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _150_1660))
end else begin
()
end
in ((m), (env)))
end))))




