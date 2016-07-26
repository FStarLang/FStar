
open Prims

type effect_cost =
| ForFree
| NotForFree


let is_ForFree = (fun _discr_ -> (match (_discr_) with
| ForFree (_) -> begin
true
end
| _ -> begin
false
end))


let is_NotForFree = (fun _discr_ -> (match (_discr_) with
| NotForFree (_) -> begin
true
end
| _ -> begin
false
end))


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (not ((let _150_5 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _150_5))))))


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
in (let _150_19 = (let _150_18 = (FStar_Syntax_Syntax.as_arg v)
in (let _150_17 = (let _150_16 = (FStar_Syntax_Syntax.as_arg tl)
in (_150_16)::[])
in (_150_18)::_150_17))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _150_19 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _58_1 -> (match (_58_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _58_32 -> begin
false
end))


let steps : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Normalize.step Prims.list = (fun env -> if (FStar_TypeChecker_Env.should_verify env) then begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::[]
end else begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]
end)


let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Beta)::[]) env t))


let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _150_32 = (steps env)
in (FStar_TypeChecker_Normalize.normalize _150_32 env t)))


let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _150_37 = (steps env)
in (FStar_TypeChecker_Normalize.normalize_comp _150_37 env c)))


let check_no_escape : FStar_Syntax_Syntax.term Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun head_opt env fvs kt -> (

let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
()
end
| _58_49 -> begin
(

let fvs' = (let _150_50 = if try_norm then begin
(norm env t)
end else begin
t
end
in (FStar_Syntax_Free.names _150_50))
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
(let _150_54 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _150_54))
end
| Some (head) -> begin
(let _150_56 = (FStar_Syntax_Print.bv_to_string x)
in (let _150_55 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _150_56 _150_55)))
end)
in (let _150_59 = (let _150_58 = (let _150_57 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (_150_57)))
in FStar_Syntax_Syntax.Error (_150_58))
in (Prims.raise _150_59)))
end))
in (

let s = (let _150_61 = (let _150_60 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _150_60))
in (FStar_TypeChecker_Util.new_uvar env _150_61))
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
(let _150_76 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _150_76 t))
end))}))


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let should_return = (fun t -> (match ((let _150_87 = (FStar_Syntax_Subst.compress t)
in _150_87.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_91, c) -> begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(

let t = (FStar_All.pipe_left FStar_Syntax_Util.unrefine (FStar_Syntax_Util.comp_result c))
in (match ((let _150_88 = (FStar_Syntax_Subst.compress t)
in _150_88.FStar_Syntax_Syntax.n)) with
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
(let _150_89 = if ((not ((should_return t))) || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _150_89))
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
(let _150_91 = (FStar_Syntax_Print.term_to_string t)
in (let _150_90 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _150_91 _150_90)))
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
(let _150_93 = (FStar_Syntax_Print.term_to_string t)
in (let _150_92 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _150_93 _150_92)))
end else begin
()
end
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let _58_128 = (let _150_99 = (FStar_All.pipe_left (fun _150_98 -> Some (_150_98)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _150_99 env e lc g))
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
(let _150_100 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _150_100))
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
(let _150_113 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (_150_113))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
if (FStar_Syntax_Util.is_pure_comp c) then begin
(let _150_114 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (_150_114))
end else begin
if (FStar_Syntax_Util.is_pure_or_ghost_comp c) then begin
(let _150_115 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (_150_115))
end else begin
None
end
end
end
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _150_116 = (norm_c env c)
in ((e), (_150_116), (FStar_TypeChecker_Rel.trivial_guard)))
end
| Some (expected_c) -> begin
(

let _58_157 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_119 = (FStar_Syntax_Print.term_to_string e)
in (let _150_118 = (FStar_Syntax_Print.comp_to_string c)
in (let _150_117 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _150_119 _150_118 _150_117))))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _58_160 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_122 = (FStar_Syntax_Print.term_to_string e)
in (let _150_121 = (FStar_Syntax_Print.comp_to_string c)
in (let _150_120 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _150_122 _150_121 _150_120))))
end else begin
()
end
in (

let _58_166 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_58_166) with
| (e, _58_164, g) -> begin
(

let g = (let _150_123 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _150_123 "could not prove post-condition" g))
in (

let _58_168 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_125 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _150_124 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _150_125 _150_124)))
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
(let _150_131 = (let _150_130 = (let _150_129 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _150_128 = (FStar_TypeChecker_Env.get_range env)
in ((_150_129), (_150_128))))
in FStar_Syntax_Syntax.Error (_150_130))
in (Prims.raise _150_131))
end)
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _150_134 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _150_134))
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
(let _150_141 = (let _150_140 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _150_140))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _150_141))
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

let t = (let _150_155 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _150_155))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _58_242 -> begin
(let _150_156 = (FStar_Syntax_Syntax.bv_to_name b)
in (_150_156)::[])
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
(match ((let _150_162 = (FStar_Syntax_Subst.compress t)
in _150_162.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _58_281 -> (match (_58_281) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _150_166 = (let _150_165 = (let _150_164 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_150_164))
in (FStar_Syntax_Syntax.new_bv _150_165 x.FStar_Syntax_Syntax.sort))
in ((_150_166), (imp)))
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

let precedes = (let _150_170 = (let _150_169 = (FStar_Syntax_Syntax.as_arg dec)
in (let _150_168 = (let _150_167 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_150_167)::[])
in (_150_169)::_150_168))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _150_170 None r))
in (

let _58_292 = (FStar_Util.prefix formals)
in (match (_58_292) with
| (bs, (last, imp)) -> begin
(

let last = (

let _58_293 = last
in (let _150_171 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _58_293.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_293.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_171}))
in (

let refined_formals = (FStar_List.append bs ((((last), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (

let _58_298 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_174 = (FStar_Syntax_Print.lbname_to_string l)
in (let _150_173 = (FStar_Syntax_Print.term_to_string t)
in (let _150_172 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _150_174 _150_173 _150_172))))
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
(let _150_244 = (let _150_242 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _150_242))
in (let _150_243 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _150_244 _150_243)))
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
in (let _150_249 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_pattern (pats))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _150_248 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((_150_249), (c), (_150_248)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _150_250 = (FStar_Syntax_Subst.compress e)
in _150_250.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_58_386, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _58_393; FStar_Syntax_Syntax.lbtyp = _58_391; FStar_Syntax_Syntax.lbeff = _58_389; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _58_404 = (let _150_251 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _150_251 e1))
in (match (_58_404) with
| (e1, c1, g1) -> begin
(

let _58_408 = (tc_term env e2)
in (match (_58_408) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((None), (c2)))
in (

let e = (let _150_256 = (let _150_255 = (let _150_254 = (let _150_253 = (let _150_252 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_TypeChecker_Common.t_unit), (e1)))
in (_150_252)::[])
in ((false), (_150_253)))
in ((_150_254), (e2)))
in FStar_Syntax_Syntax.Tm_let (_150_255))
in (FStar_Syntax_Syntax.mk _150_256 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _150_257 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e), (c), (_150_257))))))
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
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let _58_426 = (tc_term env e)
in (match (_58_426) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (m)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _58_432) -> begin
(

let _58_438 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_438) with
| (env0, _58_437) -> begin
(

let _58_443 = (tc_comp env0 expected_c)
in (match (_58_443) with
| (expected_c, _58_441, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (

let _58_448 = (let _150_258 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term _150_258 e))
in (match (_58_448) with
| (e, c', g') -> begin
(

let _58_452 = (let _150_260 = (let _150_259 = (c'.FStar_Syntax_Syntax.comp ())
in ((e), (_150_259)))
in (check_expected_effect env0 (Some (expected_c)) _150_260))
in (match (_58_452) with
| (e, expected_c, g'') -> begin
(let _150_263 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t_res)), (Some ((FStar_Syntax_Util.comp_effect_name expected_c)))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _150_262 = (let _150_261 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _150_261))
in ((_150_263), ((FStar_Syntax_Util.lcomp_of_comp expected_c)), (_150_262))))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _58_457) -> begin
(

let _58_462 = (FStar_Syntax_Util.type_u ())
in (match (_58_462) with
| (k, u) -> begin
(

let _58_467 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_467) with
| (t, _58_465, f) -> begin
(

let _58_471 = (let _150_264 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _150_264 e))
in (match (_58_471) with
| (e, c, g) -> begin
(

let _58_475 = (let _150_268 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_472 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _150_268 e c f))
in (match (_58_475) with
| (c, f) -> begin
(

let _58_479 = (let _150_269 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t)), (Some (c.FStar_Syntax_Syntax.eff_name))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _150_269 c))
in (match (_58_479) with
| (e, c, f2) -> begin
(let _150_271 = (let _150_270 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _150_270))
in ((e), (c), (_150_271)))
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

let _58_515 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_515) with
| (unary_op, _58_514) -> begin
(

let head = (let _150_272 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (Prims.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) None _150_272))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), (rest)))) None top.FStar_Syntax_Syntax.pos)
in (tc_term env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _58_523; FStar_Syntax_Syntax.pos = _58_521; FStar_Syntax_Syntax.vars = _58_519}, ((e, aqual))::[]) -> begin
(

let _58_533 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end else begin
()
end
in (

let _58_542 = (

let _58_538 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_538) with
| (env0, _58_537) -> begin
(tc_term env0 e)
end))
in (match (_58_542) with
| (e, c, g) -> begin
(

let _58_546 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_546) with
| (reify_op, _58_545) -> begin
(

let u_c = (

let _58_552 = (tc_term env c.FStar_Syntax_Syntax.res_typ)
in (match (_58_552) with
| (_58_548, c, _58_551) -> begin
(match ((let _150_273 = (FStar_Syntax_Subst.compress c.FStar_Syntax_Syntax.res_typ)
in _150_273.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| _58_556 -> begin
(FStar_All.failwith "Unexpected result type of computation")
end)
end))
in (

let repr = (FStar_TypeChecker_Util.reify_comp env c u_c)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e), (aqual)))::[])))) (Some (repr.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let c = (let _150_274 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right _150_274 FStar_Syntax_Util.lcomp_of_comp))
in (

let _58_564 = (comp_check_expected_typ env e c)
in (match (_58_564) with
| (e, c, g') -> begin
(let _150_275 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), (c), (_150_275)))
end))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.tk = _58_570; FStar_Syntax_Syntax.pos = _58_568; FStar_Syntax_Syntax.vars = _58_566}, ((e, aqual))::[]) -> begin
(

let _58_581 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end else begin
()
end
in (

let no_reflect = (fun _58_584 -> (match (()) with
| () -> begin
(let _150_280 = (let _150_279 = (let _150_278 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((_150_278), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_279))
in (Prims.raise _150_280))
end))
in (

let _58_588 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_588) with
| (reflect_op, _58_587) -> begin
(match ((FStar_TypeChecker_Env.effect_decl_opt env l)) with
| None -> begin
(no_reflect ())
end
| Some (ed) -> begin
if (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable)))) then begin
(no_reflect ())
end else begin
(

let _58_594 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_594) with
| (env_no_ex, topt) -> begin
(

let _58_622 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (let _150_286 = (let _150_285 = (let _150_284 = (let _150_283 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _150_282 = (let _150_281 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (_150_281)::[])
in (_150_283)::_150_282))
in ((repr), (_150_284)))
in FStar_Syntax_Syntax.Tm_app (_150_285))
in (FStar_Syntax_Syntax.mk _150_286 None top.FStar_Syntax_Syntax.pos))
in (

let _58_602 = (let _150_288 = (let _150_287 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _150_287 Prims.fst))
in (tc_tot_or_gtot_term _150_288 t))
in (match (_58_602) with
| (t, _58_600, g) -> begin
(match ((let _150_289 = (FStar_Syntax_Subst.compress t)
in _150_289.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_58_604, ((res, _58_611))::((wp, _58_607))::[]) -> begin
((t), (res), (wp), (g))
end
| _58_617 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))
in (match (_58_622) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let _58_636 = (

let _58_626 = (tc_tot_or_gtot_term env_no_ex e)
in (match (_58_626) with
| (e, c, g) -> begin
(

let _58_627 = if (let _150_290 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation _150_290)) then begin
(FStar_TypeChecker_Errors.add_errors env (((("Expected Tot, got a GTot computation"), (e.FStar_Syntax_Syntax.pos)))::[]))
end else begin
()
end
in (match ((FStar_TypeChecker_Rel.try_teq env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)) with
| None -> begin
(

let _58_630 = (let _150_295 = (let _150_294 = (let _150_293 = (let _150_292 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _150_291 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" _150_292 _150_291)))
in ((_150_293), (e.FStar_Syntax_Syntax.pos)))
in (_150_294)::[])
in (FStar_TypeChecker_Errors.add_errors env _150_295))
in (let _150_296 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e), (_150_296))))
end
| Some (g') -> begin
(let _150_298 = (let _150_297 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' _150_297))
in ((e), (_150_298)))
end))
end))
in (match (_58_636) with
| (e, g) -> begin
(

let c = (let _150_302 = (let _150_301 = (let _150_300 = (let _150_299 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_299)::[])
in {FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = _150_300; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp _150_301))
in (FStar_All.pipe_right _150_302 FStar_Syntax_Util.lcomp_of_comp))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e), (aqual)))::[])))) (Some (res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let _58_642 = (comp_check_expected_typ env e c)
in (match (_58_642) with
| (e, c, g') -> begin
(let _150_303 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e), (c), (_150_303)))
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

let env = (let _150_305 = (let _150_304 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _150_304 Prims.fst))
in (FStar_All.pipe_right _150_305 instantiate_both))
in (

let _58_649 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_307 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _150_306 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _150_307 _150_306)))
end else begin
()
end
in (

let _58_654 = (tc_term (no_inst env) head)
in (match (_58_654) with
| (head, chead, g_head) -> begin
(

let _58_658 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _150_308 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _150_308))
end else begin
(let _150_309 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _150_309))
end
in (match (_58_658) with
| (e, c, g) -> begin
(

let _58_659 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_310 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _150_310))
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

let _58_665 = (comp_check_expected_typ env0 e c)
in (match (_58_665) with
| (e, c, g') -> begin
(

let gimp = (match ((let _150_311 = (FStar_Syntax_Subst.compress head)
in _150_311.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _58_668) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e), (c.FStar_Syntax_Syntax.res_typ), (head.FStar_Syntax_Syntax.pos))
in (

let _58_672 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_672.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_672.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_672.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _58_675 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (

let gres = (let _150_312 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _150_312))
in (

let _58_678 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_314 = (FStar_Syntax_Print.term_to_string e)
in (let _150_313 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" _150_314 _150_313)))
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

let _58_686 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_686) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let _58_691 = (tc_term env1 e1)
in (match (_58_691) with
| (e1, c1, g1) -> begin
(

let _58_702 = (match (topt) with
| Some (t) -> begin
((env), (t))
end
| None -> begin
(

let _58_698 = (FStar_Syntax_Util.type_u ())
in (match (_58_698) with
| (k, _58_697) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _150_315 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in ((_150_315), (res_t))))
end))
end)
in (match (_58_702) with
| (env_branches, res_t) -> begin
(

let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let _58_719 = (

let _58_716 = (FStar_List.fold_right (fun _58_710 _58_713 -> (match (((_58_710), (_58_713))) with
| ((_58_706, f, c, g), (caccum, gaccum)) -> begin
(let _150_318 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (_150_318)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_58_716) with
| (cases, g) -> begin
(let _150_319 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in ((_150_319), (g)))
end))
in (match (_58_719) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (guard_x)), (c_branches)))
in (

let e = (

let mk_match = (fun scrutinee -> (

let branches = (FStar_List.map (fun _58_730 -> (match (_58_730) with
| (f, _58_725, _58_727, _58_729) -> begin
f
end)) t_eqns)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (Some (cres.FStar_Syntax_Syntax.eff_name))))) None e.FStar_Syntax_Syntax.pos))))
in if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c1.FStar_Syntax_Syntax.eff_name) then begin
(mk_match e1)
end else begin
(

let e_match = (let _150_323 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match _150_323))
in (

let lb = (let _150_324 = (FStar_TypeChecker_Env.norm_eff_name env c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = _150_324; FStar_Syntax_Syntax.lbdef = e1})
in (let _150_329 = (let _150_328 = (let _150_327 = (let _150_326 = (let _150_325 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (_150_325)::[])
in (FStar_Syntax_Subst.close _150_326 e_match))
in ((((false), ((lb)::[]))), (_150_327)))
in FStar_Syntax_Syntax.Tm_let (_150_328))
in (FStar_Syntax_Syntax.mk _150_329 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))))
end)
in (

let _58_736 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_332 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _150_331 = (let _150_330 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _150_330))
in (FStar_Util.print2 "(%s) comp type = %s\n" _150_332 _150_331)))
end else begin
()
end
in (let _150_333 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e), (cres), (_150_333))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_748); FStar_Syntax_Syntax.lbunivs = _58_746; FStar_Syntax_Syntax.lbtyp = _58_744; FStar_Syntax_Syntax.lbeff = _58_742; FStar_Syntax_Syntax.lbdef = _58_740})::[]), _58_754) -> begin
(

let _58_757 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_334 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _150_334))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _58_761), _58_764) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_779); FStar_Syntax_Syntax.lbunivs = _58_777; FStar_Syntax_Syntax.lbtyp = _58_775; FStar_Syntax_Syntax.lbeff = _58_773; FStar_Syntax_Syntax.lbdef = _58_771})::_58_769), _58_785) -> begin
(

let _58_788 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_335 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _150_335))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _58_792), _58_795) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let _58_809 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_809) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _150_349 = (let _150_348 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_348))
in FStar_Util.Inr (_150_349))
end
in (

let is_data_ctor = (fun _58_4 -> (match (_58_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _58_819 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _150_355 = (let _150_354 = (let _150_353 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _150_352 = (FStar_TypeChecker_Env.get_range env)
in ((_150_353), (_150_352))))
in FStar_Syntax_Syntax.Error (_150_354))
in (Prims.raise _150_355))
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

let g = (match ((let _150_356 = (FStar_Syntax_Subst.compress t1)
in _150_356.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_830) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _58_833 -> begin
(

let imp = (("uvar in term"), (env), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let _58_835 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_835.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_835.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_835.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _58_850 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(

let _58_843 = (FStar_Syntax_Util.type_u ())
in (match (_58_843) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
end))
end
| Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end)
in (match (_58_850) with
| (t, _58_848, g0) -> begin
(

let _58_855 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (_58_855) with
| (e, _58_853, g1) -> begin
(let _150_359 = (let _150_357 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right _150_357 FStar_Syntax_Util.lcomp_of_comp))
in (let _150_358 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e), (_150_359), (_150_358))))
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

let _58_859 = x
in {FStar_Syntax_Syntax.ppname = _58_859.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_859.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let _58_865 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_865) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _150_361 = (let _150_360 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_360))
in FStar_Util.Inr (_150_361))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _58_872; FStar_Syntax_Syntax.pos = _58_870; FStar_Syntax_Syntax.vars = _58_868}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let _58_882 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_882) with
| (us', t) -> begin
(

let _58_889 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _150_364 = (let _150_363 = (let _150_362 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (_150_362)))
in FStar_Syntax_Syntax.Error (_150_363))
in (Prims.raise _150_364))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _58_888 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (

let fv' = (

let _58_891 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _58_893 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_893.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_893.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_891.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_891.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _150_367 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_367 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let _58_901 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_901) with
| (us, t) -> begin
(

let fv' = (

let _58_902 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _58_904 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_904.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_904.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_902.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_902.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _150_368 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_368 us))
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

let _58_918 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_918) with
| (bs, c) -> begin
(

let env0 = env
in (

let _58_923 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_923) with
| (env, _58_922) -> begin
(

let _58_928 = (tc_binders env bs)
in (match (_58_928) with
| (bs, env, g, us) -> begin
(

let _58_932 = (tc_comp env c)
in (match (_58_932) with
| (c, uc, f) -> begin
(

let e = (

let _58_933 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _58_933.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_933.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_933.FStar_Syntax_Syntax.vars})
in (

let _58_936 = (check_smt_pat env e bs c)
in (

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _150_369 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _150_369))
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

let _58_952 = (let _150_371 = (let _150_370 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_370)::[])
in (FStar_Syntax_Subst.open_term _150_371 phi))
in (match (_58_952) with
| (x, phi) -> begin
(

let env0 = env
in (

let _58_957 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_957) with
| (env, _58_956) -> begin
(

let _58_962 = (let _150_372 = (FStar_List.hd x)
in (tc_binder env _150_372))
in (match (_58_962) with
| (x, env, f1, u) -> begin
(

let _58_963 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_375 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _150_374 = (FStar_Syntax_Print.term_to_string phi)
in (let _150_373 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _150_375 _150_374 _150_373))))
end else begin
()
end
in (

let _58_968 = (FStar_Syntax_Util.type_u ())
in (match (_58_968) with
| (t_phi, _58_967) -> begin
(

let _58_973 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_58_973) with
| (phi, _58_971, f2) -> begin
(

let e = (

let _58_974 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _58_974.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_974.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_974.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _150_376 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _150_376))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _58_982) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (

let _58_988 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_377 = (FStar_Syntax_Print.term_to_string (

let _58_986 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))); FStar_Syntax_Syntax.tk = _58_986.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _58_986.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_986.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _150_377))
end else begin
()
end
in (

let _58_992 = (FStar_Syntax_Subst.open_term bs body)
in (match (_58_992) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _58_994 -> begin
(let _150_380 = (let _150_379 = (FStar_Syntax_Print.term_to_string top)
in (let _150_378 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" _150_379 _150_378)))
in (FStar_All.failwith _150_380))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_58_999) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_58_1002, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_58_1007, Some (_58_1009)) -> begin
(FStar_All.failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (_58_1014) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_58_1017) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_58_1020) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_58_1024) -> begin
FStar_TypeChecker_Common.t_range
end
| _58_1027 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(

let _58_1035 = (FStar_Syntax_Util.type_u ())
in (match (_58_1035) with
| (k, u) -> begin
(

let _58_1040 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_1040) with
| (t, _58_1038, g) -> begin
(let _150_385 = (FStar_Syntax_Syntax.mk_Total t)
in ((_150_385), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(

let _58_1045 = (FStar_Syntax_Util.type_u ())
in (match (_58_1045) with
| (k, u) -> begin
(

let _58_1050 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_1050) with
| (t, _58_1048, g) -> begin
(let _150_386 = (FStar_Syntax_Syntax.mk_GTotal t)
in ((_150_386), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (

let tc = (let _150_388 = (let _150_387 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_150_387)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _150_388 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let _58_1059 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_58_1059) with
| (tc, _58_1057, f) -> begin
(

let _58_1063 = (FStar_Syntax_Util.head_and_args tc)
in (match (_58_1063) with
| (_58_1061, args) -> begin
(

let _58_1066 = (let _150_390 = (FStar_List.hd args)
in (let _150_389 = (FStar_List.tl args)
in ((_150_390), (_150_389))))
in (match (_58_1066) with
| (res, args) -> begin
(

let _58_1082 = (let _150_392 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _58_5 -> (match (_58_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _58_1073 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1073) with
| (env, _58_1072) -> begin
(

let _58_1078 = (tc_tot_or_gtot_term env e)
in (match (_58_1078) with
| (e, _58_1076, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e)), (g))
end))
end))
end
| f -> begin
((f), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right _150_392 FStar_List.unzip))
in (match (_58_1082) with
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
| _58_1093 -> begin
(FStar_All.failwith "Impossible:Unexpected sort for computation")
end)))
end
| _58_1095 -> begin
(FStar_All.failwith "Impossible:Unexpected sort for computation")
end)
in (let _150_394 = (FStar_Syntax_Syntax.mk_Comp (

let _58_1097 = c
in {FStar_Syntax_Syntax.effect_name = _58_1097.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _58_1097.FStar_Syntax_Syntax.flags}))
in (let _150_393 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((_150_394), (u), (_150_393)))))
end))
end))
end))
end))))
end)))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_58_1105) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _150_399 = (aux u)
in FStar_Syntax_Syntax.U_succ (_150_399))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _150_400 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_150_400))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _150_404 = (let _150_403 = (let _150_402 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _150_401 = (FStar_TypeChecker_Env.get_range env)
in ((_150_402), (_150_401))))
in FStar_Syntax_Syntax.Error (_150_403))
in (Prims.raise _150_404))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _150_405 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_405 Prims.snd))
end
| _58_1120 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _150_414 = (let _150_413 = (let _150_412 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in ((_150_412), (top.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_413))
in (Prims.raise _150_414)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun _58_1138 bs bs_expected -> (match (_58_1138) with
| (env, out, g, subst) -> begin
(match (((bs), (bs_expected))) with
| ([], []) -> begin
((env), ((FStar_List.rev out)), (None), (g), (subst))
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
(

let _58_1169 = (match (((imp), (imp'))) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _150_431 = (let _150_430 = (let _150_429 = (let _150_427 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _150_427))
in (let _150_428 = (FStar_Syntax_Syntax.range_of_bv hd)
in ((_150_429), (_150_428))))
in FStar_Syntax_Syntax.Error (_150_430))
in (Prims.raise _150_431))
end
| _58_1168 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _58_1186 = (match ((let _150_432 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _150_432.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| _58_1174 -> begin
(

let _58_1175 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_433 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _150_433))
end else begin
()
end
in (

let _58_1181 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_58_1181) with
| (t, _58_1179, g1) -> begin
(

let g2 = (let _150_435 = (FStar_TypeChecker_Env.get_range env)
in (let _150_434 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _150_435 "Type annotation on parameter incompatible with the expected type" _150_434)))
in (

let g = (let _150_436 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _150_436))
in ((t), (g))))
end)))
end)
in (match (_58_1186) with
| (t, g) -> begin
(

let hd = (

let _58_1187 = hd
in {FStar_Syntax_Syntax.ppname = _58_1187.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1187.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env = (push_binding env b)
in (

let subst = (let _150_437 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _150_437))
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

let _58_1208 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _58_1207 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (

let _58_1215 = (tc_binders env bs)
in (match (_58_1215) with
| (bs, envbody, g, _58_1214) -> begin
(

let _58_1233 = (match ((let _150_444 = (FStar_Syntax_Subst.compress body)
in _150_444.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _58_1220) -> begin
(

let _58_1227 = (tc_comp envbody c)
in (match (_58_1227) with
| (c, _58_1225, g') -> begin
(let _150_445 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((Some (c)), (body), (_150_445)))
end))
end
| _58_1229 -> begin
((None), (body), (g))
end)
in (match (_58_1233) with
| (copt, body, g) -> begin
((None), (bs), ([]), (copt), (envbody), (body), (g))
end))
end)))
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm t -> (match ((let _150_450 = (FStar_Syntax_Subst.compress t)
in _150_450.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let _58_1260 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _58_1259 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _58_1267 = (tc_binders env bs)
in (match (_58_1267) with
| (bs, envbody, g, _58_1266) -> begin
(

let _58_1271 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_58_1271) with
| (envbody, _58_1270) -> begin
((Some (((t), (true)))), (bs), ([]), (None), (envbody), (body), (g))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _58_1274) -> begin
(

let _58_1285 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_58_1285) with
| (_58_1278, bs, bs', copt, env, body, g) -> begin
((Some (((t), (false)))), (bs), (bs'), (copt), (env), (body), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _58_1292 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_58_1292) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun _58_1303 c_expected -> (match (_58_1303) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _150_461 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in ((env), (bs), (guard), (_150_461)))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (let _150_462 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _150_462))
in (let _150_463 = (FStar_Syntax_Subst.subst_comp subst c)
in ((env), (bs), (guard), (_150_463))))
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

let _58_1324 = (check_binders env more_bs bs_expected)
in (match (_58_1324) with
| (env, bs', more, guard', subst) -> begin
(let _150_465 = (let _150_464 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env), ((FStar_List.append bs bs')), (more), (_150_464), (subst)))
in (handle_more _150_465 c_expected))
end))
end
| _58_1326 -> begin
(let _150_467 = (let _150_466 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _150_466))
in (fail _150_467 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _150_468 = (check_binders env bs bs_expected)
in (handle_more _150_468 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let _58_1332 = envbody
in {FStar_TypeChecker_Env.solver = _58_1332.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1332.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1332.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1332.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1332.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1332.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1332.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1332.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1332.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1332.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1332.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1332.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _58_1332.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1332.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1332.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1332.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1332.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1332.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1332.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1332.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1332.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _58_1337 _58_1340 -> (match (((_58_1337), (_58_1340))) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _58_1346 = (let _150_478 = (let _150_477 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _150_477 Prims.fst))
in (tc_term _150_478 t))
in (match (_58_1346) with
| (t, _58_1343, _58_1345) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l (([]), (t)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _150_479 = (FStar_Syntax_Syntax.mk_binder (

let _58_1350 = x
in {FStar_Syntax_Syntax.ppname = _58_1350.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1350.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_150_479)::letrec_binders)
end
| _58_1353 -> begin
letrec_binders
end)
in ((env), (lb))))
end))
end)) ((envbody), ([])))))))
in (

let _58_1359 = (check_actuals_against_formals env bs bs_expected)
in (match (_58_1359) with
| (envbody, bs, g, c) -> begin
(

let _58_1362 = if (FStar_TypeChecker_Env.should_verify env) then begin
(mk_letrec_env envbody bs c)
end else begin
((envbody), ([]))
end
in (match (_58_1362) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in ((Some (((t), (false)))), (bs), (letrecs), (Some (c)), (envbody), (body), (g)))
end))
end))))
end))
end
| _58_1365 -> begin
if (not (norm)) then begin
(let _150_480 = (unfold_whnf env t)
in (as_function_typ true _150_480))
end else begin
(

let _58_1375 = (expected_function_typ env None body)
in (match (_58_1375) with
| (_58_1367, bs, _58_1370, c_opt, envbody, body, g) -> begin
((Some (((t), (false)))), (bs), ([]), (c_opt), (envbody), (body), (g))
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let _58_1379 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1379) with
| (env, topt) -> begin
(

let _58_1383 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_481 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _150_481 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (

let _58_1392 = (expected_function_typ env topt body)
in (match (_58_1392) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let _58_1398 = (tc_term (

let _58_1393 = envbody
in {FStar_TypeChecker_Env.solver = _58_1393.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1393.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1393.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1393.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1393.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1393.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1393.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1393.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1393.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1393.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1393.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1393.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1393.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_1393.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1393.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1393.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1393.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1393.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1393.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1393.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_58_1398) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _58_1400 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _150_484 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _150_483 = (let _150_482 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _150_482))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _150_484 _150_483)))
end else begin
()
end
in (

let _58_1407 = (let _150_486 = (let _150_485 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body), (_150_485)))
in (check_expected_effect (

let _58_1402 = envbody
in {FStar_TypeChecker_Env.solver = _58_1402.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1402.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1402.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1402.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1402.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1402.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1402.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1402.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1402.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1402.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1402.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1402.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1402.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1402.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1402.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1402.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1402.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1402.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1402.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1402.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1402.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _150_486))
in (match (_58_1407) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(let _150_487 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _150_487))
end else begin
(

let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _150_490 = (let _150_489 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _150_488 -> FStar_Util.Inl (_150_488)))
in Some (_150_489))
in (FStar_Syntax_Util.abs bs body _150_490))
in (

let _58_1430 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_58_1419) -> begin
((e), (t), (guard))
end
| _58_1422 -> begin
(

let _58_1425 = if use_teq then begin
(let _150_491 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in ((e), (_150_491)))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_58_1425) with
| (e, guard') -> begin
(let _150_492 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((e), (t), (_150_492)))
end))
end))
end
| None -> begin
((e), (tfun_computed), (guard))
end)
in (match (_58_1430) with
| (e, tfun, guard) -> begin
(

let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (

let _58_1434 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_58_1434) with
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

let _58_1444 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_501 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _150_500 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _150_501 _150_500)))
end else begin
()
end
in (

let monadic_application = (fun _58_1451 subst arg_comps_rev arg_rets guard fvs bs -> (match (_58_1451) with
| (head, chead, ghead, cres) -> begin
(

let _58_1458 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let _58_1486 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun _58_6 -> (match (_58_6) with
| (_58_1465, _58_1467, None) -> begin
false
end
| (_58_1471, _58_1473, Some (c)) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _150_517 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _150_517 cres))
end else begin
(

let _58_1478 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_520 = (FStar_Syntax_Print.term_to_string head)
in (let _150_519 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _150_518 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _150_520 _150_519 _150_518))))
end else begin
()
end
in cres)
end
in ((cres), (g))))))
end
| _58_1482 -> begin
(

let g = (let _150_521 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right _150_521 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _150_526 = (let _150_525 = (let _150_524 = (let _150_523 = (let _150_522 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _150_522))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _150_523))
in (FStar_Syntax_Syntax.mk_Total _150_524))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_525))
in ((_150_526), (g))))
end)
in (match (_58_1486) with
| (cres, guard) -> begin
(

let _58_1487 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_527 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _150_527))
end else begin
()
end
in (

let _58_1509 = (FStar_List.fold_left (fun _58_1492 _58_1498 -> (match (((_58_1492), (_58_1498))) with
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

let e = (FStar_TypeChecker_Util.maybe_monadic env e c.FStar_Syntax_Syntax.eff_name)
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e c.FStar_Syntax_Syntax.eff_name out_c.FStar_Syntax_Syntax.eff_name)
in (((((e), (q)))::args), (out_c), (monadic))))))
end)
end)) (([]), (cres), (false)) arg_comps_rev)
in (match (_58_1509) with
| (args, comp, monadic) -> begin
(

let comp = (FStar_TypeChecker_Util.bind head.FStar_Syntax_Syntax.pos env None chead ((None), (comp)))
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app = if monadic then begin
(FStar_TypeChecker_Util.maybe_monadic env app comp.FStar_Syntax_Syntax.eff_name)
end else begin
app
end
in (

let _58_1515 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (_58_1515) with
| (comp, g) -> begin
((app), (comp), (g))
end)))))
end)))
end)))
end))
in (

let rec tc_args = (fun head_info _58_1523 bs args -> (match (_58_1523) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args))) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (_58_1529))))::rest, ((_58_1537, None))::_58_1535) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _58_1543 = (check_no_escape (Some (head)) env fvs t)
in (

let _58_1549 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_58_1549) with
| (varg, _58_1547, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst
in (

let arg = (let _150_539 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (_150_539)))
in (let _150_541 = (let _150_540 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst), ((((arg), (None), (None)))::outargs), ((arg)::arg_rets), (_150_540), (fvs)))
in (tc_args head_info _150_541 rest args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
(

let _58_1581 = (match (((aqual), (aq))) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _58_1580 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifier"), (e.FStar_Syntax_Syntax.pos)))))
end)
in (

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let _58_1584 = x
in {FStar_Syntax_Syntax.ppname = _58_1584.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1584.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (

let _58_1587 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_542 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _150_542))
end else begin
()
end
in (

let _58_1589 = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let _58_1592 = env
in {FStar_TypeChecker_Env.solver = _58_1592.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1592.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1592.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1592.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1592.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1592.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1592.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1592.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1592.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1592.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1592.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1592.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1592.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1592.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1592.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _58_1592.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1592.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1592.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1592.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1592.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1592.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _58_1595 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_545 = (FStar_Syntax_Print.tag_of_term e)
in (let _150_544 = (FStar_Syntax_Print.term_to_string e)
in (let _150_543 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _150_545 _150_544 _150_543))))
end else begin
()
end
in (

let _58_1600 = (tc_term env e)
in (match (_58_1600) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = ((e), (aq))
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(

let subst = (let _150_546 = (FStar_List.hd bs)
in (maybe_extend_subst subst _150_546 e))
in (tc_args head_info ((subst), ((((arg), (None), (None)))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(

let subst = (let _150_547 = (FStar_List.hd bs)
in (maybe_extend_subst subst _150_547 e))
in (tc_args head_info ((subst), ((((arg), (Some (x)), (Some (c))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (let _150_548 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _150_548)) then begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _150_549 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_549))
in (tc_args head_info ((subst), ((((arg), (Some (newx)), (Some (c))))::outargs), ((arg')::arg_rets), (g), (fvs)) rest rest')))
end else begin
(let _150_553 = (let _150_552 = (let _150_551 = (let _150_550 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _150_550))
in (_150_551)::arg_rets)
in ((subst), ((((arg), (Some (x)), (Some (c))))::outargs), (_150_552), (g), ((x)::fvs)))
in (tc_args head_info _150_553 rest rest'))
end
end
end))
end))))))))))
end
| (_58_1608, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::_58_1613) -> begin
(

let _58_1620 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (_58_1620) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _150_558 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _150_558 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let _58_1631 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (_58_1631) with
| (bs, cres') -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp cres')))
in (

let _58_1633 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_559 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _150_559))
end else begin
()
end
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args)))
end))
end
| _58_1636 when (not (norm)) -> begin
(let _150_560 = (unfold_whnf env tres)
in (aux true _150_560))
end
| _58_1638 -> begin
(let _150_566 = (let _150_565 = (let _150_564 = (let _150_562 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (let _150_561 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _150_562 _150_561)))
in (let _150_563 = (FStar_Syntax_Syntax.argpos arg)
in ((_150_564), (_150_563))))
in FStar_Syntax_Syntax.Error (_150_565))
in (Prims.raise _150_566))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (match ((let _150_571 = (FStar_Syntax_Util.unrefine tf)
in _150_571.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl -> begin
(

let _58_1671 = (tc_term env e)
in (match (_58_1671) with
| (e, c, g_e) -> begin
(

let _58_1675 = (tc_args env tl)
in (match (_58_1675) with
| (args, comps, g_rest) -> begin
(let _150_576 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e), (imp)))::args), ((((e.FStar_Syntax_Syntax.pos), (c)))::comps), (_150_576)))
end))
end))
end))
in (

let _58_1679 = (tc_args env args)
in (match (_58_1679) with
| (args, comps, g_args) -> begin
(

let bs = (let _150_578 = (FStar_All.pipe_right comps (FStar_List.map (fun _58_1683 -> (match (_58_1683) with
| (_58_1681, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks _150_578))
in (

let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _58_1689 -> begin
FStar_Syntax_Util.ml_comp
end)
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _150_593 = (FStar_Syntax_Subst.compress t)
in _150_593.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_58_1695) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _58_1700 -> begin
ml_or_tot
end)
end)
in (

let cres = (let _150_598 = (let _150_597 = (let _150_596 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_596 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _150_597))
in (ml_or_tot _150_598 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (

let _58_1704 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_601 = (FStar_Syntax_Print.term_to_string head)
in (let _150_600 = (FStar_Syntax_Print.term_to_string tf)
in (let _150_599 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _150_601 _150_600 _150_599))))
end else begin
()
end
in (

let _58_1706 = (let _150_602 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _150_602))
in (

let comp = (let _150_605 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _58_1710 out -> (match (_58_1710) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c ((None), (out)))
end)) ((((head.FStar_Syntax_Syntax.pos), (chead)))::comps) _150_605))
in (let _150_607 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _150_606 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((_150_607), (comp), (_150_606))))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _58_1719 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_1719) with
| (bs, c) -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp c)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args))
end))
end
| _58_1722 -> begin
if (not (norm)) then begin
(let _150_608 = (unfold_whnf env tf)
in (check_function_app true _150_608))
end else begin
(let _150_611 = (let _150_610 = (let _150_609 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in ((_150_609), (head.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_610))
in (Prims.raise _150_611))
end
end))
in (let _150_613 = (let _150_612 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _150_612))
in (check_function_app false _150_613))))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let _58_1758 = (FStar_List.fold_left2 (fun _58_1739 _58_1742 _58_1745 -> (match (((_58_1739), (_58_1742), (_58_1745))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(

let _58_1746 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifiers"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _58_1751 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_58_1751) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (let _150_623 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _150_623 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _150_627 = (let _150_625 = (let _150_624 = (FStar_Syntax_Syntax.as_arg e)
in (_150_624)::[])
in (FStar_List.append seen _150_625))
in (let _150_626 = (FStar_TypeChecker_Rel.conj_guard guard g)
in ((_150_627), (_150_626), (ghost)))))))
end)))
end)) (([]), (g_head), (false)) args bs)
in (match (_58_1758) with
| (args, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = if ghost then begin
(let _150_628 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _150_628 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (

let _58_1763 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_58_1763) with
| (c, g) -> begin
((e), (c), (g))
end))))
end)))
end
| _58_1765 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let _58_1772 = (FStar_Syntax_Subst.open_branch branch)
in (match (_58_1772) with
| (pattern, when_clause, branch_exp) -> begin
(

let _58_1777 = branch
in (match (_58_1777) with
| (cpat, _58_1775, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _58_1785 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_58_1785) with
| (pat_bvs, exps, p) -> begin
(

let _58_1786 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_640 = (FStar_Syntax_Print.pat_to_string p0)
in (let _150_639 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _150_640 _150_639)))
end else begin
()
end
in (

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let _58_1792 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_58_1792) with
| (env1, _58_1791) -> begin
(

let env1 = (

let _58_1793 = env1
in {FStar_TypeChecker_Env.solver = _58_1793.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1793.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1793.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1793.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1793.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1793.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1793.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1793.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _58_1793.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1793.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1793.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1793.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1793.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1793.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1793.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1793.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1793.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1793.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1793.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1793.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1793.FStar_TypeChecker_Env.use_bv_sorts})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _58_1832 = (let _150_663 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _58_1798 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_643 = (FStar_Syntax_Print.term_to_string e)
in (let _150_642 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _150_643 _150_642)))
end else begin
()
end
in (

let _58_1803 = (tc_term env1 e)
in (match (_58_1803) with
| (e, lc, g) -> begin
(

let _58_1804 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_645 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _150_644 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _150_645 _150_644)))
end else begin
()
end
in (

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let _58_1810 = (let _150_646 = (FStar_TypeChecker_Rel.discharge_guard env (

let _58_1808 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_1808.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_1808.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_1808.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _150_646 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _150_651 = (let _150_650 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _150_650 (FStar_List.map (fun _58_1818 -> (match (_58_1818) with
| (u, _58_1817) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _150_651 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _58_1826 = if (let _150_652 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _150_652)) then begin
(

let unresolved = (let _150_653 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _150_653 FStar_Util.set_elements))
in (let _150_661 = (let _150_660 = (let _150_659 = (let _150_658 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _150_657 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _150_656 = (let _150_655 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _58_1825 -> (match (_58_1825) with
| (u, _58_1824) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _150_655 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _150_658 _150_657 _150_656))))
in ((_150_659), (p.FStar_Syntax_Syntax.p)))
in FStar_Syntax_Syntax.Error (_150_660))
in (Prims.raise _150_661)))
end else begin
()
end
in (

let _58_1828 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_662 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _150_662))
end else begin
()
end
in ((e), (e'))))))))))))
end))))))
in (FStar_All.pipe_right _150_663 FStar_List.unzip))
in (match (_58_1832) with
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

let _58_1839 = (let _150_664 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _150_664 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_58_1839) with
| (scrutinee_env, _58_1838) -> begin
(

let _58_1845 = (tc_pat true pat_t pattern)
in (match (_58_1845) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let _58_1855 = (match (when_clause) with
| None -> begin
((None), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (e) -> begin
if (FStar_TypeChecker_Env.should_verify env) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("When clauses are not yet supported in --verify mode; they will be some day"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
(

let _58_1852 = (let _150_665 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _150_665 e))
in (match (_58_1852) with
| (e, c, g) -> begin
((Some (e)), (g))
end))
end
end)
in (match (_58_1855) with
| (when_clause, g_when) -> begin
(

let _58_1859 = (tc_term pat_env branch_exp)
in (match (_58_1859) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _150_667 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _150_666 -> Some (_150_666)) _150_667))
end)
in (

let _58_1917 = (

let eqs = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
None
end else begin
(FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _58_1877 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _150_671 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _150_670 -> Some (_150_670)) _150_671))
end))
end))) None))
end
in (

let _58_1885 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_58_1885) with
| (c, g_branch) -> begin
(

let _58_1912 = (match (((eqs), (when_condition))) with
| _58_1887 when (not ((FStar_TypeChecker_Env.should_verify env))) -> begin
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
in (let _150_674 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _150_673 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((_150_674), (_150_673))))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (let _150_675 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_150_675))
in (let _150_678 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _150_677 = (let _150_676 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _150_676 g_when))
in ((_150_678), (_150_677))))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _150_679 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in ((_150_679), (g_when)))))
end)
in (match (_58_1912) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _150_681 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _150_680 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in ((_150_681), (_150_680), (g_branch)))))
end))
end)))
in (match (_58_1917) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
FStar_Syntax_Util.t_true
end else begin
(

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> if ((let _150_691 = (let _150_690 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _150_690))
in (FStar_List.length _150_691)) > 1) then begin
(

let disc = (let _150_692 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _150_692 FStar_Syntax_Syntax.Delta_equational None))
in (

let disc = (let _150_694 = (let _150_693 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_150_693)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _150_694 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _150_695 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_150_695)::[])))
end else begin
[]
end)
in (

let fail = (fun _58_1927 -> (match (()) with
| () -> begin
(let _150_701 = (let _150_700 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _150_699 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _150_698 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _150_700 _150_699 _150_698))))
in (FStar_All.failwith _150_701))
end))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _58_1934) -> begin
(head_constructor t)
end
| _58_1938 -> begin
(fail ())
end))
in (

let pat_exp = (let _150_704 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _150_704 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_58_1963) -> begin
(let _150_709 = (let _150_708 = (let _150_707 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _150_706 = (let _150_705 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_150_705)::[])
in (_150_707)::_150_706))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _150_708 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_150_709)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _150_710 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _150_710))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(

let sub_term_guards = (let _150_717 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _58_1981 -> (match (_58_1981) with
| (ei, _58_1980) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _58_1985 -> begin
(

let sub_term = (let _150_716 = (let _150_713 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _150_713 FStar_Syntax_Syntax.Delta_equational None))
in (let _150_715 = (let _150_714 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_150_714)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _150_716 _150_715 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _150_717 FStar_List.flatten))
in (let _150_718 = (discriminate scrutinee_tm f)
in (FStar_List.append _150_718 sub_term_guards)))
end)
end
| _58_1989 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(

let t = (let _150_723 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _150_723))
in (

let _58_1997 = (FStar_Syntax_Util.type_u ())
in (match (_58_1997) with
| (k, _58_1996) -> begin
(

let _58_2003 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_58_2003) with
| (t, _58_2000, _58_2002) -> begin
t
end))
end)))
end)
in (

let branch_guard = (let _150_724 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _150_724 FStar_Syntax_Util.mk_disj_l))
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

let _58_2011 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_725 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _150_725))
end else begin
()
end
in (let _150_726 = (FStar_Syntax_Subst.close_branch ((pattern), (when_clause), (branch_exp)))
in ((_150_726), (branch_guard), (c), (guard))))))
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

let _58_2028 = (check_let_bound_def true env lb)
in (match (_58_2028) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let _58_2040 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
((g1), (e1), (univ_vars), (c1))
end else begin
(

let g1 = (let _150_729 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _150_729 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _58_2035 = (let _150_733 = (let _150_732 = (let _150_731 = (let _150_730 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (_150_730)))
in (_150_731)::[])
in (FStar_TypeChecker_Util.generalize env _150_732))
in (FStar_List.hd _150_733))
in (match (_58_2035) with
| (_58_2031, univs, e1, c1) -> begin
((g1), (e1), (univs), ((FStar_Syntax_Util.lcomp_of_comp c1)))
end)))
end
in (match (_58_2040) with
| (g1, e1, univ_vars, c1) -> begin
(

let _58_2050 = if (FStar_TypeChecker_Env.should_verify env) then begin
(

let _58_2043 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_58_2043) with
| (ok, c1) -> begin
if ok then begin
((e2), (c1))
end else begin
(

let _58_2044 = if (FStar_Options.warn_top_level_effects ()) then begin
(let _150_734 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _150_734 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _150_735 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) None e2.FStar_Syntax_Syntax.pos)
in ((_150_735), (c1))))
end
end))
end else begin
(

let _58_2046 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _150_736 = (c1.FStar_Syntax_Syntax.comp ())
in ((e2), (_150_736))))
end
in (match (_58_2050) with
| (e2, c1) -> begin
(

let cres = (let _150_737 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_737))
in (

let _58_2052 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _150_738 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((_150_738), (cres), (FStar_TypeChecker_Rel.trivial_guard))))))
end))
end))
end))
end
| _58_2056 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let _58_2067 = env
in {FStar_TypeChecker_Env.solver = _58_2067.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2067.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2067.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2067.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2067.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2067.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2067.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2067.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2067.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2067.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2067.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2067.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2067.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_2067.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2067.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2067.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2067.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2067.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2067.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2067.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2067.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _58_2076 = (let _150_742 = (let _150_741 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _150_741 Prims.fst))
in (check_let_bound_def false _150_742 lb))
in (match (_58_2076) with
| (e1, _58_2072, c1, g1, annotated) -> begin
(

let x = (

let _58_2077 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_2077.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2077.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let _58_2083 = (let _150_744 = (let _150_743 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_743)::[])
in (FStar_Syntax_Subst.open_term _150_744 e2))
in (match (_58_2083) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _58_2089 = (let _150_745 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _150_745 e2))
in (match (_58_2089) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (x)), (c2)))
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e2 = (FStar_TypeChecker_Util.maybe_lift env e2 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e = (let _150_748 = (let _150_747 = (let _150_746 = (FStar_Syntax_Subst.close xb e2)
in ((((false), ((lb)::[]))), (_150_746)))
in FStar_Syntax_Syntax.Tm_let (_150_747))
in (FStar_Syntax_Syntax.mk _150_748 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name)
in (

let x_eq_e1 = (let _150_751 = (let _150_750 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _150_750 e1))
in (FStar_All.pipe_left (fun _150_749 -> FStar_TypeChecker_Common.NonTrivial (_150_749)) _150_751))
in (

let g2 = (let _150_753 = (let _150_752 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _150_752 g2))
in (FStar_TypeChecker_Rel.close_guard xb _150_753))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if (let _150_754 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome _150_754)) then begin
((e), (cres), (guard))
end else begin
(

let _58_2098 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in ((e), (cres), (guard)))
end))))))))
end))))
end))))
end)))
end
| _58_2101 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _58_2113 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_58_2113) with
| (lbs, e2) -> begin
(

let _58_2116 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2116) with
| (env0, topt) -> begin
(

let _58_2119 = (build_let_rec_env true env0 lbs)
in (match (_58_2119) with
| (lbs, rec_env) -> begin
(

let _58_2122 = (check_let_recs rec_env lbs)
in (match (_58_2122) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (let _150_757 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _150_757 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _150_760 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _150_760 (fun _150_759 -> Some (_150_759))))
in (

let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(

let ecs = (let _150_764 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _150_763 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (_150_763))))))
in (FStar_TypeChecker_Util.generalize env _150_764))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _58_2133 -> (match (_58_2133) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _150_766 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_766))
in (

let _58_2136 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _58_2140 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_2140) with
| (lbs, e2) -> begin
(let _150_768 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _150_767 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in ((_150_768), (cres), (_150_767))))
end)))))))
end))
end))
end))
end))
end
| _58_2142 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _58_2154 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_58_2154) with
| (lbs, e2) -> begin
(

let _58_2157 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2157) with
| (env0, topt) -> begin
(

let _58_2160 = (build_let_rec_env false env0 lbs)
in (match (_58_2160) with
| (lbs, rec_env) -> begin
(

let _58_2163 = (check_let_recs rec_env lbs)
in (match (_58_2163) with
| (lbs, g_lbs) -> begin
(

let _58_2175 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let _58_2166 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_2166.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2166.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let _58_2169 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _58_2169.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _58_2169.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _58_2169.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _58_2169.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (lb.FStar_Syntax_Syntax.lbtyp)))
in ((env), (lb)))))) env))
in (match (_58_2175) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let _58_2181 = (tc_term env e2)
in (match (_58_2181) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _58_2185 = cres
in {FStar_Syntax_Syntax.eff_name = _58_2185.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _58_2185.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_2185.FStar_Syntax_Syntax.comp})
in (

let _58_2190 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_2190) with
| (lbs, e2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_58_2193) -> begin
((e), (cres), (guard))
end
| None -> begin
(

let _58_2196 = (check_no_escape None env bvs tres)
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
| _58_2199 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let _58_2232 = (FStar_List.fold_left (fun _58_2206 lb -> (match (_58_2206) with
| (lbs, env) -> begin
(

let _58_2211 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_58_2211) with
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

let _58_2220 = (let _150_780 = (let _150_779 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _150_779))
in (tc_check_tot_or_gtot_term (

let _58_2214 = env0
in {FStar_TypeChecker_Env.solver = _58_2214.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2214.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2214.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2214.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2214.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2214.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2214.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2214.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2214.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2214.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2214.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2214.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2214.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2214.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _58_2214.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2214.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2214.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2214.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2214.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2214.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2214.FStar_TypeChecker_Env.use_bv_sorts}) t _150_780))
in (match (_58_2220) with
| (t, _58_2218, g) -> begin
(

let _58_2221 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (

let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_TypeChecker_Env.should_verify env)) then begin
(

let _58_2224 = env
in {FStar_TypeChecker_Env.solver = _58_2224.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2224.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2224.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2224.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2224.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2224.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2224.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2224.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2224.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2224.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2224.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2224.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t)))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2224.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_2224.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2224.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2224.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2224.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2224.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2224.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2224.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2224.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (t)))
end
in (

let lb = (

let _58_2227 = lb
in {FStar_Syntax_Syntax.lbname = _58_2227.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _58_2227.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb)::lbs), (env)))))))
end))
end)) (([]), (env)) lbs)
in (match (_58_2232) with
| (lbs, env) -> begin
(((FStar_List.rev lbs)), (env))
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _58_2245 = (let _150_785 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _58_2239 = (let _150_784 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _150_784 lb.FStar_Syntax_Syntax.lbdef))
in (match (_58_2239) with
| (e, c, g) -> begin
(

let _58_2240 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in ((lb), (g))))
end)))))
in (FStar_All.pipe_right _150_785 FStar_List.unzip))
in (match (_58_2245) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _58_2253 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2253) with
| (env1, _58_2252) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _58_2259 = (check_lbtyp top_level env lb)
in (match (_58_2259) with
| (topt, wf_annot, univ_vars, env1) -> begin
(

let _58_2260 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _58_2267 = (tc_maybe_toplevel_term (

let _58_2262 = env1
in {FStar_TypeChecker_Env.solver = _58_2262.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2262.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2262.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2262.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2262.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2262.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2262.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2262.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2262.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2262.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2262.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2262.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2262.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _58_2262.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2262.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2262.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2262.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2262.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2262.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2262.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2262.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_58_2267) with
| (e1, c1, g1) -> begin
(

let _58_2271 = (let _150_792 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_2268 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _150_792 e1 c1 wf_annot))
in (match (_58_2271) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _58_2273 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_793 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _150_793))
end else begin
()
end
in (let _150_794 = (FStar_Option.isSome topt)
in ((e1), (univ_vars), (c1), (g1), (_150_794)))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _58_2280 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in ((None), (FStar_TypeChecker_Rel.trivial_guard), ([]), (env)))
end
| _58_2283 -> begin
(

let _58_2286 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_58_2286) with
| (univ_vars, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _150_798 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars), (_150_798)))
end else begin
(

let _58_2291 = (FStar_Syntax_Util.type_u ())
in (match (_58_2291) with
| (k, _58_2290) -> begin
(

let _58_2296 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_58_2296) with
| (t, _58_2294, g) -> begin
(

let _58_2297 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_801 = (let _150_799 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _150_799))
in (let _150_800 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _150_801 _150_800)))
end else begin
()
end
in (

let t = (norm env1 t)
in (let _150_802 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (g), (univ_vars), (_150_802)))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _58_2303 -> (match (_58_2303) with
| (x, imp) -> begin
(

let _58_2306 = (FStar_Syntax_Util.type_u ())
in (match (_58_2306) with
| (tu, u) -> begin
(

let _58_2311 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_58_2311) with
| (t, _58_2309, g) -> begin
(

let x = (((

let _58_2312 = x
in {FStar_Syntax_Syntax.ppname = _58_2312.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2312.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in (

let _58_2315 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_806 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _150_805 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _150_806 _150_805)))
end else begin
()
end
in (let _150_807 = (push_binding env x)
in ((x), (_150_807), (g), (u)))))
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

let _58_2330 = (tc_binder env b)
in (match (_58_2330) with
| (b, env', g, u) -> begin
(

let _58_2335 = (aux env' bs)
in (match (_58_2335) with
| (bs, env', g', us) -> begin
(let _150_815 = (let _150_814 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _150_814))
in (((b)::bs), (env'), (_150_815), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun _58_2343 _58_2346 -> (match (((_58_2343), (_58_2346))) with
| ((t, imp), (args, g)) -> begin
(

let _58_2351 = (tc_term env t)
in (match (_58_2351) with
| (t, _58_2349, g') -> begin
(let _150_824 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t), (imp)))::args), (_150_824)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p _58_2355 -> (match (_58_2355) with
| (pats, g) -> begin
(

let _58_2358 = (tc_args env p)
in (match (_58_2358) with
| (args, g') -> begin
(let _150_827 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats), (_150_827)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _58_2364 = (tc_maybe_toplevel_term env e)
in (match (_58_2364) with
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

let _58_2370 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _150_830 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in ((_150_830), (false)))
end else begin
(let _150_831 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in ((_150_831), (true)))
end
in (match (_58_2370) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _150_832 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (_150_832)))
end
| _58_2374 -> begin
if allow_ghost then begin
(let _150_835 = (let _150_834 = (let _150_833 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in ((_150_833), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_834))
in (Prims.raise _150_835))
end else begin
(let _150_838 = (let _150_837 = (let _150_836 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in ((_150_836), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_837))
in (Prims.raise _150_838))
end
end)
end)))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let _58_2384 = (tc_tot_or_gtot_term env t)
in (match (_58_2384) with
| (t, c, g) -> begin
(

let _58_2385 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in ((t), (c)))
end)))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let _58_2393 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_2393) with
| (t, c, g) -> begin
(

let _58_2394 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _150_856 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _150_856)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _150_860 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (([]), (_150_860)))))


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let _58_2409 = (tc_binders env tps)
in (match (_58_2409) with
| (tps, env, g, us) -> begin
(

let _58_2410 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in ((tps), (env), (us)))
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (

let fail = (fun _58_2416 -> (match (()) with
| () -> begin
(let _150_875 = (let _150_874 = (let _150_873 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in ((_150_873), ((FStar_Ident.range_of_lid m))))
in FStar_Syntax_Syntax.Error (_150_874))
in (Prims.raise _150_875))
end))
in (

let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _58_2429))::((wp, _58_2425))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _58_2433 -> begin
(fail ())
end))
end
| _58_2435 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let _58_2442 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_58_2442) with
| (uvs, c) -> begin
((uvs), ([]), (c))
end))
end
| _58_2444 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let _58_2448 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_58_2448) with
| (uvs, t') -> begin
(match ((let _150_882 = (FStar_Syntax_Subst.compress t')
in _150_882.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
((uvs), (binders), (c))
end
| _58_2454 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))


let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (

let fail = (fun t -> (let _150_893 = (let _150_892 = (let _150_891 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in ((_150_891), ((FStar_Ident.range_of_lid mname))))
in FStar_Syntax_Syntax.Error (_150_892))
in (Prims.raise _150_893)))
in (match ((let _150_894 = (FStar_Syntax_Subst.compress signature)
in _150_894.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _58_2471))::((wp, _58_2467))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _58_2475 -> begin
(fail signature)
end))
end
| _58_2477 -> begin
(fail signature)
end)))


let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (

let _58_2482 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_58_2482) with
| (a, wp) -> begin
(

let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _58_2485 -> begin
(

let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (

let op = (fun ts -> (

let _58_2489 = ()
in (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in (([]), (t1)))))
in (

let _58_2492 = ed
in (let _150_910 = (op ed.FStar_Syntax_Syntax.ret_wp)
in (let _150_909 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _150_908 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _150_907 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _150_906 = (op ed.FStar_Syntax_Syntax.stronger)
in (let _150_905 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _150_904 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _150_903 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _150_902 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _150_901 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _58_2492.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2492.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _58_2492.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _58_2492.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _58_2492.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _150_910; FStar_Syntax_Syntax.bind_wp = _150_909; FStar_Syntax_Syntax.if_then_else = _150_908; FStar_Syntax_Syntax.ite_wp = _150_907; FStar_Syntax_Syntax.stronger = _150_906; FStar_Syntax_Syntax.close_wp = _150_905; FStar_Syntax_Syntax.assert_p = _150_904; FStar_Syntax_Syntax.assume_p = _150_903; FStar_Syntax_Syntax.null_wp = _150_902; FStar_Syntax_Syntax.trivial = _150_901; FStar_Syntax_Syntax.repr = _58_2492.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _58_2492.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _58_2492.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _58_2492.FStar_Syntax_Syntax.actions})))))))))))))
end)
in ((ed), (a), (wp)))
end)))


let rec tc_real_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  effect_cost  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed is_for_free -> (

let _58_2498 = ()
in (

let _58_2502 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_58_2502) with
| (binders_un, signature_un) -> begin
(

let _58_2507 = (tc_tparams env0 binders_un)
in (match (_58_2507) with
| (binders, env, _58_2506) -> begin
(

let _58_2511 = (tc_trivial_guard env signature_un)
in (match (_58_2511) with
| (signature, _58_2510) -> begin
(

let ed = (

let _58_2512 = ed
in {FStar_Syntax_Syntax.qualifiers = _58_2512.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2512.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _58_2512.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _58_2512.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _58_2512.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _58_2512.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _58_2512.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _58_2512.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _58_2512.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _58_2512.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _58_2512.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _58_2512.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _58_2512.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _58_2512.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _58_2512.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _58_2512.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _58_2512.FStar_Syntax_Syntax.actions})
in (

let _58_2518 = (open_effect_decl env ed)
in (match (_58_2518) with
| (ed, a, wp_a) -> begin
(

let get_effect_signature = (fun _58_2520 -> (match (()) with
| () -> begin
(

let _58_2524 = (tc_trivial_guard env signature_un)
in (match (_58_2524) with
| (signature, _58_2523) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (

let env = (let _150_939 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _150_939))
in (

let _58_2526 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _150_945 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _150_944 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _150_943 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _150_942 = (let _150_940 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Print.term_to_string _150_940))
in (let _150_941 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort)
in (FStar_Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n" _150_945 _150_944 _150_943 _150_942 _150_941))))))
end else begin
()
end
in (

let check_and_gen' = (fun env _58_2533 k -> (match (_58_2533) with
| (_58_2531, t) -> begin
(check_and_gen env t k)
end))
in (

let _58_2539 = (match (is_for_free) with
| NotForFree -> begin
((env), (ed))
end
| ForFree -> begin
(FStar_TypeChecker_DMFF.gen_wps_for_free env binders a wp_a tc_decl tc_term ed)
end)
in (match (_58_2539) with
| (env, ed) -> begin
(

let return_wp = (

let expected_k = (let _150_957 = (let _150_955 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_954 = (let _150_953 = (let _150_952 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _150_952))
in (_150_953)::[])
in (_150_955)::_150_954))
in (let _150_956 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _150_957 _150_956)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let _58_2544 = (get_effect_signature ())
in (match (_58_2544) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _150_961 = (let _150_959 = (let _150_958 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _150_958))
in (_150_959)::[])
in (let _150_960 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _150_961 _150_960)))
in (

let expected_k = (let _150_972 = (let _150_970 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _150_969 = (let _150_968 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_967 = (let _150_966 = (FStar_Syntax_Syntax.mk_binder b)
in (let _150_965 = (let _150_964 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _150_963 = (let _150_962 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (_150_962)::[])
in (_150_964)::_150_963))
in (_150_966)::_150_965))
in (_150_968)::_150_967))
in (_150_970)::_150_969))
in (let _150_971 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _150_972 _150_971)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (let _150_974 = (let _150_973 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_973 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _150_974))
in (

let expected_k = (let _150_983 = (let _150_981 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_980 = (let _150_979 = (FStar_Syntax_Syntax.mk_binder p)
in (let _150_978 = (let _150_977 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _150_976 = (let _150_975 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_975)::[])
in (_150_977)::_150_976))
in (_150_979)::_150_978))
in (_150_981)::_150_980))
in (let _150_982 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_983 _150_982)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (let _150_988 = (let _150_986 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_985 = (let _150_984 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_984)::[])
in (_150_986)::_150_985))
in (let _150_987 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_988 _150_987)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let _58_2556 = (FStar_Syntax_Util.type_u ())
in (match (_58_2556) with
| (t, _58_2555) -> begin
(

let expected_k = (let _150_995 = (let _150_993 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_992 = (let _150_991 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _150_990 = (let _150_989 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_989)::[])
in (_150_991)::_150_990))
in (_150_993)::_150_992))
in (let _150_994 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _150_995 _150_994)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (let _150_997 = (let _150_996 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_996 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _150_997))
in (

let b_wp_a = (let _150_1001 = (let _150_999 = (let _150_998 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _150_998))
in (_150_999)::[])
in (let _150_1000 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_1001 _150_1000)))
in (

let expected_k = (let _150_1008 = (let _150_1006 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1005 = (let _150_1004 = (FStar_Syntax_Syntax.mk_binder b)
in (let _150_1003 = (let _150_1002 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_150_1002)::[])
in (_150_1004)::_150_1003))
in (_150_1006)::_150_1005))
in (let _150_1007 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_1008 _150_1007)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

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
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _150_1026 = (let _150_1024 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1023 = (let _150_1022 = (let _150_1019 = (let _150_1018 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_1018 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _150_1019))
in (let _150_1021 = (let _150_1020 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_1020)::[])
in (_150_1022)::_150_1021))
in (_150_1024)::_150_1023))
in (let _150_1025 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_1026 _150_1025)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _150_1029 = (let _150_1027 = (FStar_Syntax_Syntax.mk_binder a)
in (_150_1027)::[])
in (let _150_1028 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_1029 _150_1028)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let _58_2572 = (FStar_Syntax_Util.type_u ())
in (match (_58_2572) with
| (t, _58_2571) -> begin
(

let expected_k = (let _150_1034 = (let _150_1032 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1031 = (let _150_1030 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_1030)::[])
in (_150_1032)::_150_1031))
in (let _150_1033 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _150_1034 _150_1033)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let _58_2696 = if ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) || (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable))) then begin
(

let repr = (

let _58_2578 = (FStar_Syntax_Util.type_u ())
in (match (_58_2578) with
| (t, _58_2577) -> begin
(

let expected_k = (let _150_1039 = (let _150_1037 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1036 = (let _150_1035 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_1035)::[])
in (_150_1037)::_150_1036))
in (let _150_1038 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _150_1039 _150_1038)))
in (tc_check_trivial_guard env ed.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (let _150_1050 = (let _150_1049 = (let _150_1048 = (FStar_Syntax_Util.un_uinst repr)
in (let _150_1047 = (let _150_1046 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_1045 = (let _150_1044 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_1044)::[])
in (_150_1046)::_150_1045))
in ((_150_1048), (_150_1047))))
in FStar_Syntax_Syntax.Tm_app (_150_1049))
in (FStar_Syntax_Syntax.mk _150_1050 None FStar_Range.dummyRange)))
in (

let mk_repr = (fun a wp -> (let _150_1055 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_repr' _150_1055 wp)))
in (

let destruct_repr = (fun t -> (match ((let _150_1058 = (FStar_Syntax_Subst.compress t)
in _150_1058.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_58_2590, ((t, _58_2597))::((wp, _58_2593))::[]) -> begin
((t), (wp))
end
| _58_2603 -> begin
(FStar_All.failwith "Unexpected repr type")
end))
in (

let bind_repr = (

let r = (let _150_1059 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_0 FStar_Syntax_Syntax.Delta_constant None)
in (FStar_All.pipe_right _150_1059 FStar_Syntax_Syntax.fv_to_tm))
in (

let _58_2607 = (get_effect_signature ())
in (match (_58_2607) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _150_1063 = (let _150_1061 = (let _150_1060 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _150_1060))
in (_150_1061)::[])
in (let _150_1062 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _150_1063 _150_1062)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" None a_wp_b)
in (

let x_a = (let _150_1064 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _150_1064))
in (

let wp_g_x = (let _150_1068 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (let _150_1067 = (let _150_1066 = (let _150_1065 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_1065))
in (_150_1066)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _150_1068 _150_1067 None FStar_Range.dummyRange)))
in (

let res = (

let wp = (let _150_1080 = (let _150_1069 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right _150_1069 Prims.snd))
in (let _150_1079 = (let _150_1078 = (let _150_1077 = (let _150_1076 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_1075 = (let _150_1074 = (FStar_Syntax_Syntax.bv_to_name b)
in (let _150_1073 = (let _150_1072 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (let _150_1071 = (let _150_1070 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (_150_1070)::[])
in (_150_1072)::_150_1071))
in (_150_1074)::_150_1073))
in (_150_1076)::_150_1075))
in (r)::_150_1077)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _150_1078))
in (FStar_Syntax_Syntax.mk_Tm_app _150_1080 _150_1079 None FStar_Range.dummyRange)))
in (mk_repr b wp))
in (

let expected_k = (let _150_1100 = (let _150_1098 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1097 = (let _150_1096 = (FStar_Syntax_Syntax.mk_binder b)
in (let _150_1095 = (let _150_1094 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (let _150_1093 = (let _150_1092 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (let _150_1091 = (let _150_1090 = (let _150_1082 = (let _150_1081 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a _150_1081))
in (FStar_Syntax_Syntax.null_binder _150_1082))
in (let _150_1089 = (let _150_1088 = (let _150_1087 = (let _150_1086 = (let _150_1083 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_150_1083)::[])
in (let _150_1085 = (let _150_1084 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _150_1084))
in (FStar_Syntax_Util.arrow _150_1086 _150_1085)))
in (FStar_Syntax_Syntax.null_binder _150_1087))
in (_150_1088)::[])
in (_150_1090)::_150_1089))
in (_150_1092)::_150_1091))
in (_150_1094)::_150_1093))
in (_150_1096)::_150_1095))
in (_150_1098)::_150_1097))
in (let _150_1099 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _150_1100 _150_1099)))
in (

let _58_2621 = (tc_tot_or_gtot_term env expected_k)
in (match (_58_2621) with
| (expected_k, _58_2618, _58_2620) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_repr expected_k))
end)))))))))
end)))
in (

let return_repr = (

let x_a = (let _150_1101 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _150_1101))
in (

let res = (

let wp = (let _150_1108 = (let _150_1102 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right _150_1102 Prims.snd))
in (let _150_1107 = (let _150_1106 = (let _150_1105 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_1104 = (let _150_1103 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (_150_1103)::[])
in (_150_1105)::_150_1104))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _150_1106))
in (FStar_Syntax_Syntax.mk_Tm_app _150_1108 _150_1107 None FStar_Range.dummyRange)))
in (mk_repr a wp))
in (

let expected_k = (let _150_1113 = (let _150_1111 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1110 = (let _150_1109 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_150_1109)::[])
in (_150_1111)::_150_1110))
in (let _150_1112 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _150_1113 _150_1112)))
in (

let _58_2633 = (tc_tot_or_gtot_term env expected_k)
in (match (_58_2633) with
| (expected_k, _58_2630, _58_2632) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let _58_2637 = (check_and_gen' env ed.FStar_Syntax_Syntax.return_repr expected_k)
in (match (_58_2637) with
| (univs, repr) -> begin
(match (univs) with
| [] -> begin
(([]), (repr))
end
| _58_2640 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected universe-polymorphic return for effect"), (repr.FStar_Syntax_Syntax.pos)))))
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let _58_2647 = (tc_tot_or_gtot_term env act.FStar_Syntax_Syntax.action_defn)
in (match (_58_2647) with
| (act_defn, c, g_a) -> begin
(

let _58_2667 = (match ((let _150_1116 = (FStar_Syntax_Subst.compress c.FStar_Syntax_Syntax.res_typ)
in _150_1116.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _58_2655 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_2655) with
| (bs, _58_2654) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (let _150_1117 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs _150_1117))
in (

let _58_2662 = (tc_tot_or_gtot_term env k)
in (match (_58_2662) with
| (k, _58_2660, g) -> begin
((k), (g))
end))))
end))
end
| _58_2664 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Actions must have function types"), (act_defn.FStar_Syntax_Syntax.pos)))))
end)
in (match (_58_2667) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env c.FStar_Syntax_Syntax.res_typ expected_k)
in (

let _58_2669 = (let _150_1119 = (let _150_1118 = (FStar_TypeChecker_Rel.conj_guard g_k g)
in (FStar_TypeChecker_Rel.conj_guard g_a _150_1118))
in (FStar_TypeChecker_Rel.force_trivial_guard env _150_1119))
in (

let act_ty = (match ((let _150_1120 = (FStar_Syntax_Subst.compress expected_k)
in _150_1120.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _58_2677 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_2677) with
| (bs, c) -> begin
(

let _58_2680 = (destruct_repr (FStar_Syntax_Util.comp_result c))
in (match (_58_2680) with
| (a, wp) -> begin
(

let c = (let _150_1122 = (let _150_1121 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_1121)::[])
in {FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a; FStar_Syntax_Syntax.effect_args = _150_1122; FStar_Syntax_Syntax.flags = []})
in (let _150_1123 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Util.arrow bs _150_1123)))
end))
end))
end
| _58_2683 -> begin
(FStar_All.failwith "")
end)
in (

let _58_2687 = (FStar_TypeChecker_Util.generalize_universes env act_defn)
in (match (_58_2687) with
| (univs, act_defn) -> begin
(

let act_ty = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env act_ty)
in (

let _58_2689 = act
in {FStar_Syntax_Syntax.action_name = _58_2689.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = act_defn; FStar_Syntax_Syntax.action_typ = act_ty}))
end)))))
end))
end)))
in (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.map check_action)))
in ((repr), (bind_repr), (return_repr), (actions)))))))))
end else begin
((ed.FStar_Syntax_Syntax.repr), (ed.FStar_Syntax_Syntax.bind_repr), (ed.FStar_Syntax_Syntax.return_repr), (ed.FStar_Syntax_Syntax.actions))
end
in (match (_58_2696) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t = (let _150_1124 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _150_1124))
in (

let _58_2700 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_58_2700) with
| (univs, t) -> begin
(

let _58_2716 = (match ((let _150_1126 = (let _150_1125 = (FStar_Syntax_Subst.compress t)
in _150_1125.FStar_Syntax_Syntax.n)
in ((binders), (_150_1126)))) with
| ([], _58_2703) -> begin
(([]), (t))
end
| (_58_2706, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
((binders), ((FStar_Syntax_Util.comp_result c)))
end
| _58_2713 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_58_2716) with
| (binders, signature) -> begin
(

let close = (fun n ts -> (

let ts = (let _150_1131 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _150_1131))
in ts))
in (

let close_action = (fun act -> (

let _58_2725 = (close (- (1)) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (_58_2725) with
| (univs, defn) -> begin
(

let _58_2728 = (close (- (1)) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (_58_2728) with
| (univs', typ) -> begin
(

let _58_2729 = ()
in (

let _58_2731 = act
in {FStar_Syntax_Syntax.action_name = _58_2731.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ}))
end))
end)))
in (

let ed = (

let _58_2733 = ed
in (let _150_1148 = (close 0 return_wp)
in (let _150_1147 = (close 1 bind_wp)
in (let _150_1146 = (close 0 if_then_else)
in (let _150_1145 = (close 0 ite_wp)
in (let _150_1144 = (close 0 stronger)
in (let _150_1143 = (close 1 close_wp)
in (let _150_1142 = (close 0 assert_p)
in (let _150_1141 = (close 0 assume_p)
in (let _150_1140 = (close 0 null_wp)
in (let _150_1139 = (close 0 trivial_wp)
in (let _150_1138 = (let _150_1134 = (close 0 (([]), (repr)))
in (Prims.snd _150_1134))
in (let _150_1137 = (close 0 return_repr)
in (let _150_1136 = (close 1 bind_repr)
in (let _150_1135 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.qualifiers = _58_2733.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2733.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _150_1148; FStar_Syntax_Syntax.bind_wp = _150_1147; FStar_Syntax_Syntax.if_then_else = _150_1146; FStar_Syntax_Syntax.ite_wp = _150_1145; FStar_Syntax_Syntax.stronger = _150_1144; FStar_Syntax_Syntax.close_wp = _150_1143; FStar_Syntax_Syntax.assert_p = _150_1142; FStar_Syntax_Syntax.assume_p = _150_1141; FStar_Syntax_Syntax.null_wp = _150_1140; FStar_Syntax_Syntax.trivial = _150_1139; FStar_Syntax_Syntax.repr = _150_1138; FStar_Syntax_Syntax.return_repr = _150_1137; FStar_Syntax_Syntax.bind_repr = _150_1136; FStar_Syntax_Syntax.actions = _150_1135})))))))))))))))
in (

let _58_2738 = if ((FStar_TypeChecker_Env.debug env FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EffDecl")))) then begin
(let _150_1149 = (FStar_Syntax_Print.eff_decl_to_string (match (is_for_free) with
| ForFree -> begin
true
end
| NotForFree -> begin
false
end) ed)
in (FStar_Util.print_string _150_1149))
end else begin
()
end
in ed))))
end))
end)))
end))))))))))))
end))))))
end)))
end))
end))
end))))
and elaborate_and_star : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.eff_decl) = (fun env0 ed -> (

let _58_2744 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_58_2744) with
| (binders_un, signature_un) -> begin
(

let _58_2749 = (tc_tparams env0 binders_un)
in (match (_58_2749) with
| (binders, env, _58_2748) -> begin
(

let _58_2753 = (tc_trivial_guard env signature_un)
in (match (_58_2753) with
| (signature, _58_2752) -> begin
(

let _58_2766 = (match ((let _150_1152 = (FStar_Syntax_Subst.compress signature)
in _150_1152.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (((a, _58_2756))::[], effect_marker) -> begin
((a), (effect_marker))
end
| _58_2763 -> begin
(FStar_All.failwith "bad shape for effect-for-free signature")
end)
in (match (_58_2766) with
| (a, effect_marker) -> begin
(

let open_and_check = (fun t -> (

let subst = (FStar_Syntax_Subst.opening_of_binders binders)
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (

let _58_2775 = (tc_term env t)
in (match (_58_2775) with
| (t, comp, _58_2774) -> begin
((t), (comp))
end)))))
in (

let recheck_debug = (fun s env t -> (

let _58_2780 = (let _150_1161 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Term has been %s-transformed to:\n%s\n----------\n" s _150_1161))
in (

let _58_2787 = (tc_term env t)
in (match (_58_2787) with
| (t', _58_2784, _58_2786) -> begin
(

let _58_2788 = (let _150_1162 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print1 "Re-checked; got:\n%s\n----------\n" _150_1162))
in t)
end))))
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None signature.FStar_Syntax_Syntax.pos))
in (

let _58_2794 = (open_and_check ed.FStar_Syntax_Syntax.repr)
in (match (_58_2794) with
| (repr, _comp) -> begin
(

let _58_2795 = (let _150_1165 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" _150_1165))
in (

let dmff_env = (FStar_TypeChecker_DMFF.empty env (tc_constant FStar_Range.dummyRange))
in (

let _58_2800 = (FStar_TypeChecker_DMFF.star_type_definition dmff_env repr)
in (match (_58_2800) with
| (dmff_env, wp_type) -> begin
(

let wp_type = (recheck_debug "*" env wp_type)
in (

let wp_a = (let _150_1171 = (let _150_1170 = (let _150_1169 = (let _150_1168 = (let _150_1167 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_1166 = (FStar_Syntax_Syntax.as_implicit false)
in ((_150_1167), (_150_1166))))
in (_150_1168)::[])
in ((wp_type), (_150_1169)))
in FStar_Syntax_Syntax.Tm_app (_150_1170))
in (mk _150_1171))
in (

let effect_signature = (

let binders = (let _150_1175 = (let _150_1172 = (FStar_Syntax_Syntax.as_implicit false)
in ((a), (_150_1172)))
in (let _150_1174 = (let _150_1173 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_1173)::[])
in (_150_1175)::_150_1174))
in (

let binders = (FStar_Syntax_Subst.close_binders binders)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (effect_marker)))))))
in (

let effect_signature = (recheck_debug "turned into the effect signature" env effect_signature)
in (

let elaborate_and_star = (fun dmff_env item -> (

let _58_2812 = item
in (match (_58_2812) with
| (u_item, item) -> begin
(

let _58_2815 = (open_and_check item)
in (match (_58_2815) with
| (item, item_comp) -> begin
(

let _58_2816 = if (not ((FStar_Syntax_Util.is_total_lcomp item_comp))) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Computation for [item] is not total!")))
end else begin
()
end
in (

let _58_2822 = (FStar_TypeChecker_DMFF.star_expr_definition dmff_env item)
in (match (_58_2822) with
| (dmff_env, (item_wp, item_elab)) -> begin
(

let item_wp = (recheck_debug "*" env item_wp)
in (

let item_elab = (recheck_debug "_" env item_elab)
in ((dmff_env), (item_wp), (item_elab))))
end)))
end))
end)))
in (

let _58_2828 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.bind_repr)
in (match (_58_2828) with
| (dmff_env, bind_wp, bind_elab) -> begin
(

let _58_2832 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.return_repr)
in (match (_58_2832) with
| (dmff_env, return_wp, return_elab) -> begin
(

let return_wp = (match ((let _150_1180 = (FStar_Syntax_Subst.compress return_wp)
in _150_1180.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(let _150_1181 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) _150_1181 (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_GTot_lid)))))
end
| _58_2843 -> begin
(FStar_All.failwith "unexpected shape for return")
end)
in (

let bind_wp = (match ((let _150_1182 = (FStar_Syntax_Subst.compress bind_wp)
in _150_1182.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (let _150_1185 = (let _150_1184 = (let _150_1183 = (mk (FStar_Syntax_Syntax.Tm_fvar (r)))
in (FStar_Syntax_Syntax.null_binder _150_1183))
in (_150_1184)::binders)
in (FStar_Syntax_Util.abs _150_1185 body what)))
end
| _58_2852 -> begin
(FStar_All.failwith "unexpected shape for bind")
end)
in (

let _58_2866 = (FStar_List.fold_left (fun _58_2856 action -> (match (_58_2856) with
| (dmff_env, actions) -> begin
(

let _58_2861 = (elaborate_and_star dmff_env ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (_58_2861) with
| (dmff_env, action_wp, action_elab) -> begin
((dmff_env), (((

let _58_2862 = action
in {FStar_Syntax_Syntax.action_name = _58_2862.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = _58_2862.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = action_elab; FStar_Syntax_Syntax.action_typ = _58_2862.FStar_Syntax_Syntax.action_typ}))::actions))
end))
end)) ((dmff_env), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (_58_2866) with
| (dmff_env, actions) -> begin
(

let actions = (FStar_List.rev actions)
in (

let repr = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" None wp_a)
in (

let binders = (let _150_1190 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1189 = (let _150_1188 = (FStar_Syntax_Syntax.mk_binder wp)
in (_150_1188)::[])
in (_150_1190)::_150_1189))
in (let _150_1199 = (let _150_1198 = (let _150_1196 = (let _150_1195 = (let _150_1194 = (let _150_1193 = (let _150_1192 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_1191 = (FStar_Syntax_Syntax.as_implicit false)
in ((_150_1192), (_150_1191))))
in (_150_1193)::[])
in ((ed.FStar_Syntax_Syntax.repr), (_150_1194)))
in FStar_Syntax_Syntax.Tm_app (_150_1195))
in (mk _150_1196))
in (let _150_1197 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_FC dmff_env _150_1198 _150_1197)))
in (FStar_Syntax_Util.abs binders _150_1199 None))))
in (

let repr = (recheck_debug "FC" env repr)
in (

let c = (FStar_Syntax_Subst.close binders)
in (

let ed = (

let _58_2873 = ed
in (let _150_1213 = (FStar_Syntax_Subst.close_binders binders)
in (let _150_1212 = (let _150_1201 = (c return_wp)
in (([]), (_150_1201)))
in (let _150_1211 = (let _150_1202 = (c bind_wp)
in (([]), (_150_1202)))
in (let _150_1210 = (c repr)
in (let _150_1209 = (let _150_1203 = (c return_elab)
in (([]), (_150_1203)))
in (let _150_1208 = (let _150_1204 = (c bind_elab)
in (([]), (_150_1204)))
in (let _150_1207 = (FStar_List.map (fun action -> (

let _58_2876 = action
in (let _150_1206 = (c action.FStar_Syntax_Syntax.action_defn)
in {FStar_Syntax_Syntax.action_name = _58_2876.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = _58_2876.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _150_1206; FStar_Syntax_Syntax.action_typ = _58_2876.FStar_Syntax_Syntax.action_typ}))) actions)
in {FStar_Syntax_Syntax.qualifiers = _58_2873.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2873.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _58_2873.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _150_1213; FStar_Syntax_Syntax.signature = effect_signature; FStar_Syntax_Syntax.ret_wp = _150_1212; FStar_Syntax_Syntax.bind_wp = _150_1211; FStar_Syntax_Syntax.if_then_else = _58_2873.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _58_2873.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _58_2873.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _58_2873.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _58_2873.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _58_2873.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _58_2873.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _58_2873.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _150_1210; FStar_Syntax_Syntax.return_repr = _150_1209; FStar_Syntax_Syntax.bind_repr = _150_1208; FStar_Syntax_Syntax.actions = _150_1207}))))))))
in (

let _58_2879 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _150_1214 = (FStar_Syntax_Print.eff_decl_to_string true ed)
in (FStar_Util.print_string _150_1214))
end else begin
()
end
in ((env), (ed))))))))
end))))
end))
end)))))))
end))))
end)))))
end))
end))
end))
end)))
and tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  effect_cost  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed is_for_free -> (

let _58_2888 = (match (is_for_free) with
| ForFree -> begin
(elaborate_and_star env0 ed)
end
| NotForFree -> begin
((env0), (ed))
end)
in (match (_58_2888) with
| (env0, ed) -> begin
(tc_real_eff_decl env0 ed is_for_free)
end)))
and tc_lex_t : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (

let _58_2893 = ()
in (

let _58_2901 = ()
in (match (ses) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _58_2930, _58_2932, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _58_2921, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _58_2910, r2))::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
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

let lex_top_t = (let _150_1225 = (let _150_1224 = (let _150_1223 = (let _150_1222 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _150_1222 FStar_Syntax_Syntax.Delta_constant None))
in ((_150_1223), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_150_1224))
in (FStar_Syntax_Syntax.mk _150_1225 None r1))
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

let a = (let _150_1226 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _150_1226))
in (

let hd = (let _150_1227 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _150_1227))
in (

let tl = (let _150_1232 = (let _150_1231 = (let _150_1230 = (let _150_1229 = (let _150_1228 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _150_1228 FStar_Syntax_Syntax.Delta_constant None))
in ((_150_1229), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_150_1230))
in (FStar_Syntax_Syntax.mk _150_1231 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _150_1232))
in (

let res = (let _150_1236 = (let _150_1235 = (let _150_1234 = (let _150_1233 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _150_1233 FStar_Syntax_Syntax.Delta_constant None))
in ((_150_1234), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_150_1235))
in (FStar_Syntax_Syntax.mk _150_1236 None r2))
in (let _150_1237 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (Some (FStar_Syntax_Syntax.imp_tag))))::(((hd), (None)))::(((tl), (None)))::[]) _150_1237))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t), (FStar_Syntax_Const.lex_t_lid), (0), ([]), ([]), (r2)))
in (let _150_1239 = (let _150_1238 = (FStar_TypeChecker_Env.get_range env)
in (((tc)::(dc_lextop)::(dc_lexcons)::[]), ([]), (lids), (_150_1238)))
in FStar_Syntax_Syntax.Sig_bundle (_150_1239)))))))))))))))
end
| _58_2956 -> begin
(let _150_1241 = (let _150_1240 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle (((ses), ([]), (lids), (FStar_Range.dummyRange)))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _150_1240))
in (FStar_All.failwith _150_1241))
end))))
and tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _58_2966 = (FStar_Syntax_Util.type_u ())
in (match (_58_2966) with
| (k, _58_2965) -> begin
(

let phi = (let _150_1247 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _150_1247 (norm env)))
in (

let _58_2968 = (FStar_TypeChecker_Util.check_uvars r phi)
in FStar_Syntax_Syntax.Sig_assume (((lid), (phi), (quals), (r)))))
end))))
and tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _150_1257 = (let _150_1256 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _150_1256))
in (FStar_TypeChecker_Errors.diag r _150_1257)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let _58_2991 = ()
in (

let _58_2993 = (warn_positivity tc r)
in (

let _58_2997 = (FStar_Syntax_Subst.open_term tps k)
in (match (_58_2997) with
| (tps, k) -> begin
(

let _58_3002 = (tc_binders env tps)
in (match (_58_3002) with
| (tps, env_tps, guard_params, us) -> begin
(

let _58_3005 = (FStar_Syntax_Util.arrow_formals k)
in (match (_58_3005) with
| (indices, t) -> begin
(

let _58_3010 = (tc_binders env_tps indices)
in (match (_58_3010) with
| (indices, env', guard_indices, us') -> begin
(

let _58_3018 = (

let _58_3015 = (tc_tot_or_gtot_term env' t)
in (match (_58_3015) with
| (t, _58_3013, g) -> begin
(let _150_1264 = (let _150_1263 = (let _150_1262 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params _150_1262))
in (FStar_TypeChecker_Rel.discharge_guard env' _150_1263))
in ((t), (_150_1264)))
end))
in (match (_58_3018) with
| (t, guard) -> begin
(

let k = (let _150_1265 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _150_1265))
in (

let _58_3022 = (FStar_Syntax_Util.type_u ())
in (match (_58_3022) with
| (t_type, u) -> begin
(

let _58_3023 = (let _150_1266 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _150_1266))
in (

let t_tc = (let _150_1267 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _150_1267))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _150_1268 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((_150_1268), (FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps), (k), (mutuals), (data), (quals), (r)))), (u), (guard))))))))
end)))
end))
end))
end))
end))
end))))
end
| _58_3030 -> begin
(FStar_All.failwith "impossible")
end))
in (

let positive_if_pure = (fun _58_3032 l -> ())
in (

let tc_data = (fun env tcs _58_7 -> (match (_58_7) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let _58_3049 = ()
in (

let _58_3084 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _58_3053 -> (match (_58_3053) with
| (se, u_tc) -> begin
if (let _150_1281 = (let _150_1280 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _150_1280))
in (FStar_Ident.lid_equals tc_lid _150_1281)) then begin
(

let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_3055, _58_3057, tps, _58_3060, _58_3062, _58_3064, _58_3066, _58_3068) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _58_3074 -> (match (_58_3074) with
| (x, _58_3073) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
end
| _58_3076 -> begin
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
in (match (_58_3084) with
| (tps, u_tc) -> begin
(

let _58_3104 = (match ((let _150_1283 = (FStar_Syntax_Subst.compress t)
in _150_1283.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _58_3092 = (FStar_Util.first_N ntps bs)
in (match (_58_3092) with
| (_58_3090, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res)))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _58_3098 -> (match (_58_3098) with
| (x, _58_3097) -> begin
FStar_Syntax_Syntax.DB ((((ntps - (1 + i))), (x)))
end))))
in (let _150_1286 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _150_1286))))
end))
end
| _58_3101 -> begin
(([]), (t))
end)
in (match (_58_3104) with
| (arguments, result) -> begin
(

let _58_3105 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1289 = (FStar_Syntax_Print.lid_to_string c)
in (let _150_1288 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _150_1287 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _150_1289 _150_1288 _150_1287))))
end else begin
()
end
in (

let _58_3110 = (tc_tparams env arguments)
in (match (_58_3110) with
| (arguments, env', us) -> begin
(

let _58_3114 = (tc_trivial_guard env' result)
in (match (_58_3114) with
| (result, _58_3113) -> begin
(

let _58_3118 = (FStar_Syntax_Util.head_and_args result)
in (match (_58_3118) with
| (head, _58_3117) -> begin
(

let _58_3123 = (match ((let _150_1290 = (FStar_Syntax_Subst.compress head)
in _150_1290.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _58_3122 -> begin
(let _150_1295 = (let _150_1294 = (let _150_1293 = (let _150_1292 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _150_1291 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _150_1292 _150_1291)))
in ((_150_1293), (r)))
in FStar_Syntax_Syntax.Error (_150_1294))
in (Prims.raise _150_1295))
end)
in (

let g = (FStar_List.fold_left2 (fun g _58_3129 u_x -> (match (_58_3129) with
| (x, _58_3128) -> begin
(

let _58_3131 = ()
in (let _150_1299 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _150_1299)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _150_1303 = (let _150_1301 = (FStar_All.pipe_right tps (FStar_List.map (fun _58_3137 -> (match (_58_3137) with
| (x, _58_3136) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append _150_1301 arguments))
in (let _150_1302 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _150_1303 _150_1302)))
in ((FStar_Syntax_Syntax.Sig_datacon (((c), ([]), (t), (tc_lid), (ntps), (quals), ([]), (r)))), (g)))))
end))
end))
end)))
end))
end)))
end
| _58_3140 -> begin
(FStar_All.failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let _58_3146 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _58_8 -> (match (_58_8) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_3150, _58_3152, tps, k, _58_3156, _58_3158, _58_3160, _58_3162) -> begin
(let _150_1314 = (let _150_1313 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _150_1313))
in (FStar_Syntax_Syntax.null_binder _150_1314))
end
| _58_3166 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _58_9 -> (match (_58_9) with
| FStar_Syntax_Syntax.Sig_datacon (_58_3170, _58_3172, t, _58_3175, _58_3177, _58_3179, _58_3181, _58_3183) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _58_3187 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let t = (let _150_1316 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _150_1316))
in (

let _58_3190 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1317 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _150_1317))
end else begin
()
end
in (

let _58_3194 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_58_3194) with
| (uvs, t) -> begin
(

let _58_3196 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1321 = (let _150_1319 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _150_1319 (FStar_String.concat ", ")))
in (let _150_1320 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _150_1321 _150_1320)))
end else begin
()
end
in (

let _58_3200 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_58_3200) with
| (uvs, t) -> begin
(

let _58_3204 = (FStar_Syntax_Util.arrow_formals t)
in (match (_58_3204) with
| (args, _58_3203) -> begin
(

let _58_3207 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_58_3207) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _58_3211 se -> (match (_58_3211) with
| (x, _58_3210) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _58_3215, tps, _58_3218, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let _58_3241 = (match ((let _150_1324 = (FStar_Syntax_Subst.compress ty)
in _150_1324.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _58_3232 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_58_3232) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _58_3235 -> begin
(let _150_1325 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) _150_1325 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps), (t)))
end))
end
| _58_3238 -> begin
(([]), (ty))
end)
in (match (_58_3241) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs), (tps), (t), (mutuals), (datas), (quals), (r)))
end)))
end
| _58_3243 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| _58_3247 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _150_1326 -> FStar_Syntax_Syntax.U_name (_150_1326))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _58_10 -> (match (_58_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _58_3252, _58_3254, _58_3256, _58_3258, _58_3260, _58_3262, _58_3264) -> begin
((tc), (uvs_universes))
end
| _58_3268 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _58_3273 d -> (match (_58_3273) with
| (t, _58_3272) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _58_3277, _58_3279, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _150_1330 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _150_1330 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon (((l), (uvs), (ty), (tc), (ntps), (quals), (mutuals), (r))))
end
| _58_3289 -> begin
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

let _58_3299 = (FStar_All.pipe_right ses (FStar_List.partition (fun _58_11 -> (match (_58_11) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_3293) -> begin
true
end
| _58_3296 -> begin
false
end))))
in (match (_58_3299) with
| (tys, datas) -> begin
(

let _58_3306 = if (FStar_All.pipe_right datas (FStar_Util.for_some (fun _58_12 -> (match (_58_12) with
| FStar_Syntax_Syntax.Sig_datacon (_58_3302) -> begin
false
end
| _58_3305 -> begin
true
end)))) then begin
(let _150_1335 = (let _150_1334 = (let _150_1333 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (_150_1333)))
in FStar_Syntax_Syntax.Error (_150_1334))
in (Prims.raise _150_1335))
end else begin
()
end
in (

let env0 = env
in (

let _58_3325 = (FStar_List.fold_right (fun tc _58_3313 -> (match (_58_3313) with
| (env, all_tcs, g) -> begin
(

let _58_3318 = (tc_tycon env tc)
in (match (_58_3318) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (

let _58_3320 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1338 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _150_1338))
end else begin
()
end
in (let _150_1340 = (let _150_1339 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g _150_1339))
in ((env), ((((tc), (tc_u)))::all_tcs), (_150_1340)))))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_58_3325) with
| (env, tcs, g) -> begin
(

let _58_3335 = (FStar_List.fold_right (fun se _58_3329 -> (match (_58_3329) with
| (datas, g) -> begin
(

let _58_3332 = (tc_data env tcs se)
in (match (_58_3332) with
| (data, g') -> begin
(let _150_1343 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((data)::datas), (_150_1343)))
end))
end)) datas (([]), (g)))
in (match (_58_3335) with
| (datas, g) -> begin
(

let _58_3338 = (let _150_1344 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _150_1344 datas))
in (match (_58_3338) with
| (tcs, datas) -> begin
(

let sig_bndle = (let _150_1346 = (let _150_1345 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_150_1345)))
in FStar_Syntax_Syntax.Sig_bundle (_150_1346))
in (

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (_58_3343, _58_3345, t, _58_3348, _58_3350, _58_3352, _58_3354, _58_3356) -> begin
t
end
| _58_3360 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let dr = FStar_Range.dummyRange
in (

let haseq_ty = (fun usubst us acc ty -> (

let _58_3387 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _58_3369, bs, t, _58_3373, d_lids, _58_3376, _58_3378) -> begin
((lid), (bs), (t), (d_lids))
end
| _58_3382 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_58_3387) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _150_1357 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _150_1357 t))
in (

let _58_3392 = (FStar_Syntax_Subst.open_term bs t)
in (match (_58_3392) with
| (bs, t) -> begin
(

let ibs = (match ((let _150_1358 = (FStar_Syntax_Subst.compress t)
in _150_1358.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _58_3395) -> begin
ibs
end
| _58_3399 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _150_1361 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _150_1360 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_1361 _150_1360)))
in (

let ind = (let _150_1364 = (FStar_List.map (fun _58_3406 -> (match (_58_3406) with
| (bv, aq) -> begin
(let _150_1363 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_150_1363), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _150_1364 None dr))
in (

let ind = (let _150_1367 = (FStar_List.map (fun _58_3410 -> (match (_58_3410) with
| (bv, aq) -> begin
(let _150_1366 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_150_1366), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _150_1367 None dr))
in (

let haseq_ind = (let _150_1369 = (let _150_1368 = (FStar_Syntax_Syntax.as_arg ind)
in (_150_1368)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _150_1369 None dr))
in (

let bs' = (FStar_List.filter (fun b -> (

let _58_3421 = acc
in (match (_58_3421) with
| (_58_3415, en, _58_3418, _58_3420) -> begin
(

let opt = (let _150_1372 = (let _150_1371 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _150_1371))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort _150_1372 false))
in (match (opt) with
| None -> begin
false
end
| Some (_58_3425) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (let _150_1378 = (let _150_1377 = (let _150_1376 = (let _150_1375 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg _150_1375))
in (_150_1376)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _150_1377 None dr))
in (FStar_Syntax_Util.mk_conj t _150_1378))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let _58_3432 = fml
in (let _150_1384 = (let _150_1383 = (let _150_1382 = (let _150_1381 = (let _150_1380 = (let _150_1379 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_150_1379)::[])
in (_150_1380)::[])
in FStar_Syntax_Syntax.Meta_pattern (_150_1381))
in ((fml), (_150_1382)))
in FStar_Syntax_Syntax.Tm_meta (_150_1383))
in {FStar_Syntax_Syntax.n = _150_1384; FStar_Syntax_Syntax.tk = _58_3432.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _58_3432.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_3432.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _150_1390 = (let _150_1389 = (let _150_1388 = (let _150_1387 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _150_1387 None))
in (FStar_Syntax_Syntax.as_arg _150_1388))
in (_150_1389)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _150_1390 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _150_1396 = (let _150_1395 = (let _150_1394 = (let _150_1393 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _150_1393 None))
in (FStar_Syntax_Syntax.as_arg _150_1394))
in (_150_1395)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _150_1396 None dr))) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let _58_3446 = acc
in (match (_58_3446) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_58_3451, _58_3453, _58_3455, t_lid, _58_3458, _58_3460, _58_3462, _58_3464) -> begin
(t_lid = lid)
end
| _58_3468 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let haseq_data = (fun acc data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (match ((let _150_1402 = (FStar_Syntax_Subst.compress dt)
in _150_1402.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _58_3477) -> begin
(

let dbs = (let _150_1403 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _150_1403))
in (

let dbs = (let _150_1404 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _150_1404 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (let _150_1409 = (let _150_1408 = (let _150_1407 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_150_1407)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _150_1408 None dr))
in (FStar_Syntax_Util.mk_conj t _150_1409))) FStar_Syntax_Util.t_true dbs)
in (

let _58_3488 = acc
in (match (_58_3488) with
| (env, cond') -> begin
(let _150_1411 = (FStar_TypeChecker_Env.push_binders env dbs)
in (let _150_1410 = (FStar_Syntax_Util.mk_conj cond' cond)
in ((_150_1411), (_150_1410))))
end))))))
end
| _58_3490 -> begin
acc
end))))
in (

let _58_3493 = (FStar_List.fold_left haseq_data ((env), (FStar_Syntax_Util.t_true)) t_datas)
in (match (_58_3493) with
| (env, cond) -> begin
(

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (let _150_1413 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _150_1412 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env), (_150_1413), (_150_1412)))))
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
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_3499, us, _58_3502, _58_3504, _58_3506, _58_3508, _58_3510, _58_3512) -> begin
us
end
| _58_3516 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let _58_3520 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_58_3520) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _58_3522 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _58_3524 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let _58_3531 = (FStar_List.fold_left (haseq_ty usubst us) (([]), (env), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (_58_3531) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let _58_3536 = (tc_trivial_guard env phi)
in (match (_58_3536) with
| (phi, _58_3535) -> begin
(

let _58_3537 = if (FStar_TypeChecker_Env.should_verify env) then begin
(let _150_1415 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _150_1415))
end else begin
()
end
in (

let _58_3539 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env0 us)
in (

let ses = (FStar_List.fold_left (fun l _58_3545 -> (match (_58_3545) with
| (lid, fml) -> begin
(

let se = (tc_assume env lid fml [] dr)
in (FStar_List.append l ((se)::[])))
end)) [] axioms)
in (let _150_1420 = (let _150_1419 = (let _150_1418 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_150_1418)))
in FStar_Syntax_Syntax.Sig_bundle (_150_1419))
in (_150_1420)::ses)))))
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
in (let _150_1423 = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (_150_1423)))))
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

let _58_3588 = (set_options FStar_Options.Set o)
in (((se)::[]), (env)))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(

let _58_3592 = (let _150_1430 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _150_1430 Prims.ignore))
in (

let _58_3597 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _58_3599 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (((se)::[]), (env)))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(

let ne = (tc_eff_decl env ne ForFree)
in (

let se = FStar_Syntax_Syntax.Sig_new_effect (((ne), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env)))))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(

let ne = (tc_eff_decl env ne NotForFree)
in (

let se = FStar_Syntax_Syntax.Sig_new_effect (((ne), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (

let _58_3622 = (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun _58_3617 a -> (match (_58_3617) with
| (env, ses) -> begin
(

let se_let = (FStar_Syntax_Util.action_as_lb a)
in (let _150_1433 = (FStar_TypeChecker_Env.push_sigelt env se_let)
in ((_150_1433), ((se_let)::ses))))
end)) ((env), ((se)::[]))))
in (match (_58_3622) with
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

let _58_3631 = (let _150_1434 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _150_1434))
in (match (_58_3631) with
| (a, wp_a_src) -> begin
(

let _58_3634 = (let _150_1435 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _150_1435))
in (match (_58_3634) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _150_1439 = (let _150_1438 = (let _150_1437 = (let _150_1436 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (_150_1436)))
in FStar_Syntax_Syntax.NT (_150_1437))
in (_150_1438)::[])
in (FStar_Syntax_Subst.subst _150_1439 wp_b_tgt))
in (

let expected_k = (let _150_1444 = (let _150_1442 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1441 = (let _150_1440 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_150_1440)::[])
in (_150_1442)::_150_1441))
in (let _150_1443 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _150_1444 _150_1443)))
in (

let lift_wp = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift_wp) expected_k)
in (

let repr_type = (fun eff_name a wp -> (

let no_reify = (fun l -> (let _150_1456 = (let _150_1455 = (let _150_1454 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _150_1453 = (FStar_TypeChecker_Env.get_range env)
in ((_150_1454), (_150_1453))))
in FStar_Syntax_Syntax.Error (_150_1455))
in (Prims.raise _150_1456)))
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
(let _150_1463 = (let _150_1461 = (let _150_1460 = (let _150_1459 = (FStar_Syntax_Syntax.as_arg a)
in (let _150_1458 = (let _150_1457 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_1457)::[])
in (_150_1459)::_150_1458))
in ((repr), (_150_1460)))
in FStar_Syntax_Syntax.Tm_app (_150_1461))
in (let _150_1462 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _150_1463 None _150_1462)))
end)
end)))
in (

let lift = (match (sub.FStar_Syntax_Syntax.lift) with
| None -> begin
None
end
| Some (_58_3650, lift) -> begin
(

let _58_3656 = (let _150_1464 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _150_1464))
in (match (_58_3656) with
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

let lift_wp_a = (let _150_1471 = (let _150_1469 = (let _150_1468 = (let _150_1467 = (FStar_Syntax_Syntax.as_arg a_typ)
in (let _150_1466 = (let _150_1465 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (_150_1465)::[])
in (_150_1467)::_150_1466))
in (((Prims.snd sub.FStar_Syntax_Syntax.lift_wp)), (_150_1468)))
in FStar_Syntax_Syntax.Tm_app (_150_1469))
in (let _150_1470 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _150_1471 None _150_1470)))
in (repr_type sub.FStar_Syntax_Syntax.target a_typ lift_wp_a))
in (

let expected_k = (let _150_1478 = (let _150_1476 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1475 = (let _150_1474 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (let _150_1473 = (let _150_1472 = (FStar_Syntax_Syntax.null_binder repr_f)
in (_150_1472)::[])
in (_150_1474)::_150_1473))
in (_150_1476)::_150_1475))
in (let _150_1477 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow _150_1478 _150_1477)))
in (

let _58_3669 = (tc_tot_or_gtot_term env expected_k)
in (match (_58_3669) with
| (expected_k, _58_3666, _58_3668) -> begin
(

let lift = (check_and_gen env lift expected_k)
in Some (lift))
end))))))))
end))
end)
in (

let sub = (

let _58_3672 = sub
in {FStar_Syntax_Syntax.source = _58_3672.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _58_3672.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift})
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

let _58_3685 = ()
in (

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _58_3691 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_58_3691) with
| (tps, c) -> begin
(

let _58_3695 = (tc_tparams env tps)
in (match (_58_3695) with
| (tps, env, us) -> begin
(

let _58_3699 = (tc_comp env c)
in (match (_58_3699) with
| (c, u, g) -> begin
(

let _58_3700 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let _58_3706 = (let _150_1479 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _150_1479))
in (match (_58_3706) with
| (uvs, t) -> begin
(

let _58_3725 = (match ((let _150_1481 = (let _150_1480 = (FStar_Syntax_Subst.compress t)
in _150_1480.FStar_Syntax_Syntax.n)
in ((tps), (_150_1481)))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_58_3709, c)) -> begin
(([]), (c))
end
| (_58_3715, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
((tps), (c))
end
| _58_3722 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_58_3725) with
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

let _58_3736 = ()
in (

let _58_3740 = (let _150_1483 = (let _150_1482 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _150_1482))
in (check_and_gen env t _150_1483))
in (match (_58_3740) with
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

let _58_3760 = (tc_term env e)
in (match (_58_3760) with
| (e, c, g1) -> begin
(

let _58_3765 = (let _150_1487 = (let _150_1484 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_150_1484))
in (let _150_1486 = (let _150_1485 = (c.FStar_Syntax_Syntax.comp ())
in ((e), (_150_1485)))
in (check_expected_effect env _150_1487 _150_1486)))
in (match (_58_3765) with
| (e, _58_3763, g) -> begin
(

let _58_3766 = (let _150_1488 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _150_1488))
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
(let _150_1500 = (let _150_1499 = (let _150_1498 = (let _150_1497 = (FStar_Syntax_Print.lid_to_string l)
in (let _150_1496 = (FStar_Syntax_Print.quals_to_string q)
in (let _150_1495 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _150_1497 _150_1496 _150_1495))))
in ((_150_1498), (r)))
in FStar_Syntax_Syntax.Error (_150_1499))
in (Prims.raise _150_1500))
end
end))
in (

let _58_3810 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _58_3787 lb -> (match (_58_3787) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _58_3806 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
((gen), (lb), (quals_opt))
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (

let _58_3801 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _58_3800 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _150_1503 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Syntax_Const.effect_ALL_lid), (tval), (lb.FStar_Syntax_Syntax.lbdef)))
in ((false), (_150_1503), (quals_opt)))))
end)
in (match (_58_3806) with
| (gen, lb, quals_opt) -> begin
((gen), ((lb)::lbs), (quals_opt))
end)))
end)) ((true), ([]), (if (quals = []) then begin
None
end else begin
Some (quals)
end))))
in (match (_58_3810) with
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
| _58_3819 -> begin
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

let e = (let _150_1507 = (let _150_1506 = (let _150_1505 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((((Prims.fst lbs)), (lbs'))), (_150_1505)))
in FStar_Syntax_Syntax.Tm_let (_150_1506))
in (FStar_Syntax_Syntax.mk _150_1507 None r))
in (

let _58_3853 = (match ((tc_maybe_toplevel_term (

let _58_3823 = env
in {FStar_TypeChecker_Env.solver = _58_3823.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_3823.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_3823.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_3823.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_3823.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_3823.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_3823.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_3823.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_3823.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_3823.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_3823.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _58_3823.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _58_3823.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_3823.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_3823.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_3823.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_3823.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_3823.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_3823.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_3823.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _58_3830; FStar_Syntax_Syntax.pos = _58_3828; FStar_Syntax_Syntax.vars = _58_3826}, _58_3837, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_58_3841, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _58_3847 -> begin
quals
end)
in ((FStar_Syntax_Syntax.Sig_let (((lbs), (r), (lids), (quals)))), (lbs)))
end
| _58_3850 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_58_3853) with
| (se, lbs) -> begin
(

let _58_3859 = if (log env) then begin
(let _150_1515 = (let _150_1514 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _150_1511 = (let _150_1510 = (let _150_1509 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _150_1509.FStar_Syntax_Syntax.fv_name)
in _150_1510.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _150_1511))) with
| None -> begin
true
end
| _58_3857 -> begin
false
end)
in if should_log then begin
(let _150_1513 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _150_1512 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _150_1513 _150_1512)))
end else begin
""
end))))
in (FStar_All.pipe_right _150_1514 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _150_1515))
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
| _58_3869 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _58_3879 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_58_3881) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _58_3892, _58_3894) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _58_3900 -> (match (_58_3900) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _58_3906, _58_3908, quals, r) -> begin
(

let dec = (let _150_1531 = (let _150_1530 = (let _150_1529 = (let _150_1528 = (let _150_1527 = (FStar_Syntax_Syntax.mk_Total t)
in ((bs), (_150_1527)))
in FStar_Syntax_Syntax.Tm_arrow (_150_1528))
in (FStar_Syntax_Syntax.mk _150_1529 None r))
in ((l), (us), (_150_1530), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_150_1531))
in (((dec)::out), (hidden)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _58_3918, _58_3920, _58_3922, _58_3924, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r)))
in (((dec)::out), ((l)::hidden)))
end
| _58_3930 -> begin
((out), (hidden))
end)
end)) ses (([]), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end
| FStar_Syntax_Syntax.Sig_assume (_58_3932, _58_3934, quals, _58_3937) -> begin
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
| _58_3956 -> begin
false
end)))) then begin
(((se)::[]), (hidden))
end else begin
(([]), (hidden))
end
end
end
| FStar_Syntax_Syntax.Sig_main (_58_3958) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _58_3977, _58_3979, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
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
(let _150_1538 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _150_1537 = (let _150_1536 = (let _150_1535 = (let _150_1534 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _150_1534.FStar_Syntax_Syntax.fv_name)
in _150_1535.FStar_Syntax_Syntax.v)
in ((_150_1536), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_150_1537)))))
in ((_150_1538), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let _58_4026 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _58_3999 se -> (match (_58_3999) with
| (ses, exports, env, hidden) -> begin
(

let _58_4001 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1545 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _150_1545))
end else begin
()
end
in (

let _58_4005 = (tc_decl env se)
in (match (_58_4005) with
| (ses', env) -> begin
(

let _58_4008 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _150_1550 = (FStar_List.fold_left (fun s se -> (let _150_1549 = (let _150_1548 = (FStar_Syntax_Print.sigelt_to_string se)
in (Prims.strcat s _150_1548))
in (Prims.strcat _150_1549 "\n"))) "" ses')
in (FStar_Util.print1 "Checked: %s\n" _150_1550))
end else begin
()
end
in (

let _58_4011 = (FStar_List.iter (fun se -> (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)) ses')
in (

let _58_4020 = (FStar_List.fold_left (fun _58_4015 se -> (match (_58_4015) with
| (le, lh) -> begin
(

let tup = (for_export hidden se)
in (((FStar_List.rev_append (Prims.fst tup) le)), ((FStar_List.rev_append (Prims.snd tup) lh))))
end)) (([]), ([])) ses')
in (match (_58_4020) with
| (exported, hidden) -> begin
(((FStar_List.rev_append ses' ses)), (((FStar_List.rev_append exported []))::exports), (env), (hidden))
end))))
end)))
end)) (([]), ([]), (env), ([]))))
in (match (_58_4026) with
| (ses, exports, env, _58_4025) -> begin
(let _150_1554 = (FStar_All.pipe_right (FStar_List.rev_append exports []) FStar_List.flatten)
in (((FStar_List.rev_append ses [])), (_150_1554), (env)))
end)))


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

let _58_4031 = env
in (let _150_1559 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _58_4031.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_4031.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_4031.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_4031.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_4031.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_4031.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_4031.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_4031.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_4031.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_4031.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_4031.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_4031.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_4031.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_4031.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_4031.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_4031.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _150_1559; FStar_TypeChecker_Env.lax = _58_4031.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_4031.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_4031.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_4031.FStar_TypeChecker_Env.use_bv_sorts}))
in (

let _58_4034 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let _58_4040 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_58_4040) with
| (ses, exports, env) -> begin
(((

let _58_4041 = modul
in {FStar_Syntax_Syntax.name = _58_4041.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _58_4041.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _58_4041.FStar_Syntax_Syntax.is_interface})), (exports), (env))
end))))))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let _58_4049 = (tc_decls env decls)
in (match (_58_4049) with
| (ses, exports, env) -> begin
(

let modul = (

let _58_4050 = modul
in {FStar_Syntax_Syntax.name = _58_4050.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _58_4050.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _58_4050.FStar_Syntax_Syntax.is_interface})
in ((modul), (exports), (env)))
end)))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul = (

let _58_4056 = modul
in {FStar_Syntax_Syntax.name = _58_4056.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _58_4056.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in (

let _58_4066 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(

let _58_4060 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let _58_4062 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (

let _58_4064 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _150_1572 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _150_1572 Prims.ignore)))))
end else begin
()
end
in ((modul), (env))))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let _58_4073 = (tc_partial_modul env modul)
in (match (_58_4073) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _58_4076 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _150_1581 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _150_1581))
end else begin
()
end
in (

let env = (

let _58_4078 = env
in {FStar_TypeChecker_Env.solver = _58_4078.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_4078.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_4078.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_4078.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_4078.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_4078.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_4078.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_4078.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_4078.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_4078.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_4078.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_4078.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_4078.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_4078.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_4078.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_4078.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_4078.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_4078.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_4078.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_4078.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_4078.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _58_4094 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _58_4086) -> begin
(let _150_1586 = (let _150_1585 = (let _150_1584 = (FStar_TypeChecker_Env.get_range env)
in (((Prims.strcat "Implicit argument: " msg)), (_150_1584)))
in FStar_Syntax_Syntax.Error (_150_1585))
in (Prims.raise _150_1586))
end
in (match (_58_4094) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end else begin
(let _150_1591 = (let _150_1590 = (let _150_1589 = (let _150_1587 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _150_1587))
in (let _150_1588 = (FStar_TypeChecker_Env.get_range env)
in ((_150_1589), (_150_1588))))
in FStar_Syntax_Syntax.Error (_150_1590))
in (Prims.raise _150_1591))
end
end)))))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
FStar_Syntax_Syntax.U_zero
end else begin
(

let _58_4097 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_1596 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print1 "universe_of %s\n" _150_1596))
end else begin
()
end
in (

let _58_4102 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_4102) with
| (env, _58_4101) -> begin
(

let env = (

let _58_4103 = env
in {FStar_TypeChecker_Env.solver = _58_4103.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_4103.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_4103.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_4103.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_4103.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_4103.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_4103.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_4103.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_4103.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_4103.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_4103.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_4103.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_4103.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_4103.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_4103.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_4103.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_4103.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _58_4103.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_4103.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true})
in (

let fail = (fun e t -> (let _150_1606 = (let _150_1605 = (let _150_1604 = (let _150_1602 = (FStar_Syntax_Print.term_to_string e)
in (let _150_1601 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" _150_1602 _150_1601)))
in (let _150_1603 = (FStar_TypeChecker_Env.get_range env)
in ((_150_1604), (_150_1603))))
in FStar_Syntax_Syntax.Error (_150_1605))
in (Prims.raise _150_1606)))
in (

let ok = (fun u -> (

let _58_4111 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_1610 = (FStar_Syntax_Print.tag_of_term e)
in (let _150_1609 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.print2 "<end> universe_of %s is %s\n" _150_1610 _150_1609)))
end else begin
()
end
in u))
in (

let universe_of_type = (fun e t -> (match ((let _150_1615 = (FStar_Syntax_Util.unrefine t)
in _150_1615.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(ok u)
end
| _58_4119 -> begin
(fail e t)
end))
in (

let _58_4122 = (FStar_Syntax_Util.head_and_args e)
in (match (_58_4122) with
| (head, args) -> begin
(match ((let _150_1616 = (FStar_Syntax_Subst.compress head)
in _150_1616.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_58_4124, t) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _150_1617 = (FStar_Syntax_Subst.compress t)
in _150_1617.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_4130, t) -> begin
(universe_of_type e (FStar_Syntax_Util.comp_result t))
end
| _58_4135 -> begin
(universe_of_type e t)
end))
end
| _58_4137 -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoInline)::[]) env e)
in (

let _58_4150 = (tc_term env e)
in (match (_58_4150) with
| (_58_4140, {FStar_Syntax_Syntax.eff_name = _58_4147; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_4144; FStar_Syntax_Syntax.comp = _58_4142}, g) -> begin
(

let _58_4151 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (let _150_1619 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (FStar_All.pipe_left (universe_of_type e) _150_1619)))
end)))
end)
end))))))
end)))
end)


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

let _58_4155 = if (FStar_Options.debug_any ()) then begin
(let _150_1624 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _150_1624))
end else begin
()
end
in (

let _58_4159 = (tc_modul env m)
in (match (_58_4159) with
| (m, env) -> begin
(

let _58_4160 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _150_1625 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _150_1625))
end else begin
()
end
in ((m), (env)))
end))))




