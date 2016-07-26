
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


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (not ((let _148_5 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _148_5))))))


let rng : FStar_TypeChecker_Env.env  ->  FStar_Range.range = (fun env -> (FStar_TypeChecker_Env.get_range env))


let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _57_19 = env
in {FStar_TypeChecker_Env.solver = _57_19.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_19.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_19.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_19.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_19.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_19.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_19.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_19.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_19.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _57_19.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_19.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_19.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_19.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_19.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_19.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_19.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_19.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_19.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_19.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_19.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_19.FStar_TypeChecker_Env.use_bv_sorts}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _57_22 = env
in {FStar_TypeChecker_Env.solver = _57_22.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_22.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_22.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_22.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_22.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_22.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_22.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_22.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_22.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _57_22.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_22.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_22.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_22.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_22.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_22.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_22.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_22.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_22.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_22.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_22.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_22.FStar_TypeChecker_Env.use_bv_sorts}))


let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (

let r = if (tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
v.FStar_Syntax_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos tl.FStar_Syntax_Syntax.pos)
end
in (let _148_19 = (let _148_18 = (FStar_Syntax_Syntax.as_arg v)
in (let _148_17 = (let _148_16 = (FStar_Syntax_Syntax.as_arg tl)
in (_148_16)::[])
in (_148_18)::_148_17))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _148_19 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _57_1 -> (match (_57_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _57_32 -> begin
false
end))


let steps : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Normalize.step Prims.list = (fun env -> if (FStar_TypeChecker_Env.should_verify env) then begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::[]
end else begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]
end)


let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Beta)::[]) env t))


let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _148_32 = (steps env)
in (FStar_TypeChecker_Normalize.normalize _148_32 env t)))


let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _148_37 = (steps env)
in (FStar_TypeChecker_Normalize.normalize_comp _148_37 env c)))


let check_no_escape : FStar_Syntax_Syntax.term Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun head_opt env fvs kt -> (

let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
()
end
| _57_49 -> begin
(

let fvs' = (let _148_50 = if try_norm then begin
(norm env t)
end else begin
t
end
in (FStar_Syntax_Free.names _148_50))
in (match ((FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)) with
| None -> begin
()
end
| Some (x) -> begin
if (not (try_norm)) then begin
(aux true t)
end else begin
(

let fail = (fun _57_56 -> (match (()) with
| () -> begin
(

let msg = (match (head_opt) with
| None -> begin
(let _148_54 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _148_54))
end
| Some (head) -> begin
(let _148_56 = (FStar_Syntax_Print.bv_to_string x)
in (let _148_55 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _148_56 _148_55)))
end)
in (let _148_59 = (let _148_58 = (let _148_57 = (FStar_TypeChecker_Env.get_range env)
in (msg, _148_57))
in FStar_Syntax_Syntax.Error (_148_58))
in (Prims.raise _148_59)))
end))
in (

let s = (let _148_61 = (let _148_60 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _148_60))
in (FStar_TypeChecker_Util.new_uvar env _148_61))
in (match ((FStar_TypeChecker_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g)
end
| _57_65 -> begin
(fail ())
end)))
end
end))
end))
in (aux false kt)))


let push_binding = (fun env b -> (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))


let maybe_make_subst = (fun _57_2 -> (match (_57_2) with
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Syntax_Syntax.NT ((x, e)))::[]
end
| _57_75 -> begin
[]
end))


let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.subst_t = (fun s b v -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
s
end else begin
(FStar_Syntax_Syntax.NT (((Prims.fst b), v)))::s
end)


let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (

let _57_81 = lc
in {FStar_Syntax_Syntax.eff_name = _57_81.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _57_81.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _57_83 -> (match (()) with
| () -> begin
(let _148_76 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _148_76 t))
end))}))


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let should_return = (fun t -> (match ((let _148_87 = (FStar_Syntax_Subst.compress t)
in _148_87.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_91, c) -> begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(

let t = (FStar_All.pipe_left FStar_Syntax_Util.unrefine (FStar_Syntax_Util.comp_result c))
in (match ((let _148_88 = (FStar_Syntax_Subst.compress t)
in _148_88.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (_57_99) -> begin
false
end
| _57_102 -> begin
true
end))
end else begin
false
end
end
| _57_104 -> begin
true
end))
in (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _148_89 = if ((not ((should_return t))) || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _148_89))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _57_132 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, guard)
end
| Some (t') -> begin
(

let _57_114 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_91 = (FStar_Syntax_Print.term_to_string t)
in (let _148_90 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _148_91 _148_90)))
end else begin
()
end
in (

let _57_118 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_57_118) with
| (e, lc) -> begin
(

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _57_122 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_57_122) with
| (e, g) -> begin
(

let _57_123 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_93 = (FStar_Syntax_Print.term_to_string t)
in (let _148_92 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _148_93 _148_92)))
end else begin
()
end
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let _57_128 = (let _148_99 = (FStar_All.pipe_left (fun _148_98 -> Some (_148_98)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _148_99 env e lc g))
in (match (_57_128) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))))
end)))
end)))
end)
in (match (_57_132) with
| (e, lc, g) -> begin
(

let _57_133 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_100 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _148_100))
end else begin
()
end
in (e, lc, g))
end))))))


let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (t) -> begin
(

let _57_143 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_57_143) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _57_148 -> (match (_57_148) with
| (e, c) -> begin
(

let expected_c_opt = (match (copt) with
| Some (_57_150) -> begin
copt
end
| None -> begin
if ((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Syntax_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) then begin
(let _148_113 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (_148_113))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
if (FStar_Syntax_Util.is_pure_comp c) then begin
(let _148_114 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (_148_114))
end else begin
if (FStar_Syntax_Util.is_pure_or_ghost_comp c) then begin
(let _148_115 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (_148_115))
end else begin
None
end
end
end
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _148_116 = (norm_c env c)
in (e, _148_116, FStar_TypeChecker_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(

let _57_157 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_119 = (FStar_Syntax_Print.term_to_string e)
in (let _148_118 = (FStar_Syntax_Print.comp_to_string c)
in (let _148_117 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _148_119 _148_118 _148_117))))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _57_160 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_122 = (FStar_Syntax_Print.term_to_string e)
in (let _148_121 = (FStar_Syntax_Print.comp_to_string c)
in (let _148_120 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _148_122 _148_121 _148_120))))
end else begin
()
end
in (

let _57_166 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_57_166) with
| (e, _57_164, g) -> begin
(

let g = (let _148_123 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _148_123 "could not prove post-condition" g))
in (

let _57_168 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_125 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _148_124 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _148_125 _148_124)))
end else begin
()
end
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e (FStar_Syntax_Util.comp_effect_name c) (FStar_Syntax_Util.comp_effect_name expected_c))
in (e, expected_c, g))))
end)))))
end))
end))


let no_logical_guard = (fun env _57_175 -> (match (_57_175) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
(te, kt, f)
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _148_131 = (let _148_130 = (let _148_129 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _148_128 = (FStar_TypeChecker_Env.get_range env)
in (_148_129, _148_128)))
in FStar_Syntax_Syntax.Error (_148_130))
in (Prims.raise _148_131))
end)
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _148_134 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _148_134))
end))


let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _57_199; FStar_Syntax_Syntax.result_typ = _57_197; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, _57_191))::[]; FStar_Syntax_Syntax.flags = _57_188}) -> begin
(

let pat_vars = (FStar_Syntax_Free.names pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _57_206 -> (match (_57_206) with
| (b, _57_205) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _57_210) -> begin
(let _148_141 = (let _148_140 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _148_140))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _148_141))
end))
end
| _57_214 -> begin
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

let _57_221 = env
in {FStar_TypeChecker_Env.solver = _57_221.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_221.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_221.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_221.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_221.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_221.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_221.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_221.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_221.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_221.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_221.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_221.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_221.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_221.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_221.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_221.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_221.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_221.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_221.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_221.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_221.FStar_TypeChecker_Env.use_bv_sorts})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _57_233 -> (match (_57_233) with
| (b, _57_232) -> begin
(

let t = (let _148_155 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _148_155))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _57_242 -> begin
(let _148_156 = (FStar_Syntax_Syntax.bv_to_name b)
in (_148_156)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let _57_248 = (FStar_Syntax_Util.head_and_args dec)
in (match (_57_248) with
| (head, _57_247) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _57_252 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _57_3 -> (match (_57_3) with
| FStar_Syntax_Syntax.DECREASES (_57_256) -> begin
true
end
| _57_259 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _57_264 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| _57_269 -> begin
(mk_lex_list xs)
end))
end)))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun _57_274 -> (match (_57_274) with
| (l, t) -> begin
(match ((let _148_162 = (FStar_Syntax_Subst.compress t)
in _148_162.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _57_281 -> (match (_57_281) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _148_166 = (let _148_165 = (let _148_164 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_148_164))
in (FStar_Syntax_Syntax.new_bv _148_165 x.FStar_Syntax_Syntax.sort))
in (_148_166, imp))
end else begin
(x, imp)
end
end))))
in (

let _57_285 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_57_285) with
| (formals, c) -> begin
(

let dec = (decreases_clause formals c)
in (

let precedes = (let _148_170 = (let _148_169 = (FStar_Syntax_Syntax.as_arg dec)
in (let _148_168 = (let _148_167 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_148_167)::[])
in (_148_169)::_148_168))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _148_170 None r))
in (

let _57_292 = (FStar_Util.prefix formals)
in (match (_57_292) with
| (bs, (last, imp)) -> begin
(

let last = (

let _57_293 = last
in (let _148_171 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _57_293.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_293.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_171}))
in (

let refined_formals = (FStar_List.append bs (((last, imp))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (

let _57_298 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_174 = (FStar_Syntax_Print.lbname_to_string l)
in (let _148_173 = (FStar_Syntax_Print.term_to_string t)
in (let _148_172 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _148_174 _148_173 _148_172))))
end else begin
()
end
in (l, t')))))
end))))
end)))
end
| _57_301 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end)
end)


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let _57_304 = env
in {FStar_TypeChecker_Env.solver = _57_304.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_304.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_304.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_304.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_304.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_304.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_304.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_304.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_304.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_304.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_304.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_304.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_304.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_304.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_304.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_304.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_304.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_304.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_304.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_304.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_304.FStar_TypeChecker_Env.use_bv_sorts}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (

let _57_309 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_242 = (let _148_240 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _148_240))
in (let _148_241 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _148_242 _148_241)))
end else begin
()
end
in (

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_57_313) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let _57_354 = (tc_tot_or_gtot_term env e)
in (match (_57_354) with
| (e, c, g) -> begin
(

let g = (

let _57_355 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_355.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_355.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_355.FStar_TypeChecker_Env.implicits})
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let _57_365 = (FStar_Syntax_Util.type_u ())
in (match (_57_365) with
| (t, u) -> begin
(

let _57_369 = (tc_check_tot_or_gtot_term env e t)
in (match (_57_369) with
| (e, c, g) -> begin
(

let _57_376 = (

let _57_373 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_373) with
| (env, _57_372) -> begin
(tc_pats env pats)
end))
in (match (_57_376) with
| (pats, g') -> begin
(

let g' = (

let _57_377 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_377.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_377.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_377.FStar_TypeChecker_Env.implicits})
in (let _148_247 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_pattern (pats)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _148_246 = (FStar_TypeChecker_Rel.conj_guard g g')
in (_148_247, c, _148_246))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _148_248 = (FStar_Syntax_Subst.compress e)
in _148_248.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_57_386, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _57_393; FStar_Syntax_Syntax.lbtyp = _57_391; FStar_Syntax_Syntax.lbeff = _57_389; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _57_404 = (let _148_249 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _148_249 e1))
in (match (_57_404) with
| (e1, c1, g1) -> begin
(

let _57_408 = (tc_term env e2)
in (match (_57_408) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (None, c2))
in (

let e = (let _148_254 = (let _148_253 = (let _148_252 = (let _148_251 = (let _148_250 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Common.t_unit, e1))
in (_148_250)::[])
in (false, _148_251))
in (_148_252, e2))
in FStar_Syntax_Syntax.Tm_let (_148_253))
in (FStar_Syntax_Syntax.mk _148_254 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _148_255 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _148_255)))))
end))
end))
end
| _57_413 -> begin
(

let _57_417 = (tc_term env e)
in (match (_57_417) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let _57_426 = (tc_term env e)
in (match (_57_426) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, m))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _57_432) -> begin
(

let _57_438 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_438) with
| (env0, _57_437) -> begin
(

let _57_443 = (tc_comp env0 expected_c)
in (match (_57_443) with
| (expected_c, _57_441, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (

let _57_448 = (let _148_256 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term _148_256 e))
in (match (_57_448) with
| (e, c', g') -> begin
(

let _57_452 = (let _148_258 = (let _148_257 = (c'.FStar_Syntax_Syntax.comp ())
in (e, _148_257))
in (check_expected_effect env0 (Some (expected_c)) _148_258))
in (match (_57_452) with
| (e, expected_c, g'') -> begin
(let _148_261 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t_res), Some ((FStar_Syntax_Util.comp_effect_name expected_c))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _148_260 = (let _148_259 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _148_259))
in (_148_261, (FStar_Syntax_Util.lcomp_of_comp expected_c), _148_260)))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _57_457) -> begin
(

let _57_462 = (FStar_Syntax_Util.type_u ())
in (match (_57_462) with
| (k, u) -> begin
(

let _57_467 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_467) with
| (t, _57_465, f) -> begin
(

let _57_471 = (let _148_262 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _148_262 e))
in (match (_57_471) with
| (e, c, g) -> begin
(

let _57_475 = (let _148_266 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_472 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _148_266 e c f))
in (match (_57_475) with
| (c, f) -> begin
(

let _57_479 = (let _148_267 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t), Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _148_267 c))
in (match (_57_479) with
| (e, c, f2) -> begin
(let _148_269 = (let _148_268 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _148_268))
in (e, c, _148_269))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let env0 = env
in (

let env = (let _148_271 = (let _148_270 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _148_270 Prims.fst))
in (FStar_All.pipe_right _148_271 instantiate_both))
in (

let _57_486 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_273 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _148_272 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _148_273 _148_272)))
end else begin
()
end
in (

let _57_491 = (tc_term (no_inst env) head)
in (match (_57_491) with
| (head, chead, g_head) -> begin
(

let _57_495 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _148_274 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _148_274))
end else begin
(let _148_275 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _148_275))
end
in (match (_57_495) with
| (e, c, g) -> begin
(

let _57_496 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_276 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _148_276))
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

let _57_502 = (comp_check_expected_typ env0 e c)
in (match (_57_502) with
| (e, c, g') -> begin
(

let gimp = (match ((let _148_277 = (FStar_Syntax_Subst.compress head)
in _148_277.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _57_505) -> begin
(

let imp = ("head of application is a uvar", env0, u, e, c.FStar_Syntax_Syntax.res_typ, head.FStar_Syntax_Syntax.pos)
in (

let _57_509 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_509.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_509.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_509.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _57_512 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (

let gres = (let _148_278 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _148_278))
in (

let _57_515 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_280 = (FStar_Syntax_Print.term_to_string e)
in (let _148_279 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" _148_280 _148_279)))
end else begin
()
end
in (e, c, gres))))
end))))
end))
end)))))
end
| FStar_Syntax_Syntax.Tm_match (e1, eqns) -> begin
(

let _57_523 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_523) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let _57_528 = (tc_term env1 e1)
in (match (_57_528) with
| (e1, c1, g1) -> begin
(

let _57_539 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(

let _57_535 = (FStar_Syntax_Util.type_u ())
in (match (_57_535) with
| (k, _57_534) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _148_281 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_148_281, res_t)))
end))
end)
in (match (_57_539) with
| (env_branches, res_t) -> begin
(

let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let _57_556 = (

let _57_553 = (FStar_List.fold_right (fun _57_547 _57_550 -> (match ((_57_547, _57_550)) with
| ((_57_543, f, c, g), (caccum, gaccum)) -> begin
(let _148_284 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _148_284))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_553) with
| (cases, g) -> begin
(let _148_285 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_148_285, g))
end))
in (match (_57_556) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (Some (guard_x), c_branches))
in (

let e = (

let mk_match = (fun scrutinee -> (

let branches = (FStar_List.map (fun _57_567 -> (match (_57_567) with
| (f, _57_562, _57_564, _57_566) -> begin
f
end)) t_eqns)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((scrutinee, branches))) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ), Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos))))
in if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c1.FStar_Syntax_Syntax.eff_name) then begin
(mk_match e1)
end else begin
(

let e_match = (let _148_289 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match _148_289))
in (

let lb = (let _148_290 = (FStar_TypeChecker_Env.norm_eff_name env c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = _148_290; FStar_Syntax_Syntax.lbdef = e1})
in (let _148_295 = (let _148_294 = (let _148_293 = (let _148_292 = (let _148_291 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (_148_291)::[])
in (FStar_Syntax_Subst.close _148_292 e_match))
in ((false, (lb)::[]), _148_293))
in FStar_Syntax_Syntax.Tm_let (_148_294))
in (FStar_Syntax_Syntax.mk _148_295 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))))
end)
in (

let _57_573 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_298 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _148_297 = (let _148_296 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _148_296))
in (FStar_Util.print2 "(%s) comp type = %s\n" _148_298 _148_297)))
end else begin
()
end
in (let _148_299 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _148_299)))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_585); FStar_Syntax_Syntax.lbunivs = _57_583; FStar_Syntax_Syntax.lbtyp = _57_581; FStar_Syntax_Syntax.lbeff = _57_579; FStar_Syntax_Syntax.lbdef = _57_577})::[]), _57_591) -> begin
(

let _57_594 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_300 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _148_300))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _57_598), _57_601) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_616); FStar_Syntax_Syntax.lbunivs = _57_614; FStar_Syntax_Syntax.lbtyp = _57_612; FStar_Syntax_Syntax.lbeff = _57_610; FStar_Syntax_Syntax.lbdef = _57_608})::_57_606), _57_622) -> begin
(

let _57_625 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_301 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _148_301))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _57_629), _57_632) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let _57_646 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_646) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _148_315 = (let _148_314 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_314))
in FStar_Util.Inr (_148_315))
end
in (

let is_data_ctor = (fun _57_4 -> (match (_57_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _57_656 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _148_321 = (let _148_320 = (let _148_319 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _148_318 = (FStar_TypeChecker_Env.get_range env)
in (_148_319, _148_318)))
in FStar_Syntax_Syntax.Error (_148_320))
in (Prims.raise _148_321))
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

let g = (match ((let _148_322 = (FStar_Syntax_Subst.compress t1)
in _148_322.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_667) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _57_670 -> begin
(

let imp = ("uvar in term", env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (

let _57_672 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_672.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_672.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_672.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _57_687 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(

let _57_680 = (FStar_Syntax_Util.type_u ())
in (match (_57_680) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
end))
end
| Some (t) -> begin
(t, [], FStar_TypeChecker_Rel.trivial_guard)
end)
in (match (_57_687) with
| (t, _57_685, g0) -> begin
(

let _57_692 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (_57_692) with
| (e, _57_690, g1) -> begin
(let _148_325 = (let _148_323 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right _148_323 FStar_Syntax_Util.lcomp_of_comp))
in (let _148_324 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in (e, _148_325, _148_324)))
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

let _57_696 = x
in {FStar_Syntax_Syntax.ppname = _57_696.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_696.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let _57_702 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_702) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _148_327 = (let _148_326 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_326))
in FStar_Util.Inr (_148_327))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _57_709; FStar_Syntax_Syntax.pos = _57_707; FStar_Syntax_Syntax.vars = _57_705}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let _57_719 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_719) with
| (us', t) -> begin
(

let _57_726 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _148_330 = (let _148_329 = (let _148_328 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _148_328))
in FStar_Syntax_Syntax.Error (_148_329))
in (Prims.raise _148_330))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _57_725 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (

let fv' = (

let _57_728 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _57_730 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_730.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_730.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_728.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_728.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _148_333 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _148_333 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let _57_738 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_738) with
| (us, t) -> begin
(

let fv' = (

let _57_739 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _57_741 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_741.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_741.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_739.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_739.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _148_334 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _148_334 us))
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

let _57_755 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_755) with
| (bs, c) -> begin
(

let env0 = env
in (

let _57_760 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_760) with
| (env, _57_759) -> begin
(

let _57_765 = (tc_binders env bs)
in (match (_57_765) with
| (bs, env, g, us) -> begin
(

let _57_769 = (tc_comp env c)
in (match (_57_769) with
| (c, uc, f) -> begin
(

let e = (

let _57_770 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _57_770.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_770.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_770.FStar_Syntax_Syntax.vars})
in (

let _57_773 = (check_smt_pat env e bs c)
in (

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _148_335 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _148_335))
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

let _57_789 = (let _148_337 = (let _148_336 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_336)::[])
in (FStar_Syntax_Subst.open_term _148_337 phi))
in (match (_57_789) with
| (x, phi) -> begin
(

let env0 = env
in (

let _57_794 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_794) with
| (env, _57_793) -> begin
(

let _57_799 = (let _148_338 = (FStar_List.hd x)
in (tc_binder env _148_338))
in (match (_57_799) with
| (x, env, f1, u) -> begin
(

let _57_800 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_341 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _148_340 = (FStar_Syntax_Print.term_to_string phi)
in (let _148_339 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _148_341 _148_340 _148_339))))
end else begin
()
end
in (

let _57_805 = (FStar_Syntax_Util.type_u ())
in (match (_57_805) with
| (t_phi, _57_804) -> begin
(

let _57_810 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_57_810) with
| (phi, _57_808, f2) -> begin
(

let e = (

let _57_811 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _57_811.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_811.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_811.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _148_342 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _148_342))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _57_819) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (

let _57_825 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_343 = (FStar_Syntax_Print.term_to_string (

let _57_823 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _57_823.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_823.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_823.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _148_343))
end else begin
()
end
in (

let _57_829 = (FStar_Syntax_Subst.open_term bs body)
in (match (_57_829) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _57_831 -> begin
(let _148_346 = (let _148_345 = (FStar_Syntax_Print.term_to_string top)
in (let _148_344 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" _148_345 _148_344)))
in (FStar_All.failwith _148_346))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_57_836) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_57_839, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_57_844, Some (_57_846)) -> begin
(FStar_All.failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (_57_851) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_57_854) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_57_857) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_57_861) -> begin
FStar_TypeChecker_Common.t_range
end
| _57_864 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(

let _57_872 = (FStar_Syntax_Util.type_u ())
in (match (_57_872) with
| (k, u) -> begin
(

let _57_877 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_877) with
| (t, _57_875, g) -> begin
(let _148_351 = (FStar_Syntax_Syntax.mk_Total t)
in (_148_351, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(

let _57_882 = (FStar_Syntax_Util.type_u ())
in (match (_57_882) with
| (k, u) -> begin
(

let _57_887 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_887) with
| (t, _57_885, g) -> begin
(let _148_352 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_148_352, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (

let tc = (let _148_354 = (let _148_353 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_148_353)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _148_354 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let _57_896 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_57_896) with
| (tc, _57_894, f) -> begin
(

let _57_900 = (FStar_Syntax_Util.head_and_args tc)
in (match (_57_900) with
| (_57_898, args) -> begin
(

let _57_903 = (let _148_356 = (FStar_List.hd args)
in (let _148_355 = (FStar_List.tl args)
in (_148_356, _148_355)))
in (match (_57_903) with
| (res, args) -> begin
(

let _57_919 = (let _148_358 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _57_5 -> (match (_57_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _57_910 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_910) with
| (env, _57_909) -> begin
(

let _57_915 = (tc_tot_or_gtot_term env e)
in (match (_57_915) with
| (e, _57_913, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _148_358 FStar_List.unzip))
in (match (_57_919) with
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
| _57_930 -> begin
(FStar_All.failwith "Impossible:Unexpected sort for computation")
end)))
end
| _57_932 -> begin
(FStar_All.failwith "Impossible:Unexpected sort for computation")
end)
in (let _148_360 = (FStar_Syntax_Syntax.mk_Comp (

let _57_934 = c
in {FStar_Syntax_Syntax.effect_name = _57_934.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _57_934.FStar_Syntax_Syntax.flags}))
in (let _148_359 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_148_360, u, _148_359))))
end))
end))
end))
end))))
end)))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_57_942) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _148_365 = (aux u)
in FStar_Syntax_Syntax.U_succ (_148_365))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _148_366 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_148_366))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _148_370 = (let _148_369 = (let _148_368 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _148_367 = (FStar_TypeChecker_Env.get_range env)
in (_148_368, _148_367)))
in FStar_Syntax_Syntax.Error (_148_369))
in (Prims.raise _148_370))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _148_371 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_371 Prims.snd))
end
| _57_957 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _148_380 = (let _148_379 = (let _148_378 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_148_378, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_148_379))
in (Prims.raise _148_380)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun _57_975 bs bs_expected -> (match (_57_975) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
(

let _57_1006 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _148_397 = (let _148_396 = (let _148_395 = (let _148_393 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _148_393))
in (let _148_394 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_148_395, _148_394)))
in FStar_Syntax_Syntax.Error (_148_396))
in (Prims.raise _148_397))
end
| _57_1005 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _57_1023 = (match ((let _148_398 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _148_398.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _57_1011 -> begin
(

let _57_1012 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_399 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _148_399))
end else begin
()
end
in (

let _57_1018 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_57_1018) with
| (t, _57_1016, g1) -> begin
(

let g2 = (let _148_401 = (FStar_TypeChecker_Env.get_range env)
in (let _148_400 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _148_401 "Type annotation on parameter incompatible with the expected type" _148_400)))
in (

let g = (let _148_402 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _148_402))
in (t, g)))
end)))
end)
in (match (_57_1023) with
| (t, g) -> begin
(

let hd = (

let _57_1024 = hd
in {FStar_Syntax_Syntax.ppname = _57_1024.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1024.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = (hd, imp)
in (

let b_expected = (hd_expected, imp')
in (

let env = (push_binding env b)
in (

let subst = (let _148_403 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _148_403))
in (aux (env, (b)::out, g, subst) bs bs_expected))))))
end))))
end
| (rest, []) -> begin
(env, (FStar_List.rev out), Some (FStar_Util.Inl (rest)), g, subst)
end
| ([], rest) -> begin
(env, (FStar_List.rev out), Some (FStar_Util.Inr (rest)), g, subst)
end)
end))
in (aux (env, [], FStar_TypeChecker_Rel.trivial_guard, []) bs bs_expected)))
in (

let rec expected_function_typ = (fun env t0 body -> (match (t0) with
| None -> begin
(

let _57_1045 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1044 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (

let _57_1052 = (tc_binders env bs)
in (match (_57_1052) with
| (bs, envbody, g, _57_1051) -> begin
(

let _57_1070 = (match ((let _148_410 = (FStar_Syntax_Subst.compress body)
in _148_410.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _57_1057) -> begin
(

let _57_1064 = (tc_comp envbody c)
in (match (_57_1064) with
| (c, _57_1062, g') -> begin
(let _148_411 = (FStar_TypeChecker_Rel.conj_guard g g')
in (Some (c), body, _148_411))
end))
end
| _57_1066 -> begin
(None, body, g)
end)
in (match (_57_1070) with
| (copt, body, g) -> begin
(None, bs, [], copt, envbody, body, g)
end))
end)))
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm t -> (match ((let _148_416 = (FStar_Syntax_Subst.compress t)
in _148_416.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let _57_1097 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1096 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _57_1104 = (tc_binders env bs)
in (match (_57_1104) with
| (bs, envbody, g, _57_1103) -> begin
(

let _57_1108 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_57_1108) with
| (envbody, _57_1107) -> begin
(Some ((t, true)), bs, [], None, envbody, body, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _57_1111) -> begin
(

let _57_1122 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_57_1122) with
| (_57_1115, bs, bs', copt, env, body, g) -> begin
(Some ((t, false)), bs, bs', copt, env, body, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _57_1129 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_57_1129) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun _57_1140 c_expected -> (match (_57_1140) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _148_427 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _148_427))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (let _148_428 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _148_428))
in (let _148_429 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _148_429)))
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

let _57_1161 = (check_binders env more_bs bs_expected)
in (match (_57_1161) with
| (env, bs', more, guard', subst) -> begin
(let _148_431 = (let _148_430 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _148_430, subst))
in (handle_more _148_431 c_expected))
end))
end
| _57_1163 -> begin
(let _148_433 = (let _148_432 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _148_432))
in (fail _148_433 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _148_434 = (check_binders env bs bs_expected)
in (handle_more _148_434 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let _57_1169 = envbody
in {FStar_TypeChecker_Env.solver = _57_1169.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1169.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1169.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1169.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1169.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1169.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1169.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1169.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1169.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1169.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1169.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1169.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_1169.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1169.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1169.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1169.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1169.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_1169.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_1169.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1169.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1169.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _57_1174 _57_1177 -> (match ((_57_1174, _57_1177)) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _57_1183 = (let _148_444 = (let _148_443 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _148_443 Prims.fst))
in (tc_term _148_444 t))
in (match (_57_1183) with
| (t, _57_1180, _57_1182) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _148_445 = (FStar_Syntax_Syntax.mk_binder (

let _57_1187 = x
in {FStar_Syntax_Syntax.ppname = _57_1187.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1187.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_148_445)::letrec_binders)
end
| _57_1190 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (

let _57_1196 = (check_actuals_against_formals env bs bs_expected)
in (match (_57_1196) with
| (envbody, bs, g, c) -> begin
(

let _57_1199 = if (FStar_TypeChecker_Env.should_verify env) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_57_1199) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, body, g))
end))
end))))
end))
end
| _57_1202 -> begin
if (not (norm)) then begin
(let _148_446 = (unfold_whnf env t)
in (as_function_typ true _148_446))
end else begin
(

let _57_1212 = (expected_function_typ env None body)
in (match (_57_1212) with
| (_57_1204, bs, _57_1207, c_opt, envbody, body, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, body, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let _57_1216 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1216) with
| (env, topt) -> begin
(

let _57_1220 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_447 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _148_447 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (

let _57_1229 = (expected_function_typ env topt body)
in (match (_57_1229) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let _57_1235 = (tc_term (

let _57_1230 = envbody
in {FStar_TypeChecker_Env.solver = _57_1230.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1230.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1230.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1230.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1230.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1230.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1230.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1230.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1230.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1230.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1230.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1230.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1230.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1230.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1230.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1230.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_1230.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_1230.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1230.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1230.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_57_1235) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _57_1237 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _148_450 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _148_449 = (let _148_448 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _148_448))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _148_450 _148_449)))
end else begin
()
end
in (

let _57_1244 = (let _148_452 = (let _148_451 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _148_451))
in (check_expected_effect (

let _57_1239 = envbody
in {FStar_TypeChecker_Env.solver = _57_1239.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1239.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1239.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1239.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1239.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1239.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1239.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1239.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1239.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1239.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1239.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1239.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1239.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1239.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1239.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1239.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1239.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_1239.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_1239.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1239.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1239.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _148_452))
in (match (_57_1244) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(let _148_453 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _148_453))
end else begin
(

let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _148_456 = (let _148_455 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _148_454 -> FStar_Util.Inl (_148_454)))
in Some (_148_455))
in (FStar_Syntax_Util.abs bs body _148_456))
in (

let _57_1267 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_1256) -> begin
(e, t, guard)
end
| _57_1259 -> begin
(

let _57_1262 = if use_teq then begin
(let _148_457 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _148_457))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_57_1262) with
| (e, guard') -> begin
(let _148_458 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _148_458))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_57_1267) with
| (e, tfun, guard) -> begin
(

let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (

let _57_1271 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_57_1271) with
| (c, g) -> begin
(e, c, g)
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

let _57_1281 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_467 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _148_466 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _148_467 _148_466)))
end else begin
()
end
in (

let monadic_application = (fun _57_1288 subst arg_comps_rev arg_rets guard fvs bs -> (match (_57_1288) with
| (head, chead, ghead, cres) -> begin
(

let _57_1295 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let _57_1323 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun _57_6 -> (match (_57_6) with
| (_57_1302, _57_1304, None) -> begin
false
end
| (_57_1308, _57_1310, Some (c)) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _148_483 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _148_483 cres))
end else begin
(

let _57_1315 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_486 = (FStar_Syntax_Print.term_to_string head)
in (let _148_485 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _148_484 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _148_486 _148_485 _148_484))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _57_1319 -> begin
(

let g = (let _148_487 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right _148_487 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _148_492 = (let _148_491 = (let _148_490 = (let _148_489 = (let _148_488 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _148_488))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _148_489))
in (FStar_Syntax_Syntax.mk_Total _148_490))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_491))
in (_148_492, g)))
end)
in (match (_57_1323) with
| (cres, guard) -> begin
(

let _57_1324 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_493 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _148_493))
end else begin
()
end
in (

let _57_1342 = (FStar_List.fold_left (fun _57_1328 _57_1334 -> (match ((_57_1328, _57_1334)) with
| ((args, out_c), ((e, q), x, c)) -> begin
(match (c) with
| None -> begin
(((e, q))::args, out_c)
end
| Some (c) -> begin
(

let out_c = (FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env None c (x, out_c))
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e c.FStar_Syntax_Syntax.eff_name out_c.FStar_Syntax_Syntax.eff_name)
in (((e, q))::args, out_c)))
end)
end)) ([], cres) arg_comps_rev)
in (match (_57_1342) with
| (args, comp) -> begin
(

let comp = (FStar_TypeChecker_Util.bind head.FStar_Syntax_Syntax.pos env None chead (None, comp))
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app = (FStar_TypeChecker_Util.maybe_monadic env app comp.FStar_Syntax_Syntax.eff_name)
in (

let _57_1348 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (_57_1348) with
| (comp, g) -> begin
(app, comp, g)
end)))))
end)))
end)))
end))
in (

let rec tc_args = (fun head_info _57_1356 bs args -> (match (_57_1356) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match ((bs, args)) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (_57_1362))))::rest, ((_57_1370, None))::_57_1368) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _57_1376 = (check_no_escape (Some (head)) env fvs t)
in (

let _57_1382 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_57_1382) with
| (varg, _57_1380, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (

let arg = (let _148_505 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _148_505))
in (let _148_507 = (let _148_506 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, ((arg, None, None))::outargs, (arg)::arg_rets, _148_506, fvs))
in (tc_args head_info _148_507 rest args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
(

let _57_1414 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _57_1413 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let _57_1417 = x
in {FStar_Syntax_Syntax.ppname = _57_1417.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1417.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (

let _57_1420 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_508 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _148_508))
end else begin
()
end
in (

let _57_1422 = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let _57_1425 = env
in {FStar_TypeChecker_Env.solver = _57_1425.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1425.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1425.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1425.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1425.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1425.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1425.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1425.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1425.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1425.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1425.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1425.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1425.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1425.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1425.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _57_1425.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1425.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_1425.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_1425.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1425.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1425.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_1428 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_511 = (FStar_Syntax_Print.tag_of_term e)
in (let _148_510 = (FStar_Syntax_Print.term_to_string e)
in (let _148_509 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _148_511 _148_510 _148_509))))
end else begin
()
end
in (

let _57_1433 = (tc_term env e)
in (match (_57_1433) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(

let subst = (let _148_512 = (FStar_List.hd bs)
in (maybe_extend_subst subst _148_512 e))
in (tc_args head_info (subst, ((arg, None, None))::outargs, (arg)::arg_rets, g, fvs) rest rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(

let subst = (let _148_513 = (FStar_List.hd bs)
in (maybe_extend_subst subst _148_513 e))
in (tc_args head_info (subst, ((arg, Some (x), Some (c)))::outargs, (arg)::arg_rets, g, fvs) rest rest'))
end else begin
if (let _148_514 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _148_514)) then begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _148_515 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _148_515))
in (tc_args head_info (subst, ((arg, Some (newx), Some (c)))::outargs, (arg')::arg_rets, g, fvs) rest rest')))
end else begin
(let _148_519 = (let _148_518 = (let _148_517 = (let _148_516 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _148_516))
in (_148_517)::arg_rets)
in (subst, ((arg, Some (x), Some (c)))::outargs, _148_518, g, (x)::fvs))
in (tc_args head_info _148_519 rest rest'))
end
end
end))
end))))))))))
end
| (_57_1441, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::_57_1446) -> begin
(

let _57_1453 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (_57_1453) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _148_524 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _148_524 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let _57_1464 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (_57_1464) with
| (bs, cres') -> begin
(

let head_info = (head, chead, ghead, (FStar_Syntax_Util.lcomp_of_comp cres'))
in (

let _57_1466 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_525 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _148_525))
end else begin
()
end
in (tc_args head_info ([], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs args)))
end))
end
| _57_1469 when (not (norm)) -> begin
(let _148_526 = (unfold_whnf env tres)
in (aux true _148_526))
end
| _57_1471 -> begin
(let _148_532 = (let _148_531 = (let _148_530 = (let _148_528 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (let _148_527 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _148_528 _148_527)))
in (let _148_529 = (FStar_Syntax_Syntax.argpos arg)
in (_148_530, _148_529)))
in FStar_Syntax_Syntax.Error (_148_531))
in (Prims.raise _148_532))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (match ((let _148_537 = (FStar_Syntax_Util.unrefine tf)
in _148_537.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| ((e, imp))::tl -> begin
(

let _57_1504 = (tc_term env e)
in (match (_57_1504) with
| (e, c, g_e) -> begin
(

let _57_1508 = (tc_args env tl)
in (match (_57_1508) with
| (args, comps, g_rest) -> begin
(let _148_542 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, ((e.FStar_Syntax_Syntax.pos, c))::comps, _148_542))
end))
end))
end))
in (

let _57_1512 = (tc_args env args)
in (match (_57_1512) with
| (args, comps, g_args) -> begin
(

let bs = (let _148_544 = (FStar_All.pipe_right comps (FStar_List.map (fun _57_1516 -> (match (_57_1516) with
| (_57_1514, c) -> begin
(c.FStar_Syntax_Syntax.res_typ, None)
end))))
in (FStar_Syntax_Util.null_binders_of_tks _148_544))
in (

let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _57_1522 -> begin
FStar_Syntax_Util.ml_comp
end)
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _148_559 = (FStar_Syntax_Subst.compress t)
in _148_559.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_1528) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _57_1533 -> begin
ml_or_tot
end)
end)
in (

let cres = (let _148_564 = (let _148_563 = (let _148_562 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_562 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _148_563))
in (ml_or_tot _148_564 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (

let _57_1537 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _148_567 = (FStar_Syntax_Print.term_to_string head)
in (let _148_566 = (FStar_Syntax_Print.term_to_string tf)
in (let _148_565 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _148_567 _148_566 _148_565))))
end else begin
()
end
in (

let _57_1539 = (let _148_568 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _148_568))
in (

let comp = (let _148_571 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _57_1543 out -> (match (_57_1543) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c (None, out))
end)) (((head.FStar_Syntax_Syntax.pos, chead))::comps) _148_571))
in (let _148_573 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _148_572 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_148_573, comp, _148_572)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _57_1552 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_1552) with
| (bs, c) -> begin
(

let head_info = (head, chead, ghead, (FStar_Syntax_Util.lcomp_of_comp c))
in (tc_args head_info ([], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs args))
end))
end
| _57_1555 -> begin
if (not (norm)) then begin
(let _148_574 = (unfold_whnf env tf)
in (check_function_app true _148_574))
end else begin
(let _148_577 = (let _148_576 = (let _148_575 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_148_575, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_148_576))
in (Prims.raise _148_577))
end
end))
in (let _148_579 = (let _148_578 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _148_578))
in (check_function_app false _148_579))))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let _57_1591 = (FStar_List.fold_left2 (fun _57_1572 _57_1575 _57_1578 -> (match ((_57_1572, _57_1575, _57_1578)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(

let _57_1579 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let _57_1584 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_57_1584) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (let _148_589 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _148_589 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _148_593 = (let _148_591 = (let _148_590 = (FStar_Syntax_Syntax.as_arg e)
in (_148_590)::[])
in (FStar_List.append seen _148_591))
in (let _148_592 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_148_593, _148_592, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_57_1591) with
| (args, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = if ghost then begin
(let _148_594 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _148_594 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (

let _57_1596 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_57_1596) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _57_1598 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let _57_1605 = (FStar_Syntax_Subst.open_branch branch)
in (match (_57_1605) with
| (pattern, when_clause, branch_exp) -> begin
(

let _57_1610 = branch
in (match (_57_1610) with
| (cpat, _57_1608, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _57_1618 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_57_1618) with
| (pat_bvs, exps, p) -> begin
(

let _57_1619 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_606 = (FStar_Syntax_Print.pat_to_string p0)
in (let _148_605 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _148_606 _148_605)))
end else begin
()
end
in (

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let _57_1625 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_57_1625) with
| (env1, _57_1624) -> begin
(

let env1 = (

let _57_1626 = env1
in {FStar_TypeChecker_Env.solver = _57_1626.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1626.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1626.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1626.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1626.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1626.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1626.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1626.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _57_1626.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1626.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1626.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1626.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1626.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1626.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1626.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1626.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1626.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_1626.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_1626.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1626.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1626.FStar_TypeChecker_Env.use_bv_sorts})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _57_1665 = (let _148_629 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _57_1631 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_609 = (FStar_Syntax_Print.term_to_string e)
in (let _148_608 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _148_609 _148_608)))
end else begin
()
end
in (

let _57_1636 = (tc_term env1 e)
in (match (_57_1636) with
| (e, lc, g) -> begin
(

let _57_1637 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_611 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _148_610 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _148_611 _148_610)))
end else begin
()
end
in (

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let _57_1643 = (let _148_612 = (FStar_TypeChecker_Rel.discharge_guard env (

let _57_1641 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_1641.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_1641.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_1641.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _148_612 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _148_617 = (let _148_616 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _148_616 (FStar_List.map (fun _57_1651 -> (match (_57_1651) with
| (u, _57_1650) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _148_617 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _57_1659 = if (let _148_618 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _148_618)) then begin
(

let unresolved = (let _148_619 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _148_619 FStar_Util.set_elements))
in (let _148_627 = (let _148_626 = (let _148_625 = (let _148_624 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _148_623 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _148_622 = (let _148_621 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _57_1658 -> (match (_57_1658) with
| (u, _57_1657) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _148_621 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _148_624 _148_623 _148_622))))
in (_148_625, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_148_626))
in (Prims.raise _148_627)))
end else begin
()
end
in (

let _57_1661 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_628 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _148_628))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _148_629 FStar_List.unzip))
in (match (_57_1665) with
| (exps, norm_exps) -> begin
(

let p = (FStar_TypeChecker_Util.decorate_pattern env p exps)
in (p, pat_bvs, pat_env, exps, norm_exps))
end))))
end))))
end)))
in (

let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (

let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (

let _57_1672 = (let _148_630 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _148_630 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_57_1672) with
| (scrutinee_env, _57_1671) -> begin
(

let _57_1678 = (tc_pat true pat_t pattern)
in (match (_57_1678) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let _57_1688 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_TypeChecker_Env.should_verify env) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(

let _57_1685 = (let _148_631 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _148_631 e))
in (match (_57_1685) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_57_1688) with
| (when_clause, g_when) -> begin
(

let _57_1692 = (tc_term pat_env branch_exp)
in (match (_57_1692) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _148_633 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _148_632 -> Some (_148_632)) _148_633))
end)
in (

let _57_1750 = (

let eqs = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
None
end else begin
(FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _57_1710 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _148_637 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _148_636 -> Some (_148_636)) _148_637))
end))
end))) None))
end
in (

let _57_1718 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_57_1718) with
| (c, g_branch) -> begin
(

let _57_1745 = (match ((eqs, when_condition)) with
| _57_1720 when (not ((FStar_TypeChecker_Env.should_verify env))) -> begin
(c, g_when)
end
| (None, None) -> begin
(c, g_when)
end
| (Some (f), None) -> begin
(

let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _148_640 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _148_639 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_148_640, _148_639)))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (let _148_641 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_148_641))
in (let _148_644 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _148_643 = (let _148_642 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _148_642 g_when))
in (_148_644, _148_643)))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _148_645 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_148_645, g_when))))
end)
in (match (_57_1745) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _148_647 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _148_646 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_148_647, _148_646, g_branch))))
end))
end)))
in (match (_57_1750) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
FStar_Syntax_Util.t_true
end else begin
(

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> if ((let _148_657 = (let _148_656 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _148_656))
in (FStar_List.length _148_657)) > 1) then begin
(

let disc = (let _148_658 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _148_658 FStar_Syntax_Syntax.Delta_equational None))
in (

let disc = (let _148_660 = (let _148_659 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_148_659)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _148_660 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _148_661 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_148_661)::[])))
end else begin
[]
end)
in (

let fail = (fun _57_1760 -> (match (()) with
| () -> begin
(let _148_667 = (let _148_666 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _148_665 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _148_664 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _148_666 _148_665 _148_664))))
in (FStar_All.failwith _148_667))
end))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _57_1767) -> begin
(head_constructor t)
end
| _57_1771 -> begin
(fail ())
end))
in (

let pat_exp = (let _148_670 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _148_670 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_57_1796) -> begin
(let _148_675 = (let _148_674 = (let _148_673 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _148_672 = (let _148_671 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_148_671)::[])
in (_148_673)::_148_672))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _148_674 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_148_675)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _148_676 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _148_676))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(

let sub_term_guards = (let _148_683 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _57_1814 -> (match (_57_1814) with
| (ei, _57_1813) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _57_1818 -> begin
(

let sub_term = (let _148_682 = (let _148_679 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _148_679 FStar_Syntax_Syntax.Delta_equational None))
in (let _148_681 = (let _148_680 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_148_680)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _148_682 _148_681 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _148_683 FStar_List.flatten))
in (let _148_684 = (discriminate scrutinee_tm f)
in (FStar_List.append _148_684 sub_term_guards)))
end)
end
| _57_1822 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(

let t = (let _148_689 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _148_689))
in (

let _57_1830 = (FStar_Syntax_Util.type_u ())
in (match (_57_1830) with
| (k, _57_1829) -> begin
(

let _57_1836 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_57_1836) with
| (t, _57_1833, _57_1835) -> begin
t
end))
end)))
end)
in (

let branch_guard = (let _148_690 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _148_690 FStar_Syntax_Util.mk_disj_l))
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

let _57_1844 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_691 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _148_691))
end else begin
()
end
in (let _148_692 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_148_692, branch_guard, c, guard)))))
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

let _57_1861 = (check_let_bound_def true env lb)
in (match (_57_1861) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let _57_1873 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(

let g1 = (let _148_695 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _148_695 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _57_1868 = (let _148_699 = (let _148_698 = (let _148_697 = (let _148_696 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _148_696))
in (_148_697)::[])
in (FStar_TypeChecker_Util.generalize env _148_698))
in (FStar_List.hd _148_699))
in (match (_57_1868) with
| (_57_1864, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_57_1873) with
| (g1, e1, univ_vars, c1) -> begin
(

let _57_1883 = if (FStar_TypeChecker_Env.should_verify env) then begin
(

let _57_1876 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_57_1876) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(

let _57_1877 = if (FStar_Options.warn_top_level_effects ()) then begin
(let _148_700 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _148_700 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _148_701 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_148_701, c1)))
end
end))
end else begin
(

let _57_1879 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _148_702 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _148_702)))
end
in (match (_57_1883) with
| (e2, c1) -> begin
(

let cres = (let _148_703 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_703))
in (

let _57_1885 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _148_704 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_148_704, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _57_1889 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let _57_1900 = env
in {FStar_TypeChecker_Env.solver = _57_1900.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1900.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1900.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1900.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1900.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1900.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1900.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1900.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1900.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1900.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1900.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1900.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1900.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1900.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1900.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1900.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1900.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_1900.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_1900.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1900.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1900.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_1909 = (let _148_708 = (let _148_707 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _148_707 Prims.fst))
in (check_let_bound_def false _148_708 lb))
in (match (_57_1909) with
| (e1, _57_1905, c1, g1, annotated) -> begin
(

let x = (

let _57_1910 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1910.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1910.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let _57_1916 = (let _148_710 = (let _148_709 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_709)::[])
in (FStar_Syntax_Subst.open_term _148_710 e2))
in (match (_57_1916) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _57_1922 = (let _148_711 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _148_711 e2))
in (match (_57_1922) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (Some (x), c2))
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e2 = (FStar_TypeChecker_Util.maybe_lift env e2 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e = (let _148_714 = (let _148_713 = (let _148_712 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _148_712))
in FStar_Syntax_Syntax.Tm_let (_148_713))
in (FStar_Syntax_Syntax.mk _148_714 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name)
in (

let x_eq_e1 = (let _148_717 = (let _148_716 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _148_716 e1))
in (FStar_All.pipe_left (fun _148_715 -> FStar_TypeChecker_Common.NonTrivial (_148_715)) _148_717))
in (

let g2 = (let _148_719 = (let _148_718 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _148_718 g2))
in (FStar_TypeChecker_Rel.close_guard xb _148_719))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if (let _148_720 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome _148_720)) then begin
(e, cres, guard)
end else begin
(

let _57_1931 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end))))))))
end))))
end))))
end)))
end
| _57_1934 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _57_1946 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1946) with
| (lbs, e2) -> begin
(

let _57_1949 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1949) with
| (env0, topt) -> begin
(

let _57_1952 = (build_let_rec_env true env0 lbs)
in (match (_57_1952) with
| (lbs, rec_env) -> begin
(

let _57_1955 = (check_let_recs rec_env lbs)
in (match (_57_1955) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (let _148_723 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _148_723 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _148_726 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _148_726 (fun _148_725 -> Some (_148_725))))
in (

let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(

let ecs = (let _148_730 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _148_729 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _148_729)))))
in (FStar_TypeChecker_Util.generalize env _148_730))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _57_1966 -> (match (_57_1966) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _148_732 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_732))
in (

let _57_1969 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _57_1973 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1973) with
| (lbs, e2) -> begin
(let _148_734 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _148_733 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_148_734, cres, _148_733)))
end)))))))
end))
end))
end))
end))
end
| _57_1975 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _57_1987 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1987) with
| (lbs, e2) -> begin
(

let _57_1990 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1990) with
| (env0, topt) -> begin
(

let _57_1993 = (build_let_rec_env false env0 lbs)
in (match (_57_1993) with
| (lbs, rec_env) -> begin
(

let _57_1996 = (check_let_recs rec_env lbs)
in (match (_57_1996) with
| (lbs, g_lbs) -> begin
(

let _57_2008 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let _57_1999 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1999.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1999.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let _57_2002 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _57_2002.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_2002.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_2002.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _57_2002.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], lb.FStar_Syntax_Syntax.lbtyp))
in (env, lb))))) env))
in (match (_57_2008) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let _57_2014 = (tc_term env e2)
in (match (_57_2014) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _57_2018 = cres
in {FStar_Syntax_Syntax.eff_name = _57_2018.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _57_2018.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_2018.FStar_Syntax_Syntax.comp})
in (

let _57_2023 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_2023) with
| (lbs, e2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_57_2026) -> begin
(e, cres, guard)
end
| None -> begin
(

let _57_2029 = (check_no_escape None env bvs tres)
in (e, cres, guard))
end))
end))))))
end)))
end))
end))
end))
end))
end))
end
| _57_2032 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let _57_2065 = (FStar_List.fold_left (fun _57_2039 lb -> (match (_57_2039) with
| (lbs, env) -> begin
(

let _57_2044 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_57_2044) with
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

let _57_2053 = (let _148_746 = (let _148_745 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _148_745))
in (tc_check_tot_or_gtot_term (

let _57_2047 = env0
in {FStar_TypeChecker_Env.solver = _57_2047.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2047.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2047.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2047.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2047.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2047.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2047.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2047.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2047.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2047.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2047.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2047.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2047.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2047.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _57_2047.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2047.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2047.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_2047.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_2047.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2047.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2047.FStar_TypeChecker_Env.use_bv_sorts}) t _148_746))
in (match (_57_2053) with
| (t, _57_2051, g) -> begin
(

let _57_2054 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (

let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_TypeChecker_Env.should_verify env)) then begin
(

let _57_2057 = env
in {FStar_TypeChecker_Env.solver = _57_2057.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2057.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2057.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2057.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2057.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2057.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2057.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2057.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2057.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2057.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2057.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2057.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2057.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_2057.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2057.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2057.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2057.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_2057.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_2057.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2057.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2057.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (

let lb = (

let _57_2060 = lb
in {FStar_Syntax_Syntax.lbname = _57_2060.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _57_2060.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_57_2065) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _57_2078 = (let _148_751 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _57_2072 = (let _148_750 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _148_750 lb.FStar_Syntax_Syntax.lbdef))
in (match (_57_2072) with
| (e, c, g) -> begin
(

let _57_2073 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _148_751 FStar_List.unzip))
in (match (_57_2078) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _57_2086 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_2086) with
| (env1, _57_2085) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _57_2092 = (check_lbtyp top_level env lb)
in (match (_57_2092) with
| (topt, wf_annot, univ_vars, env1) -> begin
(

let _57_2093 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let _57_2100 = (tc_maybe_toplevel_term (

let _57_2095 = env1
in {FStar_TypeChecker_Env.solver = _57_2095.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2095.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2095.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2095.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2095.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2095.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2095.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2095.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2095.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2095.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2095.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2095.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2095.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _57_2095.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2095.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2095.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2095.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_2095.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_2095.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2095.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2095.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_57_2100) with
| (e1, c1, g1) -> begin
(

let _57_2104 = (let _148_758 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_2101 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _148_758 e1 c1 wf_annot))
in (match (_57_2104) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _57_2106 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_759 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _148_759))
end else begin
()
end
in (let _148_760 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _148_760))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _57_2113 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _57_2116 -> begin
(

let _57_2119 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_57_2119) with
| (univ_vars, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _148_764 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _148_764))
end else begin
(

let _57_2124 = (FStar_Syntax_Util.type_u ())
in (match (_57_2124) with
| (k, _57_2123) -> begin
(

let _57_2129 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_57_2129) with
| (t, _57_2127, g) -> begin
(

let _57_2130 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _148_767 = (let _148_765 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _148_765))
in (let _148_766 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _148_767 _148_766)))
end else begin
()
end
in (

let t = (norm env1 t)
in (let _148_768 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _148_768))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _57_2136 -> (match (_57_2136) with
| (x, imp) -> begin
(

let _57_2139 = (FStar_Syntax_Util.type_u ())
in (match (_57_2139) with
| (tu, u) -> begin
(

let _57_2144 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_57_2144) with
| (t, _57_2142, g) -> begin
(

let x = ((

let _57_2145 = x
in {FStar_Syntax_Syntax.ppname = _57_2145.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2145.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (

let _57_2148 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_772 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _148_771 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _148_772 _148_771)))
end else begin
()
end
in (let _148_773 = (push_binding env x)
in (x, _148_773, g, u))))
end))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe Prims.list) = (fun env bs -> (

let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_TypeChecker_Rel.trivial_guard, [])
end
| (b)::bs -> begin
(

let _57_2163 = (tc_binder env b)
in (match (_57_2163) with
| (b, env', g, u) -> begin
(

let _57_2168 = (aux env' bs)
in (match (_57_2168) with
| (bs, env', g', us) -> begin
(let _148_781 = (let _148_780 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _148_780))
in ((b)::bs, env', _148_781, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun _57_2176 _57_2179 -> (match ((_57_2176, _57_2179)) with
| ((t, imp), (args, g)) -> begin
(

let _57_2184 = (tc_term env t)
in (match (_57_2184) with
| (t, _57_2182, g') -> begin
(let _148_790 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _148_790))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _57_2188 -> (match (_57_2188) with
| (pats, g) -> begin
(

let _57_2191 = (tc_args env p)
in (match (_57_2191) with
| (args, g') -> begin
(let _148_793 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _148_793))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _57_2197 = (tc_maybe_toplevel_term env e)
in (match (_57_2197) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let _57_2200 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_796 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _148_796))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _57_2205 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _148_797 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_148_797, false))
end else begin
(let _148_798 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_148_798, true))
end
in (match (_57_2205) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _148_799 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _148_799))
end
| _57_2209 -> begin
if allow_ghost then begin
(let _148_802 = (let _148_801 = (let _148_800 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_148_800, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_148_801))
in (Prims.raise _148_802))
end else begin
(let _148_805 = (let _148_804 = (let _148_803 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_148_803, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_148_804))
in (Prims.raise _148_805))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))


let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let _57_2219 = (tc_tot_or_gtot_term env t)
in (match (_57_2219) with
| (t, c, g) -> begin
(

let _57_2220 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let _57_2228 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_2228) with
| (t, c, g) -> begin
(

let _57_2229 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _148_825 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _148_825)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _148_829 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _148_829))))


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let _57_2244 = (tc_binders env tps)
in (match (_57_2244) with
| (tps, env, g, us) -> begin
(

let _57_2245 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (

let fail = (fun _57_2251 -> (match (()) with
| () -> begin
(let _148_844 = (let _148_843 = (let _148_842 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_148_842, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_148_843))
in (Prims.raise _148_844))
end))
in (

let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _57_2264))::((wp, _57_2260))::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2268 -> begin
(fail ())
end))
end
| _57_2270 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let _57_2277 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_57_2277) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _57_2279 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let _57_2283 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_57_2283) with
| (uvs, t') -> begin
(match ((let _148_851 = (FStar_Syntax_Subst.compress t')
in _148_851.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _57_2289 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))


let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (

let fail = (fun t -> (let _148_862 = (let _148_861 = (let _148_860 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_148_860, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_148_861))
in (Prims.raise _148_862)))
in (match ((let _148_863 = (FStar_Syntax_Subst.compress signature)
in _148_863.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _57_2306))::((wp, _57_2302))::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2310 -> begin
(fail signature)
end))
end
| _57_2312 -> begin
(fail signature)
end)))


let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (

let _57_2317 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_57_2317) with
| (a, wp) -> begin
(

let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _57_2320 -> begin
(

let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (

let op = (fun ts -> (

let _57_2324 = ()
in (

let t0 = (Prims.snd ts)
in (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (

let _57_2328 = ed
in (let _148_879 = (op ed.FStar_Syntax_Syntax.ret)
in (let _148_878 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _148_877 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _148_876 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _148_875 = (op ed.FStar_Syntax_Syntax.stronger)
in (let _148_874 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _148_873 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _148_872 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _148_871 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _148_870 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _57_2328.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2328.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2328.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2328.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2328.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _148_879; FStar_Syntax_Syntax.bind_wp = _148_878; FStar_Syntax_Syntax.if_then_else = _148_877; FStar_Syntax_Syntax.ite_wp = _148_876; FStar_Syntax_Syntax.stronger = _148_875; FStar_Syntax_Syntax.close_wp = _148_874; FStar_Syntax_Syntax.assert_p = _148_873; FStar_Syntax_Syntax.assume_p = _148_872; FStar_Syntax_Syntax.null_wp = _148_871; FStar_Syntax_Syntax.trivial = _148_870})))))))))))))
end)
in (ed, a, wp))
end)))


let gen_wps_for_free : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env binders a wp_a ed -> (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env)
in (

let d = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))
in (

let normalize_and_make_binders_explicit = (fun tm -> (

let tm = (normalize tm)
in (

let rec visit_term = (fun tm -> (

let n = (match ((let _148_901 = (FStar_Syntax_Subst.compress tm)
in _148_901.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let comp = (visit_comp comp)
in (

let binders = (FStar_List.map visit_binder binders)
in FStar_Syntax_Syntax.Tm_arrow ((binders, comp))))
end
| FStar_Syntax_Syntax.Tm_abs (binders, term, comp) -> begin
(

let comp = (visit_maybe_lcomp comp)
in (

let term = (visit_term term)
in (

let binders = (FStar_List.map visit_binder binders)
in FStar_Syntax_Syntax.Tm_abs ((binders, term, comp)))))
end
| _57_2363 -> begin
tm.FStar_Syntax_Syntax.n
end)
in (

let _57_2365 = tm
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2365.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2365.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2365.FStar_Syntax_Syntax.vars})))
and visit_binder = (fun _57_2369 -> (match (_57_2369) with
| (bv, a) -> begin
(let _148_905 = (

let _57_2370 = bv
in (let _148_903 = (visit_term bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_2370.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2370.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_903}))
in (let _148_904 = (FStar_Syntax_Syntax.as_implicit false)
in (_148_905, _148_904)))
end))
and visit_maybe_lcomp = (fun lcomp -> (match (lcomp) with
| Some (FStar_Util.Inl (lcomp)) -> begin
(let _148_910 = (let _148_909 = (let _148_908 = (let _148_907 = (lcomp.FStar_Syntax_Syntax.comp ())
in (visit_comp _148_907))
in (FStar_Syntax_Util.lcomp_of_comp _148_908))
in FStar_Util.Inl (_148_909))
in Some (_148_910))
end
| comp -> begin
comp
end))
and visit_comp = (fun comp -> (

let n = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tm) -> begin
(let _148_912 = (visit_term tm)
in FStar_Syntax_Syntax.Total (_148_912))
end
| FStar_Syntax_Syntax.GTotal (tm) -> begin
(let _148_913 = (visit_term tm)
in FStar_Syntax_Syntax.GTotal (_148_913))
end
| comp -> begin
comp
end)
in (

let _57_2384 = comp
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2384.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2384.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2384.FStar_Syntax_Syntax.vars})))
and visit_args = (fun args -> (FStar_List.map (fun _57_2389 -> (match (_57_2389) with
| (tm, q) -> begin
(let _148_916 = (visit_term tm)
in (_148_916, q))
end)) args))
in (visit_term tm))))
in (

let check = (fun str t -> if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _57_2393 = (let _148_921 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Generated term for %s: %s\n" str _148_921))
in (

let t = (normalize t)
in (

let t = (FStar_Syntax_Subst.compress t)
in (

let _57_2408 = (tc_term env t)
in (match (_57_2408) with
| (e, {FStar_Syntax_Syntax.eff_name = _57_2404; FStar_Syntax_Syntax.res_typ = res_typ; FStar_Syntax_Syntax.cflags = _57_2401; FStar_Syntax_Syntax.comp = _57_2399}, _57_2407) -> begin
(

let _57_2409 = (let _148_924 = (let _148_923 = (normalize res_typ)
in (FStar_Syntax_Print.term_to_string _148_923))
in (FStar_Util.print2 "Inferred type for %s: %s\n" str _148_924))
in (let _148_926 = (let _148_925 = (normalize e)
in (FStar_Syntax_Print.term_to_string _148_925))
in (FStar_Util.print2 "Elaborated term for %s: %s\n" str _148_926)))
end)))))
end else begin
()
end)
in (

let rec collect_binders = (fun t -> (match ((let _148_929 = (FStar_Syntax_Subst.compress t)
in _148_929.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
t
end
| _57_2420 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _148_930 = (collect_binders rest)
in (FStar_List.append bs _148_930)))
end
| FStar_Syntax_Syntax.Tm_type (_57_2423) -> begin
[]
end
| _57_2426 -> begin
(FStar_All.failwith "wp_a doesn\'t end in Type0")
end))
in (

let _57_2441 = (

let i = (FStar_ST.alloc 0)
in (

let wp_binders = (let _148_937 = (normalize wp_a)
in (collect_binders _148_937))
in ((fun t -> (let _148_943 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow wp_binders _148_943))), (fun t -> (let _148_946 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow wp_binders _148_946))), (fun _57_2431 -> (match (()) with
| () -> begin
(FStar_List.map (fun _57_2435 -> (match (_57_2435) with
| (bv, _57_2434) -> begin
(

let _57_2436 = (let _148_950 = ((FStar_ST.read i) + 1)
in (FStar_ST.op_Colon_Equals i _148_950))
in (let _148_953 = (let _148_952 = (let _148_951 = (FStar_ST.read i)
in (FStar_Util.string_of_int _148_951))
in (Prims.strcat "g" _148_952))
in (FStar_Syntax_Syntax.gen_bv _148_953 None bv.FStar_Syntax_Syntax.sort)))
end)) wp_binders)
end)))))
in (match (_57_2441) with
| (mk_ctx, mk_gctx, mk_gamma) -> begin
(

let binders_of_list = (FStar_List.map (fun _57_2444 -> (match (_57_2444) with
| (t, b) -> begin
(let _148_959 = (FStar_Syntax_Syntax.as_implicit b)
in (t, _148_959))
end)))
in (

let implicit_binders_of_list = (FStar_List.map (fun t -> (let _148_962 = (FStar_Syntax_Syntax.as_implicit true)
in (t, _148_962))))
in (

let args_of_bv = (FStar_List.map (fun bv -> (let _148_965 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_Syntax_Syntax.as_arg _148_965))))
in (

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let x = (let _148_966 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _148_966))
in (

let ret = (let _148_971 = (let _148_970 = (let _148_969 = (let _148_968 = (let _148_967 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx _148_967))
in (FStar_Syntax_Syntax.mk_Total _148_968))
in (FStar_Syntax_Util.lcomp_of_comp _148_969))
in FStar_Util.Inl (_148_970))
in Some (_148_971))
in (

let gamma = (mk_gamma ())
in (

let body = (let _148_973 = (implicit_binders_of_list gamma)
in (let _148_972 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs _148_973 _148_972 ret)))
in (let _148_974 = (binders_of_list (((t, true))::((x, false))::[]))
in (FStar_Syntax_Util.abs _148_974 body ret)))))))
in (

let _57_2456 = (let _148_978 = (let _148_977 = (let _148_976 = (let _148_975 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_975)::[])
in (FStar_List.append binders _148_976))
in (FStar_Syntax_Util.abs _148_977 c_pure None))
in (check "pure" _148_978))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let l = (let _148_986 = (let _148_985 = (let _148_984 = (let _148_981 = (let _148_980 = (let _148_979 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _148_979))
in (FStar_Syntax_Syntax.mk_binder _148_980))
in (_148_981)::[])
in (let _148_983 = (let _148_982 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _148_982))
in (FStar_Syntax_Util.arrow _148_984 _148_983)))
in (mk_gctx _148_985))
in (FStar_Syntax_Syntax.gen_bv "l" None _148_986))
in (

let r = (let _148_988 = (let _148_987 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _148_987))
in (FStar_Syntax_Syntax.gen_bv "r" None _148_988))
in (

let ret = (let _148_993 = (let _148_992 = (let _148_991 = (let _148_990 = (let _148_989 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _148_989))
in (FStar_Syntax_Syntax.mk_Total _148_990))
in (FStar_Syntax_Util.lcomp_of_comp _148_991))
in FStar_Util.Inl (_148_992))
in Some (_148_993))
in (

let outer_body = (

let gamma = (mk_gamma ())
in (

let gamma_as_args = (args_of_bv gamma)
in (

let inner_body = (let _148_999 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _148_998 = (let _148_997 = (let _148_996 = (let _148_995 = (let _148_994 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _148_994 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg _148_995))
in (_148_996)::[])
in (FStar_List.append gamma_as_args _148_997))
in (FStar_Syntax_Util.mk_app _148_999 _148_998)))
in (let _148_1000 = (implicit_binders_of_list gamma)
in (FStar_Syntax_Util.abs _148_1000 inner_body ret)))))
in (let _148_1001 = (binders_of_list (((t1, true))::((t2, true))::((l, false))::((r, false))::[]))
in (FStar_Syntax_Util.abs _148_1001 outer_body ret))))))))
in (

let _57_2468 = (let _148_1005 = (let _148_1004 = (let _148_1003 = (let _148_1002 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_1002)::[])
in (FStar_List.append binders _148_1003))
in (FStar_Syntax_Util.abs _148_1004 c_app None))
in (check "app" _148_1005))
in (

let unknown = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _148_1010 = (let _148_1007 = (let _148_1006 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _148_1006))
in (_148_1007)::[])
in (let _148_1009 = (let _148_1008 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _148_1008))
in (FStar_Syntax_Util.arrow _148_1010 _148_1009)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _148_1012 = (let _148_1011 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _148_1011))
in (FStar_Syntax_Syntax.gen_bv "a1" None _148_1012))
in (

let ret = (let _148_1017 = (let _148_1016 = (let _148_1015 = (let _148_1014 = (let _148_1013 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _148_1013))
in (FStar_Syntax_Syntax.mk_Total _148_1014))
in (FStar_Syntax_Util.lcomp_of_comp _148_1015))
in FStar_Util.Inl (_148_1016))
in Some (_148_1017))
in (let _148_1030 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::((a1, false))::[]))
in (let _148_1029 = (let _148_1028 = (let _148_1027 = (let _148_1026 = (let _148_1025 = (let _148_1024 = (let _148_1021 = (let _148_1020 = (let _148_1019 = (let _148_1018 = (FStar_Syntax_Syntax.bv_to_name f)
in (_148_1018)::[])
in (unknown)::_148_1019)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1020))
in (FStar_Syntax_Util.mk_app c_pure _148_1021))
in (let _148_1023 = (let _148_1022 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_148_1022)::[])
in (_148_1024)::_148_1023))
in (unknown)::_148_1025)
in (unknown)::_148_1026)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1027))
in (FStar_Syntax_Util.mk_app c_app _148_1028))
in (FStar_Syntax_Util.abs _148_1030 _148_1029 ret)))))))))
in (

let _57_2478 = (let _148_1034 = (let _148_1033 = (let _148_1032 = (let _148_1031 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_1031)::[])
in (FStar_List.append binders _148_1032))
in (FStar_Syntax_Util.abs _148_1033 c_lift1 None))
in (check "lift1" _148_1034))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _148_1042 = (let _148_1039 = (let _148_1035 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _148_1035))
in (let _148_1038 = (let _148_1037 = (let _148_1036 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder _148_1036))
in (_148_1037)::[])
in (_148_1039)::_148_1038))
in (let _148_1041 = (let _148_1040 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal _148_1040))
in (FStar_Syntax_Util.arrow _148_1042 _148_1041)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _148_1044 = (let _148_1043 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _148_1043))
in (FStar_Syntax_Syntax.gen_bv "a1" None _148_1044))
in (

let a2 = (let _148_1046 = (let _148_1045 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _148_1045))
in (FStar_Syntax_Syntax.gen_bv "a2" None _148_1046))
in (

let ret = (let _148_1051 = (let _148_1050 = (let _148_1049 = (let _148_1048 = (let _148_1047 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx _148_1047))
in (FStar_Syntax_Syntax.mk_Total _148_1048))
in (FStar_Syntax_Util.lcomp_of_comp _148_1049))
in FStar_Util.Inl (_148_1050))
in Some (_148_1051))
in (let _148_1071 = (binders_of_list (((t1, true))::((t2, true))::((t3, true))::((f, false))::((a1, false))::((a2, false))::[]))
in (let _148_1070 = (let _148_1069 = (let _148_1068 = (let _148_1067 = (let _148_1066 = (let _148_1065 = (let _148_1062 = (let _148_1061 = (let _148_1060 = (let _148_1059 = (let _148_1058 = (let _148_1055 = (let _148_1054 = (let _148_1053 = (let _148_1052 = (FStar_Syntax_Syntax.bv_to_name f)
in (_148_1052)::[])
in (unknown)::_148_1053)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1054))
in (FStar_Syntax_Util.mk_app c_pure _148_1055))
in (let _148_1057 = (let _148_1056 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_148_1056)::[])
in (_148_1058)::_148_1057))
in (unknown)::_148_1059)
in (unknown)::_148_1060)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1061))
in (FStar_Syntax_Util.mk_app c_app _148_1062))
in (let _148_1064 = (let _148_1063 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_148_1063)::[])
in (_148_1065)::_148_1064))
in (unknown)::_148_1066)
in (unknown)::_148_1067)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1068))
in (FStar_Syntax_Util.mk_app c_app _148_1069))
in (FStar_Syntax_Util.abs _148_1071 _148_1070 ret)))))))))))
in (

let _57_2489 = (let _148_1075 = (let _148_1074 = (let _148_1073 = (let _148_1072 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_1072)::[])
in (FStar_List.append binders _148_1073))
in (FStar_Syntax_Util.abs _148_1074 c_lift2 None))
in (check "lift2" _148_1075))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _148_1081 = (let _148_1077 = (let _148_1076 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _148_1076))
in (_148_1077)::[])
in (let _148_1080 = (let _148_1079 = (let _148_1078 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _148_1078))
in (FStar_Syntax_Syntax.mk_Total _148_1079))
in (FStar_Syntax_Util.arrow _148_1081 _148_1080)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let ret = (let _148_1091 = (let _148_1090 = (let _148_1089 = (let _148_1088 = (let _148_1087 = (let _148_1086 = (let _148_1083 = (let _148_1082 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _148_1082))
in (_148_1083)::[])
in (let _148_1085 = (let _148_1084 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _148_1084))
in (FStar_Syntax_Util.arrow _148_1086 _148_1085)))
in (mk_ctx _148_1087))
in (FStar_Syntax_Syntax.mk_Total _148_1088))
in (FStar_Syntax_Util.lcomp_of_comp _148_1089))
in FStar_Util.Inl (_148_1090))
in Some (_148_1091))
in (

let e1 = (let _148_1092 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _148_1092))
in (

let gamma = (mk_gamma ())
in (

let body = (let _148_1102 = (let _148_1095 = (FStar_Syntax_Syntax.binders_of_list gamma)
in (let _148_1094 = (let _148_1093 = (FStar_Syntax_Syntax.mk_binder e1)
in (_148_1093)::[])
in (FStar_List.append _148_1095 _148_1094)))
in (let _148_1101 = (let _148_1100 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _148_1099 = (let _148_1098 = (let _148_1096 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _148_1096))
in (let _148_1097 = (args_of_bv gamma)
in (_148_1098)::_148_1097))
in (FStar_Syntax_Util.mk_app _148_1100 _148_1099)))
in (FStar_Syntax_Util.abs _148_1102 _148_1101 ret)))
in (let _148_1103 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::[]))
in (FStar_Syntax_Util.abs _148_1103 body ret))))))))))
in (

let _57_2500 = (let _148_1107 = (let _148_1106 = (let _148_1105 = (let _148_1104 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_1104)::[])
in (FStar_List.append binders _148_1105))
in (FStar_Syntax_Util.abs _148_1106 c_push None))
in (check "push" _148_1107))
in (

let ret_tot_wp_a = (let _148_1110 = (let _148_1109 = (let _148_1108 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _148_1108))
in FStar_Util.Inl (_148_1109))
in Some (_148_1110))
in (

let wp_if_then_else = (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _148_1121 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (let _148_1120 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_unfoldable (2)) None)
in (let _148_1119 = (let _148_1118 = (let _148_1117 = (let _148_1116 = (let _148_1115 = (let _148_1114 = (let _148_1113 = (let _148_1112 = (let _148_1111 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _148_1111))
in (_148_1112)::[])
in (FStar_Syntax_Util.mk_app l_ite _148_1113))
in (_148_1114)::[])
in (unknown)::_148_1115)
in (unknown)::_148_1116)
in (unknown)::_148_1117)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1118))
in (FStar_Syntax_Util.mk_app c_lift2 _148_1119)))
in (FStar_Syntax_Util.abs _148_1121 _148_1120 ret_tot_wp_a))))
in (

let wp_if_then_else = (normalize_and_make_binders_explicit wp_if_then_else)
in (

let _57_2507 = (let _148_1122 = (FStar_Syntax_Util.abs binders wp_if_then_else None)
in (check "wp_if_then_else" _148_1122))
in (

let wp_assert = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_and = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (

let body = (let _148_1136 = (let _148_1135 = (let _148_1134 = (let _148_1133 = (let _148_1132 = (let _148_1129 = (let _148_1128 = (let _148_1127 = (let _148_1126 = (let _148_1125 = (let _148_1124 = (let _148_1123 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _148_1123))
in (_148_1124)::[])
in (FStar_Syntax_Util.mk_app l_and _148_1125))
in (_148_1126)::[])
in (unknown)::_148_1127)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1128))
in (FStar_Syntax_Util.mk_app c_pure _148_1129))
in (let _148_1131 = (let _148_1130 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_148_1130)::[])
in (_148_1132)::_148_1131))
in (unknown)::_148_1133)
in (unknown)::_148_1134)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1135))
in (FStar_Syntax_Util.mk_app c_app _148_1136))
in (let _148_1137 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _148_1137 body ret_tot_wp_a))))))
in (

let wp_assert = (normalize_and_make_binders_explicit wp_assert)
in (

let _57_2515 = (let _148_1138 = (FStar_Syntax_Util.abs binders wp_assert None)
in (check "wp_assert" _148_1138))
in (

let wp_assume = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_imp = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (

let body = (let _148_1152 = (let _148_1151 = (let _148_1150 = (let _148_1149 = (let _148_1148 = (let _148_1145 = (let _148_1144 = (let _148_1143 = (let _148_1142 = (let _148_1141 = (let _148_1140 = (let _148_1139 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _148_1139))
in (_148_1140)::[])
in (FStar_Syntax_Util.mk_app l_imp _148_1141))
in (_148_1142)::[])
in (unknown)::_148_1143)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1144))
in (FStar_Syntax_Util.mk_app c_pure _148_1145))
in (let _148_1147 = (let _148_1146 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_148_1146)::[])
in (_148_1148)::_148_1147))
in (unknown)::_148_1149)
in (unknown)::_148_1150)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1151))
in (FStar_Syntax_Util.mk_app c_app _148_1152))
in (let _148_1153 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _148_1153 body ret_tot_wp_a))))))
in (

let wp_assume = (normalize_and_make_binders_explicit wp_assume)
in (

let _57_2523 = (let _148_1154 = (FStar_Syntax_Util.abs binders wp_assume None)
in (check "wp_assume" _148_1154))
in (

let tforall = (let _148_1157 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _148_1156 = (let _148_1155 = (FStar_Syntax_Syntax.as_arg unknown)
in (_148_1155)::[])
in (FStar_Syntax_Util.mk_app _148_1157 _148_1156)))
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _148_1161 = (let _148_1159 = (let _148_1158 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _148_1158))
in (_148_1159)::[])
in (let _148_1160 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1161 _148_1160)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (let _148_1174 = (let _148_1173 = (let _148_1172 = (let _148_1171 = (let _148_1170 = (let _148_1162 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((unknown)::(tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _148_1162))
in (let _148_1169 = (let _148_1168 = (let _148_1167 = (let _148_1166 = (let _148_1165 = (let _148_1164 = (let _148_1163 = (FStar_Syntax_Syntax.bv_to_name f)
in (_148_1163)::[])
in (unknown)::_148_1164)
in (unknown)::_148_1165)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1166))
in (FStar_Syntax_Util.mk_app c_push _148_1167))
in (_148_1168)::[])
in (_148_1170)::_148_1169))
in (unknown)::_148_1171)
in (unknown)::_148_1172)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1173))
in (FStar_Syntax_Util.mk_app c_app _148_1174))
in (let _148_1175 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_Syntax_Util.abs _148_1175 body ret_tot_wp_a))))))
in (

let wp_close = (normalize_and_make_binders_explicit wp_close)
in (

let _57_2532 = (let _148_1176 = (FStar_Syntax_Util.abs binders wp_close None)
in (check "wp_close" _148_1176))
in (

let ret_tot_type0 = (let _148_1179 = (let _148_1178 = (let _148_1177 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_1177))
in FStar_Util.Inl (_148_1178))
in Some (_148_1179))
in (

let mk_forall = (fun x body -> (

let tforall = (let _148_1186 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _148_1185 = (let _148_1184 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (_148_1184)::[])
in (FStar_Syntax_Util.mk_app _148_1186 _148_1185)))
in (let _148_1193 = (let _148_1192 = (let _148_1191 = (let _148_1190 = (let _148_1189 = (let _148_1188 = (let _148_1187 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_1187)::[])
in (FStar_Syntax_Util.abs _148_1188 body ret_tot_type0))
in (FStar_Syntax_Syntax.as_arg _148_1189))
in (_148_1190)::[])
in (tforall, _148_1191))
in FStar_Syntax_Syntax.Tm_app (_148_1192))
in (FStar_Syntax_Syntax.mk _148_1193 None FStar_Range.dummyRange))))
in (

let rec mk_leq = (fun t x y -> (match ((let _148_1201 = (let _148_1200 = (FStar_Syntax_Subst.compress t)
in (normalize _148_1200))
in _148_1201.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_2544) -> begin
(FStar_Syntax_Util.mk_imp x y)
end
| (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) when (FStar_Syntax_Syntax.is_null_binder binder) -> begin
(

let a = (Prims.fst binder).FStar_Syntax_Syntax.sort
in (

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (

let body = (let _148_1213 = (let _148_1203 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _148_1202 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_leq a _148_1203 _148_1202)))
in (let _148_1212 = (let _148_1211 = (let _148_1206 = (let _148_1205 = (let _148_1204 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _148_1204))
in (_148_1205)::[])
in (FStar_Syntax_Util.mk_app x _148_1206))
in (let _148_1210 = (let _148_1209 = (let _148_1208 = (let _148_1207 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _148_1207))
in (_148_1208)::[])
in (FStar_Syntax_Util.mk_app y _148_1209))
in (mk_leq b _148_1211 _148_1210)))
in (FStar_Syntax_Util.mk_imp _148_1213 _148_1212)))
in (let _148_1214 = (mk_forall a2 body)
in (mk_forall a1 _148_1214))))))
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let _57_2580 = t
in (let _148_1218 = (let _148_1217 = (let _148_1216 = (let _148_1215 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _148_1215))
in ((binder)::[], _148_1216))
in FStar_Syntax_Syntax.Tm_arrow (_148_1217))
in {FStar_Syntax_Syntax.n = _148_1218; FStar_Syntax_Syntax.tk = _57_2580.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2580.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2580.FStar_Syntax_Syntax.vars}))
in (mk_leq t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_57_2584) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _57_2587 -> begin
(FStar_Syntax_Util.mk_eq t t x y)
end))
in (

let stronger = (

let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (

let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (

let body = (let _148_1220 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _148_1219 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_leq wp_a _148_1220 _148_1219)))
in (let _148_1221 = (FStar_Syntax_Syntax.binders_of_list ((wp1)::(wp2)::[]))
in (FStar_Syntax_Util.abs _148_1221 body ret_tot_type0)))))
in (

let _57_2592 = (let _148_1225 = (let _148_1224 = (let _148_1223 = (let _148_1222 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_1222)::[])
in (FStar_List.append binders _148_1223))
in (FStar_Syntax_Util.abs _148_1224 stronger None))
in (check "stronger" _148_1225))
in (

let null_wp = (Prims.snd ed.FStar_Syntax_Syntax.null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (let _148_1233 = (let _148_1232 = (let _148_1231 = (let _148_1228 = (let _148_1227 = (let _148_1226 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _148_1226))
in (_148_1227)::[])
in (FStar_Syntax_Util.mk_app null_wp _148_1228))
in (let _148_1230 = (let _148_1229 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_148_1229)::[])
in (_148_1231)::_148_1230))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1232))
in (FStar_Syntax_Util.mk_app stronger _148_1233))
in (let _148_1234 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_Syntax_Util.abs _148_1234 body ret_tot_type0))))
in (

let wp_trivial = (normalize_and_make_binders_explicit wp_trivial)
in (

let _57_2599 = (let _148_1235 = (FStar_Syntax_Util.abs binders wp_trivial None)
in (check "wp_trivial" _148_1235))
in (

let _57_2601 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2601.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2601.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2601.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2601.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2601.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _57_2601.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2601.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = ([], wp_if_then_else); FStar_Syntax_Syntax.ite_wp = _57_2601.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _57_2601.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = ([], wp_close); FStar_Syntax_Syntax.assert_p = ([], wp_assert); FStar_Syntax_Syntax.assume_p = ([], wp_assume); FStar_Syntax_Syntax.null_wp = _57_2601.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = ([], wp_trivial)}))))))))))))))))))))))))))))))))))))))
end))))))))


let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  effect_cost  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed is_for_free -> (

let _57_2606 = ()
in (

let _57_2610 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_57_2610) with
| (binders_un, signature_un) -> begin
(

let _57_2615 = (tc_tparams env0 binders_un)
in (match (_57_2615) with
| (binders, env, _57_2614) -> begin
(

let _57_2619 = (tc_trivial_guard env signature_un)
in (match (_57_2619) with
| (signature, _57_2618) -> begin
(

let ed = (

let _57_2620 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2620.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2620.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2620.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _57_2620.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2620.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _57_2620.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _57_2620.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _57_2620.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _57_2620.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _57_2620.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _57_2620.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _57_2620.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _57_2620.FStar_Syntax_Syntax.trivial})
in (

let _57_2626 = (open_effect_decl env ed)
in (match (_57_2626) with
| (ed, a, wp_a) -> begin
(

let get_effect_signature = (fun _57_2628 -> (match (()) with
| () -> begin
(

let _57_2632 = (tc_trivial_guard env signature_un)
in (match (_57_2632) with
| (signature, _57_2631) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (

let env = (let _148_1244 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _148_1244))
in (

let _57_2634 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _148_1247 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _148_1246 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _148_1245 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checking effect signature: %s %s : %s\n" _148_1247 _148_1246 _148_1245))))
end else begin
()
end
in (

let check_and_gen' = (fun env _57_2641 k -> (match (_57_2641) with
| (_57_2639, t) -> begin
(check_and_gen env t k)
end))
in (

let ed = (match (is_for_free) with
| NotForFree -> begin
ed
end
| ForFree -> begin
(gen_wps_for_free env binders a wp_a ed)
end)
in (

let ret = (

let expected_k = (let _148_1259 = (let _148_1257 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1256 = (let _148_1255 = (let _148_1254 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _148_1254))
in (_148_1255)::[])
in (_148_1257)::_148_1256))
in (let _148_1258 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _148_1259 _148_1258)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (

let bind_wp = (

let _57_2650 = (get_effect_signature ())
in (match (_57_2650) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _148_1263 = (let _148_1261 = (let _148_1260 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _148_1260))
in (_148_1261)::[])
in (let _148_1262 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _148_1263 _148_1262)))
in (

let expected_k = (let _148_1274 = (let _148_1272 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _148_1271 = (let _148_1270 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1269 = (let _148_1268 = (FStar_Syntax_Syntax.mk_binder b)
in (let _148_1267 = (let _148_1266 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _148_1265 = (let _148_1264 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (_148_1264)::[])
in (_148_1266)::_148_1265))
in (_148_1268)::_148_1267))
in (_148_1270)::_148_1269))
in (_148_1272)::_148_1271))
in (let _148_1273 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _148_1274 _148_1273)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (let _148_1276 = (let _148_1275 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_1275 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _148_1276))
in (

let expected_k = (let _148_1285 = (let _148_1283 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1282 = (let _148_1281 = (FStar_Syntax_Syntax.mk_binder p)
in (let _148_1280 = (let _148_1279 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _148_1278 = (let _148_1277 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1277)::[])
in (_148_1279)::_148_1278))
in (_148_1281)::_148_1280))
in (_148_1283)::_148_1282))
in (let _148_1284 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1285 _148_1284)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (let _148_1290 = (let _148_1288 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1287 = (let _148_1286 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1286)::[])
in (_148_1288)::_148_1287))
in (let _148_1289 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1290 _148_1289)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let _57_2662 = (FStar_Syntax_Util.type_u ())
in (match (_57_2662) with
| (t, _57_2661) -> begin
(

let expected_k = (let _148_1297 = (let _148_1295 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1294 = (let _148_1293 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _148_1292 = (let _148_1291 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1291)::[])
in (_148_1293)::_148_1292))
in (_148_1295)::_148_1294))
in (let _148_1296 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _148_1297 _148_1296)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (let _148_1299 = (let _148_1298 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_1298 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _148_1299))
in (

let b_wp_a = (let _148_1303 = (let _148_1301 = (let _148_1300 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _148_1300))
in (_148_1301)::[])
in (let _148_1302 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1303 _148_1302)))
in (

let expected_k = (let _148_1310 = (let _148_1308 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1307 = (let _148_1306 = (FStar_Syntax_Syntax.mk_binder b)
in (let _148_1305 = (let _148_1304 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_148_1304)::[])
in (_148_1306)::_148_1305))
in (_148_1308)::_148_1307))
in (let _148_1309 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1310 _148_1309)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (let _148_1319 = (let _148_1317 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1316 = (let _148_1315 = (let _148_1312 = (let _148_1311 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_1311 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _148_1312))
in (let _148_1314 = (let _148_1313 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1313)::[])
in (_148_1315)::_148_1314))
in (_148_1317)::_148_1316))
in (let _148_1318 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1319 _148_1318)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _148_1328 = (let _148_1326 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1325 = (let _148_1324 = (let _148_1321 = (let _148_1320 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_1320 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _148_1321))
in (let _148_1323 = (let _148_1322 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1322)::[])
in (_148_1324)::_148_1323))
in (_148_1326)::_148_1325))
in (let _148_1327 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1328 _148_1327)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _148_1331 = (let _148_1329 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_1329)::[])
in (let _148_1330 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1331 _148_1330)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let _57_2678 = (FStar_Syntax_Util.type_u ())
in (match (_57_2678) with
| (t, _57_2677) -> begin
(

let expected_k = (let _148_1336 = (let _148_1334 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1333 = (let _148_1332 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1332)::[])
in (_148_1334)::_148_1333))
in (let _148_1335 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _148_1336 _148_1335)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let t = (let _148_1337 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _148_1337))
in (

let _57_2684 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_57_2684) with
| (univs, t) -> begin
(

let _57_2700 = (match ((let _148_1339 = (let _148_1338 = (FStar_Syntax_Subst.compress t)
in _148_1338.FStar_Syntax_Syntax.n)
in (binders, _148_1339))) with
| ([], _57_2687) -> begin
([], t)
end
| (_57_2690, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _57_2697 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_2700) with
| (binders, signature) -> begin
(

let close = (fun n ts -> (

let ts = (let _148_1344 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _148_1344))
in (

let _57_2705 = ()
in ts)))
in (

let ed = (

let _57_2707 = ed
in (let _148_1354 = (close 0 ret)
in (let _148_1353 = (close 1 bind_wp)
in (let _148_1352 = (close 0 if_then_else)
in (let _148_1351 = (close 0 ite_wp)
in (let _148_1350 = (close 0 stronger)
in (let _148_1349 = (close 1 close_wp)
in (let _148_1348 = (close 0 assert_p)
in (let _148_1347 = (close 0 assume_p)
in (let _148_1346 = (close 0 null_wp)
in (let _148_1345 = (close 0 trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _57_2707.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2707.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _148_1354; FStar_Syntax_Syntax.bind_wp = _148_1353; FStar_Syntax_Syntax.if_then_else = _148_1352; FStar_Syntax_Syntax.ite_wp = _148_1351; FStar_Syntax_Syntax.stronger = _148_1350; FStar_Syntax_Syntax.close_wp = _148_1349; FStar_Syntax_Syntax.assert_p = _148_1348; FStar_Syntax_Syntax.assume_p = _148_1347; FStar_Syntax_Syntax.null_wp = _148_1346; FStar_Syntax_Syntax.trivial = _148_1345})))))))))))
in (

let _57_2710 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1355 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _148_1355))
end else begin
()
end
in ed)))
end))
end))))))))))))))))))
end)))
end))
end))
end))))


let tc_lex_t = (fun env ses quals lids -> (

let _57_2716 = ()
in (

let _57_2724 = ()
in (match (ses) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _57_2753, _57_2755, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _57_2744, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _57_2733, r2))::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(

let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (

let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (

let tc = FStar_Syntax_Syntax.Sig_inductive_typ ((lex_t, (u)::[], [], t, [], (FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[], [], r))
in (

let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (

let lex_top_t = (let _148_1363 = (let _148_1362 = (let _148_1361 = (let _148_1360 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _148_1360 FStar_Syntax_Syntax.Delta_constant None))
in (_148_1361, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_148_1362))
in (FStar_Syntax_Syntax.mk _148_1363 None r1))
in (

let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (

let dc_lextop = FStar_Syntax_Syntax.Sig_datacon ((lex_top, (utop)::[], lex_top_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r1))
in (

let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (

let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (

let lex_cons_t = (

let a = (let _148_1364 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _148_1364))
in (

let hd = (let _148_1365 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _148_1365))
in (

let tl = (let _148_1370 = (let _148_1369 = (let _148_1368 = (let _148_1367 = (let _148_1366 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _148_1366 FStar_Syntax_Syntax.Delta_constant None))
in (_148_1367, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_148_1368))
in (FStar_Syntax_Syntax.mk _148_1369 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _148_1370))
in (

let res = (let _148_1374 = (let _148_1373 = (let _148_1372 = (let _148_1371 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _148_1371 FStar_Syntax_Syntax.Delta_constant None))
in (_148_1372, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_148_1373))
in (FStar_Syntax_Syntax.mk _148_1374 None r2))
in (let _148_1375 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _148_1375))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _148_1377 = (let _148_1376 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _148_1376))
in FStar_Syntax_Syntax.Sig_bundle (_148_1377)))))))))))))))
end
| _57_2779 -> begin
(let _148_1379 = (let _148_1378 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _148_1378))
in (FStar_All.failwith _148_1379))
end))))


let tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _57_2789 = (FStar_Syntax_Util.type_u ())
in (match (_57_2789) with
| (k, _57_2788) -> begin
(

let phi = (let _148_1390 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _148_1390 (norm env)))
in (

let _57_2791 = (FStar_TypeChecker_Util.check_uvars r phi)
in FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))))
end))))


let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _148_1404 = (let _148_1403 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _148_1403))
in (FStar_TypeChecker_Errors.diag r _148_1404)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let _57_2814 = ()
in (

let _57_2816 = (warn_positivity tc r)
in (

let _57_2820 = (FStar_Syntax_Subst.open_term tps k)
in (match (_57_2820) with
| (tps, k) -> begin
(

let _57_2825 = (tc_binders env tps)
in (match (_57_2825) with
| (tps, env_tps, guard_params, us) -> begin
(

let _57_2828 = (FStar_Syntax_Util.arrow_formals k)
in (match (_57_2828) with
| (indices, t) -> begin
(

let _57_2833 = (tc_binders env_tps indices)
in (match (_57_2833) with
| (indices, env', guard_indices, us') -> begin
(

let _57_2841 = (

let _57_2838 = (tc_tot_or_gtot_term env' t)
in (match (_57_2838) with
| (t, _57_2836, g) -> begin
(let _148_1411 = (let _148_1410 = (let _148_1409 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params _148_1409))
in (FStar_TypeChecker_Rel.discharge_guard env' _148_1410))
in (t, _148_1411))
end))
in (match (_57_2841) with
| (t, guard) -> begin
(

let k = (let _148_1412 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _148_1412))
in (

let _57_2845 = (FStar_Syntax_Util.type_u ())
in (match (_57_2845) with
| (t_type, u) -> begin
(

let _57_2846 = (let _148_1413 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _148_1413))
in (

let t_tc = (let _148_1414 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _148_1414))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _148_1415 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) ([], t_tc))
in (_148_1415, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u, guard)))))))
end)))
end))
end))
end))
end))
end))))
end
| _57_2853 -> begin
(FStar_All.failwith "impossible")
end))
in (

let positive_if_pure = (fun _57_2855 l -> ())
in (

let tc_data = (fun env tcs _57_7 -> (match (_57_7) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let _57_2872 = ()
in (

let _57_2907 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _57_2876 -> (match (_57_2876) with
| (se, u_tc) -> begin
if (let _148_1428 = (let _148_1427 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _148_1427))
in (FStar_Ident.lid_equals tc_lid _148_1428)) then begin
(

let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2878, _57_2880, tps, _57_2883, _57_2885, _57_2887, _57_2889, _57_2891) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _57_2897 -> (match (_57_2897) with
| (x, _57_2896) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _57_2899 -> begin
(FStar_All.failwith "Impossible")
end)
in Some ((tps, u_tc)))
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
([], FStar_Syntax_Syntax.U_zero)
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected data constructor", r))))
end
end))
in (match (_57_2907) with
| (tps, u_tc) -> begin
(

let _57_2927 = (match ((let _148_1430 = (FStar_Syntax_Subst.compress t)
in _148_1430.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _57_2915 = (FStar_Util.first_N ntps bs)
in (match (_57_2915) with
| (_57_2913, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _57_2921 -> (match (_57_2921) with
| (x, _57_2920) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _148_1433 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _148_1433))))
end))
end
| _57_2924 -> begin
([], t)
end)
in (match (_57_2927) with
| (arguments, result) -> begin
(

let _57_2928 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1436 = (FStar_Syntax_Print.lid_to_string c)
in (let _148_1435 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _148_1434 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _148_1436 _148_1435 _148_1434))))
end else begin
()
end
in (

let _57_2933 = (tc_tparams env arguments)
in (match (_57_2933) with
| (arguments, env', us) -> begin
(

let _57_2937 = (tc_trivial_guard env' result)
in (match (_57_2937) with
| (result, _57_2936) -> begin
(

let _57_2941 = (FStar_Syntax_Util.head_and_args result)
in (match (_57_2941) with
| (head, _57_2940) -> begin
(

let _57_2946 = (match ((let _148_1437 = (FStar_Syntax_Subst.compress head)
in _148_1437.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _57_2945 -> begin
(let _148_1442 = (let _148_1441 = (let _148_1440 = (let _148_1439 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _148_1438 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _148_1439 _148_1438)))
in (_148_1440, r))
in FStar_Syntax_Syntax.Error (_148_1441))
in (Prims.raise _148_1442))
end)
in (

let g = (FStar_List.fold_left2 (fun g _57_2952 u_x -> (match (_57_2952) with
| (x, _57_2951) -> begin
(

let _57_2954 = ()
in (let _148_1446 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _148_1446)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _148_1450 = (let _148_1448 = (FStar_All.pipe_right tps (FStar_List.map (fun _57_2960 -> (match (_57_2960) with
| (x, _57_2959) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _148_1448 arguments))
in (let _148_1449 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _148_1450 _148_1449)))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _57_2963 -> begin
(FStar_All.failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let _57_2969 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_8 -> (match (_57_8) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2973, _57_2975, tps, k, _57_2979, _57_2981, _57_2983, _57_2985) -> begin
(let _148_1461 = (let _148_1460 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _148_1460))
in (FStar_Syntax_Syntax.null_binder _148_1461))
end
| _57_2989 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _57_9 -> (match (_57_9) with
| FStar_Syntax_Syntax.Sig_datacon (_57_2993, _57_2995, t, _57_2998, _57_3000, _57_3002, _57_3004, _57_3006) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _57_3010 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let t = (let _148_1463 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _148_1463))
in (

let _57_3013 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1464 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _148_1464))
end else begin
()
end
in (

let _57_3017 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_57_3017) with
| (uvs, t) -> begin
(

let _57_3019 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1468 = (let _148_1466 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _148_1466 (FStar_String.concat ", ")))
in (let _148_1467 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _148_1468 _148_1467)))
end else begin
()
end
in (

let _57_3023 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_57_3023) with
| (uvs, t) -> begin
(

let _57_3027 = (FStar_Syntax_Util.arrow_formals t)
in (match (_57_3027) with
| (args, _57_3026) -> begin
(

let _57_3030 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_57_3030) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _57_3034 se -> (match (_57_3034) with
| (x, _57_3033) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3038, tps, _57_3041, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let _57_3064 = (match ((let _148_1471 = (FStar_Syntax_Subst.compress ty)
in _148_1471.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _57_3055 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_57_3055) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _57_3058 -> begin
(let _148_1472 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _148_1472 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _57_3061 -> begin
([], ty)
end)
in (match (_57_3064) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _57_3066 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| _57_3070 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _148_1473 -> FStar_Syntax_Syntax.U_name (_148_1473))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_10 -> (match (_57_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3075, _57_3077, _57_3079, _57_3081, _57_3083, _57_3085, _57_3087) -> begin
(tc, uvs_universes)
end
| _57_3091 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _57_3096 d -> (match (_57_3096) with
| (t, _57_3095) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _57_3100, _57_3102, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _148_1477 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _148_1477 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _57_3112 -> begin
(FStar_All.failwith "Impossible")
end)
end)) data_types datas)))
end)
in (tcs, datas)))
end))
end))
end)))
end))))))))
in (

let _57_3122 = (FStar_All.pipe_right ses (FStar_List.partition (fun _57_11 -> (match (_57_11) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_3116) -> begin
true
end
| _57_3119 -> begin
false
end))))
in (match (_57_3122) with
| (tys, datas) -> begin
(

let _57_3129 = if (FStar_All.pipe_right datas (FStar_Util.for_some (fun _57_12 -> (match (_57_12) with
| FStar_Syntax_Syntax.Sig_datacon (_57_3125) -> begin
false
end
| _57_3128 -> begin
true
end)))) then begin
(let _148_1482 = (let _148_1481 = (let _148_1480 = (FStar_TypeChecker_Env.get_range env)
in ("Mutually defined type contains a non-inductive element", _148_1480))
in FStar_Syntax_Syntax.Error (_148_1481))
in (Prims.raise _148_1482))
end else begin
()
end
in (

let env0 = env
in (

let _57_3148 = (FStar_List.fold_right (fun tc _57_3136 -> (match (_57_3136) with
| (env, all_tcs, g) -> begin
(

let _57_3141 = (tc_tycon env tc)
in (match (_57_3141) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (

let _57_3143 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1485 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _148_1485))
end else begin
()
end
in (let _148_1487 = (let _148_1486 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g _148_1486))
in (env, ((tc, tc_u))::all_tcs, _148_1487))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_3148) with
| (env, tcs, g) -> begin
(

let _57_3158 = (FStar_List.fold_right (fun se _57_3152 -> (match (_57_3152) with
| (datas, g) -> begin
(

let _57_3155 = (tc_data env tcs se)
in (match (_57_3155) with
| (data, g') -> begin
(let _148_1490 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _148_1490))
end))
end)) datas ([], g))
in (match (_57_3158) with
| (datas, g) -> begin
(

let _57_3161 = (let _148_1491 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _148_1491 datas))
in (match (_57_3161) with
| (tcs, datas) -> begin
(

let sig_bndle = (let _148_1493 = (let _148_1492 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _148_1492))
in FStar_Syntax_Syntax.Sig_bundle (_148_1493))
in (

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (_57_3166, _57_3168, t, _57_3171, _57_3173, _57_3175, _57_3177, _57_3179) -> begin
t
end
| _57_3183 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let dr = FStar_Range.dummyRange
in (

let haseq_ty = (fun usubst us acc ty -> (

let _57_3210 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _57_3192, bs, t, _57_3196, d_lids, _57_3199, _57_3201) -> begin
(lid, bs, t, d_lids)
end
| _57_3205 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_57_3210) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _148_1504 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _148_1504 t))
in (

let _57_3215 = (FStar_Syntax_Subst.open_term bs t)
in (match (_57_3215) with
| (bs, t) -> begin
(

let ibs = (match ((let _148_1505 = (FStar_Syntax_Subst.compress t)
in _148_1505.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _57_3218) -> begin
ibs
end
| _57_3222 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _148_1508 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _148_1507 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _148_1508 _148_1507)))
in (

let ind = (let _148_1511 = (FStar_List.map (fun _57_3229 -> (match (_57_3229) with
| (bv, aq) -> begin
(let _148_1510 = (FStar_Syntax_Syntax.bv_to_name bv)
in (_148_1510, aq))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _148_1511 None dr))
in (

let ind = (let _148_1514 = (FStar_List.map (fun _57_3233 -> (match (_57_3233) with
| (bv, aq) -> begin
(let _148_1513 = (FStar_Syntax_Syntax.bv_to_name bv)
in (_148_1513, aq))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _148_1514 None dr))
in (

let haseq_ind = (let _148_1516 = (let _148_1515 = (FStar_Syntax_Syntax.as_arg ind)
in (_148_1515)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _148_1516 None dr))
in (

let bs' = (FStar_List.filter (fun b -> (

let _57_3244 = acc
in (match (_57_3244) with
| (_57_3238, en, _57_3241, _57_3243) -> begin
(

let opt = (let _148_1519 = (let _148_1518 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _148_1518))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort _148_1519 false))
in (match (opt) with
| None -> begin
false
end
| Some (_57_3248) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (let _148_1525 = (let _148_1524 = (let _148_1523 = (let _148_1522 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg _148_1522))
in (_148_1523)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _148_1524 None dr))
in (FStar_Syntax_Util.mk_conj t _148_1525))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let _57_3255 = fml
in (let _148_1531 = (let _148_1530 = (let _148_1529 = (let _148_1528 = (let _148_1527 = (let _148_1526 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_148_1526)::[])
in (_148_1527)::[])
in FStar_Syntax_Syntax.Meta_pattern (_148_1528))
in (fml, _148_1529))
in FStar_Syntax_Syntax.Tm_meta (_148_1530))
in {FStar_Syntax_Syntax.n = _148_1531; FStar_Syntax_Syntax.tk = _57_3255.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_3255.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_3255.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _148_1537 = (let _148_1536 = (let _148_1535 = (let _148_1534 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs ((((Prims.fst b), None))::[]) _148_1534 None))
in (FStar_Syntax_Syntax.as_arg _148_1535))
in (_148_1536)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _148_1537 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _148_1543 = (let _148_1542 = (let _148_1541 = (let _148_1540 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs ((((Prims.fst b), None))::[]) _148_1540 None))
in (FStar_Syntax_Syntax.as_arg _148_1541))
in (_148_1542)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _148_1543 None dr))) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let _57_3269 = acc
in (match (_57_3269) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_57_3274, _57_3276, _57_3278, t_lid, _57_3281, _57_3283, _57_3285, _57_3287) -> begin
(t_lid = lid)
end
| _57_3291 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let haseq_data = (fun acc data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (match ((let _148_1549 = (FStar_Syntax_Subst.compress dt)
in _148_1549.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _57_3300) -> begin
(

let dbs = (let _148_1550 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _148_1550))
in (

let dbs = (let _148_1551 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _148_1551 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (let _148_1556 = (let _148_1555 = (let _148_1554 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_148_1554)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _148_1555 None dr))
in (FStar_Syntax_Util.mk_conj t _148_1556))) FStar_Syntax_Util.t_true dbs)
in (

let _57_3311 = acc
in (match (_57_3311) with
| (env, cond') -> begin
(let _148_1558 = (FStar_TypeChecker_Env.push_binders env dbs)
in (let _148_1557 = (FStar_Syntax_Util.mk_conj cond' cond)
in (_148_1558, _148_1557)))
end))))))
end
| _57_3313 -> begin
acc
end))))
in (

let _57_3316 = (FStar_List.fold_left haseq_data (env, FStar_Syntax_Util.t_true) t_datas)
in (match (_57_3316) with
| (env, cond) -> begin
(

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (let _148_1560 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _148_1559 = (FStar_Syntax_Util.mk_conj cond' cond)
in ((FStar_List.append l_axioms (((axiom_lid, fml))::[])), env, _148_1560, _148_1559))))
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
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_3322, us, _57_3325, _57_3327, _57_3329, _57_3331, _57_3333, _57_3335) -> begin
us
end
| _57_3339 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let _57_3343 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_57_3343) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _57_3345 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _57_3347 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let _57_3354 = (FStar_List.fold_left (haseq_ty usubst us) ([], env, FStar_Syntax_Util.t_true, FStar_Syntax_Util.t_true) tcs)
in (match (_57_3354) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let _57_3359 = (tc_trivial_guard env phi)
in (match (_57_3359) with
| (phi, _57_3358) -> begin
(

let _57_3360 = if (FStar_TypeChecker_Env.should_verify env) then begin
(let _148_1562 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _148_1562))
end else begin
()
end
in (

let _57_3362 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env0 us)
in (

let ses = (FStar_List.fold_left (fun l _57_3368 -> (match (_57_3368) with
| (lid, fml) -> begin
(

let se = (tc_assume env lid fml [] dr)
in (FStar_List.append l ((se)::[])))
end)) [] axioms)
in (let _148_1567 = (let _148_1566 = (let _148_1565 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _148_1565))
in FStar_Syntax_Syntax.Sig_bundle (_148_1566))
in (_148_1567)::ses)))))
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


let rec tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let se = (tc_lex_t env ses quals lids)
in (let _148_1572 = (FStar_TypeChecker_Env.push_sigelt env se)
in ((se)::[], _148_1572))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let ses = (tc_inductive env ses quals lids)
in (

let env = (FStar_List.fold_left (fun env' se -> (FStar_TypeChecker_Env.push_sigelt env' se)) env ses)
in (ses, env))))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(

let set_options = (fun t s -> (match ((FStar_Options.set_options t s)) with
| FStar_Getopt.GoOn -> begin
()
end
| FStar_Getopt.Help -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Failed to process pragma: use \'fstar --help\' to see which options are available", r))))
end
| FStar_Getopt.Die (s) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Failed to process pragma: " s), r))))
end))
in (match (p) with
| FStar_Syntax_Syntax.SetOptions (o) -> begin
(

let _57_3411 = (set_options FStar_Options.Set o)
in ((se)::[], env))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(

let _57_3415 = (let _148_1579 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _148_1579 Prims.ignore))
in (

let _57_3420 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _57_3422 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in ((se)::[], env))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(

let ne = (tc_eff_decl env ne ForFree)
in (

let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in ((se)::[], env))))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(

let ne = (tc_eff_decl env ne NotForFree)
in (

let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in ((se)::[], env))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(

let _57_3444 = (let _148_1580 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _148_1580))
in (match (_57_3444) with
| (a, wp_a_src) -> begin
(

let _57_3447 = (let _148_1581 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _148_1581))
in (match (_57_3447) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _148_1585 = (let _148_1584 = (let _148_1583 = (let _148_1582 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _148_1582))
in FStar_Syntax_Syntax.NT (_148_1583))
in (_148_1584)::[])
in (FStar_Syntax_Subst.subst _148_1585 wp_b_tgt))
in (

let expected_k = (let _148_1590 = (let _148_1588 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1587 = (let _148_1586 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_148_1586)::[])
in (_148_1588)::_148_1587))
in (let _148_1589 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _148_1590 _148_1589)))
in (

let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (

let sub = (

let _57_3451 = sub
in {FStar_Syntax_Syntax.source = _57_3451.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _57_3451.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
in (

let se = FStar_Syntax_Syntax.Sig_sub_effect ((sub, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in ((se)::[], env)))))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(

let _57_3464 = ()
in (

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _57_3470 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_57_3470) with
| (tps, c) -> begin
(

let _57_3474 = (tc_tparams env tps)
in (match (_57_3474) with
| (tps, env, us) -> begin
(

let _57_3478 = (tc_comp env c)
in (match (_57_3478) with
| (c, u, g) -> begin
(

let _57_3479 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let _57_3485 = (let _148_1591 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _148_1591))
in (match (_57_3485) with
| (uvs, t) -> begin
(

let _57_3504 = (match ((let _148_1593 = (let _148_1592 = (FStar_Syntax_Subst.compress t)
in _148_1592.FStar_Syntax_Syntax.n)
in (tps, _148_1593))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_57_3488, c)) -> begin
([], c)
end
| (_57_3494, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _57_3501 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_3504) with
| (tps, c) -> begin
(

let se = FStar_Syntax_Syntax.Sig_effect_abbrev ((lid, uvs, tps, c, tags, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 se)
in ((se)::[], env)))
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

let _57_3515 = ()
in (

let _57_3519 = (let _148_1595 = (let _148_1594 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _148_1594))
in (check_and_gen env t _148_1595))
in (match (_57_3519) with
| (uvs, t) -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in ((se)::[], env)))
end))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(

let se = (tc_assume env lid phi quals r)
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in ((se)::[], env)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (

let _57_3539 = (tc_term env e)
in (match (_57_3539) with
| (e, c, g1) -> begin
(

let _57_3544 = (let _148_1599 = (let _148_1596 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_148_1596))
in (let _148_1598 = (let _148_1597 = (c.FStar_Syntax_Syntax.comp ())
in (e, _148_1597))
in (check_expected_effect env _148_1599 _148_1598)))
in (match (_57_3544) with
| (e, _57_3542, g) -> begin
(

let _57_3545 = (let _148_1600 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _148_1600))
in (

let se = FStar_Syntax_Syntax.Sig_main ((e, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in ((se)::[], env))))
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
(let _148_1612 = (let _148_1611 = (let _148_1610 = (let _148_1609 = (FStar_Syntax_Print.lid_to_string l)
in (let _148_1608 = (FStar_Syntax_Print.quals_to_string q)
in (let _148_1607 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _148_1609 _148_1608 _148_1607))))
in (_148_1610, r))
in FStar_Syntax_Syntax.Error (_148_1611))
in (Prims.raise _148_1612))
end
end))
in (

let _57_3589 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _57_3566 lb -> (match (_57_3566) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _57_3585 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (

let _57_3580 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _57_3579 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _148_1615 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _148_1615, quals_opt))))
end)
in (match (_57_3585) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_57_3589) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _57_13 -> (match (_57_13) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _57_3598 -> begin
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

let e = (let _148_1619 = (let _148_1618 = (let _148_1617 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _148_1617))
in FStar_Syntax_Syntax.Tm_let (_148_1618))
in (FStar_Syntax_Syntax.mk _148_1619 None r))
in (

let _57_3632 = (match ((tc_maybe_toplevel_term (

let _57_3602 = env
in {FStar_TypeChecker_Env.solver = _57_3602.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3602.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3602.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3602.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3602.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3602.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3602.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3602.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3602.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3602.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3602.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _57_3602.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _57_3602.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3602.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3602.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3602.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_3602.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_3602.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3602.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3602.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _57_3609; FStar_Syntax_Syntax.pos = _57_3607; FStar_Syntax_Syntax.vars = _57_3605}, _57_3616, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_57_3620, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _57_3626 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _57_3629 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_57_3632) with
| (se, lbs) -> begin
(

let _57_3638 = if (log env) then begin
(let _148_1627 = (let _148_1626 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _148_1623 = (let _148_1622 = (let _148_1621 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _148_1621.FStar_Syntax_Syntax.fv_name)
in _148_1622.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _148_1623))) with
| None -> begin
true
end
| _57_3636 -> begin
false
end)
in if should_log then begin
(let _148_1625 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _148_1624 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _148_1625 _148_1624)))
end else begin
""
end))))
in (FStar_All.pipe_right _148_1626 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _148_1627))
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in ((se)::[], env)))
end)))))
end))))
end))


let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _57_14 -> (match (_57_14) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _57_3648 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _57_3658 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_57_3660) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _57_3671, _57_3673) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _57_3679 -> (match (_57_3679) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _57_3685, _57_3687, quals, r) -> begin
(

let dec = (let _148_1643 = (let _148_1642 = (let _148_1641 = (let _148_1640 = (let _148_1639 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _148_1639))
in FStar_Syntax_Syntax.Tm_arrow (_148_1640))
in (FStar_Syntax_Syntax.mk _148_1641 None r))
in (l, us, _148_1642, (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_148_1643))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _57_3697, _57_3699, _57_3701, _57_3703, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _57_3709 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_57_3711, _57_3713, quals, _57_3716) -> begin
if (is_abstract quals) then begin
([], hidden)
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, us, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) then begin
((FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r)))::[], (l)::hidden)
end else begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _57_15 -> (match (_57_15) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _57_3735 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_57_3737) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _57_3756, _57_3758, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))) then begin
([], hidden)
end else begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::[], (FStar_Ident.range_of_lid lid)))
in ((dec)::[], (lid)::hidden))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (is_abstract quals) then begin
(let _148_1650 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _148_1649 = (let _148_1648 = (let _148_1647 = (let _148_1646 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _148_1646.FStar_Syntax_Syntax.fv_name)
in _148_1647.FStar_Syntax_Syntax.v)
in (_148_1648, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_148_1649)))))
in (_148_1650, hidden))
end else begin
((se)::[], hidden)
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let _57_3805 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _57_3778 se -> (match (_57_3778) with
| (ses, exports, env, hidden) -> begin
(

let _57_3780 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1657 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _148_1657))
end else begin
()
end
in (

let _57_3784 = (tc_decl env se)
in (match (_57_3784) with
| (ses', env) -> begin
(

let _57_3787 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _148_1662 = (FStar_List.fold_left (fun s se -> (let _148_1661 = (let _148_1660 = (FStar_Syntax_Print.sigelt_to_string se)
in (Prims.strcat s _148_1660))
in (Prims.strcat _148_1661 "\n"))) "" ses')
in (FStar_Util.print1 "Checked: %s\n" _148_1662))
end else begin
()
end
in (

let _57_3790 = (FStar_List.iter (fun se -> (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)) ses')
in (

let _57_3799 = (FStar_List.fold_left (fun _57_3794 se -> (match (_57_3794) with
| (le, lh) -> begin
(

let tup = (for_export hidden se)
in ((FStar_List.rev_append (Prims.fst tup) le), (FStar_List.rev_append (Prims.snd tup) lh)))
end)) ([], []) ses')
in (match (_57_3799) with
| (exported, hidden) -> begin
((FStar_List.rev_append ses' ses), ((FStar_List.rev_append exported []))::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_57_3805) with
| (ses, exports, env, _57_3804) -> begin
(let _148_1666 = (FStar_All.pipe_right (FStar_List.rev_append exports []) FStar_List.flatten)
in ((FStar_List.rev_append ses []), _148_1666, env))
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

let _57_3810 = env
in (let _148_1671 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _57_3810.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3810.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3810.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3810.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3810.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3810.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3810.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3810.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3810.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3810.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3810.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3810.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3810.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_3810.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_3810.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3810.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _148_1671; FStar_TypeChecker_Env.lax = _57_3810.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_3810.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3810.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3810.FStar_TypeChecker_Env.use_bv_sorts}))
in (

let _57_3813 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let _57_3819 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_57_3819) with
| (ses, exports, env) -> begin
((

let _57_3820 = modul
in {FStar_Syntax_Syntax.name = _57_3820.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _57_3820.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3820.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let _57_3828 = (tc_decls env decls)
in (match (_57_3828) with
| (ses, exports, env) -> begin
(

let modul = (

let _57_3829 = modul
in {FStar_Syntax_Syntax.name = _57_3829.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _57_3829.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3829.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul = (

let _57_3835 = modul
in {FStar_Syntax_Syntax.name = _57_3835.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _57_3835.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in (

let _57_3845 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(

let _57_3839 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let _57_3841 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (

let _57_3843 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _148_1684 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _148_1684 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let _57_3852 = (tc_partial_modul env modul)
in (match (_57_3852) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _57_3855 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _148_1693 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _148_1693))
end else begin
()
end
in (

let env = (

let _57_3857 = env
in {FStar_TypeChecker_Env.solver = _57_3857.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3857.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3857.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3857.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3857.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3857.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3857.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3857.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3857.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3857.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3857.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3857.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3857.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_3857.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3857.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3857.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3857.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_3857.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_3857.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3857.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3857.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_3873 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _57_3865) -> begin
(let _148_1698 = (let _148_1697 = (let _148_1696 = (FStar_TypeChecker_Env.get_range env)
in ((Prims.strcat "Implicit argument: " msg), _148_1696))
in FStar_Syntax_Syntax.Error (_148_1697))
in (Prims.raise _148_1698))
end
in (match (_57_3873) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(t, c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(let _148_1703 = (let _148_1702 = (let _148_1701 = (let _148_1699 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _148_1699))
in (let _148_1700 = (FStar_TypeChecker_Env.get_range env)
in (_148_1701, _148_1700)))
in FStar_Syntax_Syntax.Error (_148_1702))
in (Prims.raise _148_1703))
end
end)))))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
FStar_Syntax_Syntax.U_zero
end else begin
(

let _57_3876 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_1708 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print1 "universe_of %s\n" _148_1708))
end else begin
()
end
in (

let _57_3881 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_3881) with
| (env, _57_3880) -> begin
(

let env = (

let _57_3882 = env
in {FStar_TypeChecker_Env.solver = _57_3882.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3882.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3882.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3882.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3882.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3882.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3882.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3882.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3882.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3882.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3882.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3882.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3882.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_3882.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3882.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3882.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3882.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _57_3882.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3882.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true})
in (

let fail = (fun e t -> (let _148_1718 = (let _148_1717 = (let _148_1716 = (let _148_1714 = (FStar_Syntax_Print.term_to_string e)
in (let _148_1713 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" _148_1714 _148_1713)))
in (let _148_1715 = (FStar_TypeChecker_Env.get_range env)
in (_148_1716, _148_1715)))
in FStar_Syntax_Syntax.Error (_148_1717))
in (Prims.raise _148_1718)))
in (

let ok = (fun u -> (

let _57_3890 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_1722 = (FStar_Syntax_Print.tag_of_term e)
in (let _148_1721 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.print2 "<end> universe_of %s is %s\n" _148_1722 _148_1721)))
end else begin
()
end
in u))
in (

let universe_of_type = (fun e t -> (match ((let _148_1727 = (FStar_Syntax_Util.unrefine t)
in _148_1727.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(ok u)
end
| _57_3898 -> begin
(fail e t)
end))
in (

let _57_3901 = (FStar_Syntax_Util.head_and_args e)
in (match (_57_3901) with
| (head, args) -> begin
(match ((let _148_1728 = (FStar_Syntax_Subst.compress head)
in _148_1728.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_57_3903, t) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _148_1729 = (FStar_Syntax_Subst.compress t)
in _148_1729.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_3909, t) -> begin
(universe_of_type e (FStar_Syntax_Util.comp_result t))
end
| _57_3914 -> begin
(universe_of_type e t)
end))
end
| _57_3916 -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoInline)::[]) env e)
in (

let _57_3930 = (tc_term env e)
in (match (_57_3930) with
| (_57_3919, {FStar_Syntax_Syntax.eff_name = _57_3926; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _57_3923; FStar_Syntax_Syntax.comp = _57_3921}, _57_3929) -> begin
(let _148_1731 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (FStar_All.pipe_left (universe_of_type e) _148_1731))
end)))
end)
end))))))
end)))
end)


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

let _57_3933 = if (FStar_Options.debug_any ()) then begin
(let _148_1736 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _148_1736))
end else begin
()
end
in (

let _57_3937 = (tc_modul env m)
in (match (_57_3937) with
| (m, env) -> begin
(

let _57_3938 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _148_1737 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _148_1737))
end else begin
()
end
in (m, env))
end))))




