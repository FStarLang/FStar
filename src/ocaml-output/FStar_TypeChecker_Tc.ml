
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

let e = (let _148_289 = (let _148_288 = (let _148_287 = (FStar_List.map (fun _57_565 -> (match (_57_565) with
| (f, _57_560, _57_562, _57_564) -> begin
f
end)) t_eqns)
in (e1, _148_287))
in FStar_Syntax_Syntax.Tm_match (_148_288))
in (FStar_Syntax_Syntax.mk _148_289 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ), Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (

let _57_568 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_292 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _148_291 = (let _148_290 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _148_290))
in (FStar_Util.print2 "(%s) comp type = %s\n" _148_292 _148_291)))
end else begin
()
end
in (let _148_293 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _148_293))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_580); FStar_Syntax_Syntax.lbunivs = _57_578; FStar_Syntax_Syntax.lbtyp = _57_576; FStar_Syntax_Syntax.lbeff = _57_574; FStar_Syntax_Syntax.lbdef = _57_572})::[]), _57_586) -> begin
(

let _57_589 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_294 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _148_294))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _57_593), _57_596) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_611); FStar_Syntax_Syntax.lbunivs = _57_609; FStar_Syntax_Syntax.lbtyp = _57_607; FStar_Syntax_Syntax.lbeff = _57_605; FStar_Syntax_Syntax.lbdef = _57_603})::_57_601), _57_617) -> begin
(

let _57_620 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_295 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _148_295))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _57_624), _57_627) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let _57_641 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_641) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _148_309 = (let _148_308 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_308))
in FStar_Util.Inr (_148_309))
end
in (

let is_data_ctor = (fun _57_4 -> (match (_57_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _57_651 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _148_315 = (let _148_314 = (let _148_313 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _148_312 = (FStar_TypeChecker_Env.get_range env)
in (_148_313, _148_312)))
in FStar_Syntax_Syntax.Error (_148_314))
in (Prims.raise _148_315))
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

let g = (match ((let _148_316 = (FStar_Syntax_Subst.compress t1)
in _148_316.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_662) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _57_665 -> begin
(

let imp = ("uvar in term", env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (

let _57_667 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_667.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_667.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_667.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _57_682 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(

let _57_675 = (FStar_Syntax_Util.type_u ())
in (match (_57_675) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
end))
end
| Some (t) -> begin
(t, [], FStar_TypeChecker_Rel.trivial_guard)
end)
in (match (_57_682) with
| (t, _57_680, g0) -> begin
(

let _57_687 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (_57_687) with
| (e, _57_685, g1) -> begin
(let _148_319 = (let _148_317 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right _148_317 FStar_Syntax_Util.lcomp_of_comp))
in (let _148_318 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in (e, _148_319, _148_318)))
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

let _57_691 = x
in {FStar_Syntax_Syntax.ppname = _57_691.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_691.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let _57_697 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_697) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _148_321 = (let _148_320 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_320))
in FStar_Util.Inr (_148_321))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _57_704; FStar_Syntax_Syntax.pos = _57_702; FStar_Syntax_Syntax.vars = _57_700}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let _57_714 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_714) with
| (us', t) -> begin
(

let _57_721 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _148_324 = (let _148_323 = (let _148_322 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _148_322))
in FStar_Syntax_Syntax.Error (_148_323))
in (Prims.raise _148_324))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _57_720 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (

let fv' = (

let _57_723 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _57_725 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_725.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_725.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_723.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_723.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _148_327 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _148_327 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let _57_733 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_733) with
| (us, t) -> begin
(

let fv' = (

let _57_734 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _57_736 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_736.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_736.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_734.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_734.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _148_328 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _148_328 us))
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

let _57_750 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_750) with
| (bs, c) -> begin
(

let env0 = env
in (

let _57_755 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_755) with
| (env, _57_754) -> begin
(

let _57_760 = (tc_binders env bs)
in (match (_57_760) with
| (bs, env, g, us) -> begin
(

let _57_764 = (tc_comp env c)
in (match (_57_764) with
| (c, uc, f) -> begin
(

let e = (

let _57_765 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _57_765.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_765.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_765.FStar_Syntax_Syntax.vars})
in (

let _57_768 = (check_smt_pat env e bs c)
in (

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _148_329 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _148_329))
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

let _57_784 = (let _148_331 = (let _148_330 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_330)::[])
in (FStar_Syntax_Subst.open_term _148_331 phi))
in (match (_57_784) with
| (x, phi) -> begin
(

let env0 = env
in (

let _57_789 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_789) with
| (env, _57_788) -> begin
(

let _57_794 = (let _148_332 = (FStar_List.hd x)
in (tc_binder env _148_332))
in (match (_57_794) with
| (x, env, f1, u) -> begin
(

let _57_795 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_335 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _148_334 = (FStar_Syntax_Print.term_to_string phi)
in (let _148_333 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _148_335 _148_334 _148_333))))
end else begin
()
end
in (

let _57_800 = (FStar_Syntax_Util.type_u ())
in (match (_57_800) with
| (t_phi, _57_799) -> begin
(

let _57_805 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_57_805) with
| (phi, _57_803, f2) -> begin
(

let e = (

let _57_806 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _57_806.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_806.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_806.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _148_336 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _148_336))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _57_814) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (

let _57_820 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_337 = (FStar_Syntax_Print.term_to_string (

let _57_818 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _57_818.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_818.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_818.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _148_337))
end else begin
()
end
in (

let _57_824 = (FStar_Syntax_Subst.open_term bs body)
in (match (_57_824) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _57_826 -> begin
(let _148_340 = (let _148_339 = (FStar_Syntax_Print.term_to_string top)
in (let _148_338 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" _148_339 _148_338)))
in (FStar_All.failwith _148_340))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_57_831) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_57_834, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_57_839, Some (_57_841)) -> begin
(FStar_All.failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (_57_846) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_57_849) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_57_852) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_57_856) -> begin
FStar_TypeChecker_Common.t_range
end
| _57_859 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(

let _57_867 = (FStar_Syntax_Util.type_u ())
in (match (_57_867) with
| (k, u) -> begin
(

let _57_872 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_872) with
| (t, _57_870, g) -> begin
(let _148_345 = (FStar_Syntax_Syntax.mk_Total t)
in (_148_345, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(

let _57_877 = (FStar_Syntax_Util.type_u ())
in (match (_57_877) with
| (k, u) -> begin
(

let _57_882 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_882) with
| (t, _57_880, g) -> begin
(let _148_346 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_148_346, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (

let tc = (let _148_348 = (let _148_347 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_148_347)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _148_348 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let _57_891 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_57_891) with
| (tc, _57_889, f) -> begin
(

let _57_895 = (FStar_Syntax_Util.head_and_args tc)
in (match (_57_895) with
| (_57_893, args) -> begin
(

let _57_898 = (let _148_350 = (FStar_List.hd args)
in (let _148_349 = (FStar_List.tl args)
in (_148_350, _148_349)))
in (match (_57_898) with
| (res, args) -> begin
(

let _57_914 = (let _148_352 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _57_5 -> (match (_57_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _57_905 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_905) with
| (env, _57_904) -> begin
(

let _57_910 = (tc_tot_or_gtot_term env e)
in (match (_57_910) with
| (e, _57_908, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _148_352 FStar_List.unzip))
in (match (_57_914) with
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
| _57_925 -> begin
(FStar_All.failwith "Impossible:Unexpected sort for computation")
end)))
end
| _57_927 -> begin
(FStar_All.failwith "Impossible:Unexpected sort for computation")
end)
in (let _148_354 = (FStar_Syntax_Syntax.mk_Comp (

let _57_929 = c
in {FStar_Syntax_Syntax.effect_name = _57_929.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _57_929.FStar_Syntax_Syntax.flags}))
in (let _148_353 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_148_354, u, _148_353))))
end))
end))
end))
end))))
end)))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_57_937) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _148_359 = (aux u)
in FStar_Syntax_Syntax.U_succ (_148_359))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _148_360 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_148_360))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _148_364 = (let _148_363 = (let _148_362 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _148_361 = (FStar_TypeChecker_Env.get_range env)
in (_148_362, _148_361)))
in FStar_Syntax_Syntax.Error (_148_363))
in (Prims.raise _148_364))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _148_365 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_365 Prims.snd))
end
| _57_952 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _148_374 = (let _148_373 = (let _148_372 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_148_372, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_148_373))
in (Prims.raise _148_374)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun _57_970 bs bs_expected -> (match (_57_970) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
(

let _57_1001 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _148_391 = (let _148_390 = (let _148_389 = (let _148_387 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _148_387))
in (let _148_388 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_148_389, _148_388)))
in FStar_Syntax_Syntax.Error (_148_390))
in (Prims.raise _148_391))
end
| _57_1000 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _57_1018 = (match ((let _148_392 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _148_392.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _57_1006 -> begin
(

let _57_1007 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_393 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _148_393))
end else begin
()
end
in (

let _57_1013 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_57_1013) with
| (t, _57_1011, g1) -> begin
(

let g2 = (let _148_395 = (FStar_TypeChecker_Env.get_range env)
in (let _148_394 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _148_395 "Type annotation on parameter incompatible with the expected type" _148_394)))
in (

let g = (let _148_396 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _148_396))
in (t, g)))
end)))
end)
in (match (_57_1018) with
| (t, g) -> begin
(

let hd = (

let _57_1019 = hd
in {FStar_Syntax_Syntax.ppname = _57_1019.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1019.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = (hd, imp)
in (

let b_expected = (hd_expected, imp')
in (

let env = (push_binding env b)
in (

let subst = (let _148_397 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _148_397))
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

let _57_1040 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1039 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (

let _57_1047 = (tc_binders env bs)
in (match (_57_1047) with
| (bs, envbody, g, _57_1046) -> begin
(

let _57_1065 = (match ((let _148_404 = (FStar_Syntax_Subst.compress body)
in _148_404.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _57_1052) -> begin
(

let _57_1059 = (tc_comp envbody c)
in (match (_57_1059) with
| (c, _57_1057, g') -> begin
(let _148_405 = (FStar_TypeChecker_Rel.conj_guard g g')
in (Some (c), body, _148_405))
end))
end
| _57_1061 -> begin
(None, body, g)
end)
in (match (_57_1065) with
| (copt, body, g) -> begin
(None, bs, [], copt, envbody, body, g)
end))
end)))
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm t -> (match ((let _148_410 = (FStar_Syntax_Subst.compress t)
in _148_410.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let _57_1092 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1091 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _57_1099 = (tc_binders env bs)
in (match (_57_1099) with
| (bs, envbody, g, _57_1098) -> begin
(

let _57_1103 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_57_1103) with
| (envbody, _57_1102) -> begin
(Some ((t, true)), bs, [], None, envbody, body, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _57_1106) -> begin
(

let _57_1117 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_57_1117) with
| (_57_1110, bs, bs', copt, env, body, g) -> begin
(Some ((t, false)), bs, bs', copt, env, body, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _57_1124 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_57_1124) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun _57_1135 c_expected -> (match (_57_1135) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _148_421 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _148_421))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (let _148_422 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _148_422))
in (let _148_423 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _148_423)))
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

let _57_1156 = (check_binders env more_bs bs_expected)
in (match (_57_1156) with
| (env, bs', more, guard', subst) -> begin
(let _148_425 = (let _148_424 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _148_424, subst))
in (handle_more _148_425 c_expected))
end))
end
| _57_1158 -> begin
(let _148_427 = (let _148_426 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _148_426))
in (fail _148_427 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _148_428 = (check_binders env bs bs_expected)
in (handle_more _148_428 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let _57_1164 = envbody
in {FStar_TypeChecker_Env.solver = _57_1164.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1164.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1164.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1164.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1164.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1164.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1164.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1164.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1164.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1164.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1164.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1164.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_1164.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1164.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1164.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1164.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1164.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_1164.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_1164.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1164.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1164.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _57_1169 _57_1172 -> (match ((_57_1169, _57_1172)) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _57_1178 = (let _148_438 = (let _148_437 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _148_437 Prims.fst))
in (tc_term _148_438 t))
in (match (_57_1178) with
| (t, _57_1175, _57_1177) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _148_439 = (FStar_Syntax_Syntax.mk_binder (

let _57_1182 = x
in {FStar_Syntax_Syntax.ppname = _57_1182.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1182.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_148_439)::letrec_binders)
end
| _57_1185 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (

let _57_1191 = (check_actuals_against_formals env bs bs_expected)
in (match (_57_1191) with
| (envbody, bs, g, c) -> begin
(

let _57_1194 = if (FStar_TypeChecker_Env.should_verify env) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_57_1194) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, body, g))
end))
end))))
end))
end
| _57_1197 -> begin
if (not (norm)) then begin
(let _148_440 = (unfold_whnf env t)
in (as_function_typ true _148_440))
end else begin
(

let _57_1207 = (expected_function_typ env None body)
in (match (_57_1207) with
| (_57_1199, bs, _57_1202, c_opt, envbody, body, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, body, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let _57_1211 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1211) with
| (env, topt) -> begin
(

let _57_1215 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_441 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _148_441 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (

let _57_1224 = (expected_function_typ env topt body)
in (match (_57_1224) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let _57_1230 = (tc_term (

let _57_1225 = envbody
in {FStar_TypeChecker_Env.solver = _57_1225.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1225.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1225.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1225.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1225.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1225.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1225.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1225.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1225.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1225.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1225.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1225.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1225.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1225.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1225.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1225.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_1225.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_1225.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1225.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1225.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_57_1230) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _57_1232 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _148_444 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _148_443 = (let _148_442 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _148_442))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _148_444 _148_443)))
end else begin
()
end
in (

let _57_1239 = (let _148_446 = (let _148_445 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _148_445))
in (check_expected_effect (

let _57_1234 = envbody
in {FStar_TypeChecker_Env.solver = _57_1234.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1234.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1234.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1234.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1234.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1234.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1234.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1234.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1234.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1234.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1234.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1234.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1234.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1234.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1234.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1234.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1234.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_1234.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_1234.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1234.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1234.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _148_446))
in (match (_57_1239) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(let _148_447 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _148_447))
end else begin
(

let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _148_450 = (let _148_449 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _148_448 -> FStar_Util.Inl (_148_448)))
in Some (_148_449))
in (FStar_Syntax_Util.abs bs body _148_450))
in (

let _57_1262 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_1251) -> begin
(e, t, guard)
end
| _57_1254 -> begin
(

let _57_1257 = if use_teq then begin
(let _148_451 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _148_451))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_57_1257) with
| (e, guard') -> begin
(let _148_452 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _148_452))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_57_1262) with
| (e, tfun, guard) -> begin
(

let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (

let _57_1266 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_57_1266) with
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

let _57_1276 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_461 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _148_460 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _148_461 _148_460)))
end else begin
()
end
in (

let monadic_application = (fun _57_1283 subst arg_comps_rev arg_rets guard fvs bs -> (match (_57_1283) with
| (head, chead, ghead, cres) -> begin
(

let _57_1290 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let _57_1318 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun _57_6 -> (match (_57_6) with
| (_57_1297, _57_1299, None) -> begin
false
end
| (_57_1303, _57_1305, Some (c)) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _148_477 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _148_477 cres))
end else begin
(

let _57_1310 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_480 = (FStar_Syntax_Print.term_to_string head)
in (let _148_479 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _148_478 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _148_480 _148_479 _148_478))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _57_1314 -> begin
(

let g = (let _148_481 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right _148_481 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _148_486 = (let _148_485 = (let _148_484 = (let _148_483 = (let _148_482 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _148_482))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _148_483))
in (FStar_Syntax_Syntax.mk_Total _148_484))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_485))
in (_148_486, g)))
end)
in (match (_57_1318) with
| (cres, guard) -> begin
(

let _57_1319 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_487 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _148_487))
end else begin
()
end
in (

let _57_1337 = (FStar_List.fold_left (fun _57_1323 _57_1329 -> (match ((_57_1323, _57_1329)) with
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
in (match (_57_1337) with
| (args, comp) -> begin
(

let comp = (FStar_TypeChecker_Util.bind head.FStar_Syntax_Syntax.pos env None chead (None, comp))
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app = (FStar_TypeChecker_Util.maybe_monadic env app comp.FStar_Syntax_Syntax.eff_name)
in (

let _57_1343 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (_57_1343) with
| (comp, g) -> begin
(app, comp, g)
end)))))
end)))
end)))
end))
in (

let rec tc_args = (fun head_info _57_1351 bs args -> (match (_57_1351) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match ((bs, args)) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (_57_1357))))::rest, ((_57_1365, None))::_57_1363) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _57_1371 = (check_no_escape (Some (head)) env fvs t)
in (

let _57_1377 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_57_1377) with
| (varg, _57_1375, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (

let arg = (let _148_499 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _148_499))
in (let _148_501 = (let _148_500 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, ((arg, None, None))::outargs, (arg)::arg_rets, _148_500, fvs))
in (tc_args head_info _148_501 rest args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
(

let _57_1409 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _57_1408 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let _57_1412 = x
in {FStar_Syntax_Syntax.ppname = _57_1412.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1412.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (

let _57_1415 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_502 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _148_502))
end else begin
()
end
in (

let _57_1417 = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let _57_1420 = env
in {FStar_TypeChecker_Env.solver = _57_1420.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1420.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1420.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1420.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1420.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1420.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1420.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1420.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1420.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1420.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1420.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1420.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1420.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1420.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1420.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _57_1420.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1420.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_1420.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_1420.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1420.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1420.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_1423 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_505 = (FStar_Syntax_Print.tag_of_term e)
in (let _148_504 = (FStar_Syntax_Print.term_to_string e)
in (let _148_503 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _148_505 _148_504 _148_503))))
end else begin
()
end
in (

let _57_1428 = (tc_term env e)
in (match (_57_1428) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(

let subst = (let _148_506 = (FStar_List.hd bs)
in (maybe_extend_subst subst _148_506 e))
in (tc_args head_info (subst, ((arg, None, None))::outargs, (arg)::arg_rets, g, fvs) rest rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(

let subst = (let _148_507 = (FStar_List.hd bs)
in (maybe_extend_subst subst _148_507 e))
in (tc_args head_info (subst, ((arg, Some (x), Some (c)))::outargs, (arg)::arg_rets, g, fvs) rest rest'))
end else begin
if (let _148_508 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _148_508)) then begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _148_509 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _148_509))
in (tc_args head_info (subst, ((arg, Some (newx), Some (c)))::outargs, (arg')::arg_rets, g, fvs) rest rest')))
end else begin
(let _148_513 = (let _148_512 = (let _148_511 = (let _148_510 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _148_510))
in (_148_511)::arg_rets)
in (subst, ((arg, Some (x), Some (c)))::outargs, _148_512, g, (x)::fvs))
in (tc_args head_info _148_513 rest rest'))
end
end
end))
end))))))))))
end
| (_57_1436, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::_57_1441) -> begin
(

let _57_1448 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (_57_1448) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _148_518 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _148_518 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let _57_1459 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (_57_1459) with
| (bs, cres') -> begin
(

let head_info = (head, chead, ghead, (FStar_Syntax_Util.lcomp_of_comp cres'))
in (

let _57_1461 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_519 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _148_519))
end else begin
()
end
in (tc_args head_info ([], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs args)))
end))
end
| _57_1464 when (not (norm)) -> begin
(let _148_520 = (unfold_whnf env tres)
in (aux true _148_520))
end
| _57_1466 -> begin
(let _148_526 = (let _148_525 = (let _148_524 = (let _148_522 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (let _148_521 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _148_522 _148_521)))
in (let _148_523 = (FStar_Syntax_Syntax.argpos arg)
in (_148_524, _148_523)))
in FStar_Syntax_Syntax.Error (_148_525))
in (Prims.raise _148_526))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (match ((let _148_531 = (FStar_Syntax_Util.unrefine tf)
in _148_531.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| ((e, imp))::tl -> begin
(

let _57_1499 = (tc_term env e)
in (match (_57_1499) with
| (e, c, g_e) -> begin
(

let _57_1503 = (tc_args env tl)
in (match (_57_1503) with
| (args, comps, g_rest) -> begin
(let _148_536 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, ((e.FStar_Syntax_Syntax.pos, c))::comps, _148_536))
end))
end))
end))
in (

let _57_1507 = (tc_args env args)
in (match (_57_1507) with
| (args, comps, g_args) -> begin
(

let bs = (let _148_538 = (FStar_All.pipe_right comps (FStar_List.map (fun _57_1511 -> (match (_57_1511) with
| (_57_1509, c) -> begin
(c.FStar_Syntax_Syntax.res_typ, None)
end))))
in (FStar_Syntax_Util.null_binders_of_tks _148_538))
in (

let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _57_1517 -> begin
FStar_Syntax_Util.ml_comp
end)
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _148_553 = (FStar_Syntax_Subst.compress t)
in _148_553.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_1523) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _57_1528 -> begin
ml_or_tot
end)
end)
in (

let cres = (let _148_558 = (let _148_557 = (let _148_556 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_556 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _148_557))
in (ml_or_tot _148_558 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (

let _57_1532 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _148_561 = (FStar_Syntax_Print.term_to_string head)
in (let _148_560 = (FStar_Syntax_Print.term_to_string tf)
in (let _148_559 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _148_561 _148_560 _148_559))))
end else begin
()
end
in (

let _57_1534 = (let _148_562 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _148_562))
in (

let comp = (let _148_565 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _57_1538 out -> (match (_57_1538) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c (None, out))
end)) (((head.FStar_Syntax_Syntax.pos, chead))::comps) _148_565))
in (let _148_567 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _148_566 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_148_567, comp, _148_566)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _57_1547 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_1547) with
| (bs, c) -> begin
(

let head_info = (head, chead, ghead, (FStar_Syntax_Util.lcomp_of_comp c))
in (tc_args head_info ([], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs args))
end))
end
| _57_1550 -> begin
if (not (norm)) then begin
(let _148_568 = (unfold_whnf env tf)
in (check_function_app true _148_568))
end else begin
(let _148_571 = (let _148_570 = (let _148_569 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_148_569, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_148_570))
in (Prims.raise _148_571))
end
end))
in (let _148_573 = (let _148_572 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _148_572))
in (check_function_app false _148_573))))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let _57_1586 = (FStar_List.fold_left2 (fun _57_1567 _57_1570 _57_1573 -> (match ((_57_1567, _57_1570, _57_1573)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(

let _57_1574 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let _57_1579 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_57_1579) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (let _148_583 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _148_583 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _148_587 = (let _148_585 = (let _148_584 = (FStar_Syntax_Syntax.as_arg e)
in (_148_584)::[])
in (FStar_List.append seen _148_585))
in (let _148_586 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_148_587, _148_586, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_57_1586) with
| (args, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = if ghost then begin
(let _148_588 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _148_588 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (

let _57_1591 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_57_1591) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _57_1593 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let _57_1600 = (FStar_Syntax_Subst.open_branch branch)
in (match (_57_1600) with
| (pattern, when_clause, branch_exp) -> begin
(

let _57_1605 = branch
in (match (_57_1605) with
| (cpat, _57_1603, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _57_1613 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_57_1613) with
| (pat_bvs, exps, p) -> begin
(

let _57_1614 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_600 = (FStar_Syntax_Print.pat_to_string p0)
in (let _148_599 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _148_600 _148_599)))
end else begin
()
end
in (

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let _57_1620 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_57_1620) with
| (env1, _57_1619) -> begin
(

let env1 = (

let _57_1621 = env1
in {FStar_TypeChecker_Env.solver = _57_1621.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1621.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1621.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1621.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1621.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1621.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1621.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1621.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _57_1621.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1621.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1621.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1621.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1621.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1621.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1621.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1621.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1621.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_1621.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_1621.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1621.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1621.FStar_TypeChecker_Env.use_bv_sorts})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _57_1660 = (let _148_623 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _57_1626 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_603 = (FStar_Syntax_Print.term_to_string e)
in (let _148_602 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _148_603 _148_602)))
end else begin
()
end
in (

let _57_1631 = (tc_term env1 e)
in (match (_57_1631) with
| (e, lc, g) -> begin
(

let _57_1632 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_605 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _148_604 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _148_605 _148_604)))
end else begin
()
end
in (

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let _57_1638 = (let _148_606 = (FStar_TypeChecker_Rel.discharge_guard env (

let _57_1636 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_1636.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_1636.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_1636.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _148_606 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _148_611 = (let _148_610 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _148_610 (FStar_List.map (fun _57_1646 -> (match (_57_1646) with
| (u, _57_1645) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _148_611 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _57_1654 = if (let _148_612 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _148_612)) then begin
(

let unresolved = (let _148_613 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _148_613 FStar_Util.set_elements))
in (let _148_621 = (let _148_620 = (let _148_619 = (let _148_618 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _148_617 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _148_616 = (let _148_615 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _57_1653 -> (match (_57_1653) with
| (u, _57_1652) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _148_615 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _148_618 _148_617 _148_616))))
in (_148_619, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_148_620))
in (Prims.raise _148_621)))
end else begin
()
end
in (

let _57_1656 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_622 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _148_622))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _148_623 FStar_List.unzip))
in (match (_57_1660) with
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

let _57_1667 = (let _148_624 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _148_624 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_57_1667) with
| (scrutinee_env, _57_1666) -> begin
(

let _57_1673 = (tc_pat true pat_t pattern)
in (match (_57_1673) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let _57_1683 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_TypeChecker_Env.should_verify env) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(

let _57_1680 = (let _148_625 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _148_625 e))
in (match (_57_1680) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_57_1683) with
| (when_clause, g_when) -> begin
(

let _57_1687 = (tc_term pat_env branch_exp)
in (match (_57_1687) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _148_627 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _148_626 -> Some (_148_626)) _148_627))
end)
in (

let _57_1745 = (

let eqs = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
None
end else begin
(FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _57_1705 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _148_631 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _148_630 -> Some (_148_630)) _148_631))
end))
end))) None))
end
in (

let _57_1713 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_57_1713) with
| (c, g_branch) -> begin
(

let _57_1740 = (match ((eqs, when_condition)) with
| _57_1715 when (not ((FStar_TypeChecker_Env.should_verify env))) -> begin
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
in (let _148_634 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _148_633 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_148_634, _148_633)))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (let _148_635 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_148_635))
in (let _148_638 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _148_637 = (let _148_636 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _148_636 g_when))
in (_148_638, _148_637)))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _148_639 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_148_639, g_when))))
end)
in (match (_57_1740) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _148_641 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _148_640 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_148_641, _148_640, g_branch))))
end))
end)))
in (match (_57_1745) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
FStar_Syntax_Util.t_true
end else begin
(

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> if ((let _148_651 = (let _148_650 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _148_650))
in (FStar_List.length _148_651)) > 1) then begin
(

let disc = (let _148_652 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _148_652 FStar_Syntax_Syntax.Delta_equational None))
in (

let disc = (let _148_654 = (let _148_653 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_148_653)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _148_654 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _148_655 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_148_655)::[])))
end else begin
[]
end)
in (

let fail = (fun _57_1755 -> (match (()) with
| () -> begin
(let _148_661 = (let _148_660 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _148_659 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _148_658 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _148_660 _148_659 _148_658))))
in (FStar_All.failwith _148_661))
end))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _57_1762) -> begin
(head_constructor t)
end
| _57_1766 -> begin
(fail ())
end))
in (

let pat_exp = (let _148_664 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _148_664 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_57_1791) -> begin
(let _148_669 = (let _148_668 = (let _148_667 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _148_666 = (let _148_665 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_148_665)::[])
in (_148_667)::_148_666))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _148_668 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_148_669)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _148_670 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _148_670))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(

let sub_term_guards = (let _148_677 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _57_1809 -> (match (_57_1809) with
| (ei, _57_1808) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _57_1813 -> begin
(

let sub_term = (let _148_676 = (let _148_673 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _148_673 FStar_Syntax_Syntax.Delta_equational None))
in (let _148_675 = (let _148_674 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_148_674)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _148_676 _148_675 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _148_677 FStar_List.flatten))
in (let _148_678 = (discriminate scrutinee_tm f)
in (FStar_List.append _148_678 sub_term_guards)))
end)
end
| _57_1817 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(

let t = (let _148_683 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _148_683))
in (

let _57_1825 = (FStar_Syntax_Util.type_u ())
in (match (_57_1825) with
| (k, _57_1824) -> begin
(

let _57_1831 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_57_1831) with
| (t, _57_1828, _57_1830) -> begin
t
end))
end)))
end)
in (

let branch_guard = (let _148_684 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _148_684 FStar_Syntax_Util.mk_disj_l))
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

let _57_1839 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_685 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _148_685))
end else begin
()
end
in (let _148_686 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_148_686, branch_guard, c, guard)))))
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

let _57_1856 = (check_let_bound_def true env lb)
in (match (_57_1856) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let _57_1868 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(

let g1 = (let _148_689 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _148_689 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _57_1863 = (let _148_693 = (let _148_692 = (let _148_691 = (let _148_690 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _148_690))
in (_148_691)::[])
in (FStar_TypeChecker_Util.generalize env _148_692))
in (FStar_List.hd _148_693))
in (match (_57_1863) with
| (_57_1859, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_57_1868) with
| (g1, e1, univ_vars, c1) -> begin
(

let _57_1878 = if (FStar_TypeChecker_Env.should_verify env) then begin
(

let _57_1871 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_57_1871) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(

let _57_1872 = if (FStar_Options.warn_top_level_effects ()) then begin
(let _148_694 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _148_694 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _148_695 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_148_695, c1)))
end
end))
end else begin
(

let _57_1874 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _148_696 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _148_696)))
end
in (match (_57_1878) with
| (e2, c1) -> begin
(

let cres = (let _148_697 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_697))
in (

let _57_1880 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _148_698 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_148_698, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _57_1884 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let _57_1895 = env
in {FStar_TypeChecker_Env.solver = _57_1895.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1895.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1895.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1895.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1895.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1895.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1895.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1895.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1895.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1895.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1895.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1895.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1895.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1895.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1895.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1895.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1895.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_1895.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_1895.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1895.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1895.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_1904 = (let _148_702 = (let _148_701 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _148_701 Prims.fst))
in (check_let_bound_def false _148_702 lb))
in (match (_57_1904) with
| (e1, _57_1900, c1, g1, annotated) -> begin
(

let x = (

let _57_1905 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1905.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1905.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let _57_1911 = (let _148_704 = (let _148_703 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_703)::[])
in (FStar_Syntax_Subst.open_term _148_704 e2))
in (match (_57_1911) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _57_1917 = (let _148_705 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _148_705 e2))
in (match (_57_1917) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (Some (x), c2))
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e2 = (FStar_TypeChecker_Util.maybe_lift env e2 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e = (let _148_708 = (let _148_707 = (let _148_706 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _148_706))
in FStar_Syntax_Syntax.Tm_let (_148_707))
in (FStar_Syntax_Syntax.mk _148_708 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name)
in (

let x_eq_e1 = (let _148_711 = (let _148_710 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _148_710 e1))
in (FStar_All.pipe_left (fun _148_709 -> FStar_TypeChecker_Common.NonTrivial (_148_709)) _148_711))
in (

let g2 = (let _148_713 = (let _148_712 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _148_712 g2))
in (FStar_TypeChecker_Rel.close_guard xb _148_713))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if (let _148_714 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome _148_714)) then begin
(e, cres, guard)
end else begin
(

let _57_1926 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end))))))))
end))))
end))))
end)))
end
| _57_1929 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _57_1941 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1941) with
| (lbs, e2) -> begin
(

let _57_1944 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1944) with
| (env0, topt) -> begin
(

let _57_1947 = (build_let_rec_env true env0 lbs)
in (match (_57_1947) with
| (lbs, rec_env) -> begin
(

let _57_1950 = (check_let_recs rec_env lbs)
in (match (_57_1950) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (let _148_717 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _148_717 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _148_720 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _148_720 (fun _148_719 -> Some (_148_719))))
in (

let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(

let ecs = (let _148_724 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _148_723 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _148_723)))))
in (FStar_TypeChecker_Util.generalize env _148_724))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _57_1961 -> (match (_57_1961) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _148_726 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_726))
in (

let _57_1964 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _57_1968 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1968) with
| (lbs, e2) -> begin
(let _148_728 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _148_727 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_148_728, cres, _148_727)))
end)))))))
end))
end))
end))
end))
end
| _57_1970 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _57_1982 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1982) with
| (lbs, e2) -> begin
(

let _57_1985 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1985) with
| (env0, topt) -> begin
(

let _57_1988 = (build_let_rec_env false env0 lbs)
in (match (_57_1988) with
| (lbs, rec_env) -> begin
(

let _57_1991 = (check_let_recs rec_env lbs)
in (match (_57_1991) with
| (lbs, g_lbs) -> begin
(

let _57_2003 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let _57_1994 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1994.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1994.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let _57_1997 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _57_1997.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1997.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1997.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _57_1997.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], lb.FStar_Syntax_Syntax.lbtyp))
in (env, lb))))) env))
in (match (_57_2003) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let _57_2009 = (tc_term env e2)
in (match (_57_2009) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _57_2013 = cres
in {FStar_Syntax_Syntax.eff_name = _57_2013.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _57_2013.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_2013.FStar_Syntax_Syntax.comp})
in (

let _57_2018 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_2018) with
| (lbs, e2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_57_2021) -> begin
(e, cres, guard)
end
| None -> begin
(

let _57_2024 = (check_no_escape None env bvs tres)
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
| _57_2027 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let _57_2060 = (FStar_List.fold_left (fun _57_2034 lb -> (match (_57_2034) with
| (lbs, env) -> begin
(

let _57_2039 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_57_2039) with
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

let _57_2048 = (let _148_740 = (let _148_739 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _148_739))
in (tc_check_tot_or_gtot_term (

let _57_2042 = env0
in {FStar_TypeChecker_Env.solver = _57_2042.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2042.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2042.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2042.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2042.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2042.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2042.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2042.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2042.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2042.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2042.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2042.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2042.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2042.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _57_2042.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2042.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2042.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_2042.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_2042.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2042.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2042.FStar_TypeChecker_Env.use_bv_sorts}) t _148_740))
in (match (_57_2048) with
| (t, _57_2046, g) -> begin
(

let _57_2049 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (

let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_TypeChecker_Env.should_verify env)) then begin
(

let _57_2052 = env
in {FStar_TypeChecker_Env.solver = _57_2052.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2052.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2052.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2052.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2052.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2052.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2052.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2052.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2052.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2052.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2052.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2052.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2052.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_2052.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2052.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2052.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2052.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_2052.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_2052.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2052.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2052.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (

let lb = (

let _57_2055 = lb
in {FStar_Syntax_Syntax.lbname = _57_2055.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _57_2055.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_57_2060) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _57_2073 = (let _148_745 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _57_2067 = (let _148_744 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _148_744 lb.FStar_Syntax_Syntax.lbdef))
in (match (_57_2067) with
| (e, c, g) -> begin
(

let _57_2068 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _148_745 FStar_List.unzip))
in (match (_57_2073) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _57_2081 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_2081) with
| (env1, _57_2080) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _57_2087 = (check_lbtyp top_level env lb)
in (match (_57_2087) with
| (topt, wf_annot, univ_vars, env1) -> begin
(

let _57_2088 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let _57_2095 = (tc_maybe_toplevel_term (

let _57_2090 = env1
in {FStar_TypeChecker_Env.solver = _57_2090.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2090.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2090.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2090.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2090.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2090.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2090.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2090.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2090.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2090.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2090.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2090.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2090.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _57_2090.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2090.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2090.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2090.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_2090.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_2090.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2090.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2090.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_57_2095) with
| (e1, c1, g1) -> begin
(

let _57_2099 = (let _148_752 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_2096 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _148_752 e1 c1 wf_annot))
in (match (_57_2099) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _57_2101 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_753 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _148_753))
end else begin
()
end
in (let _148_754 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _148_754))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _57_2108 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _57_2111 -> begin
(

let _57_2114 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_57_2114) with
| (univ_vars, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _148_758 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _148_758))
end else begin
(

let _57_2119 = (FStar_Syntax_Util.type_u ())
in (match (_57_2119) with
| (k, _57_2118) -> begin
(

let _57_2124 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_57_2124) with
| (t, _57_2122, g) -> begin
(

let _57_2125 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _148_761 = (let _148_759 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _148_759))
in (let _148_760 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _148_761 _148_760)))
end else begin
()
end
in (

let t = (norm env1 t)
in (let _148_762 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _148_762))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _57_2131 -> (match (_57_2131) with
| (x, imp) -> begin
(

let _57_2134 = (FStar_Syntax_Util.type_u ())
in (match (_57_2134) with
| (tu, u) -> begin
(

let _57_2139 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_57_2139) with
| (t, _57_2137, g) -> begin
(

let x = ((

let _57_2140 = x
in {FStar_Syntax_Syntax.ppname = _57_2140.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2140.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (

let _57_2143 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_766 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _148_765 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _148_766 _148_765)))
end else begin
()
end
in (let _148_767 = (push_binding env x)
in (x, _148_767, g, u))))
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

let _57_2158 = (tc_binder env b)
in (match (_57_2158) with
| (b, env', g, u) -> begin
(

let _57_2163 = (aux env' bs)
in (match (_57_2163) with
| (bs, env', g', us) -> begin
(let _148_775 = (let _148_774 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _148_774))
in ((b)::bs, env', _148_775, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun _57_2171 _57_2174 -> (match ((_57_2171, _57_2174)) with
| ((t, imp), (args, g)) -> begin
(

let _57_2179 = (tc_term env t)
in (match (_57_2179) with
| (t, _57_2177, g') -> begin
(let _148_784 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _148_784))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _57_2183 -> (match (_57_2183) with
| (pats, g) -> begin
(

let _57_2186 = (tc_args env p)
in (match (_57_2186) with
| (args, g') -> begin
(let _148_787 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _148_787))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _57_2192 = (tc_maybe_toplevel_term env e)
in (match (_57_2192) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let _57_2195 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_790 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _148_790))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _57_2200 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _148_791 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_148_791, false))
end else begin
(let _148_792 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_148_792, true))
end
in (match (_57_2200) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _148_793 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _148_793))
end
| _57_2204 -> begin
if allow_ghost then begin
(let _148_796 = (let _148_795 = (let _148_794 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_148_794, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_148_795))
in (Prims.raise _148_796))
end else begin
(let _148_799 = (let _148_798 = (let _148_797 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_148_797, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_148_798))
in (Prims.raise _148_799))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))


let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let _57_2214 = (tc_tot_or_gtot_term env t)
in (match (_57_2214) with
| (t, c, g) -> begin
(

let _57_2215 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let _57_2223 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_2223) with
| (t, c, g) -> begin
(

let _57_2224 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _148_819 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _148_819)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _148_823 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _148_823))))


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let _57_2239 = (tc_binders env tps)
in (match (_57_2239) with
| (tps, env, g, us) -> begin
(

let _57_2240 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (

let fail = (fun _57_2246 -> (match (()) with
| () -> begin
(let _148_838 = (let _148_837 = (let _148_836 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_148_836, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_148_837))
in (Prims.raise _148_838))
end))
in (

let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _57_2259))::((wp, _57_2255))::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2263 -> begin
(fail ())
end))
end
| _57_2265 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let _57_2272 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_57_2272) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _57_2274 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let _57_2278 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_57_2278) with
| (uvs, t') -> begin
(match ((let _148_845 = (FStar_Syntax_Subst.compress t')
in _148_845.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _57_2284 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))


let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (

let fail = (fun t -> (let _148_856 = (let _148_855 = (let _148_854 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_148_854, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_148_855))
in (Prims.raise _148_856)))
in (match ((let _148_857 = (FStar_Syntax_Subst.compress signature)
in _148_857.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _57_2301))::((wp, _57_2297))::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2305 -> begin
(fail signature)
end))
end
| _57_2307 -> begin
(fail signature)
end)))


let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (

let _57_2312 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_57_2312) with
| (a, wp) -> begin
(

let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _57_2315 -> begin
(

let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (

let op = (fun ts -> (

let _57_2319 = ()
in (

let t0 = (Prims.snd ts)
in (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (

let _57_2323 = ed
in (let _148_873 = (op ed.FStar_Syntax_Syntax.ret)
in (let _148_872 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _148_871 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _148_870 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _148_869 = (op ed.FStar_Syntax_Syntax.stronger)
in (let _148_868 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _148_867 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _148_866 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _148_865 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _148_864 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _57_2323.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2323.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2323.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2323.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2323.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _148_873; FStar_Syntax_Syntax.bind_wp = _148_872; FStar_Syntax_Syntax.if_then_else = _148_871; FStar_Syntax_Syntax.ite_wp = _148_870; FStar_Syntax_Syntax.stronger = _148_869; FStar_Syntax_Syntax.close_wp = _148_868; FStar_Syntax_Syntax.assert_p = _148_867; FStar_Syntax_Syntax.assume_p = _148_866; FStar_Syntax_Syntax.null_wp = _148_865; FStar_Syntax_Syntax.trivial = _148_864})))))))))))))
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

let n = (match ((let _148_895 = (FStar_Syntax_Subst.compress tm)
in _148_895.FStar_Syntax_Syntax.n)) with
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
| _57_2358 -> begin
tm.FStar_Syntax_Syntax.n
end)
in (

let _57_2360 = tm
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2360.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2360.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2360.FStar_Syntax_Syntax.vars})))
and visit_binder = (fun _57_2364 -> (match (_57_2364) with
| (bv, a) -> begin
(let _148_899 = (

let _57_2365 = bv
in (let _148_897 = (visit_term bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_2365.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2365.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_897}))
in (let _148_898 = (FStar_Syntax_Syntax.as_implicit false)
in (_148_899, _148_898)))
end))
and visit_maybe_lcomp = (fun lcomp -> (match (lcomp) with
| Some (FStar_Util.Inl (lcomp)) -> begin
(let _148_904 = (let _148_903 = (let _148_902 = (let _148_901 = (lcomp.FStar_Syntax_Syntax.comp ())
in (visit_comp _148_901))
in (FStar_Syntax_Util.lcomp_of_comp _148_902))
in FStar_Util.Inl (_148_903))
in Some (_148_904))
end
| comp -> begin
comp
end))
and visit_comp = (fun comp -> (

let n = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tm) -> begin
(let _148_906 = (visit_term tm)
in FStar_Syntax_Syntax.Total (_148_906))
end
| FStar_Syntax_Syntax.GTotal (tm) -> begin
(let _148_907 = (visit_term tm)
in FStar_Syntax_Syntax.GTotal (_148_907))
end
| comp -> begin
comp
end)
in (

let _57_2379 = comp
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2379.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2379.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2379.FStar_Syntax_Syntax.vars})))
and visit_args = (fun args -> (FStar_List.map (fun _57_2384 -> (match (_57_2384) with
| (tm, q) -> begin
(let _148_910 = (visit_term tm)
in (_148_910, q))
end)) args))
in (visit_term tm))))
in (

let check = (fun str t -> if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _57_2388 = (let _148_915 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Generated term for %s: %s\n" str _148_915))
in (

let t = (normalize t)
in (

let t = (FStar_Syntax_Subst.compress t)
in (

let _57_2403 = (tc_term env t)
in (match (_57_2403) with
| (e, {FStar_Syntax_Syntax.eff_name = _57_2399; FStar_Syntax_Syntax.res_typ = res_typ; FStar_Syntax_Syntax.cflags = _57_2396; FStar_Syntax_Syntax.comp = _57_2394}, _57_2402) -> begin
(

let _57_2404 = (let _148_918 = (let _148_917 = (normalize res_typ)
in (FStar_Syntax_Print.term_to_string _148_917))
in (FStar_Util.print2 "Inferred type for %s: %s\n" str _148_918))
in (let _148_920 = (let _148_919 = (normalize e)
in (FStar_Syntax_Print.term_to_string _148_919))
in (FStar_Util.print2 "Elaborated term for %s: %s\n" str _148_920)))
end)))))
end else begin
()
end)
in (

let rec collect_binders = (fun t -> (match ((let _148_923 = (FStar_Syntax_Subst.compress t)
in _148_923.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
t
end
| _57_2415 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _148_924 = (collect_binders rest)
in (FStar_List.append bs _148_924)))
end
| FStar_Syntax_Syntax.Tm_type (_57_2418) -> begin
[]
end
| _57_2421 -> begin
(FStar_All.failwith "wp_a doesn\'t end in Type0")
end))
in (

let _57_2436 = (

let i = (FStar_ST.alloc 0)
in (

let wp_binders = (let _148_931 = (normalize wp_a)
in (collect_binders _148_931))
in ((fun t -> (let _148_937 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow wp_binders _148_937))), (fun t -> (let _148_940 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow wp_binders _148_940))), (fun _57_2426 -> (match (()) with
| () -> begin
(FStar_List.map (fun _57_2430 -> (match (_57_2430) with
| (bv, _57_2429) -> begin
(

let _57_2431 = (let _148_944 = ((FStar_ST.read i) + 1)
in (FStar_ST.op_Colon_Equals i _148_944))
in (let _148_947 = (let _148_946 = (let _148_945 = (FStar_ST.read i)
in (FStar_Util.string_of_int _148_945))
in (Prims.strcat "g" _148_946))
in (FStar_Syntax_Syntax.gen_bv _148_947 None bv.FStar_Syntax_Syntax.sort)))
end)) wp_binders)
end)))))
in (match (_57_2436) with
| (mk_ctx, mk_gctx, mk_gamma) -> begin
(

let binders_of_list = (FStar_List.map (fun _57_2439 -> (match (_57_2439) with
| (t, b) -> begin
(let _148_953 = (FStar_Syntax_Syntax.as_implicit b)
in (t, _148_953))
end)))
in (

let implicit_binders_of_list = (FStar_List.map (fun t -> (let _148_956 = (FStar_Syntax_Syntax.as_implicit true)
in (t, _148_956))))
in (

let args_of_bv = (FStar_List.map (fun bv -> (let _148_959 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_Syntax_Syntax.as_arg _148_959))))
in (

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let x = (let _148_960 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _148_960))
in (

let ret = (let _148_965 = (let _148_964 = (let _148_963 = (let _148_962 = (let _148_961 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx _148_961))
in (FStar_Syntax_Syntax.mk_Total _148_962))
in (FStar_Syntax_Util.lcomp_of_comp _148_963))
in FStar_Util.Inl (_148_964))
in Some (_148_965))
in (

let gamma = (mk_gamma ())
in (

let body = (let _148_967 = (implicit_binders_of_list gamma)
in (let _148_966 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs _148_967 _148_966 ret)))
in (let _148_968 = (binders_of_list (((t, true))::((x, false))::[]))
in (FStar_Syntax_Util.abs _148_968 body ret)))))))
in (

let _57_2451 = (let _148_972 = (let _148_971 = (let _148_970 = (let _148_969 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_969)::[])
in (FStar_List.append binders _148_970))
in (FStar_Syntax_Util.abs _148_971 c_pure None))
in (check "pure" _148_972))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let l = (let _148_980 = (let _148_979 = (let _148_978 = (let _148_975 = (let _148_974 = (let _148_973 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _148_973))
in (FStar_Syntax_Syntax.mk_binder _148_974))
in (_148_975)::[])
in (let _148_977 = (let _148_976 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _148_976))
in (FStar_Syntax_Util.arrow _148_978 _148_977)))
in (mk_gctx _148_979))
in (FStar_Syntax_Syntax.gen_bv "l" None _148_980))
in (

let r = (let _148_982 = (let _148_981 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _148_981))
in (FStar_Syntax_Syntax.gen_bv "r" None _148_982))
in (

let ret = (let _148_987 = (let _148_986 = (let _148_985 = (let _148_984 = (let _148_983 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _148_983))
in (FStar_Syntax_Syntax.mk_Total _148_984))
in (FStar_Syntax_Util.lcomp_of_comp _148_985))
in FStar_Util.Inl (_148_986))
in Some (_148_987))
in (

let outer_body = (

let gamma = (mk_gamma ())
in (

let gamma_as_args = (args_of_bv gamma)
in (

let inner_body = (let _148_993 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _148_992 = (let _148_991 = (let _148_990 = (let _148_989 = (let _148_988 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _148_988 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg _148_989))
in (_148_990)::[])
in (FStar_List.append gamma_as_args _148_991))
in (FStar_Syntax_Util.mk_app _148_993 _148_992)))
in (let _148_994 = (implicit_binders_of_list gamma)
in (FStar_Syntax_Util.abs _148_994 inner_body ret)))))
in (let _148_995 = (binders_of_list (((t1, true))::((t2, true))::((l, false))::((r, false))::[]))
in (FStar_Syntax_Util.abs _148_995 outer_body ret))))))))
in (

let _57_2463 = (let _148_999 = (let _148_998 = (let _148_997 = (let _148_996 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_996)::[])
in (FStar_List.append binders _148_997))
in (FStar_Syntax_Util.abs _148_998 c_app None))
in (check "app" _148_999))
in (

let unknown = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _148_1004 = (let _148_1001 = (let _148_1000 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _148_1000))
in (_148_1001)::[])
in (let _148_1003 = (let _148_1002 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _148_1002))
in (FStar_Syntax_Util.arrow _148_1004 _148_1003)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _148_1006 = (let _148_1005 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _148_1005))
in (FStar_Syntax_Syntax.gen_bv "a1" None _148_1006))
in (

let ret = (let _148_1011 = (let _148_1010 = (let _148_1009 = (let _148_1008 = (let _148_1007 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _148_1007))
in (FStar_Syntax_Syntax.mk_Total _148_1008))
in (FStar_Syntax_Util.lcomp_of_comp _148_1009))
in FStar_Util.Inl (_148_1010))
in Some (_148_1011))
in (let _148_1024 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::((a1, false))::[]))
in (let _148_1023 = (let _148_1022 = (let _148_1021 = (let _148_1020 = (let _148_1019 = (let _148_1018 = (let _148_1015 = (let _148_1014 = (let _148_1013 = (let _148_1012 = (FStar_Syntax_Syntax.bv_to_name f)
in (_148_1012)::[])
in (unknown)::_148_1013)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1014))
in (FStar_Syntax_Util.mk_app c_pure _148_1015))
in (let _148_1017 = (let _148_1016 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_148_1016)::[])
in (_148_1018)::_148_1017))
in (unknown)::_148_1019)
in (unknown)::_148_1020)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1021))
in (FStar_Syntax_Util.mk_app c_app _148_1022))
in (FStar_Syntax_Util.abs _148_1024 _148_1023 ret)))))))))
in (

let _57_2473 = (let _148_1028 = (let _148_1027 = (let _148_1026 = (let _148_1025 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_1025)::[])
in (FStar_List.append binders _148_1026))
in (FStar_Syntax_Util.abs _148_1027 c_lift1 None))
in (check "lift1" _148_1028))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _148_1036 = (let _148_1033 = (let _148_1029 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _148_1029))
in (let _148_1032 = (let _148_1031 = (let _148_1030 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder _148_1030))
in (_148_1031)::[])
in (_148_1033)::_148_1032))
in (let _148_1035 = (let _148_1034 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal _148_1034))
in (FStar_Syntax_Util.arrow _148_1036 _148_1035)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _148_1038 = (let _148_1037 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _148_1037))
in (FStar_Syntax_Syntax.gen_bv "a1" None _148_1038))
in (

let a2 = (let _148_1040 = (let _148_1039 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _148_1039))
in (FStar_Syntax_Syntax.gen_bv "a2" None _148_1040))
in (

let ret = (let _148_1045 = (let _148_1044 = (let _148_1043 = (let _148_1042 = (let _148_1041 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx _148_1041))
in (FStar_Syntax_Syntax.mk_Total _148_1042))
in (FStar_Syntax_Util.lcomp_of_comp _148_1043))
in FStar_Util.Inl (_148_1044))
in Some (_148_1045))
in (let _148_1065 = (binders_of_list (((t1, true))::((t2, true))::((t3, true))::((f, false))::((a1, false))::((a2, false))::[]))
in (let _148_1064 = (let _148_1063 = (let _148_1062 = (let _148_1061 = (let _148_1060 = (let _148_1059 = (let _148_1056 = (let _148_1055 = (let _148_1054 = (let _148_1053 = (let _148_1052 = (let _148_1049 = (let _148_1048 = (let _148_1047 = (let _148_1046 = (FStar_Syntax_Syntax.bv_to_name f)
in (_148_1046)::[])
in (unknown)::_148_1047)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1048))
in (FStar_Syntax_Util.mk_app c_pure _148_1049))
in (let _148_1051 = (let _148_1050 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_148_1050)::[])
in (_148_1052)::_148_1051))
in (unknown)::_148_1053)
in (unknown)::_148_1054)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1055))
in (FStar_Syntax_Util.mk_app c_app _148_1056))
in (let _148_1058 = (let _148_1057 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_148_1057)::[])
in (_148_1059)::_148_1058))
in (unknown)::_148_1060)
in (unknown)::_148_1061)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1062))
in (FStar_Syntax_Util.mk_app c_app _148_1063))
in (FStar_Syntax_Util.abs _148_1065 _148_1064 ret)))))))))))
in (

let _57_2484 = (let _148_1069 = (let _148_1068 = (let _148_1067 = (let _148_1066 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_1066)::[])
in (FStar_List.append binders _148_1067))
in (FStar_Syntax_Util.abs _148_1068 c_lift2 None))
in (check "lift2" _148_1069))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _148_1075 = (let _148_1071 = (let _148_1070 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _148_1070))
in (_148_1071)::[])
in (let _148_1074 = (let _148_1073 = (let _148_1072 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _148_1072))
in (FStar_Syntax_Syntax.mk_Total _148_1073))
in (FStar_Syntax_Util.arrow _148_1075 _148_1074)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let ret = (let _148_1085 = (let _148_1084 = (let _148_1083 = (let _148_1082 = (let _148_1081 = (let _148_1080 = (let _148_1077 = (let _148_1076 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _148_1076))
in (_148_1077)::[])
in (let _148_1079 = (let _148_1078 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _148_1078))
in (FStar_Syntax_Util.arrow _148_1080 _148_1079)))
in (mk_ctx _148_1081))
in (FStar_Syntax_Syntax.mk_Total _148_1082))
in (FStar_Syntax_Util.lcomp_of_comp _148_1083))
in FStar_Util.Inl (_148_1084))
in Some (_148_1085))
in (

let e1 = (let _148_1086 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _148_1086))
in (

let gamma = (mk_gamma ())
in (

let body = (let _148_1096 = (let _148_1089 = (FStar_Syntax_Syntax.binders_of_list gamma)
in (let _148_1088 = (let _148_1087 = (FStar_Syntax_Syntax.mk_binder e1)
in (_148_1087)::[])
in (FStar_List.append _148_1089 _148_1088)))
in (let _148_1095 = (let _148_1094 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _148_1093 = (let _148_1092 = (let _148_1090 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _148_1090))
in (let _148_1091 = (args_of_bv gamma)
in (_148_1092)::_148_1091))
in (FStar_Syntax_Util.mk_app _148_1094 _148_1093)))
in (FStar_Syntax_Util.abs _148_1096 _148_1095 ret)))
in (let _148_1097 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::[]))
in (FStar_Syntax_Util.abs _148_1097 body ret))))))))))
in (

let _57_2495 = (let _148_1101 = (let _148_1100 = (let _148_1099 = (let _148_1098 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_1098)::[])
in (FStar_List.append binders _148_1099))
in (FStar_Syntax_Util.abs _148_1100 c_push None))
in (check "push" _148_1101))
in (

let ret_tot_wp_a = (let _148_1104 = (let _148_1103 = (let _148_1102 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _148_1102))
in FStar_Util.Inl (_148_1103))
in Some (_148_1104))
in (

let wp_if_then_else = (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _148_1115 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (let _148_1114 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_unfoldable (2)) None)
in (let _148_1113 = (let _148_1112 = (let _148_1111 = (let _148_1110 = (let _148_1109 = (let _148_1108 = (let _148_1107 = (let _148_1106 = (let _148_1105 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _148_1105))
in (_148_1106)::[])
in (FStar_Syntax_Util.mk_app l_ite _148_1107))
in (_148_1108)::[])
in (unknown)::_148_1109)
in (unknown)::_148_1110)
in (unknown)::_148_1111)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1112))
in (FStar_Syntax_Util.mk_app c_lift2 _148_1113)))
in (FStar_Syntax_Util.abs _148_1115 _148_1114 ret_tot_wp_a))))
in (

let wp_if_then_else = (normalize_and_make_binders_explicit wp_if_then_else)
in (

let _57_2502 = (let _148_1116 = (FStar_Syntax_Util.abs binders wp_if_then_else None)
in (check "wp_if_then_else" _148_1116))
in (

let wp_assert = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_and = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (

let body = (let _148_1130 = (let _148_1129 = (let _148_1128 = (let _148_1127 = (let _148_1126 = (let _148_1123 = (let _148_1122 = (let _148_1121 = (let _148_1120 = (let _148_1119 = (let _148_1118 = (let _148_1117 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _148_1117))
in (_148_1118)::[])
in (FStar_Syntax_Util.mk_app l_and _148_1119))
in (_148_1120)::[])
in (unknown)::_148_1121)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1122))
in (FStar_Syntax_Util.mk_app c_pure _148_1123))
in (let _148_1125 = (let _148_1124 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_148_1124)::[])
in (_148_1126)::_148_1125))
in (unknown)::_148_1127)
in (unknown)::_148_1128)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1129))
in (FStar_Syntax_Util.mk_app c_app _148_1130))
in (let _148_1131 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _148_1131 body ret_tot_wp_a))))))
in (

let wp_assert = (normalize_and_make_binders_explicit wp_assert)
in (

let _57_2510 = (let _148_1132 = (FStar_Syntax_Util.abs binders wp_assert None)
in (check "wp_assert" _148_1132))
in (

let wp_assume = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_imp = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (

let body = (let _148_1146 = (let _148_1145 = (let _148_1144 = (let _148_1143 = (let _148_1142 = (let _148_1139 = (let _148_1138 = (let _148_1137 = (let _148_1136 = (let _148_1135 = (let _148_1134 = (let _148_1133 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _148_1133))
in (_148_1134)::[])
in (FStar_Syntax_Util.mk_app l_imp _148_1135))
in (_148_1136)::[])
in (unknown)::_148_1137)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1138))
in (FStar_Syntax_Util.mk_app c_pure _148_1139))
in (let _148_1141 = (let _148_1140 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_148_1140)::[])
in (_148_1142)::_148_1141))
in (unknown)::_148_1143)
in (unknown)::_148_1144)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1145))
in (FStar_Syntax_Util.mk_app c_app _148_1146))
in (let _148_1147 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _148_1147 body ret_tot_wp_a))))))
in (

let wp_assume = (normalize_and_make_binders_explicit wp_assume)
in (

let _57_2518 = (let _148_1148 = (FStar_Syntax_Util.abs binders wp_assume None)
in (check "wp_assume" _148_1148))
in (

let tforall = (let _148_1151 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _148_1150 = (let _148_1149 = (FStar_Syntax_Syntax.as_arg unknown)
in (_148_1149)::[])
in (FStar_Syntax_Util.mk_app _148_1151 _148_1150)))
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _148_1155 = (let _148_1153 = (let _148_1152 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _148_1152))
in (_148_1153)::[])
in (let _148_1154 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1155 _148_1154)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (let _148_1168 = (let _148_1167 = (let _148_1166 = (let _148_1165 = (let _148_1164 = (let _148_1156 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((unknown)::(tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _148_1156))
in (let _148_1163 = (let _148_1162 = (let _148_1161 = (let _148_1160 = (let _148_1159 = (let _148_1158 = (let _148_1157 = (FStar_Syntax_Syntax.bv_to_name f)
in (_148_1157)::[])
in (unknown)::_148_1158)
in (unknown)::_148_1159)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1160))
in (FStar_Syntax_Util.mk_app c_push _148_1161))
in (_148_1162)::[])
in (_148_1164)::_148_1163))
in (unknown)::_148_1165)
in (unknown)::_148_1166)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1167))
in (FStar_Syntax_Util.mk_app c_app _148_1168))
in (let _148_1169 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_Syntax_Util.abs _148_1169 body ret_tot_wp_a))))))
in (

let wp_close = (normalize_and_make_binders_explicit wp_close)
in (

let _57_2527 = (let _148_1170 = (FStar_Syntax_Util.abs binders wp_close None)
in (check "wp_close" _148_1170))
in (

let ret_tot_type0 = (let _148_1173 = (let _148_1172 = (let _148_1171 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_1171))
in FStar_Util.Inl (_148_1172))
in Some (_148_1173))
in (

let mk_forall = (fun x body -> (

let tforall = (let _148_1180 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _148_1179 = (let _148_1178 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (_148_1178)::[])
in (FStar_Syntax_Util.mk_app _148_1180 _148_1179)))
in (let _148_1187 = (let _148_1186 = (let _148_1185 = (let _148_1184 = (let _148_1183 = (let _148_1182 = (let _148_1181 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_1181)::[])
in (FStar_Syntax_Util.abs _148_1182 body ret_tot_type0))
in (FStar_Syntax_Syntax.as_arg _148_1183))
in (_148_1184)::[])
in (tforall, _148_1185))
in FStar_Syntax_Syntax.Tm_app (_148_1186))
in (FStar_Syntax_Syntax.mk _148_1187 None FStar_Range.dummyRange))))
in (

let rec mk_leq = (fun t x y -> (match ((let _148_1195 = (let _148_1194 = (FStar_Syntax_Subst.compress t)
in (normalize _148_1194))
in _148_1195.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_2539) -> begin
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

let body = (let _148_1207 = (let _148_1197 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _148_1196 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_leq a _148_1197 _148_1196)))
in (let _148_1206 = (let _148_1205 = (let _148_1200 = (let _148_1199 = (let _148_1198 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _148_1198))
in (_148_1199)::[])
in (FStar_Syntax_Util.mk_app x _148_1200))
in (let _148_1204 = (let _148_1203 = (let _148_1202 = (let _148_1201 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _148_1201))
in (_148_1202)::[])
in (FStar_Syntax_Util.mk_app y _148_1203))
in (mk_leq b _148_1205 _148_1204)))
in (FStar_Syntax_Util.mk_imp _148_1207 _148_1206)))
in (let _148_1208 = (mk_forall a2 body)
in (mk_forall a1 _148_1208))))))
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let _57_2575 = t
in (let _148_1212 = (let _148_1211 = (let _148_1210 = (let _148_1209 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _148_1209))
in ((binder)::[], _148_1210))
in FStar_Syntax_Syntax.Tm_arrow (_148_1211))
in {FStar_Syntax_Syntax.n = _148_1212; FStar_Syntax_Syntax.tk = _57_2575.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2575.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2575.FStar_Syntax_Syntax.vars}))
in (mk_leq t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_57_2579) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _57_2582 -> begin
(FStar_Syntax_Util.mk_eq t t x y)
end))
in (

let stronger = (

let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (

let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (

let body = (let _148_1214 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _148_1213 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_leq wp_a _148_1214 _148_1213)))
in (let _148_1215 = (FStar_Syntax_Syntax.binders_of_list ((wp1)::(wp2)::[]))
in (FStar_Syntax_Util.abs _148_1215 body ret_tot_type0)))))
in (

let _57_2587 = (let _148_1219 = (let _148_1218 = (let _148_1217 = (let _148_1216 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_1216)::[])
in (FStar_List.append binders _148_1217))
in (FStar_Syntax_Util.abs _148_1218 stronger None))
in (check "stronger" _148_1219))
in (

let null_wp = (Prims.snd ed.FStar_Syntax_Syntax.null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (let _148_1227 = (let _148_1226 = (let _148_1225 = (let _148_1222 = (let _148_1221 = (let _148_1220 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _148_1220))
in (_148_1221)::[])
in (FStar_Syntax_Util.mk_app null_wp _148_1222))
in (let _148_1224 = (let _148_1223 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_148_1223)::[])
in (_148_1225)::_148_1224))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1226))
in (FStar_Syntax_Util.mk_app stronger _148_1227))
in (let _148_1228 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_Syntax_Util.abs _148_1228 body ret_tot_type0))))
in (

let wp_trivial = (normalize_and_make_binders_explicit wp_trivial)
in (

let _57_2594 = (let _148_1229 = (FStar_Syntax_Util.abs binders wp_trivial None)
in (check "wp_trivial" _148_1229))
in (

let _57_2596 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2596.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2596.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2596.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2596.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2596.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _57_2596.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2596.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = ([], wp_if_then_else); FStar_Syntax_Syntax.ite_wp = _57_2596.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _57_2596.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = ([], wp_close); FStar_Syntax_Syntax.assert_p = ([], wp_assert); FStar_Syntax_Syntax.assume_p = ([], wp_assume); FStar_Syntax_Syntax.null_wp = _57_2596.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = ([], wp_trivial)}))))))))))))))))))))))))))))))))))))))
end))))))))


let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  effect_cost  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed is_for_free -> (

let _57_2601 = ()
in (

let _57_2605 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_57_2605) with
| (binders_un, signature_un) -> begin
(

let _57_2610 = (tc_tparams env0 binders_un)
in (match (_57_2610) with
| (binders, env, _57_2609) -> begin
(

let _57_2614 = (tc_trivial_guard env signature_un)
in (match (_57_2614) with
| (signature, _57_2613) -> begin
(

let ed = (

let _57_2615 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2615.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2615.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2615.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _57_2615.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2615.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _57_2615.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _57_2615.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _57_2615.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _57_2615.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _57_2615.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _57_2615.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _57_2615.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _57_2615.FStar_Syntax_Syntax.trivial})
in (

let _57_2621 = (open_effect_decl env ed)
in (match (_57_2621) with
| (ed, a, wp_a) -> begin
(

let get_effect_signature = (fun _57_2623 -> (match (()) with
| () -> begin
(

let _57_2627 = (tc_trivial_guard env signature_un)
in (match (_57_2627) with
| (signature, _57_2626) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (

let env = (let _148_1238 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _148_1238))
in (

let _57_2629 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _148_1241 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _148_1240 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _148_1239 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checking effect signature: %s %s : %s\n" _148_1241 _148_1240 _148_1239))))
end else begin
()
end
in (

let check_and_gen' = (fun env _57_2636 k -> (match (_57_2636) with
| (_57_2634, t) -> begin
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

let expected_k = (let _148_1253 = (let _148_1251 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1250 = (let _148_1249 = (let _148_1248 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _148_1248))
in (_148_1249)::[])
in (_148_1251)::_148_1250))
in (let _148_1252 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _148_1253 _148_1252)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (

let bind_wp = (

let _57_2645 = (get_effect_signature ())
in (match (_57_2645) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _148_1257 = (let _148_1255 = (let _148_1254 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _148_1254))
in (_148_1255)::[])
in (let _148_1256 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _148_1257 _148_1256)))
in (

let expected_k = (let _148_1268 = (let _148_1266 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _148_1265 = (let _148_1264 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1263 = (let _148_1262 = (FStar_Syntax_Syntax.mk_binder b)
in (let _148_1261 = (let _148_1260 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _148_1259 = (let _148_1258 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (_148_1258)::[])
in (_148_1260)::_148_1259))
in (_148_1262)::_148_1261))
in (_148_1264)::_148_1263))
in (_148_1266)::_148_1265))
in (let _148_1267 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _148_1268 _148_1267)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (let _148_1270 = (let _148_1269 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_1269 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _148_1270))
in (

let expected_k = (let _148_1279 = (let _148_1277 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1276 = (let _148_1275 = (FStar_Syntax_Syntax.mk_binder p)
in (let _148_1274 = (let _148_1273 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _148_1272 = (let _148_1271 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1271)::[])
in (_148_1273)::_148_1272))
in (_148_1275)::_148_1274))
in (_148_1277)::_148_1276))
in (let _148_1278 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1279 _148_1278)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (let _148_1284 = (let _148_1282 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1281 = (let _148_1280 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1280)::[])
in (_148_1282)::_148_1281))
in (let _148_1283 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1284 _148_1283)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let _57_2657 = (FStar_Syntax_Util.type_u ())
in (match (_57_2657) with
| (t, _57_2656) -> begin
(

let expected_k = (let _148_1291 = (let _148_1289 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1288 = (let _148_1287 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _148_1286 = (let _148_1285 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1285)::[])
in (_148_1287)::_148_1286))
in (_148_1289)::_148_1288))
in (let _148_1290 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _148_1291 _148_1290)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (let _148_1293 = (let _148_1292 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_1292 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _148_1293))
in (

let b_wp_a = (let _148_1297 = (let _148_1295 = (let _148_1294 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _148_1294))
in (_148_1295)::[])
in (let _148_1296 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1297 _148_1296)))
in (

let expected_k = (let _148_1304 = (let _148_1302 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1301 = (let _148_1300 = (FStar_Syntax_Syntax.mk_binder b)
in (let _148_1299 = (let _148_1298 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_148_1298)::[])
in (_148_1300)::_148_1299))
in (_148_1302)::_148_1301))
in (let _148_1303 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1304 _148_1303)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (let _148_1313 = (let _148_1311 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1310 = (let _148_1309 = (let _148_1306 = (let _148_1305 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_1305 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _148_1306))
in (let _148_1308 = (let _148_1307 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1307)::[])
in (_148_1309)::_148_1308))
in (_148_1311)::_148_1310))
in (let _148_1312 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1313 _148_1312)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _148_1322 = (let _148_1320 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1319 = (let _148_1318 = (let _148_1315 = (let _148_1314 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_1314 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _148_1315))
in (let _148_1317 = (let _148_1316 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1316)::[])
in (_148_1318)::_148_1317))
in (_148_1320)::_148_1319))
in (let _148_1321 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1322 _148_1321)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _148_1325 = (let _148_1323 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_1323)::[])
in (let _148_1324 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1325 _148_1324)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let _57_2673 = (FStar_Syntax_Util.type_u ())
in (match (_57_2673) with
| (t, _57_2672) -> begin
(

let expected_k = (let _148_1330 = (let _148_1328 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1327 = (let _148_1326 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1326)::[])
in (_148_1328)::_148_1327))
in (let _148_1329 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _148_1330 _148_1329)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let t = (let _148_1331 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _148_1331))
in (

let _57_2679 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_57_2679) with
| (univs, t) -> begin
(

let _57_2695 = (match ((let _148_1333 = (let _148_1332 = (FStar_Syntax_Subst.compress t)
in _148_1332.FStar_Syntax_Syntax.n)
in (binders, _148_1333))) with
| ([], _57_2682) -> begin
([], t)
end
| (_57_2685, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _57_2692 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_2695) with
| (binders, signature) -> begin
(

let close = (fun n ts -> (

let ts = (let _148_1338 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _148_1338))
in (

let _57_2700 = ()
in ts)))
in (

let ed = (

let _57_2702 = ed
in (let _148_1348 = (close 0 ret)
in (let _148_1347 = (close 1 bind_wp)
in (let _148_1346 = (close 0 if_then_else)
in (let _148_1345 = (close 0 ite_wp)
in (let _148_1344 = (close 0 stronger)
in (let _148_1343 = (close 1 close_wp)
in (let _148_1342 = (close 0 assert_p)
in (let _148_1341 = (close 0 assume_p)
in (let _148_1340 = (close 0 null_wp)
in (let _148_1339 = (close 0 trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _57_2702.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2702.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _148_1348; FStar_Syntax_Syntax.bind_wp = _148_1347; FStar_Syntax_Syntax.if_then_else = _148_1346; FStar_Syntax_Syntax.ite_wp = _148_1345; FStar_Syntax_Syntax.stronger = _148_1344; FStar_Syntax_Syntax.close_wp = _148_1343; FStar_Syntax_Syntax.assert_p = _148_1342; FStar_Syntax_Syntax.assume_p = _148_1341; FStar_Syntax_Syntax.null_wp = _148_1340; FStar_Syntax_Syntax.trivial = _148_1339})))))))))))
in (

let _57_2705 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1349 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _148_1349))
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

let _57_2711 = ()
in (

let _57_2719 = ()
in (match (ses) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _57_2748, _57_2750, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _57_2739, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _57_2728, r2))::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
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

let lex_top_t = (let _148_1357 = (let _148_1356 = (let _148_1355 = (let _148_1354 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _148_1354 FStar_Syntax_Syntax.Delta_constant None))
in (_148_1355, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_148_1356))
in (FStar_Syntax_Syntax.mk _148_1357 None r1))
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

let a = (let _148_1358 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _148_1358))
in (

let hd = (let _148_1359 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _148_1359))
in (

let tl = (let _148_1364 = (let _148_1363 = (let _148_1362 = (let _148_1361 = (let _148_1360 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _148_1360 FStar_Syntax_Syntax.Delta_constant None))
in (_148_1361, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_148_1362))
in (FStar_Syntax_Syntax.mk _148_1363 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _148_1364))
in (

let res = (let _148_1368 = (let _148_1367 = (let _148_1366 = (let _148_1365 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _148_1365 FStar_Syntax_Syntax.Delta_constant None))
in (_148_1366, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_148_1367))
in (FStar_Syntax_Syntax.mk _148_1368 None r2))
in (let _148_1369 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _148_1369))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _148_1371 = (let _148_1370 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _148_1370))
in FStar_Syntax_Syntax.Sig_bundle (_148_1371)))))))))))))))
end
| _57_2774 -> begin
(let _148_1373 = (let _148_1372 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _148_1372))
in (FStar_All.failwith _148_1373))
end))))


let tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _57_2784 = (FStar_Syntax_Util.type_u ())
in (match (_57_2784) with
| (k, _57_2783) -> begin
(

let phi = (let _148_1384 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _148_1384 (norm env)))
in (

let _57_2786 = (FStar_TypeChecker_Util.check_uvars r phi)
in FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))))
end))))


let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _148_1398 = (let _148_1397 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _148_1397))
in (FStar_TypeChecker_Errors.diag r _148_1398)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let _57_2809 = ()
in (

let _57_2811 = (warn_positivity tc r)
in (

let _57_2815 = (FStar_Syntax_Subst.open_term tps k)
in (match (_57_2815) with
| (tps, k) -> begin
(

let _57_2820 = (tc_binders env tps)
in (match (_57_2820) with
| (tps, env_tps, guard_params, us) -> begin
(

let _57_2823 = (FStar_Syntax_Util.arrow_formals k)
in (match (_57_2823) with
| (indices, t) -> begin
(

let _57_2828 = (tc_binders env_tps indices)
in (match (_57_2828) with
| (indices, env', guard_indices, us') -> begin
(

let _57_2836 = (

let _57_2833 = (tc_tot_or_gtot_term env' t)
in (match (_57_2833) with
| (t, _57_2831, g) -> begin
(let _148_1405 = (let _148_1404 = (let _148_1403 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params _148_1403))
in (FStar_TypeChecker_Rel.discharge_guard env' _148_1404))
in (t, _148_1405))
end))
in (match (_57_2836) with
| (t, guard) -> begin
(

let k = (let _148_1406 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _148_1406))
in (

let _57_2840 = (FStar_Syntax_Util.type_u ())
in (match (_57_2840) with
| (t_type, u) -> begin
(

let _57_2841 = (let _148_1407 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _148_1407))
in (

let t_tc = (let _148_1408 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _148_1408))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _148_1409 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) ([], t_tc))
in (_148_1409, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u, guard)))))))
end)))
end))
end))
end))
end))
end))))
end
| _57_2848 -> begin
(FStar_All.failwith "impossible")
end))
in (

let positive_if_pure = (fun _57_2850 l -> ())
in (

let tc_data = (fun env tcs _57_7 -> (match (_57_7) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let _57_2867 = ()
in (

let _57_2902 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _57_2871 -> (match (_57_2871) with
| (se, u_tc) -> begin
if (let _148_1422 = (let _148_1421 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _148_1421))
in (FStar_Ident.lid_equals tc_lid _148_1422)) then begin
(

let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2873, _57_2875, tps, _57_2878, _57_2880, _57_2882, _57_2884, _57_2886) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _57_2892 -> (match (_57_2892) with
| (x, _57_2891) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _57_2894 -> begin
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
in (match (_57_2902) with
| (tps, u_tc) -> begin
(

let _57_2922 = (match ((let _148_1424 = (FStar_Syntax_Subst.compress t)
in _148_1424.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _57_2910 = (FStar_Util.first_N ntps bs)
in (match (_57_2910) with
| (_57_2908, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _57_2916 -> (match (_57_2916) with
| (x, _57_2915) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _148_1427 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _148_1427))))
end))
end
| _57_2919 -> begin
([], t)
end)
in (match (_57_2922) with
| (arguments, result) -> begin
(

let _57_2923 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1430 = (FStar_Syntax_Print.lid_to_string c)
in (let _148_1429 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _148_1428 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _148_1430 _148_1429 _148_1428))))
end else begin
()
end
in (

let _57_2928 = (tc_tparams env arguments)
in (match (_57_2928) with
| (arguments, env', us) -> begin
(

let _57_2932 = (tc_trivial_guard env' result)
in (match (_57_2932) with
| (result, _57_2931) -> begin
(

let _57_2936 = (FStar_Syntax_Util.head_and_args result)
in (match (_57_2936) with
| (head, _57_2935) -> begin
(

let _57_2941 = (match ((let _148_1431 = (FStar_Syntax_Subst.compress head)
in _148_1431.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _57_2940 -> begin
(let _148_1436 = (let _148_1435 = (let _148_1434 = (let _148_1433 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _148_1432 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _148_1433 _148_1432)))
in (_148_1434, r))
in FStar_Syntax_Syntax.Error (_148_1435))
in (Prims.raise _148_1436))
end)
in (

let g = (FStar_List.fold_left2 (fun g _57_2947 u_x -> (match (_57_2947) with
| (x, _57_2946) -> begin
(

let _57_2949 = ()
in (let _148_1440 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _148_1440)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _148_1444 = (let _148_1442 = (FStar_All.pipe_right tps (FStar_List.map (fun _57_2955 -> (match (_57_2955) with
| (x, _57_2954) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _148_1442 arguments))
in (let _148_1443 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _148_1444 _148_1443)))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _57_2958 -> begin
(FStar_All.failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let _57_2964 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_8 -> (match (_57_8) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2968, _57_2970, tps, k, _57_2974, _57_2976, _57_2978, _57_2980) -> begin
(let _148_1455 = (let _148_1454 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _148_1454))
in (FStar_Syntax_Syntax.null_binder _148_1455))
end
| _57_2984 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _57_9 -> (match (_57_9) with
| FStar_Syntax_Syntax.Sig_datacon (_57_2988, _57_2990, t, _57_2993, _57_2995, _57_2997, _57_2999, _57_3001) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _57_3005 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let t = (let _148_1457 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _148_1457))
in (

let _57_3008 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1458 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _148_1458))
end else begin
()
end
in (

let _57_3012 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_57_3012) with
| (uvs, t) -> begin
(

let _57_3014 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1462 = (let _148_1460 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _148_1460 (FStar_String.concat ", ")))
in (let _148_1461 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _148_1462 _148_1461)))
end else begin
()
end
in (

let _57_3018 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_57_3018) with
| (uvs, t) -> begin
(

let _57_3022 = (FStar_Syntax_Util.arrow_formals t)
in (match (_57_3022) with
| (args, _57_3021) -> begin
(

let _57_3025 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_57_3025) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _57_3029 se -> (match (_57_3029) with
| (x, _57_3028) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3033, tps, _57_3036, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let _57_3059 = (match ((let _148_1465 = (FStar_Syntax_Subst.compress ty)
in _148_1465.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _57_3050 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_57_3050) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _57_3053 -> begin
(let _148_1466 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _148_1466 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _57_3056 -> begin
([], ty)
end)
in (match (_57_3059) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _57_3061 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| _57_3065 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _148_1467 -> FStar_Syntax_Syntax.U_name (_148_1467))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_10 -> (match (_57_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3070, _57_3072, _57_3074, _57_3076, _57_3078, _57_3080, _57_3082) -> begin
(tc, uvs_universes)
end
| _57_3086 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _57_3091 d -> (match (_57_3091) with
| (t, _57_3090) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _57_3095, _57_3097, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _148_1471 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _148_1471 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _57_3107 -> begin
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

let _57_3117 = (FStar_All.pipe_right ses (FStar_List.partition (fun _57_11 -> (match (_57_11) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_3111) -> begin
true
end
| _57_3114 -> begin
false
end))))
in (match (_57_3117) with
| (tys, datas) -> begin
(

let _57_3124 = if (FStar_All.pipe_right datas (FStar_Util.for_some (fun _57_12 -> (match (_57_12) with
| FStar_Syntax_Syntax.Sig_datacon (_57_3120) -> begin
false
end
| _57_3123 -> begin
true
end)))) then begin
(let _148_1476 = (let _148_1475 = (let _148_1474 = (FStar_TypeChecker_Env.get_range env)
in ("Mutually defined type contains a non-inductive element", _148_1474))
in FStar_Syntax_Syntax.Error (_148_1475))
in (Prims.raise _148_1476))
end else begin
()
end
in (

let env0 = env
in (

let _57_3143 = (FStar_List.fold_right (fun tc _57_3131 -> (match (_57_3131) with
| (env, all_tcs, g) -> begin
(

let _57_3136 = (tc_tycon env tc)
in (match (_57_3136) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (

let _57_3138 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1479 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _148_1479))
end else begin
()
end
in (let _148_1481 = (let _148_1480 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g _148_1480))
in (env, ((tc, tc_u))::all_tcs, _148_1481))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_3143) with
| (env, tcs, g) -> begin
(

let _57_3153 = (FStar_List.fold_right (fun se _57_3147 -> (match (_57_3147) with
| (datas, g) -> begin
(

let _57_3150 = (tc_data env tcs se)
in (match (_57_3150) with
| (data, g') -> begin
(let _148_1484 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _148_1484))
end))
end)) datas ([], g))
in (match (_57_3153) with
| (datas, g) -> begin
(

let _57_3156 = (let _148_1485 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _148_1485 datas))
in (match (_57_3156) with
| (tcs, datas) -> begin
(

let sig_bndle = (let _148_1487 = (let _148_1486 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _148_1486))
in FStar_Syntax_Syntax.Sig_bundle (_148_1487))
in (

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (_57_3161, _57_3163, t, _57_3166, _57_3168, _57_3170, _57_3172, _57_3174) -> begin
t
end
| _57_3178 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let dr = FStar_Range.dummyRange
in (

let haseq_ty = (fun usubst us acc ty -> (

let _57_3205 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _57_3187, bs, t, _57_3191, d_lids, _57_3194, _57_3196) -> begin
(lid, bs, t, d_lids)
end
| _57_3200 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_57_3205) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _148_1498 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _148_1498 t))
in (

let _57_3210 = (FStar_Syntax_Subst.open_term bs t)
in (match (_57_3210) with
| (bs, t) -> begin
(

let ibs = (match ((let _148_1499 = (FStar_Syntax_Subst.compress t)
in _148_1499.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _57_3213) -> begin
ibs
end
| _57_3217 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _148_1502 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _148_1501 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _148_1502 _148_1501)))
in (

let ind = (let _148_1505 = (FStar_List.map (fun _57_3224 -> (match (_57_3224) with
| (bv, aq) -> begin
(let _148_1504 = (FStar_Syntax_Syntax.bv_to_name bv)
in (_148_1504, aq))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _148_1505 None dr))
in (

let ind = (let _148_1508 = (FStar_List.map (fun _57_3228 -> (match (_57_3228) with
| (bv, aq) -> begin
(let _148_1507 = (FStar_Syntax_Syntax.bv_to_name bv)
in (_148_1507, aq))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _148_1508 None dr))
in (

let haseq_ind = (let _148_1510 = (let _148_1509 = (FStar_Syntax_Syntax.as_arg ind)
in (_148_1509)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _148_1510 None dr))
in (

let bs' = (FStar_List.filter (fun b -> (

let _57_3239 = acc
in (match (_57_3239) with
| (_57_3233, en, _57_3236, _57_3238) -> begin
(

let opt = (let _148_1513 = (let _148_1512 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _148_1512))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort _148_1513 false))
in (match (opt) with
| None -> begin
false
end
| Some (_57_3243) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (let _148_1519 = (let _148_1518 = (let _148_1517 = (let _148_1516 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg _148_1516))
in (_148_1517)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _148_1518 None dr))
in (FStar_Syntax_Util.mk_conj t _148_1519))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let _57_3250 = fml
in (let _148_1525 = (let _148_1524 = (let _148_1523 = (let _148_1522 = (let _148_1521 = (let _148_1520 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_148_1520)::[])
in (_148_1521)::[])
in FStar_Syntax_Syntax.Meta_pattern (_148_1522))
in (fml, _148_1523))
in FStar_Syntax_Syntax.Tm_meta (_148_1524))
in {FStar_Syntax_Syntax.n = _148_1525; FStar_Syntax_Syntax.tk = _57_3250.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_3250.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_3250.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _148_1531 = (let _148_1530 = (let _148_1529 = (let _148_1528 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs ((((Prims.fst b), None))::[]) _148_1528 None))
in (FStar_Syntax_Syntax.as_arg _148_1529))
in (_148_1530)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _148_1531 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _148_1537 = (let _148_1536 = (let _148_1535 = (let _148_1534 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs ((((Prims.fst b), None))::[]) _148_1534 None))
in (FStar_Syntax_Syntax.as_arg _148_1535))
in (_148_1536)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _148_1537 None dr))) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let _57_3264 = acc
in (match (_57_3264) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_57_3269, _57_3271, _57_3273, t_lid, _57_3276, _57_3278, _57_3280, _57_3282) -> begin
(t_lid = lid)
end
| _57_3286 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let haseq_data = (fun acc data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (match ((let _148_1543 = (FStar_Syntax_Subst.compress dt)
in _148_1543.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _57_3295) -> begin
(

let dbs = (let _148_1544 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _148_1544))
in (

let dbs = (let _148_1545 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _148_1545 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (let _148_1550 = (let _148_1549 = (let _148_1548 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_148_1548)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _148_1549 None dr))
in (FStar_Syntax_Util.mk_conj t _148_1550))) FStar_Syntax_Util.t_true dbs)
in (

let _57_3306 = acc
in (match (_57_3306) with
| (env, cond') -> begin
(let _148_1552 = (FStar_TypeChecker_Env.push_binders env dbs)
in (let _148_1551 = (FStar_Syntax_Util.mk_conj cond' cond)
in (_148_1552, _148_1551)))
end))))))
end
| _57_3308 -> begin
acc
end))))
in (

let _57_3311 = (FStar_List.fold_left haseq_data (env, FStar_Syntax_Util.t_true) t_datas)
in (match (_57_3311) with
| (env, cond) -> begin
(

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (let _148_1554 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _148_1553 = (FStar_Syntax_Util.mk_conj cond' cond)
in ((FStar_List.append l_axioms (((axiom_lid, fml))::[])), env, _148_1554, _148_1553))))
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
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_3317, us, _57_3320, _57_3322, _57_3324, _57_3326, _57_3328, _57_3330) -> begin
us
end
| _57_3334 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let _57_3338 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_57_3338) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _57_3340 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _57_3342 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let _57_3349 = (FStar_List.fold_left (haseq_ty usubst us) ([], env, FStar_Syntax_Util.t_true, FStar_Syntax_Util.t_true) tcs)
in (match (_57_3349) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let _57_3354 = (tc_trivial_guard env phi)
in (match (_57_3354) with
| (phi, _57_3353) -> begin
(

let _57_3355 = if (FStar_TypeChecker_Env.should_verify env) then begin
(let _148_1556 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _148_1556))
end else begin
()
end
in (

let _57_3357 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env0 us)
in (

let ses = (FStar_List.fold_left (fun l _57_3363 -> (match (_57_3363) with
| (lid, fml) -> begin
(

let se = (tc_assume env lid fml [] dr)
in (FStar_List.append l ((se)::[])))
end)) [] axioms)
in (let _148_1561 = (let _148_1560 = (let _148_1559 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _148_1559))
in FStar_Syntax_Syntax.Sig_bundle (_148_1560))
in (_148_1561)::ses)))))
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
in (let _148_1566 = (FStar_TypeChecker_Env.push_sigelt env se)
in ((se)::[], _148_1566))))
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

let _57_3406 = (set_options FStar_Options.Set o)
in ((se)::[], env))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(

let _57_3410 = (let _148_1573 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _148_1573 Prims.ignore))
in (

let _57_3415 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _57_3417 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
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

let _57_3439 = (let _148_1574 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _148_1574))
in (match (_57_3439) with
| (a, wp_a_src) -> begin
(

let _57_3442 = (let _148_1575 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _148_1575))
in (match (_57_3442) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _148_1579 = (let _148_1578 = (let _148_1577 = (let _148_1576 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _148_1576))
in FStar_Syntax_Syntax.NT (_148_1577))
in (_148_1578)::[])
in (FStar_Syntax_Subst.subst _148_1579 wp_b_tgt))
in (

let expected_k = (let _148_1584 = (let _148_1582 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1581 = (let _148_1580 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_148_1580)::[])
in (_148_1582)::_148_1581))
in (let _148_1583 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _148_1584 _148_1583)))
in (

let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (

let sub = (

let _57_3446 = sub
in {FStar_Syntax_Syntax.source = _57_3446.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _57_3446.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
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

let _57_3459 = ()
in (

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _57_3465 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_57_3465) with
| (tps, c) -> begin
(

let _57_3469 = (tc_tparams env tps)
in (match (_57_3469) with
| (tps, env, us) -> begin
(

let _57_3473 = (tc_comp env c)
in (match (_57_3473) with
| (c, u, g) -> begin
(

let _57_3474 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let _57_3480 = (let _148_1585 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _148_1585))
in (match (_57_3480) with
| (uvs, t) -> begin
(

let _57_3499 = (match ((let _148_1587 = (let _148_1586 = (FStar_Syntax_Subst.compress t)
in _148_1586.FStar_Syntax_Syntax.n)
in (tps, _148_1587))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_57_3483, c)) -> begin
([], c)
end
| (_57_3489, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _57_3496 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_3499) with
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

let _57_3510 = ()
in (

let _57_3514 = (let _148_1589 = (let _148_1588 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _148_1588))
in (check_and_gen env t _148_1589))
in (match (_57_3514) with
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

let _57_3534 = (tc_term env e)
in (match (_57_3534) with
| (e, c, g1) -> begin
(

let _57_3539 = (let _148_1593 = (let _148_1590 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_148_1590))
in (let _148_1592 = (let _148_1591 = (c.FStar_Syntax_Syntax.comp ())
in (e, _148_1591))
in (check_expected_effect env _148_1593 _148_1592)))
in (match (_57_3539) with
| (e, _57_3537, g) -> begin
(

let _57_3540 = (let _148_1594 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _148_1594))
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
(let _148_1606 = (let _148_1605 = (let _148_1604 = (let _148_1603 = (FStar_Syntax_Print.lid_to_string l)
in (let _148_1602 = (FStar_Syntax_Print.quals_to_string q)
in (let _148_1601 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _148_1603 _148_1602 _148_1601))))
in (_148_1604, r))
in FStar_Syntax_Syntax.Error (_148_1605))
in (Prims.raise _148_1606))
end
end))
in (

let _57_3584 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _57_3561 lb -> (match (_57_3561) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _57_3580 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (

let _57_3575 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _57_3574 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _148_1609 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _148_1609, quals_opt))))
end)
in (match (_57_3580) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_57_3584) with
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
| _57_3593 -> begin
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

let e = (let _148_1613 = (let _148_1612 = (let _148_1611 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _148_1611))
in FStar_Syntax_Syntax.Tm_let (_148_1612))
in (FStar_Syntax_Syntax.mk _148_1613 None r))
in (

let _57_3627 = (match ((tc_maybe_toplevel_term (

let _57_3597 = env
in {FStar_TypeChecker_Env.solver = _57_3597.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3597.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3597.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3597.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3597.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3597.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3597.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3597.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3597.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3597.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3597.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _57_3597.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _57_3597.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3597.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3597.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3597.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_3597.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_3597.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3597.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3597.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _57_3604; FStar_Syntax_Syntax.pos = _57_3602; FStar_Syntax_Syntax.vars = _57_3600}, _57_3611, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_57_3615, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _57_3621 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _57_3624 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_57_3627) with
| (se, lbs) -> begin
(

let _57_3633 = if (log env) then begin
(let _148_1621 = (let _148_1620 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _148_1617 = (let _148_1616 = (let _148_1615 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _148_1615.FStar_Syntax_Syntax.fv_name)
in _148_1616.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _148_1617))) with
| None -> begin
true
end
| _57_3631 -> begin
false
end)
in if should_log then begin
(let _148_1619 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _148_1618 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _148_1619 _148_1618)))
end else begin
""
end))))
in (FStar_All.pipe_right _148_1620 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _148_1621))
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
| _57_3643 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _57_3653 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_57_3655) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _57_3666, _57_3668) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _57_3674 -> (match (_57_3674) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _57_3680, _57_3682, quals, r) -> begin
(

let dec = (let _148_1637 = (let _148_1636 = (let _148_1635 = (let _148_1634 = (let _148_1633 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _148_1633))
in FStar_Syntax_Syntax.Tm_arrow (_148_1634))
in (FStar_Syntax_Syntax.mk _148_1635 None r))
in (l, us, _148_1636, (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_148_1637))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _57_3692, _57_3694, _57_3696, _57_3698, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _57_3704 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_57_3706, _57_3708, quals, _57_3711) -> begin
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
| _57_3730 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_57_3732) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _57_3751, _57_3753, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
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
(let _148_1644 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _148_1643 = (let _148_1642 = (let _148_1641 = (let _148_1640 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _148_1640.FStar_Syntax_Syntax.fv_name)
in _148_1641.FStar_Syntax_Syntax.v)
in (_148_1642, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_148_1643)))))
in (_148_1644, hidden))
end else begin
((se)::[], hidden)
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let _57_3800 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _57_3773 se -> (match (_57_3773) with
| (ses, exports, env, hidden) -> begin
(

let _57_3775 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1651 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _148_1651))
end else begin
()
end
in (

let _57_3779 = (tc_decl env se)
in (match (_57_3779) with
| (ses', env) -> begin
(

let _57_3782 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _148_1656 = (FStar_List.fold_left (fun s se -> (let _148_1655 = (let _148_1654 = (FStar_Syntax_Print.sigelt_to_string se)
in (Prims.strcat s _148_1654))
in (Prims.strcat _148_1655 "\n"))) "" ses')
in (FStar_Util.print1 "Checked: %s\n" _148_1656))
end else begin
()
end
in (

let _57_3785 = (FStar_List.iter (fun se -> (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)) ses')
in (

let _57_3794 = (FStar_List.fold_left (fun _57_3789 se -> (match (_57_3789) with
| (le, lh) -> begin
(

let tup = (for_export hidden se)
in ((FStar_List.rev_append (Prims.fst tup) le), (FStar_List.rev_append (Prims.snd tup) lh)))
end)) ([], []) ses')
in (match (_57_3794) with
| (exported, hidden) -> begin
((FStar_List.rev_append ses' ses), ((FStar_List.rev_append exported []))::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_57_3800) with
| (ses, exports, env, _57_3799) -> begin
(let _148_1660 = (FStar_All.pipe_right (FStar_List.rev_append exports []) FStar_List.flatten)
in ((FStar_List.rev_append ses []), _148_1660, env))
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

let _57_3805 = env
in (let _148_1665 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _57_3805.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3805.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3805.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3805.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3805.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3805.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3805.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3805.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3805.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3805.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3805.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3805.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3805.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_3805.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_3805.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3805.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _148_1665; FStar_TypeChecker_Env.lax = _57_3805.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_3805.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3805.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3805.FStar_TypeChecker_Env.use_bv_sorts}))
in (

let _57_3808 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let _57_3814 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_57_3814) with
| (ses, exports, env) -> begin
((

let _57_3815 = modul
in {FStar_Syntax_Syntax.name = _57_3815.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _57_3815.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3815.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let _57_3823 = (tc_decls env decls)
in (match (_57_3823) with
| (ses, exports, env) -> begin
(

let modul = (

let _57_3824 = modul
in {FStar_Syntax_Syntax.name = _57_3824.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _57_3824.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3824.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul = (

let _57_3830 = modul
in {FStar_Syntax_Syntax.name = _57_3830.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _57_3830.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in (

let _57_3840 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(

let _57_3834 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let _57_3836 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (

let _57_3838 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _148_1678 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _148_1678 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let _57_3847 = (tc_partial_modul env modul)
in (match (_57_3847) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _57_3850 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _148_1687 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _148_1687))
end else begin
()
end
in (

let env = (

let _57_3852 = env
in {FStar_TypeChecker_Env.solver = _57_3852.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3852.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3852.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3852.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3852.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3852.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3852.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3852.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3852.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3852.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3852.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3852.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3852.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_3852.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3852.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3852.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3852.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_3852.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _57_3852.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3852.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3852.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_3868 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _57_3860) -> begin
(let _148_1692 = (let _148_1691 = (let _148_1690 = (FStar_TypeChecker_Env.get_range env)
in ((Prims.strcat "Implicit argument: " msg), _148_1690))
in FStar_Syntax_Syntax.Error (_148_1691))
in (Prims.raise _148_1692))
end
in (match (_57_3868) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(t, c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(let _148_1697 = (let _148_1696 = (let _148_1695 = (let _148_1693 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _148_1693))
in (let _148_1694 = (FStar_TypeChecker_Env.get_range env)
in (_148_1695, _148_1694)))
in FStar_Syntax_Syntax.Error (_148_1696))
in (Prims.raise _148_1697))
end
end)))))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
FStar_Syntax_Syntax.U_zero
end else begin
(

let _57_3871 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_1702 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print1 "universe_of %s\n" _148_1702))
end else begin
()
end
in (

let _57_3876 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_3876) with
| (env, _57_3875) -> begin
(

let env = (

let _57_3877 = env
in {FStar_TypeChecker_Env.solver = _57_3877.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3877.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3877.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3877.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3877.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3877.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3877.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3877.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3877.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3877.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3877.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3877.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3877.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_3877.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3877.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3877.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3877.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _57_3877.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3877.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true})
in (

let fail = (fun e t -> (let _148_1712 = (let _148_1711 = (let _148_1710 = (let _148_1708 = (FStar_Syntax_Print.term_to_string e)
in (let _148_1707 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" _148_1708 _148_1707)))
in (let _148_1709 = (FStar_TypeChecker_Env.get_range env)
in (_148_1710, _148_1709)))
in FStar_Syntax_Syntax.Error (_148_1711))
in (Prims.raise _148_1712)))
in (

let ok = (fun u -> (

let _57_3885 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_1716 = (FStar_Syntax_Print.tag_of_term e)
in (let _148_1715 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.print2 "<end> universe_of %s is %s\n" _148_1716 _148_1715)))
end else begin
()
end
in u))
in (

let universe_of_type = (fun e t -> (match ((let _148_1721 = (FStar_Syntax_Util.unrefine t)
in _148_1721.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(ok u)
end
| _57_3893 -> begin
(fail e t)
end))
in (

let _57_3896 = (FStar_Syntax_Util.head_and_args e)
in (match (_57_3896) with
| (head, args) -> begin
(match ((let _148_1722 = (FStar_Syntax_Subst.compress head)
in _148_1722.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_57_3898, t) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _148_1723 = (FStar_Syntax_Subst.compress t)
in _148_1723.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_3904, t) -> begin
(universe_of_type e (FStar_Syntax_Util.comp_result t))
end
| _57_3909 -> begin
(universe_of_type e t)
end))
end
| _57_3911 -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoInline)::[]) env e)
in (

let _57_3925 = (tc_term env e)
in (match (_57_3925) with
| (_57_3914, {FStar_Syntax_Syntax.eff_name = _57_3921; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _57_3918; FStar_Syntax_Syntax.comp = _57_3916}, _57_3924) -> begin
(let _148_1725 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (FStar_All.pipe_left (universe_of_type e) _148_1725))
end)))
end)
end))))))
end)))
end)


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

let _57_3928 = if (FStar_Options.debug_any ()) then begin
(let _148_1730 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _148_1730))
end else begin
()
end
in (

let _57_3932 = (tc_modul env m)
in (match (_57_3932) with
| (m, env) -> begin
(

let _57_3933 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _148_1731 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _148_1731))
end else begin
()
end
in (m, env))
end))))




