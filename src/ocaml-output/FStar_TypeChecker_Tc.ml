
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


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (not ((let _147_5 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _147_5))))))


let rng : FStar_TypeChecker_Env.env  ->  FStar_Range.range = (fun env -> (FStar_TypeChecker_Env.get_range env))


let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _57_17 = env
in {FStar_TypeChecker_Env.solver = _57_17.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_17.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_17.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_17.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_17.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_17.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_17.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_17.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_17.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _57_17.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_17.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_17.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_17.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_17.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_17.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_17.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_17.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_17.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_17.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_17.FStar_TypeChecker_Env.use_bv_sorts}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _57_20 = env
in {FStar_TypeChecker_Env.solver = _57_20.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_20.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_20.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_20.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_20.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_20.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_20.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_20.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_20.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _57_20.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_20.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_20.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_20.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_20.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_20.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_20.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_20.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_20.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_20.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_20.FStar_TypeChecker_Env.use_bv_sorts}))


let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (

let r = if (tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
v.FStar_Syntax_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos tl.FStar_Syntax_Syntax.pos)
end
in (let _147_19 = (let _147_18 = (FStar_Syntax_Syntax.as_arg v)
in (let _147_17 = (let _147_16 = (FStar_Syntax_Syntax.as_arg tl)
in (_147_16)::[])
in (_147_18)::_147_17))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _147_19 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _57_1 -> (match (_57_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _57_30 -> begin
false
end))


let steps : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Normalize.step Prims.list = (fun env -> if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::[]
end else begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]
end)


let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Beta)::[]) env t))


let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _147_32 = (steps env)
in (FStar_TypeChecker_Normalize.normalize _147_32 env t)))


let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _147_37 = (steps env)
in (FStar_TypeChecker_Normalize.normalize_comp _147_37 env c)))


let check_no_escape : FStar_Syntax_Syntax.term Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun head_opt env fvs kt -> (

let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
()
end
| _57_47 -> begin
(

let fvs' = (let _147_50 = if try_norm then begin
(norm env t)
end else begin
t
end
in (FStar_Syntax_Free.names _147_50))
in (match ((FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)) with
| None -> begin
()
end
| Some (x) -> begin
if (not (try_norm)) then begin
(aux true t)
end else begin
(

let fail = (fun _57_54 -> (match (()) with
| () -> begin
(

let msg = (match (head_opt) with
| None -> begin
(let _147_54 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _147_54))
end
| Some (head) -> begin
(let _147_56 = (FStar_Syntax_Print.bv_to_string x)
in (let _147_55 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _147_56 _147_55)))
end)
in (let _147_59 = (let _147_58 = (let _147_57 = (FStar_TypeChecker_Env.get_range env)
in (msg, _147_57))
in FStar_Syntax_Syntax.Error (_147_58))
in (Prims.raise _147_59)))
end))
in (

let s = (let _147_61 = (let _147_60 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _147_60))
in (FStar_TypeChecker_Util.new_uvar env _147_61))
in (match ((FStar_TypeChecker_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g)
end
| _57_63 -> begin
(fail ())
end)))
end
end))
end))
in (aux false kt)))


let maybe_push_binding : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder  ->  FStar_TypeChecker_Env.env = (fun env b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
env
end else begin
(

let _57_66 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_67 = (FStar_Syntax_Print.bv_to_string (Prims.fst b))
in (let _147_66 = (FStar_Syntax_Print.term_to_string (Prims.fst b).FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _147_67 _147_66)))
end else begin
()
end
in (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))
end)


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
(let _147_80 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _147_80 t))
end))}))


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _147_89 = if (not ((FStar_Syntax_Util.is_pure_or_ghost_function t))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _147_89))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _57_115 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, guard)
end
| Some (t') -> begin
(

let _57_97 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_91 = (FStar_Syntax_Print.term_to_string t)
in (let _147_90 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _147_91 _147_90)))
end else begin
()
end
in (

let _57_101 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_57_101) with
| (e, lc) -> begin
(

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _57_105 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_57_105) with
| (e, g) -> begin
(

let _57_106 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_93 = (FStar_Syntax_Print.term_to_string t)
in (let _147_92 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _147_93 _147_92)))
end else begin
()
end
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let _57_111 = (let _147_99 = (FStar_All.pipe_left (fun _147_98 -> Some (_147_98)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _147_99 env e lc g))
in (match (_57_111) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))))
end)))
end)))
end)
in (match (_57_115) with
| (e, lc, g) -> begin
(

let _57_116 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_100 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _147_100))
end else begin
()
end
in (e, lc, g))
end)))))


let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (t) -> begin
(

let _57_126 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_57_126) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _57_131 -> (match (_57_131) with
| (e, c) -> begin
(

let expected_c_opt = (match (copt) with
| Some (_57_133) -> begin
copt
end
| None -> begin
if ((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Syntax_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) then begin
(let _147_113 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (_147_113))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
if (FStar_Syntax_Util.is_pure_comp c) then begin
(let _147_114 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (_147_114))
end else begin
if (FStar_Syntax_Util.is_pure_or_ghost_comp c) then begin
(let _147_115 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (_147_115))
end else begin
None
end
end
end
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _147_116 = (norm_c env c)
in (e, _147_116, FStar_TypeChecker_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(

let _57_140 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_119 = (FStar_Syntax_Print.term_to_string e)
in (let _147_118 = (FStar_Syntax_Print.comp_to_string c)
in (let _147_117 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _147_119 _147_118 _147_117))))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _57_143 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_122 = (FStar_Syntax_Print.term_to_string e)
in (let _147_121 = (FStar_Syntax_Print.comp_to_string c)
in (let _147_120 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _147_122 _147_121 _147_120))))
end else begin
()
end
in (

let _57_149 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_57_149) with
| (e, _57_147, g) -> begin
(

let g = (let _147_123 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _147_123 "could not prove post-condition" g))
in (

let _57_151 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_125 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _147_124 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _147_125 _147_124)))
end else begin
()
end
in (e, expected_c, g)))
end)))))
end))
end))


let no_logical_guard = (fun env _57_157 -> (match (_57_157) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
(te, kt, f)
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _147_131 = (let _147_130 = (let _147_129 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _147_128 = (FStar_TypeChecker_Env.get_range env)
in (_147_129, _147_128)))
in FStar_Syntax_Syntax.Error (_147_130))
in (Prims.raise _147_131))
end)
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _147_134 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _147_134))
end))


let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _57_181; FStar_Syntax_Syntax.result_typ = _57_179; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, _57_173))::[]; FStar_Syntax_Syntax.flags = _57_170}) -> begin
(

let pat_vars = (FStar_Syntax_Free.names pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _57_188 -> (match (_57_188) with
| (b, _57_187) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _57_192) -> begin
(let _147_141 = (let _147_140 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _147_140))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _147_141))
end))
end
| _57_196 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end)


let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun env actuals expected_c -> (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let env = (

let _57_203 = env
in {FStar_TypeChecker_Env.solver = _57_203.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_203.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_203.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_203.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_203.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_203.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_203.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_203.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_203.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_203.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_203.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_203.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_203.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_203.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_203.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_203.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_203.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_203.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_203.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_203.FStar_TypeChecker_Env.use_bv_sorts})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _57_215 -> (match (_57_215) with
| (b, _57_214) -> begin
(

let t = (let _147_155 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _147_155))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _57_224 -> begin
(let _147_156 = (FStar_Syntax_Syntax.bv_to_name b)
in (_147_156)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let _57_230 = (FStar_Syntax_Util.head_and_args dec)
in (match (_57_230) with
| (head, _57_229) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _57_234 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _57_3 -> (match (_57_3) with
| FStar_Syntax_Syntax.DECREASES (_57_238) -> begin
true
end
| _57_241 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _57_246 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| _57_251 -> begin
(mk_lex_list xs)
end))
end)))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun _57_256 -> (match (_57_256) with
| (l, t) -> begin
(match ((let _147_162 = (FStar_Syntax_Subst.compress t)
in _147_162.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _57_263 -> (match (_57_263) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _147_166 = (let _147_165 = (let _147_164 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_147_164))
in (FStar_Syntax_Syntax.new_bv _147_165 x.FStar_Syntax_Syntax.sort))
in (_147_166, imp))
end else begin
(x, imp)
end
end))))
in (

let _57_267 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_57_267) with
| (formals, c) -> begin
(

let dec = (decreases_clause formals c)
in (

let precedes = (let _147_170 = (let _147_169 = (FStar_Syntax_Syntax.as_arg dec)
in (let _147_168 = (let _147_167 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_147_167)::[])
in (_147_169)::_147_168))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _147_170 None r))
in (

let _57_274 = (FStar_Util.prefix formals)
in (match (_57_274) with
| (bs, (last, imp)) -> begin
(

let last = (

let _57_275 = last
in (let _147_171 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _57_275.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_275.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_171}))
in (

let refined_formals = (FStar_List.append bs (((last, imp))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (

let _57_280 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_174 = (FStar_Syntax_Print.lbname_to_string l)
in (let _147_173 = (FStar_Syntax_Print.term_to_string t)
in (let _147_172 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _147_174 _147_173 _147_172))))
end else begin
()
end
in (l, t')))))
end))))
end)))
end
| _57_283 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end))


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let _57_286 = env
in {FStar_TypeChecker_Env.solver = _57_286.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_286.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_286.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_286.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_286.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_286.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_286.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_286.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_286.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_286.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_286.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_286.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_286.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_286.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_286.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_286.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_286.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_286.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_286.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_286.FStar_TypeChecker_Env.use_bv_sorts}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (

let _57_291 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_242 = (let _147_240 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _147_240))
in (let _147_241 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _147_242 _147_241)))
end else begin
()
end
in (

let top = e
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_57_295) -> begin
(let _147_246 = (FStar_Syntax_Subst.compress e)
in (tc_term env _147_246))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let _57_336 = (tc_tot_or_gtot_term env e)
in (match (_57_336) with
| (e, c, g) -> begin
(

let g = (

let _57_337 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_337.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_337.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_337.FStar_TypeChecker_Env.implicits})
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let _57_347 = (FStar_Syntax_Util.type_u ())
in (match (_57_347) with
| (t, u) -> begin
(

let _57_351 = (tc_check_tot_or_gtot_term env e t)
in (match (_57_351) with
| (e, c, g) -> begin
(

let _57_358 = (

let _57_355 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_355) with
| (env, _57_354) -> begin
(tc_pats env pats)
end))
in (match (_57_358) with
| (pats, g') -> begin
(

let g' = (

let _57_359 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_359.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_359.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_359.FStar_TypeChecker_Env.implicits})
in (let _147_248 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_pattern (pats)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _147_247 = (FStar_TypeChecker_Rel.conj_guard g g')
in (_147_248, c, _147_247))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _147_249 = (FStar_Syntax_Subst.compress e)
in _147_249.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_57_368, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _57_375; FStar_Syntax_Syntax.lbtyp = _57_373; FStar_Syntax_Syntax.lbeff = _57_371; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _57_386 = (let _147_250 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _147_250 e1))
in (match (_57_386) with
| (e1, c1, g1) -> begin
(

let _57_390 = (tc_term env e2)
in (match (_57_390) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (None, c2))
in (

let e = (let _147_255 = (let _147_254 = (let _147_253 = (let _147_252 = (let _147_251 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Common.t_unit, e1))
in (_147_251)::[])
in (false, _147_252))
in (_147_253, e2))
in FStar_Syntax_Syntax.Tm_let (_147_254))
in (FStar_Syntax_Syntax.mk _147_255 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _147_256 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _147_256)))))
end))
end))
end
| _57_395 -> begin
(

let _57_399 = (tc_term env e)
in (match (_57_399) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let _57_408 = (tc_term env e)
in (match (_57_408) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, m))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _57_414) -> begin
(

let _57_421 = (tc_comp env expected_c)
in (match (_57_421) with
| (expected_c, _57_419, g) -> begin
(

let _57_425 = (tc_term env e)
in (match (_57_425) with
| (e, c', g') -> begin
(

let _57_429 = (let _147_258 = (let _147_257 = (c'.FStar_Syntax_Syntax.comp ())
in (e, _147_257))
in (check_expected_effect env (Some (expected_c)) _147_258))
in (match (_57_429) with
| (e, expected_c, g'') -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (let _147_261 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t_res), Some ((FStar_Syntax_Util.comp_effect_name expected_c))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _147_260 = (let _147_259 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _147_259))
in (_147_261, (FStar_Syntax_Util.lcomp_of_comp expected_c), _147_260))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _57_435) -> begin
(

let _57_440 = (FStar_Syntax_Util.type_u ())
in (match (_57_440) with
| (k, u) -> begin
(

let _57_445 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_445) with
| (t, _57_443, f) -> begin
(

let _57_449 = (let _147_262 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _147_262 e))
in (match (_57_449) with
| (e, c, g) -> begin
(

let _57_453 = (let _147_266 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_450 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _147_266 e c f))
in (match (_57_453) with
| (c, f) -> begin
(

let _57_457 = (let _147_267 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t), Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _147_267 c))
in (match (_57_457) with
| (e, c, f2) -> begin
(let _147_269 = (let _147_268 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _147_268))
in (e, c, _147_269))
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

let env = (let _147_271 = (let _147_270 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _147_270 Prims.fst))
in (FStar_All.pipe_right _147_271 instantiate_both))
in (

let _57_464 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_273 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _147_272 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _147_273 _147_272)))
end else begin
()
end
in (

let _57_469 = (tc_term (no_inst env) head)
in (match (_57_469) with
| (head, chead, g_head) -> begin
(

let _57_473 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _147_274 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _147_274))
end else begin
(let _147_275 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _147_275))
end
in (match (_57_473) with
| (e, c, g) -> begin
(

let _57_474 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _147_276 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _147_276))
end else begin
()
end
in (

let c = if (((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) && (not ((FStar_Syntax_Util.is_lcomp_partial_return c)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)) then begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e c)
end else begin
c
end
in (

let _57_480 = (comp_check_expected_typ env0 e c)
in (match (_57_480) with
| (e, c, g') -> begin
(

let gimp = (match ((let _147_277 = (FStar_Syntax_Subst.compress head)
in _147_277.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _57_483) -> begin
(

let imp = ("head of application is a uvar", env0, u, e, c.FStar_Syntax_Syntax.res_typ, head.FStar_Syntax_Syntax.pos)
in (

let _57_487 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_487.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_487.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_487.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _57_490 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (

let gres = (let _147_278 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _147_278))
in (

let _57_493 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _147_279 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print1 "Guard from application node is %s\n" _147_279))
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

let _57_501 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_501) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let _57_506 = (tc_term env1 e1)
in (match (_57_506) with
| (e1, c1, g1) -> begin
(

let _57_517 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(

let _57_513 = (FStar_Syntax_Util.type_u ())
in (match (_57_513) with
| (k, _57_512) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _147_280 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_147_280, res_t)))
end))
end)
in (match (_57_517) with
| (env_branches, res_t) -> begin
(

let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let _57_534 = (

let _57_531 = (FStar_List.fold_right (fun _57_525 _57_528 -> (match ((_57_525, _57_528)) with
| ((_57_521, f, c, g), (caccum, gaccum)) -> begin
(let _147_283 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _147_283))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_531) with
| (cases, g) -> begin
(let _147_284 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_147_284, g))
end))
in (match (_57_534) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (Some (guard_x), c_branches))
in (

let e = (let _147_288 = (let _147_287 = (let _147_286 = (FStar_List.map (fun _57_543 -> (match (_57_543) with
| (f, _57_538, _57_540, _57_542) -> begin
f
end)) t_eqns)
in (e1, _147_286))
in FStar_Syntax_Syntax.Tm_match (_147_287))
in (FStar_Syntax_Syntax.mk _147_288 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ), Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (

let _57_546 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _147_291 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _147_290 = (let _147_289 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _147_289))
in (FStar_Util.print2 "(%s) comp type = %s\n" _147_291 _147_290)))
end else begin
()
end
in (let _147_292 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _147_292))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_558); FStar_Syntax_Syntax.lbunivs = _57_556; FStar_Syntax_Syntax.lbtyp = _57_554; FStar_Syntax_Syntax.lbeff = _57_552; FStar_Syntax_Syntax.lbdef = _57_550})::[]), _57_564) -> begin
(

let _57_567 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_293 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _147_293))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _57_571), _57_574) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_589); FStar_Syntax_Syntax.lbunivs = _57_587; FStar_Syntax_Syntax.lbtyp = _57_585; FStar_Syntax_Syntax.lbeff = _57_583; FStar_Syntax_Syntax.lbdef = _57_581})::_57_579), _57_595) -> begin
(

let _57_598 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_294 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _147_294))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _57_602), _57_605) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let _57_619 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_619) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _147_308 = (let _147_307 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _147_307))
in FStar_Util.Inr (_147_308))
end
in (

let is_data_ctor = (fun _57_4 -> (match (_57_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _57_629 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _147_314 = (let _147_313 = (let _147_312 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _147_311 = (FStar_TypeChecker_Env.get_range env)
in (_147_312, _147_311)))
in FStar_Syntax_Syntax.Error (_147_313))
in (Prims.raise _147_314))
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

let g = (match ((let _147_315 = (FStar_Syntax_Subst.compress t1)
in _147_315.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_640) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _57_643 -> begin
(

let imp = ("uvar in term", env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (

let _57_645 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_645.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_645.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_645.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _57_651 = (FStar_Syntax_Util.type_u ())
in (match (_57_651) with
| (k, u) -> begin
(

let t = (FStar_TypeChecker_Util.new_uvar env k)
in (

let e = (FStar_TypeChecker_Util.new_uvar env t)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end))
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

let _57_657 = x
in {FStar_Syntax_Syntax.ppname = _57_657.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_657.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let _57_663 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_663) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _147_317 = (let _147_316 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _147_316))
in FStar_Util.Inr (_147_317))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _57_670; FStar_Syntax_Syntax.pos = _57_668; FStar_Syntax_Syntax.vars = _57_666}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let _57_680 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_680) with
| (us', t) -> begin
(

let _57_687 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _147_320 = (let _147_319 = (let _147_318 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _147_318))
in FStar_Syntax_Syntax.Error (_147_319))
in (Prims.raise _147_320))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _57_686 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (

let fv' = (

let _57_689 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _57_691 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_691.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_691.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_689.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_689.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _147_323 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _147_323 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let _57_699 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_699) with
| (us, t) -> begin
(

let fv' = (

let _57_700 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _57_702 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_702.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_702.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_700.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_700.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _147_324 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _147_324 us))
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

let _57_716 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_716) with
| (bs, c) -> begin
(

let env0 = env
in (

let _57_721 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_721) with
| (env, _57_720) -> begin
(

let _57_726 = (tc_binders env bs)
in (match (_57_726) with
| (bs, env, g, us) -> begin
(

let _57_730 = (tc_comp env c)
in (match (_57_730) with
| (c, uc, f) -> begin
(

let e = (

let _57_731 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _57_731.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_731.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_731.FStar_Syntax_Syntax.vars})
in (

let _57_734 = (check_smt_pat env e bs c)
in (

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _147_325 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _147_325))
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

let _57_750 = (let _147_327 = (let _147_326 = (FStar_Syntax_Syntax.mk_binder x)
in (_147_326)::[])
in (FStar_Syntax_Subst.open_term _147_327 phi))
in (match (_57_750) with
| (x, phi) -> begin
(

let env0 = env
in (

let _57_755 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_755) with
| (env, _57_754) -> begin
(

let _57_760 = (let _147_328 = (FStar_List.hd x)
in (tc_binder env _147_328))
in (match (_57_760) with
| (x, env, f1, u) -> begin
(

let _57_761 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_331 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _147_330 = (FStar_Syntax_Print.term_to_string phi)
in (let _147_329 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _147_331 _147_330 _147_329))))
end else begin
()
end
in (

let _57_766 = (FStar_Syntax_Util.type_u ())
in (match (_57_766) with
| (t_phi, _57_765) -> begin
(

let _57_771 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_57_771) with
| (phi, _57_769, f2) -> begin
(

let e = (

let _57_772 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _57_772.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_772.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_772.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _147_332 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _147_332))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _57_780) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (

let _57_786 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_333 = (FStar_Syntax_Print.term_to_string (

let _57_784 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _57_784.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_784.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_784.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _147_333))
end else begin
()
end
in (

let _57_790 = (FStar_Syntax_Subst.open_term bs body)
in (match (_57_790) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _57_792 -> begin
(let _147_335 = (let _147_334 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _147_334))
in (FStar_All.failwith _147_335))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_57_797) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_57_800, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_57_805, Some (FStar_Const.Unsigned, FStar_Const.Int8)) -> begin
FStar_TypeChecker_Common.t_uint8
end
| FStar_Const.Const_int (_57_813, Some (FStar_Const.Signed, FStar_Const.Int8)) -> begin
FStar_TypeChecker_Common.t_int8
end
| FStar_Const.Const_int (_57_821, Some (FStar_Const.Unsigned, FStar_Const.Int16)) -> begin
FStar_TypeChecker_Common.t_uint16
end
| FStar_Const.Const_int (_57_829, Some (FStar_Const.Signed, FStar_Const.Int16)) -> begin
FStar_TypeChecker_Common.t_int16
end
| FStar_Const.Const_int (_57_837, Some (FStar_Const.Unsigned, FStar_Const.Int32)) -> begin
FStar_TypeChecker_Common.t_uint32
end
| FStar_Const.Const_int (_57_845, Some (FStar_Const.Signed, FStar_Const.Int32)) -> begin
FStar_TypeChecker_Common.t_int32
end
| FStar_Const.Const_int (_57_853, Some (FStar_Const.Unsigned, FStar_Const.Int64)) -> begin
FStar_TypeChecker_Common.t_uint64
end
| FStar_Const.Const_int (_57_861, Some (FStar_Const.Signed, FStar_Const.Int64)) -> begin
FStar_TypeChecker_Common.t_int64
end
| FStar_Const.Const_string (_57_869) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_57_872) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_57_875) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_57_879) -> begin
FStar_TypeChecker_Common.t_range
end
| _57_882 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(

let _57_889 = (FStar_Syntax_Util.type_u ())
in (match (_57_889) with
| (k, u) -> begin
(

let _57_894 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_894) with
| (t, _57_892, g) -> begin
(let _147_340 = (FStar_Syntax_Syntax.mk_Total t)
in (_147_340, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(

let _57_899 = (FStar_Syntax_Util.type_u ())
in (match (_57_899) with
| (k, u) -> begin
(

let _57_904 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_904) with
| (t, _57_902, g) -> begin
(let _147_341 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_147_341, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (

let tc = (let _147_343 = (let _147_342 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_147_342)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _147_343 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let _57_913 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_57_913) with
| (tc, _57_911, f) -> begin
(

let _57_917 = (FStar_Syntax_Util.head_and_args tc)
in (match (_57_917) with
| (_57_915, args) -> begin
(

let _57_920 = (let _147_345 = (FStar_List.hd args)
in (let _147_344 = (FStar_List.tl args)
in (_147_345, _147_344)))
in (match (_57_920) with
| (res, args) -> begin
(

let _57_936 = (let _147_347 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _57_5 -> (match (_57_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _57_927 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_927) with
| (env, _57_926) -> begin
(

let _57_932 = (tc_tot_or_gtot_term env e)
in (match (_57_932) with
| (e, _57_930, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _147_347 FStar_List.unzip))
in (match (_57_936) with
| (flags, guards) -> begin
(

let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| _57_941 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _147_349 = (FStar_Syntax_Syntax.mk_Comp (

let _57_943 = c
in {FStar_Syntax_Syntax.effect_name = _57_943.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _57_943.FStar_Syntax_Syntax.flags}))
in (let _147_348 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_147_349, u, _147_348))))
end))
end))
end))
end))))
end))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_57_951) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _147_354 = (aux u)
in FStar_Syntax_Syntax.U_succ (_147_354))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _147_355 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_147_355))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _147_359 = (let _147_358 = (let _147_357 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _147_356 = (FStar_TypeChecker_Env.get_range env)
in (_147_357, _147_356)))
in FStar_Syntax_Syntax.Error (_147_358))
in (Prims.raise _147_359))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _147_360 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _147_360 Prims.snd))
end
| _57_966 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _147_369 = (let _147_368 = (let _147_367 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_147_367, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_147_368))
in (Prims.raise _147_369)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun _57_984 bs bs_expected -> (match (_57_984) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
(

let _57_1015 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _147_386 = (let _147_385 = (let _147_384 = (let _147_382 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _147_382))
in (let _147_383 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_147_384, _147_383)))
in FStar_Syntax_Syntax.Error (_147_385))
in (Prims.raise _147_386))
end
| _57_1014 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _57_1032 = (match ((let _147_387 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _147_387.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _57_1020 -> begin
(

let _57_1021 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_388 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _147_388))
end else begin
()
end
in (

let _57_1027 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_57_1027) with
| (t, _57_1025, g1) -> begin
(

let g2 = (let _147_390 = (FStar_TypeChecker_Env.get_range env)
in (let _147_389 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _147_390 "Type annotation on parameter incompatible with the expected type" _147_389)))
in (

let g = (let _147_391 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _147_391))
in (t, g)))
end)))
end)
in (match (_57_1032) with
| (t, g) -> begin
(

let hd = (

let _57_1033 = hd
in {FStar_Syntax_Syntax.ppname = _57_1033.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1033.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = (hd, imp)
in (

let b_expected = (hd_expected, imp')
in (

let env = (maybe_push_binding env b)
in (

let subst = (let _147_392 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _147_392))
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

let _57_1054 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1053 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (

let _57_1061 = (tc_binders env bs)
in (match (_57_1061) with
| (bs, envbody, g, _57_1060) -> begin
(

let _57_1079 = (match ((let _147_399 = (FStar_Syntax_Subst.compress body)
in _147_399.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _57_1066) -> begin
(

let _57_1073 = (tc_comp envbody c)
in (match (_57_1073) with
| (c, _57_1071, g') -> begin
(let _147_400 = (FStar_TypeChecker_Rel.conj_guard g g')
in (Some (c), body, _147_400))
end))
end
| _57_1075 -> begin
(None, body, g)
end)
in (match (_57_1079) with
| (copt, body, g) -> begin
(None, bs, [], copt, envbody, body, g)
end))
end)))
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm t -> (match ((let _147_405 = (FStar_Syntax_Subst.compress t)
in _147_405.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let _57_1106 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1105 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _57_1113 = (tc_binders env bs)
in (match (_57_1113) with
| (bs, envbody, g, _57_1112) -> begin
(

let _57_1117 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_57_1117) with
| (envbody, _57_1116) -> begin
(Some ((t, true)), bs, [], None, envbody, body, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _57_1120) -> begin
(

let _57_1131 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_57_1131) with
| (_57_1124, bs, bs', copt, env, body, g) -> begin
(Some ((t, false)), bs, bs', copt, env, body, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _57_1138 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_57_1138) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun _57_1149 c_expected -> (match (_57_1149) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _147_416 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _147_416))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (let _147_417 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _147_417))
in (let _147_418 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _147_418)))
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

let _57_1170 = (check_binders env more_bs bs_expected)
in (match (_57_1170) with
| (env, bs', more, guard', subst) -> begin
(let _147_420 = (let _147_419 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _147_419, subst))
in (handle_more _147_420 c_expected))
end))
end
| _57_1172 -> begin
(let _147_422 = (let _147_421 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _147_421))
in (fail _147_422 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _147_423 = (check_binders env bs bs_expected)
in (handle_more _147_423 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let _57_1178 = envbody
in {FStar_TypeChecker_Env.solver = _57_1178.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1178.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1178.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1178.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1178.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1178.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1178.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1178.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1178.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1178.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1178.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1178.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_1178.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1178.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1178.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1178.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1178.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1178.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1178.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1178.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _57_1183 _57_1186 -> (match ((_57_1183, _57_1186)) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _57_1192 = (let _147_433 = (let _147_432 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _147_432 Prims.fst))
in (tc_term _147_433 t))
in (match (_57_1192) with
| (t, _57_1189, _57_1191) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _147_434 = (FStar_Syntax_Syntax.mk_binder (

let _57_1196 = x
in {FStar_Syntax_Syntax.ppname = _57_1196.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1196.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_147_434)::letrec_binders)
end
| _57_1199 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (

let _57_1205 = (check_actuals_against_formals env bs bs_expected)
in (match (_57_1205) with
| (envbody, bs, g, c) -> begin
(

let _57_1208 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_57_1208) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, body, g))
end))
end))))
end))
end
| _57_1211 -> begin
if (not (norm)) then begin
(let _147_435 = (unfold_whnf env t)
in (as_function_typ true _147_435))
end else begin
(

let _57_1221 = (expected_function_typ env None body)
in (match (_57_1221) with
| (_57_1213, bs, _57_1216, c_opt, envbody, body, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, body, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let _57_1225 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1225) with
| (env, topt) -> begin
(

let _57_1229 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_436 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _147_436 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (

let _57_1238 = (expected_function_typ env topt body)
in (match (_57_1238) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let _57_1244 = (tc_term (

let _57_1239 = envbody
in {FStar_TypeChecker_Env.solver = _57_1239.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1239.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1239.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1239.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1239.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1239.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1239.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1239.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1239.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1239.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1239.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1239.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1239.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1239.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1239.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1239.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1239.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1239.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1239.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_57_1244) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _57_1246 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _147_439 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _147_438 = (let _147_437 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _147_437))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _147_439 _147_438)))
end else begin
()
end
in (

let _57_1253 = (let _147_441 = (let _147_440 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _147_440))
in (check_expected_effect (

let _57_1248 = envbody
in {FStar_TypeChecker_Env.solver = _57_1248.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1248.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1248.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1248.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1248.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1248.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1248.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1248.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1248.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1248.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1248.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1248.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1248.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1248.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1248.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1248.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1248.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1248.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1248.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1248.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _147_441))
in (match (_57_1253) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _147_442 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _147_442))
end else begin
(

let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _147_445 = (let _147_444 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _147_443 -> FStar_Util.Inl (_147_443)))
in Some (_147_444))
in (FStar_Syntax_Util.abs bs body _147_445))
in (

let _57_1276 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_1265) -> begin
(e, t, guard)
end
| _57_1268 -> begin
(

let _57_1271 = if use_teq then begin
(let _147_446 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _147_446))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_57_1271) with
| (e, guard') -> begin
(let _147_447 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _147_447))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_57_1276) with
| (e, tfun, guard) -> begin
(

let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (

let _57_1280 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_57_1280) with
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

let _57_1290 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_456 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _147_455 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _147_456 _147_455)))
end else begin
()
end
in (

let rec check_function_app = (fun norm tf -> (match ((let _147_461 = (FStar_Syntax_Util.unrefine tf)
in _147_461.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| ((e, imp))::tl -> begin
(

let _57_1324 = (tc_term env e)
in (match (_57_1324) with
| (e, c, g_e) -> begin
(

let _57_1328 = (tc_args env tl)
in (match (_57_1328) with
| (args, comps, g_rest) -> begin
(let _147_466 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, ((e.FStar_Syntax_Syntax.pos, c))::comps, _147_466))
end))
end))
end))
in (

let _57_1332 = (tc_args env args)
in (match (_57_1332) with
| (args, comps, g_args) -> begin
(

let bs = (let _147_468 = (FStar_All.pipe_right comps (FStar_List.map (fun _57_1336 -> (match (_57_1336) with
| (_57_1334, c) -> begin
(c.FStar_Syntax_Syntax.res_typ, None)
end))))
in (FStar_Syntax_Util.null_binders_of_tks _147_468))
in (

let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _57_1342 -> begin
FStar_Syntax_Util.ml_comp
end)
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _147_483 = (FStar_Syntax_Subst.compress t)
in _147_483.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_1348) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _57_1353 -> begin
ml_or_tot
end)
end)
in (

let cres = (let _147_488 = (let _147_487 = (let _147_486 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _147_486 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _147_487))
in (ml_or_tot _147_488 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (

let _57_1357 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _147_491 = (FStar_Syntax_Print.term_to_string head)
in (let _147_490 = (FStar_Syntax_Print.term_to_string tf)
in (let _147_489 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _147_491 _147_490 _147_489))))
end else begin
()
end
in (

let _57_1359 = (let _147_492 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _147_492))
in (

let comp = (let _147_495 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _57_1363 out -> (match (_57_1363) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c (None, out))
end)) (((head.FStar_Syntax_Syntax.pos, chead))::comps) _147_495))
in (let _147_497 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _147_496 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_147_497, comp, _147_496)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _57_1372 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_1372) with
| (bs, c) -> begin
(

let rec tc_args = (fun _57_1380 bs cres args -> (match (_57_1380) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (_57_1387))))::rest, ((_57_1395, None))::_57_1393) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _57_1401 = (check_no_escape (Some (head)) env fvs t)
in (

let _57_1407 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_57_1407) with
| (varg, _57_1405, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (

let arg = (let _147_506 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _147_506))
in (let _147_508 = (let _147_507 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _147_507, fvs))
in (tc_args _147_508 rest cres args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
(

let _57_1439 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _57_1438 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let _57_1442 = x
in {FStar_Syntax_Syntax.ppname = _57_1442.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1442.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (

let _57_1445 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _147_509 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _147_509))
end else begin
()
end
in (

let _57_1447 = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let _57_1450 = env
in {FStar_TypeChecker_Env.solver = _57_1450.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1450.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1450.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1450.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1450.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1450.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1450.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1450.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1450.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1450.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1450.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1450.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1450.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1450.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1450.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _57_1450.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1450.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1450.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1450.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1450.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_1453 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_512 = (FStar_Syntax_Print.tag_of_term e)
in (let _147_511 = (FStar_Syntax_Print.term_to_string e)
in (let _147_510 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _147_512 _147_511 _147_510))))
end else begin
()
end
in (

let _57_1458 = (tc_term env e)
in (match (_57_1458) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(

let subst = (let _147_513 = (FStar_List.hd bs)
in (maybe_extend_subst subst _147_513 e))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(

let subst = (let _147_514 = (FStar_List.hd bs)
in (maybe_extend_subst subst _147_514 e))
in (

let _57_1465 = (((e.FStar_Syntax_Syntax.pos, Some (x), c))::comps, g)
in (match (_57_1465) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _147_515 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _147_515)) then begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _147_516 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _147_516))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((e.FStar_Syntax_Syntax.pos, Some (newx), c))::comps, g, fvs) rest cres rest')))
end else begin
(let _147_520 = (let _147_519 = (let _147_518 = (let _147_517 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _147_517))
in (_147_518)::arg_rets)
in (subst, (arg)::outargs, _147_519, ((e.FStar_Syntax_Syntax.pos, Some (x), c))::comps, g, (x)::fvs))
in (tc_args _147_520 rest cres rest'))
end
end
end))
end))))))))))
end
| (_57_1469, []) -> begin
(

let _57_1472 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let _57_1492 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _57_1482 -> (match (_57_1482) with
| (_57_1478, _57_1480, c) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _147_522 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _147_522 cres))
end else begin
(

let _57_1484 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_525 = (FStar_Syntax_Print.term_to_string head)
in (let _147_524 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _147_523 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _147_525 _147_524 _147_523))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _57_1488 -> begin
(

let g = (let _147_526 = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (FStar_All.pipe_right _147_526 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _147_531 = (let _147_530 = (let _147_529 = (let _147_528 = (let _147_527 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _147_527))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _147_528))
in (FStar_Syntax_Syntax.mk_Total _147_529))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _147_530))
in (_147_531, g)))
end)
in (match (_57_1492) with
| (cres, g) -> begin
(

let _57_1493 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_532 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _147_532))
end else begin
()
end
in (

let comp = (FStar_List.fold_left (fun out _57_1499 -> (match (_57_1499) with
| (r1, x, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c (x, out))
end)) cres comps)
in (

let comp = (FStar_TypeChecker_Util.bind head.FStar_Syntax_Syntax.pos env None chead (None, comp))
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev outargs) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let _57_1505 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp g)
in (match (_57_1505) with
| (comp, g) -> begin
(app, comp, g)
end))))))
end)))
end
| ([], (arg)::_57_1508) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _147_540 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _147_540 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let _57_1522 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (_57_1522) with
| (bs, cres') -> begin
(

let _57_1523 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_541 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _147_541))
end else begin
()
end
in (let _147_545 = (let _147_544 = (let _147_543 = (let _147_542 = (FStar_TypeChecker_Env.get_range env)
in (_147_542, None, cres))
in (_147_543)::comps)
in (subst, outargs, arg_rets, _147_544, g, fvs))
in (tc_args _147_545 bs (FStar_Syntax_Util.lcomp_of_comp cres') args)))
end))
end
| _57_1526 when (not (norm)) -> begin
(let _147_546 = (unfold_whnf env tres)
in (aux true _147_546))
end
| _57_1528 -> begin
(let _147_552 = (let _147_551 = (let _147_550 = (let _147_548 = (FStar_TypeChecker_Normalize.term_to_string env tf)
in (let _147_547 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _147_548 _147_547)))
in (let _147_549 = (FStar_Syntax_Syntax.argpos arg)
in (_147_550, _147_549)))
in FStar_Syntax_Syntax.Error (_147_551))
in (Prims.raise _147_552))
end)))
in (aux false cres.FStar_Syntax_Syntax.res_typ))
end)
end))
in (tc_args ([], [], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs (FStar_Syntax_Util.lcomp_of_comp c) args))
end))
end
| _57_1530 -> begin
if (not (norm)) then begin
(let _147_553 = (unfold_whnf env tf)
in (check_function_app true _147_553))
end else begin
(let _147_556 = (let _147_555 = (let _147_554 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_147_554, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_147_555))
in (Prims.raise _147_556))
end
end))
in (let _147_558 = (let _147_557 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _147_557))
in (check_function_app false _147_558))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let _57_1566 = (FStar_List.fold_left2 (fun _57_1547 _57_1550 _57_1553 -> (match ((_57_1547, _57_1550, _57_1553)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(

let _57_1554 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let _57_1559 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_57_1559) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (let _147_568 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _147_568 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _147_572 = (let _147_570 = (let _147_569 = (FStar_Syntax_Syntax.as_arg e)
in (_147_569)::[])
in (FStar_List.append seen _147_570))
in (let _147_571 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_147_572, _147_571, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_57_1566) with
| (args, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = if ghost then begin
(let _147_573 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _147_573 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (

let _57_1571 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_57_1571) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _57_1573 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let _57_1580 = (FStar_Syntax_Subst.open_branch branch)
in (match (_57_1580) with
| (pattern, when_clause, branch_exp) -> begin
(

let _57_1585 = branch
in (match (_57_1585) with
| (cpat, _57_1583, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _57_1593 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_57_1593) with
| (pat_bvs, exps, p) -> begin
(

let _57_1594 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_585 = (FStar_Syntax_Print.pat_to_string p0)
in (let _147_584 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _147_585 _147_584)))
end else begin
()
end
in (

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let _57_1600 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_57_1600) with
| (env1, _57_1599) -> begin
(

let env1 = (

let _57_1601 = env1
in {FStar_TypeChecker_Env.solver = _57_1601.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1601.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1601.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1601.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1601.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1601.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1601.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1601.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _57_1601.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1601.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1601.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1601.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1601.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1601.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1601.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1601.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1601.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1601.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1601.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1601.FStar_TypeChecker_Env.use_bv_sorts})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _57_1640 = (let _147_608 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _57_1606 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_588 = (FStar_Syntax_Print.term_to_string e)
in (let _147_587 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _147_588 _147_587)))
end else begin
()
end
in (

let _57_1611 = (tc_term env1 e)
in (match (_57_1611) with
| (e, lc, g) -> begin
(

let _57_1612 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_590 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _147_589 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _147_590 _147_589)))
end else begin
()
end
in (

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let _57_1618 = (let _147_591 = (FStar_TypeChecker_Rel.discharge_guard env (

let _57_1616 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_1616.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_1616.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_1616.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _147_591 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _147_596 = (let _147_595 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _147_595 (FStar_List.map (fun _57_1626 -> (match (_57_1626) with
| (u, _57_1625) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _147_596 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _57_1634 = if (let _147_597 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _147_597)) then begin
(

let unresolved = (let _147_598 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _147_598 FStar_Util.set_elements))
in (let _147_606 = (let _147_605 = (let _147_604 = (let _147_603 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _147_602 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _147_601 = (let _147_600 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _57_1633 -> (match (_57_1633) with
| (u, _57_1632) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _147_600 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _147_603 _147_602 _147_601))))
in (_147_604, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_147_605))
in (Prims.raise _147_606)))
end else begin
()
end
in (

let _57_1636 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_607 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _147_607))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _147_608 FStar_List.unzip))
in (match (_57_1640) with
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

let _57_1647 = (let _147_609 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _147_609 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_57_1647) with
| (scrutinee_env, _57_1646) -> begin
(

let _57_1653 = (tc_pat true pat_t pattern)
in (match (_57_1653) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let _57_1663 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(

let _57_1660 = (let _147_610 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _147_610 e))
in (match (_57_1660) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_57_1663) with
| (when_clause, g_when) -> begin
(

let _57_1667 = (tc_term pat_env branch_exp)
in (match (_57_1667) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _147_612 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _147_611 -> Some (_147_611)) _147_612))
end)
in (

let _57_1723 = (

let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _57_1685 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _147_616 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _147_615 -> Some (_147_615)) _147_616))
end))
end))) None))
in (

let _57_1693 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_57_1693) with
| (c, g_branch) -> begin
(

let _57_1718 = (match ((eqs, when_condition)) with
| (None, None) -> begin
(c, g_when)
end
| (Some (f), None) -> begin
(

let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _147_619 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _147_618 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_147_619, _147_618)))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (let _147_620 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_147_620))
in (let _147_623 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _147_622 = (let _147_621 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _147_621 g_when))
in (_147_623, _147_622)))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _147_624 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_147_624, g_when))))
end)
in (match (_57_1718) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _147_626 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _147_625 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_147_626, _147_625, g_branch))))
end))
end)))
in (match (_57_1723) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = (

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> if ((let _147_636 = (let _147_635 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _147_635))
in (FStar_List.length _147_636)) > 1) then begin
(

let disc = (let _147_637 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _147_637 FStar_Syntax_Syntax.Delta_equational None))
in (

let disc = (let _147_639 = (let _147_638 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_147_638)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _147_639 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _147_640 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_147_640)::[])))
end else begin
[]
end)
in (

let fail = (fun _57_1733 -> (match (()) with
| () -> begin
(let _147_646 = (let _147_645 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _147_644 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _147_643 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _147_645 _147_644 _147_643))))
in (FStar_All.failwith _147_646))
end))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _57_1740) -> begin
(head_constructor t)
end
| _57_1744 -> begin
(fail ())
end))
in (

let pat_exp = (let _147_649 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _147_649 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_57_1769) -> begin
(let _147_654 = (let _147_653 = (let _147_652 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _147_651 = (let _147_650 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_147_650)::[])
in (_147_652)::_147_651))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _147_653 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_147_654)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _147_655 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _147_655))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(

let sub_term_guards = (let _147_662 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _57_1787 -> (match (_57_1787) with
| (ei, _57_1786) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _57_1791 -> begin
(

let sub_term = (let _147_661 = (let _147_658 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _147_658 FStar_Syntax_Syntax.Delta_equational None))
in (let _147_660 = (let _147_659 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_147_659)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _147_661 _147_660 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _147_662 FStar_List.flatten))
in (let _147_663 = (discriminate scrutinee_tm f)
in (FStar_List.append _147_663 sub_term_guards)))
end)
end
| _57_1795 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(

let t = (let _147_668 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _147_668))
in (

let _57_1803 = (FStar_Syntax_Util.type_u ())
in (match (_57_1803) with
| (k, _57_1802) -> begin
(

let _57_1809 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_57_1809) with
| (t, _57_1806, _57_1808) -> begin
t
end))
end)))
end)
in (

let branch_guard = (let _147_669 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _147_669 FStar_Syntax_Util.mk_disj_l))
in (

let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (

let _57_1817 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_670 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _147_670))
end else begin
()
end
in (let _147_671 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_147_671, branch_guard, c, guard)))))
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

let _57_1834 = (check_let_bound_def true env lb)
in (match (_57_1834) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let _57_1846 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(

let g1 = (let _147_674 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _147_674 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _57_1841 = (let _147_678 = (let _147_677 = (let _147_676 = (let _147_675 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _147_675))
in (_147_676)::[])
in (FStar_TypeChecker_Util.generalize env _147_677))
in (FStar_List.hd _147_678))
in (match (_57_1841) with
| (_57_1837, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_57_1846) with
| (g1, e1, univ_vars, c1) -> begin
(

let _57_1856 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(

let _57_1849 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_57_1849) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(

let _57_1850 = if (FStar_Options.warn_top_level_effects ()) then begin
(let _147_679 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _147_679 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _147_680 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_147_680, c1)))
end
end))
end else begin
(

let _57_1852 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _147_681 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _147_681)))
end
in (match (_57_1856) with
| (e2, c1) -> begin
(

let cres = (let _147_682 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _147_682))
in (

let _57_1858 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _147_683 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_147_683, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _57_1862 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let _57_1873 = env
in {FStar_TypeChecker_Env.solver = _57_1873.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1873.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1873.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1873.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1873.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1873.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1873.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1873.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1873.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1873.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1873.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1873.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1873.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1873.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1873.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1873.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1873.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1873.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1873.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1873.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_1882 = (let _147_687 = (let _147_686 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _147_686 Prims.fst))
in (check_let_bound_def false _147_687 lb))
in (match (_57_1882) with
| (e1, _57_1878, c1, g1, annotated) -> begin
(

let x = (

let _57_1883 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1883.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1883.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let _57_1889 = (let _147_689 = (let _147_688 = (FStar_Syntax_Syntax.mk_binder x)
in (_147_688)::[])
in (FStar_Syntax_Subst.open_term _147_689 e2))
in (match (_57_1889) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _57_1895 = (let _147_690 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _147_690 e2))
in (match (_57_1895) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (Some (x), c2))
in (

let e = (let _147_693 = (let _147_692 = (let _147_691 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _147_691))
in FStar_Syntax_Syntax.Tm_let (_147_692))
in (FStar_Syntax_Syntax.mk _147_693 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let x_eq_e1 = (let _147_696 = (let _147_695 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _147_695 e1))
in (FStar_All.pipe_left (fun _147_694 -> FStar_TypeChecker_Common.NonTrivial (_147_694)) _147_696))
in (

let g2 = (let _147_698 = (let _147_697 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _147_697 g2))
in (FStar_TypeChecker_Rel.close_guard xb _147_698))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if (let _147_699 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome _147_699)) then begin
(e, cres, guard)
end else begin
(

let _57_1901 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end)))))
end))))
end))))
end)))
end
| _57_1904 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _57_1916 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1916) with
| (lbs, e2) -> begin
(

let _57_1919 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1919) with
| (env0, topt) -> begin
(

let _57_1922 = (build_let_rec_env true env0 lbs)
in (match (_57_1922) with
| (lbs, rec_env) -> begin
(

let _57_1925 = (check_let_recs rec_env lbs)
in (match (_57_1925) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (let _147_702 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _147_702 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _147_705 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _147_705 (fun _147_704 -> Some (_147_704))))
in (

let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(

let ecs = (let _147_709 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _147_708 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _147_708)))))
in (FStar_TypeChecker_Util.generalize env _147_709))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _57_1936 -> (match (_57_1936) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _147_711 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _147_711))
in (

let _57_1939 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _57_1943 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1943) with
| (lbs, e2) -> begin
(let _147_713 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _147_712 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_147_713, cres, _147_712)))
end)))))))
end))
end))
end))
end))
end
| _57_1945 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _57_1957 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1957) with
| (lbs, e2) -> begin
(

let _57_1960 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1960) with
| (env0, topt) -> begin
(

let _57_1963 = (build_let_rec_env false env0 lbs)
in (match (_57_1963) with
| (lbs, rec_env) -> begin
(

let _57_1966 = (check_let_recs rec_env lbs)
in (match (_57_1966) with
| (lbs, g_lbs) -> begin
(

let _57_1978 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let _57_1969 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1969.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1969.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let _57_1972 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _57_1972.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1972.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1972.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _57_1972.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], lb.FStar_Syntax_Syntax.lbtyp))
in (env, lb))))) env))
in (match (_57_1978) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let _57_1984 = (tc_term env e2)
in (match (_57_1984) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _57_1988 = cres
in {FStar_Syntax_Syntax.eff_name = _57_1988.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _57_1988.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_1988.FStar_Syntax_Syntax.comp})
in (

let _57_1993 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1993) with
| (lbs, e2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_57_1996) -> begin
(e, cres, guard)
end
| None -> begin
(

let _57_1999 = (check_no_escape None env bvs tres)
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
| _57_2002 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let _57_2035 = (FStar_List.fold_left (fun _57_2009 lb -> (match (_57_2009) with
| (lbs, env) -> begin
(

let _57_2014 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_57_2014) with
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

let _57_2023 = (let _147_725 = (let _147_724 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _147_724))
in (tc_check_tot_or_gtot_term (

let _57_2017 = env0
in {FStar_TypeChecker_Env.solver = _57_2017.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2017.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2017.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2017.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2017.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2017.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2017.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2017.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2017.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2017.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2017.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2017.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2017.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2017.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _57_2017.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2017.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2017.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2017.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2017.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2017.FStar_TypeChecker_Env.use_bv_sorts}) t _147_725))
in (match (_57_2023) with
| (t, _57_2021, g) -> begin
(

let _57_2024 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (

let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(

let _57_2027 = env
in {FStar_TypeChecker_Env.solver = _57_2027.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2027.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2027.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2027.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2027.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2027.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2027.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2027.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2027.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2027.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2027.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2027.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2027.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_2027.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2027.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2027.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2027.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2027.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2027.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2027.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (

let lb = (

let _57_2030 = lb
in {FStar_Syntax_Syntax.lbname = _57_2030.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _57_2030.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_57_2035) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _57_2048 = (let _147_730 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _57_2042 = (let _147_729 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _147_729 lb.FStar_Syntax_Syntax.lbdef))
in (match (_57_2042) with
| (e, c, g) -> begin
(

let _57_2043 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _147_730 FStar_List.unzip))
in (match (_57_2048) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _57_2056 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_2056) with
| (env1, _57_2055) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _57_2062 = (check_lbtyp top_level env lb)
in (match (_57_2062) with
| (topt, wf_annot, univ_vars, env1) -> begin
(

let _57_2063 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let _57_2070 = (tc_maybe_toplevel_term (

let _57_2065 = env1
in {FStar_TypeChecker_Env.solver = _57_2065.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2065.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2065.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2065.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2065.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2065.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2065.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2065.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2065.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2065.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2065.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2065.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2065.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _57_2065.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2065.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2065.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2065.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2065.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2065.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2065.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_57_2070) with
| (e1, c1, g1) -> begin
(

let _57_2074 = (let _147_737 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_2071 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _147_737 e1 c1 wf_annot))
in (match (_57_2074) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _57_2076 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _147_738 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _147_738))
end else begin
()
end
in (let _147_739 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _147_739))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _57_2083 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _57_2086 -> begin
(

let _57_2089 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_57_2089) with
| (univ_vars, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _147_743 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _147_743))
end else begin
(

let _57_2094 = (FStar_Syntax_Util.type_u ())
in (match (_57_2094) with
| (k, _57_2093) -> begin
(

let _57_2099 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_57_2099) with
| (t, _57_2097, g) -> begin
(

let _57_2100 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _147_746 = (let _147_744 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _147_744))
in (let _147_745 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _147_746 _147_745)))
end else begin
()
end
in (

let t = (norm env1 t)
in (let _147_747 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _147_747))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _57_2106 -> (match (_57_2106) with
| (x, imp) -> begin
(

let _57_2109 = (FStar_Syntax_Util.type_u ())
in (match (_57_2109) with
| (tu, u) -> begin
(

let _57_2114 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_57_2114) with
| (t, _57_2112, g) -> begin
(

let x = ((

let _57_2115 = x
in {FStar_Syntax_Syntax.ppname = _57_2115.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2115.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (

let _57_2118 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_751 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _147_750 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _147_751 _147_750)))
end else begin
()
end
in (let _147_752 = (maybe_push_binding env x)
in (x, _147_752, g, u))))
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

let _57_2133 = (tc_binder env b)
in (match (_57_2133) with
| (b, env', g, u) -> begin
(

let _57_2138 = (aux env' bs)
in (match (_57_2138) with
| (bs, env', g', us) -> begin
(let _147_760 = (let _147_759 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _147_759))
in ((b)::bs, env', _147_760, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun _57_2146 _57_2149 -> (match ((_57_2146, _57_2149)) with
| ((t, imp), (args, g)) -> begin
(

let _57_2154 = (tc_term env t)
in (match (_57_2154) with
| (t, _57_2152, g') -> begin
(let _147_769 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _147_769))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _57_2158 -> (match (_57_2158) with
| (pats, g) -> begin
(

let _57_2161 = (tc_args env p)
in (match (_57_2161) with
| (args, g') -> begin
(let _147_772 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _147_772))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _57_2167 = (tc_maybe_toplevel_term env e)
in (match (_57_2167) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let _57_2170 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_775 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _147_775))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _57_2175 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _147_776 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_147_776, false))
end else begin
(let _147_777 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_147_777, true))
end
in (match (_57_2175) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _147_778 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _147_778))
end
| _57_2179 -> begin
if allow_ghost then begin
(let _147_781 = (let _147_780 = (let _147_779 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_147_779, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_147_780))
in (Prims.raise _147_781))
end else begin
(let _147_784 = (let _147_783 = (let _147_782 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_147_782, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_147_783))
in (Prims.raise _147_784))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))


let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let _57_2189 = (tc_tot_or_gtot_term env t)
in (match (_57_2189) with
| (t, c, g) -> begin
(

let _57_2190 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let _57_2198 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_2198) with
| (t, c, g) -> begin
(

let _57_2199 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _147_804 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _147_804)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _147_808 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _147_808))))


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let _57_2214 = (tc_binders env tps)
in (match (_57_2214) with
| (tps, env, g, us) -> begin
(

let _57_2215 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (

let fail = (fun _57_2221 -> (match (()) with
| () -> begin
(let _147_823 = (let _147_822 = (let _147_821 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_147_821, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_147_822))
in (Prims.raise _147_823))
end))
in (

let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _57_2234))::((wp, _57_2230))::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2238 -> begin
(fail ())
end))
end
| _57_2240 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let _57_2247 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_57_2247) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _57_2249 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let _57_2253 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_57_2253) with
| (uvs, t') -> begin
(match ((let _147_830 = (FStar_Syntax_Subst.compress t')
in _147_830.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _57_2259 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))


let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (

let fail = (fun t -> (let _147_841 = (let _147_840 = (let _147_839 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_147_839, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_147_840))
in (Prims.raise _147_841)))
in (match ((let _147_842 = (FStar_Syntax_Subst.compress signature)
in _147_842.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _57_2276))::((wp, _57_2272))::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2280 -> begin
(fail signature)
end))
end
| _57_2282 -> begin
(fail signature)
end)))


let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (

let _57_2287 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_57_2287) with
| (a, wp) -> begin
(

let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _57_2290 -> begin
(

let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (

let op = (fun ts -> (

let _57_2294 = ()
in (

let t0 = (Prims.snd ts)
in (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (

let _57_2298 = ed
in (let _147_859 = (op ed.FStar_Syntax_Syntax.ret)
in (let _147_858 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _147_857 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _147_856 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _147_855 = (op ed.FStar_Syntax_Syntax.wp_binop)
in (let _147_854 = (op ed.FStar_Syntax_Syntax.wp_as_type)
in (let _147_853 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _147_852 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _147_851 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _147_850 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _147_849 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _57_2298.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2298.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2298.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2298.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2298.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _147_859; FStar_Syntax_Syntax.bind_wp = _147_858; FStar_Syntax_Syntax.if_then_else = _147_857; FStar_Syntax_Syntax.ite_wp = _147_856; FStar_Syntax_Syntax.wp_binop = _147_855; FStar_Syntax_Syntax.wp_as_type = _147_854; FStar_Syntax_Syntax.close_wp = _147_853; FStar_Syntax_Syntax.assert_p = _147_852; FStar_Syntax_Syntax.assume_p = _147_851; FStar_Syntax_Syntax.null_wp = _147_850; FStar_Syntax_Syntax.trivial = _147_849}))))))))))))))
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

let n = (match ((let _147_881 = (FStar_Syntax_Subst.compress tm)
in _147_881.FStar_Syntax_Syntax.n)) with
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
| _57_2333 -> begin
tm.FStar_Syntax_Syntax.n
end)
in (

let _57_2335 = tm
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2335.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2335.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2335.FStar_Syntax_Syntax.vars})))
and visit_binder = (fun _57_2339 -> (match (_57_2339) with
| (bv, a) -> begin
(let _147_885 = (

let _57_2340 = bv
in (let _147_883 = (visit_term bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_2340.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2340.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_883}))
in (let _147_884 = (FStar_Syntax_Syntax.as_implicit false)
in (_147_885, _147_884)))
end))
and visit_maybe_lcomp = (fun lcomp -> (match (lcomp) with
| Some (FStar_Util.Inl (lcomp)) -> begin
(let _147_890 = (let _147_889 = (let _147_888 = (let _147_887 = (lcomp.FStar_Syntax_Syntax.comp ())
in (visit_comp _147_887))
in (FStar_Syntax_Util.lcomp_of_comp _147_888))
in FStar_Util.Inl (_147_889))
in Some (_147_890))
end
| comp -> begin
comp
end))
and visit_comp = (fun comp -> (

let n = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tm) -> begin
(let _147_892 = (visit_term tm)
in FStar_Syntax_Syntax.Total (_147_892))
end
| FStar_Syntax_Syntax.GTotal (tm) -> begin
(let _147_893 = (visit_term tm)
in FStar_Syntax_Syntax.GTotal (_147_893))
end
| comp -> begin
comp
end)
in (

let _57_2354 = comp
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2354.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2354.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2354.FStar_Syntax_Syntax.vars})))
and visit_args = (fun args -> (FStar_List.map (fun _57_2359 -> (match (_57_2359) with
| (tm, q) -> begin
(let _147_896 = (visit_term tm)
in (_147_896, q))
end)) args))
in (visit_term tm))))
in (

let check = (fun str t -> if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _57_2363 = (let _147_901 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Generated term for %s: %s\n" str _147_901))
in (

let t = (normalize t)
in (

let t = (FStar_Syntax_Subst.compress t)
in (

let _57_2378 = (tc_term env t)
in (match (_57_2378) with
| (e, {FStar_Syntax_Syntax.eff_name = _57_2374; FStar_Syntax_Syntax.res_typ = res_typ; FStar_Syntax_Syntax.cflags = _57_2371; FStar_Syntax_Syntax.comp = _57_2369}, _57_2377) -> begin
(

let _57_2379 = (let _147_904 = (let _147_903 = (normalize res_typ)
in (FStar_Syntax_Print.term_to_string _147_903))
in (FStar_Util.print2 "Inferred type for %s: %s\n" str _147_904))
in (let _147_906 = (let _147_905 = (normalize e)
in (FStar_Syntax_Print.term_to_string _147_905))
in (FStar_Util.print2 "Elaborated term for %s: %s\n" str _147_906)))
end)))))
end else begin
()
end)
in (

let rec collect_binders = (fun t -> (match ((let _147_909 = (FStar_Syntax_Subst.compress t)
in _147_909.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
t
end
| _57_2390 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _147_910 = (collect_binders rest)
in (FStar_List.append bs _147_910)))
end
| FStar_Syntax_Syntax.Tm_type (_57_2393) -> begin
[]
end
| _57_2396 -> begin
(FStar_All.failwith "wp_a doesn\'t end in Type0")
end))
in (

let _57_2411 = (

let i = (FStar_ST.alloc 0)
in (

let wp_binders = (let _147_917 = (normalize wp_a)
in (collect_binders _147_917))
in ((fun t -> (let _147_923 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow wp_binders _147_923))), (fun t -> (let _147_926 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow wp_binders _147_926))), (fun _57_2401 -> (match (()) with
| () -> begin
(FStar_List.map (fun _57_2405 -> (match (_57_2405) with
| (bv, _57_2404) -> begin
(

let _57_2406 = (let _147_930 = ((FStar_ST.read i) + 1)
in (FStar_ST.op_Colon_Equals i _147_930))
in (let _147_933 = (let _147_932 = (let _147_931 = (FStar_ST.read i)
in (FStar_Util.string_of_int _147_931))
in (Prims.strcat "g" _147_932))
in (FStar_Syntax_Syntax.gen_bv _147_933 None bv.FStar_Syntax_Syntax.sort)))
end)) wp_binders)
end)))))
in (match (_57_2411) with
| (mk_ctx, mk_gctx, mk_gamma) -> begin
(

let binders_of_list = (FStar_List.map (fun _57_2414 -> (match (_57_2414) with
| (t, b) -> begin
(let _147_939 = (FStar_Syntax_Syntax.as_implicit b)
in (t, _147_939))
end)))
in (

let implicit_binders_of_list = (FStar_List.map (fun t -> (let _147_942 = (FStar_Syntax_Syntax.as_implicit true)
in (t, _147_942))))
in (

let args_of_bv = (FStar_List.map (fun bv -> (let _147_945 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_Syntax_Syntax.as_arg _147_945))))
in (

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let x = (let _147_946 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _147_946))
in (

let ret = (let _147_951 = (let _147_950 = (let _147_949 = (let _147_948 = (let _147_947 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx _147_947))
in (FStar_Syntax_Syntax.mk_Total _147_948))
in (FStar_Syntax_Util.lcomp_of_comp _147_949))
in FStar_Util.Inl (_147_950))
in Some (_147_951))
in (

let gamma = (mk_gamma ())
in (

let body = (let _147_953 = (implicit_binders_of_list gamma)
in (let _147_952 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs _147_953 _147_952 ret)))
in (let _147_954 = (binders_of_list (((t, true))::((x, false))::[]))
in (FStar_Syntax_Util.abs _147_954 body ret)))))))
in (

let _57_2426 = (let _147_958 = (let _147_957 = (let _147_956 = (let _147_955 = (FStar_Syntax_Syntax.mk_binder a)
in (_147_955)::[])
in (FStar_List.append binders _147_956))
in (FStar_Syntax_Util.abs _147_957 c_pure None))
in (check "pure" _147_958))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let l = (let _147_966 = (let _147_965 = (let _147_964 = (let _147_961 = (let _147_960 = (let _147_959 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _147_959))
in (FStar_Syntax_Syntax.mk_binder _147_960))
in (_147_961)::[])
in (let _147_963 = (let _147_962 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _147_962))
in (FStar_Syntax_Util.arrow _147_964 _147_963)))
in (mk_gctx _147_965))
in (FStar_Syntax_Syntax.gen_bv "l" None _147_966))
in (

let r = (let _147_968 = (let _147_967 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _147_967))
in (FStar_Syntax_Syntax.gen_bv "r" None _147_968))
in (

let ret = (let _147_973 = (let _147_972 = (let _147_971 = (let _147_970 = (let _147_969 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _147_969))
in (FStar_Syntax_Syntax.mk_Total _147_970))
in (FStar_Syntax_Util.lcomp_of_comp _147_971))
in FStar_Util.Inl (_147_972))
in Some (_147_973))
in (

let outer_body = (

let gamma = (mk_gamma ())
in (

let gamma_as_args = (args_of_bv gamma)
in (

let inner_body = (let _147_979 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _147_978 = (let _147_977 = (let _147_976 = (let _147_975 = (let _147_974 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _147_974 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg _147_975))
in (_147_976)::[])
in (FStar_List.append gamma_as_args _147_977))
in (FStar_Syntax_Util.mk_app _147_979 _147_978)))
in (let _147_980 = (implicit_binders_of_list gamma)
in (FStar_Syntax_Util.abs _147_980 inner_body ret)))))
in (let _147_981 = (binders_of_list (((t1, true))::((t2, true))::((l, false))::((r, false))::[]))
in (FStar_Syntax_Util.abs _147_981 outer_body ret))))))))
in (

let _57_2438 = (let _147_985 = (let _147_984 = (let _147_983 = (let _147_982 = (FStar_Syntax_Syntax.mk_binder a)
in (_147_982)::[])
in (FStar_List.append binders _147_983))
in (FStar_Syntax_Util.abs _147_984 c_app None))
in (check "app" _147_985))
in (

let unknown = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _147_990 = (let _147_987 = (let _147_986 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _147_986))
in (_147_987)::[])
in (let _147_989 = (let _147_988 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _147_988))
in (FStar_Syntax_Util.arrow _147_990 _147_989)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _147_992 = (let _147_991 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _147_991))
in (FStar_Syntax_Syntax.gen_bv "a1" None _147_992))
in (

let ret = (let _147_997 = (let _147_996 = (let _147_995 = (let _147_994 = (let _147_993 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _147_993))
in (FStar_Syntax_Syntax.mk_Total _147_994))
in (FStar_Syntax_Util.lcomp_of_comp _147_995))
in FStar_Util.Inl (_147_996))
in Some (_147_997))
in (let _147_1010 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::((a1, false))::[]))
in (let _147_1009 = (let _147_1008 = (let _147_1007 = (let _147_1006 = (let _147_1005 = (let _147_1004 = (let _147_1001 = (let _147_1000 = (let _147_999 = (let _147_998 = (FStar_Syntax_Syntax.bv_to_name f)
in (_147_998)::[])
in (unknown)::_147_999)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1000))
in (FStar_Syntax_Util.mk_app c_pure _147_1001))
in (let _147_1003 = (let _147_1002 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_147_1002)::[])
in (_147_1004)::_147_1003))
in (unknown)::_147_1005)
in (unknown)::_147_1006)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1007))
in (FStar_Syntax_Util.mk_app c_app _147_1008))
in (FStar_Syntax_Util.abs _147_1010 _147_1009 ret)))))))))
in (

let _57_2448 = (let _147_1014 = (let _147_1013 = (let _147_1012 = (let _147_1011 = (FStar_Syntax_Syntax.mk_binder a)
in (_147_1011)::[])
in (FStar_List.append binders _147_1012))
in (FStar_Syntax_Util.abs _147_1013 c_lift1 None))
in (check "lift1" _147_1014))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _147_1022 = (let _147_1019 = (let _147_1015 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _147_1015))
in (let _147_1018 = (let _147_1017 = (let _147_1016 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder _147_1016))
in (_147_1017)::[])
in (_147_1019)::_147_1018))
in (let _147_1021 = (let _147_1020 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal _147_1020))
in (FStar_Syntax_Util.arrow _147_1022 _147_1021)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _147_1024 = (let _147_1023 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _147_1023))
in (FStar_Syntax_Syntax.gen_bv "a1" None _147_1024))
in (

let a2 = (let _147_1026 = (let _147_1025 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _147_1025))
in (FStar_Syntax_Syntax.gen_bv "a2" None _147_1026))
in (

let ret = (let _147_1031 = (let _147_1030 = (let _147_1029 = (let _147_1028 = (let _147_1027 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx _147_1027))
in (FStar_Syntax_Syntax.mk_Total _147_1028))
in (FStar_Syntax_Util.lcomp_of_comp _147_1029))
in FStar_Util.Inl (_147_1030))
in Some (_147_1031))
in (let _147_1051 = (binders_of_list (((t1, true))::((t2, true))::((t3, true))::((f, false))::((a1, false))::((a2, false))::[]))
in (let _147_1050 = (let _147_1049 = (let _147_1048 = (let _147_1047 = (let _147_1046 = (let _147_1045 = (let _147_1042 = (let _147_1041 = (let _147_1040 = (let _147_1039 = (let _147_1038 = (let _147_1035 = (let _147_1034 = (let _147_1033 = (let _147_1032 = (FStar_Syntax_Syntax.bv_to_name f)
in (_147_1032)::[])
in (unknown)::_147_1033)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1034))
in (FStar_Syntax_Util.mk_app c_pure _147_1035))
in (let _147_1037 = (let _147_1036 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_147_1036)::[])
in (_147_1038)::_147_1037))
in (unknown)::_147_1039)
in (unknown)::_147_1040)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1041))
in (FStar_Syntax_Util.mk_app c_app _147_1042))
in (let _147_1044 = (let _147_1043 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_147_1043)::[])
in (_147_1045)::_147_1044))
in (unknown)::_147_1046)
in (unknown)::_147_1047)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1048))
in (FStar_Syntax_Util.mk_app c_app _147_1049))
in (FStar_Syntax_Util.abs _147_1051 _147_1050 ret)))))))))))
in (

let _57_2459 = (let _147_1055 = (let _147_1054 = (let _147_1053 = (let _147_1052 = (FStar_Syntax_Syntax.mk_binder a)
in (_147_1052)::[])
in (FStar_List.append binders _147_1053))
in (FStar_Syntax_Util.abs _147_1054 c_lift2 None))
in (check "lift2" _147_1055))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _147_1061 = (let _147_1057 = (let _147_1056 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _147_1056))
in (_147_1057)::[])
in (let _147_1060 = (let _147_1059 = (let _147_1058 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _147_1058))
in (FStar_Syntax_Syntax.mk_Total _147_1059))
in (FStar_Syntax_Util.arrow _147_1061 _147_1060)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let ret = (let _147_1071 = (let _147_1070 = (let _147_1069 = (let _147_1068 = (let _147_1067 = (let _147_1066 = (let _147_1063 = (let _147_1062 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _147_1062))
in (_147_1063)::[])
in (let _147_1065 = (let _147_1064 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _147_1064))
in (FStar_Syntax_Util.arrow _147_1066 _147_1065)))
in (mk_ctx _147_1067))
in (FStar_Syntax_Syntax.mk_Total _147_1068))
in (FStar_Syntax_Util.lcomp_of_comp _147_1069))
in FStar_Util.Inl (_147_1070))
in Some (_147_1071))
in (

let e1 = (let _147_1072 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _147_1072))
in (

let gamma = (mk_gamma ())
in (

let body = (let _147_1082 = (let _147_1075 = (FStar_Syntax_Syntax.binders_of_list gamma)
in (let _147_1074 = (let _147_1073 = (FStar_Syntax_Syntax.mk_binder e1)
in (_147_1073)::[])
in (FStar_List.append _147_1075 _147_1074)))
in (let _147_1081 = (let _147_1080 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _147_1079 = (let _147_1078 = (let _147_1076 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _147_1076))
in (let _147_1077 = (args_of_bv gamma)
in (_147_1078)::_147_1077))
in (FStar_Syntax_Util.mk_app _147_1080 _147_1079)))
in (FStar_Syntax_Util.abs _147_1082 _147_1081 ret)))
in (let _147_1083 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::[]))
in (FStar_Syntax_Util.abs _147_1083 body ret))))))))))
in (

let _57_2470 = (let _147_1087 = (let _147_1086 = (let _147_1085 = (let _147_1084 = (FStar_Syntax_Syntax.mk_binder a)
in (_147_1084)::[])
in (FStar_List.append binders _147_1085))
in (FStar_Syntax_Util.abs _147_1086 c_push None))
in (check "push" _147_1087))
in (

let ret_tot_wp_a = (let _147_1090 = (let _147_1089 = (let _147_1088 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _147_1088))
in FStar_Util.Inl (_147_1089))
in Some (_147_1090))
in (

let wp_if_then_else = (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _147_1101 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (let _147_1100 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_unfoldable (2)) None)
in (let _147_1099 = (let _147_1098 = (let _147_1097 = (let _147_1096 = (let _147_1095 = (let _147_1094 = (let _147_1093 = (let _147_1092 = (let _147_1091 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _147_1091))
in (_147_1092)::[])
in (FStar_Syntax_Util.mk_app l_ite _147_1093))
in (_147_1094)::[])
in (unknown)::_147_1095)
in (unknown)::_147_1096)
in (unknown)::_147_1097)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1098))
in (FStar_Syntax_Util.mk_app c_lift2 _147_1099)))
in (FStar_Syntax_Util.abs _147_1101 _147_1100 ret_tot_wp_a))))
in (

let wp_if_then_else = (normalize_and_make_binders_explicit wp_if_then_else)
in (

let _57_2477 = (let _147_1102 = (FStar_Syntax_Util.abs binders wp_if_then_else None)
in (check "wp_if_then_else" _147_1102))
in (

let wp_binop = (

let l = (FStar_Syntax_Syntax.gen_bv "l" None wp_a)
in (

let op = (let _147_1108 = (let _147_1107 = (let _147_1105 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Util.ktype0)
in (let _147_1104 = (let _147_1103 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Util.ktype0)
in (_147_1103)::[])
in (_147_1105)::_147_1104))
in (let _147_1106 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _147_1107 _147_1106)))
in (FStar_Syntax_Syntax.gen_bv "op" None _147_1108))
in (

let r = (FStar_Syntax_Syntax.gen_bv "r" None wp_a)
in (let _147_1120 = (FStar_Syntax_Syntax.binders_of_list ((a)::(l)::(op)::(r)::[]))
in (let _147_1119 = (let _147_1118 = (let _147_1117 = (let _147_1116 = (let _147_1115 = (let _147_1114 = (let _147_1113 = (FStar_Syntax_Syntax.bv_to_name op)
in (let _147_1112 = (let _147_1111 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _147_1110 = (let _147_1109 = (FStar_Syntax_Syntax.bv_to_name r)
in (_147_1109)::[])
in (_147_1111)::_147_1110))
in (_147_1113)::_147_1112))
in (unknown)::_147_1114)
in (unknown)::_147_1115)
in (unknown)::_147_1116)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1117))
in (FStar_Syntax_Util.mk_app c_lift2 _147_1118))
in (FStar_Syntax_Util.abs _147_1120 _147_1119 ret_tot_wp_a))))))
in (

let wp_binop = (normalize_and_make_binders_explicit wp_binop)
in (

let _57_2484 = (let _147_1121 = (FStar_Syntax_Util.abs binders wp_binop None)
in (check "wp_binop" _147_1121))
in (

let wp_assert = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_and = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (

let body = (let _147_1135 = (let _147_1134 = (let _147_1133 = (let _147_1132 = (let _147_1131 = (let _147_1128 = (let _147_1127 = (let _147_1126 = (let _147_1125 = (let _147_1124 = (let _147_1123 = (let _147_1122 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _147_1122))
in (_147_1123)::[])
in (FStar_Syntax_Util.mk_app l_and _147_1124))
in (_147_1125)::[])
in (unknown)::_147_1126)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1127))
in (FStar_Syntax_Util.mk_app c_pure _147_1128))
in (let _147_1130 = (let _147_1129 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_147_1129)::[])
in (_147_1131)::_147_1130))
in (unknown)::_147_1132)
in (unknown)::_147_1133)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1134))
in (FStar_Syntax_Util.mk_app c_app _147_1135))
in (let _147_1136 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _147_1136 body ret_tot_wp_a))))))
in (

let wp_assert = (normalize_and_make_binders_explicit wp_assert)
in (

let _57_2492 = (let _147_1137 = (FStar_Syntax_Util.abs binders wp_assert None)
in (check "wp_assert" _147_1137))
in (

let wp_assume = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_imp = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (

let body = (let _147_1151 = (let _147_1150 = (let _147_1149 = (let _147_1148 = (let _147_1147 = (let _147_1144 = (let _147_1143 = (let _147_1142 = (let _147_1141 = (let _147_1140 = (let _147_1139 = (let _147_1138 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _147_1138))
in (_147_1139)::[])
in (FStar_Syntax_Util.mk_app l_imp _147_1140))
in (_147_1141)::[])
in (unknown)::_147_1142)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1143))
in (FStar_Syntax_Util.mk_app c_pure _147_1144))
in (let _147_1146 = (let _147_1145 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_147_1145)::[])
in (_147_1147)::_147_1146))
in (unknown)::_147_1148)
in (unknown)::_147_1149)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1150))
in (FStar_Syntax_Util.mk_app c_app _147_1151))
in (let _147_1152 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _147_1152 body ret_tot_wp_a))))))
in (

let wp_assume = (normalize_and_make_binders_explicit wp_assume)
in (

let _57_2500 = (let _147_1153 = (FStar_Syntax_Util.abs binders wp_assume None)
in (check "wp_assume" _147_1153))
in (

let tforall = (let _147_1156 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _147_1155 = (let _147_1154 = (FStar_Syntax_Syntax.as_arg unknown)
in (_147_1154)::[])
in (FStar_Syntax_Util.mk_app _147_1156 _147_1155)))
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _147_1160 = (let _147_1158 = (let _147_1157 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _147_1157))
in (_147_1158)::[])
in (let _147_1159 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _147_1160 _147_1159)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (let _147_1173 = (let _147_1172 = (let _147_1171 = (let _147_1170 = (let _147_1169 = (let _147_1161 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((unknown)::(tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _147_1161))
in (let _147_1168 = (let _147_1167 = (let _147_1166 = (let _147_1165 = (let _147_1164 = (let _147_1163 = (let _147_1162 = (FStar_Syntax_Syntax.bv_to_name f)
in (_147_1162)::[])
in (unknown)::_147_1163)
in (unknown)::_147_1164)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1165))
in (FStar_Syntax_Util.mk_app c_push _147_1166))
in (_147_1167)::[])
in (_147_1169)::_147_1168))
in (unknown)::_147_1170)
in (unknown)::_147_1171)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1172))
in (FStar_Syntax_Util.mk_app c_app _147_1173))
in (let _147_1174 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_Syntax_Util.abs _147_1174 body ret_tot_wp_a))))))
in (

let wp_close = (normalize_and_make_binders_explicit wp_close)
in (

let _57_2509 = (let _147_1175 = (FStar_Syntax_Util.abs binders wp_close None)
in (check "wp_close" _147_1175))
in (

let ret_tot_type0 = (let _147_1178 = (let _147_1177 = (let _147_1176 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _147_1176))
in FStar_Util.Inl (_147_1177))
in Some (_147_1178))
in (

let mk_forall = (fun x body -> (

let tforall = (let _147_1185 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _147_1184 = (let _147_1183 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (_147_1183)::[])
in (FStar_Syntax_Util.mk_app _147_1185 _147_1184)))
in (let _147_1192 = (let _147_1191 = (let _147_1190 = (let _147_1189 = (let _147_1188 = (let _147_1187 = (let _147_1186 = (FStar_Syntax_Syntax.mk_binder x)
in (_147_1186)::[])
in (FStar_Syntax_Util.abs _147_1187 body ret_tot_type0))
in (FStar_Syntax_Syntax.as_arg _147_1188))
in (_147_1189)::[])
in (tforall, _147_1190))
in FStar_Syntax_Syntax.Tm_app (_147_1191))
in (FStar_Syntax_Syntax.mk _147_1192 None FStar_Range.dummyRange))))
in (

let rec mk_leq = (fun t x y -> (match ((let _147_1200 = (let _147_1199 = (FStar_Syntax_Subst.compress t)
in (normalize _147_1199))
in _147_1200.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_2521) -> begin
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

let body = (let _147_1212 = (let _147_1202 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _147_1201 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_leq a _147_1202 _147_1201)))
in (let _147_1211 = (let _147_1210 = (let _147_1205 = (let _147_1204 = (let _147_1203 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _147_1203))
in (_147_1204)::[])
in (FStar_Syntax_Util.mk_app x _147_1205))
in (let _147_1209 = (let _147_1208 = (let _147_1207 = (let _147_1206 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _147_1206))
in (_147_1207)::[])
in (FStar_Syntax_Util.mk_app y _147_1208))
in (mk_leq b _147_1210 _147_1209)))
in (FStar_Syntax_Util.mk_imp _147_1212 _147_1211)))
in (let _147_1213 = (mk_forall a2 body)
in (mk_forall a1 _147_1213))))))
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let _57_2557 = t
in (let _147_1217 = (let _147_1216 = (let _147_1215 = (let _147_1214 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _147_1214))
in ((binder)::[], _147_1215))
in FStar_Syntax_Syntax.Tm_arrow (_147_1216))
in {FStar_Syntax_Syntax.n = _147_1217; FStar_Syntax_Syntax.tk = _57_2557.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2557.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2557.FStar_Syntax_Syntax.vars}))
in (mk_leq t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_57_2561) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _57_2564 -> begin
(FStar_Syntax_Util.mk_eq t t x y)
end))
in (

let stronger = (

let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (

let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (

let body = (let _147_1219 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _147_1218 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_leq wp_a _147_1219 _147_1218)))
in (let _147_1220 = (FStar_Syntax_Syntax.binders_of_list ((wp1)::(wp2)::[]))
in (FStar_Syntax_Util.abs _147_1220 body ret_tot_type0)))))
in (

let _57_2569 = (let _147_1224 = (let _147_1223 = (let _147_1222 = (let _147_1221 = (FStar_Syntax_Syntax.mk_binder a)
in (_147_1221)::[])
in (FStar_List.append binders _147_1222))
in (FStar_Syntax_Util.abs _147_1223 stronger None))
in (check "stronger" _147_1224))
in (

let null_wp = (Prims.snd ed.FStar_Syntax_Syntax.null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (let _147_1232 = (let _147_1231 = (let _147_1230 = (let _147_1227 = (let _147_1226 = (let _147_1225 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _147_1225))
in (_147_1226)::[])
in (FStar_Syntax_Util.mk_app null_wp _147_1227))
in (let _147_1229 = (let _147_1228 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_147_1228)::[])
in (_147_1230)::_147_1229))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1231))
in (FStar_Syntax_Util.mk_app stronger _147_1232))
in (let _147_1233 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_Syntax_Util.abs _147_1233 body ret_tot_type0))))
in (

let wp_trivial = (normalize_and_make_binders_explicit wp_trivial)
in (

let _57_2576 = (let _147_1234 = (FStar_Syntax_Util.abs binders wp_trivial None)
in (check "wp_trivial" _147_1234))
in (

let _57_2578 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2578.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2578.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2578.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2578.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2578.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _57_2578.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2578.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = ([], wp_if_then_else); FStar_Syntax_Syntax.ite_wp = _57_2578.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.wp_binop = ([], wp_binop); FStar_Syntax_Syntax.wp_as_type = _57_2578.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = ([], wp_close); FStar_Syntax_Syntax.assert_p = ([], wp_assert); FStar_Syntax_Syntax.assume_p = ([], wp_assume); FStar_Syntax_Syntax.null_wp = _57_2578.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = ([], wp_trivial)})))))))))))))))))))))))))))))))))))))))))
end))))))))


let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  effect_cost  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed is_for_free -> (

let _57_2583 = ()
in (

let _57_2587 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_57_2587) with
| (binders_un, signature_un) -> begin
(

let _57_2592 = (tc_tparams env0 binders_un)
in (match (_57_2592) with
| (binders, env, _57_2591) -> begin
(

let _57_2596 = (tc_trivial_guard env signature_un)
in (match (_57_2596) with
| (signature, _57_2595) -> begin
(

let ed = (

let _57_2597 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2597.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2597.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2597.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _57_2597.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2597.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _57_2597.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _57_2597.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.wp_binop = _57_2597.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _57_2597.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _57_2597.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _57_2597.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _57_2597.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _57_2597.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _57_2597.FStar_Syntax_Syntax.trivial})
in (

let _57_2603 = (open_effect_decl env ed)
in (match (_57_2603) with
| (ed, a, wp_a) -> begin
(

let get_effect_signature = (fun _57_2605 -> (match (()) with
| () -> begin
(

let _57_2609 = (tc_trivial_guard env signature_un)
in (match (_57_2609) with
| (signature, _57_2608) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (

let env = (let _147_1243 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _147_1243))
in (

let _57_2611 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _147_1246 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _147_1245 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _147_1244 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checking effect signature: %s %s : %s\n" _147_1246 _147_1245 _147_1244))))
end else begin
()
end
in (

let check_and_gen' = (fun env _57_2618 k -> (match (_57_2618) with
| (_57_2616, t) -> begin
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

let expected_k = (let _147_1258 = (let _147_1256 = (FStar_Syntax_Syntax.mk_binder a)
in (let _147_1255 = (let _147_1254 = (let _147_1253 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _147_1253))
in (_147_1254)::[])
in (_147_1256)::_147_1255))
in (let _147_1257 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _147_1258 _147_1257)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (

let bind_wp = (

let _57_2627 = (get_effect_signature ())
in (match (_57_2627) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _147_1262 = (let _147_1260 = (let _147_1259 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _147_1259))
in (_147_1260)::[])
in (let _147_1261 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _147_1262 _147_1261)))
in (

let expected_k = (let _147_1273 = (let _147_1271 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _147_1270 = (let _147_1269 = (FStar_Syntax_Syntax.mk_binder a)
in (let _147_1268 = (let _147_1267 = (FStar_Syntax_Syntax.mk_binder b)
in (let _147_1266 = (let _147_1265 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _147_1264 = (let _147_1263 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (_147_1263)::[])
in (_147_1265)::_147_1264))
in (_147_1267)::_147_1266))
in (_147_1269)::_147_1268))
in (_147_1271)::_147_1270))
in (let _147_1272 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _147_1273 _147_1272)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (let _147_1275 = (let _147_1274 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _147_1274 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _147_1275))
in (

let expected_k = (let _147_1284 = (let _147_1282 = (FStar_Syntax_Syntax.mk_binder a)
in (let _147_1281 = (let _147_1280 = (FStar_Syntax_Syntax.mk_binder p)
in (let _147_1279 = (let _147_1278 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _147_1277 = (let _147_1276 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_147_1276)::[])
in (_147_1278)::_147_1277))
in (_147_1280)::_147_1279))
in (_147_1282)::_147_1281))
in (let _147_1283 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _147_1284 _147_1283)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (let _147_1289 = (let _147_1287 = (FStar_Syntax_Syntax.mk_binder a)
in (let _147_1286 = (let _147_1285 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_147_1285)::[])
in (_147_1287)::_147_1286))
in (let _147_1288 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _147_1289 _147_1288)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let wp_binop = (

let bin_op = (

let _57_2638 = (FStar_Syntax_Util.type_u ())
in (match (_57_2638) with
| (t1, u1) -> begin
(

let _57_2641 = (FStar_Syntax_Util.type_u ())
in (match (_57_2641) with
| (t2, u2) -> begin
(

let t = (let _147_1290 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_max ((u1)::(u2)::[]))) None _147_1290))
in (let _147_1295 = (let _147_1293 = (FStar_Syntax_Syntax.null_binder t1)
in (let _147_1292 = (let _147_1291 = (FStar_Syntax_Syntax.null_binder t2)
in (_147_1291)::[])
in (_147_1293)::_147_1292))
in (let _147_1294 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _147_1295 _147_1294))))
end))
end))
in (

let expected_k = (let _147_1304 = (let _147_1302 = (FStar_Syntax_Syntax.mk_binder a)
in (let _147_1301 = (let _147_1300 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _147_1299 = (let _147_1298 = (FStar_Syntax_Syntax.null_binder bin_op)
in (let _147_1297 = (let _147_1296 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_147_1296)::[])
in (_147_1298)::_147_1297))
in (_147_1300)::_147_1299))
in (_147_1302)::_147_1301))
in (let _147_1303 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _147_1304 _147_1303)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_binop expected_k)))
in (

let wp_as_type = (

let _57_2649 = (FStar_Syntax_Util.type_u ())
in (match (_57_2649) with
| (t, _57_2648) -> begin
(

let expected_k = (let _147_1309 = (let _147_1307 = (FStar_Syntax_Syntax.mk_binder a)
in (let _147_1306 = (let _147_1305 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_147_1305)::[])
in (_147_1307)::_147_1306))
in (let _147_1308 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _147_1309 _147_1308)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (

let close_wp = (

let b = (let _147_1311 = (let _147_1310 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _147_1310 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _147_1311))
in (

let b_wp_a = (let _147_1315 = (let _147_1313 = (let _147_1312 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _147_1312))
in (_147_1313)::[])
in (let _147_1314 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _147_1315 _147_1314)))
in (

let expected_k = (let _147_1322 = (let _147_1320 = (FStar_Syntax_Syntax.mk_binder a)
in (let _147_1319 = (let _147_1318 = (FStar_Syntax_Syntax.mk_binder b)
in (let _147_1317 = (let _147_1316 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_147_1316)::[])
in (_147_1318)::_147_1317))
in (_147_1320)::_147_1319))
in (let _147_1321 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _147_1322 _147_1321)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (let _147_1331 = (let _147_1329 = (FStar_Syntax_Syntax.mk_binder a)
in (let _147_1328 = (let _147_1327 = (let _147_1324 = (let _147_1323 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _147_1323 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _147_1324))
in (let _147_1326 = (let _147_1325 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_147_1325)::[])
in (_147_1327)::_147_1326))
in (_147_1329)::_147_1328))
in (let _147_1330 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _147_1331 _147_1330)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _147_1340 = (let _147_1338 = (FStar_Syntax_Syntax.mk_binder a)
in (let _147_1337 = (let _147_1336 = (let _147_1333 = (let _147_1332 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _147_1332 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _147_1333))
in (let _147_1335 = (let _147_1334 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_147_1334)::[])
in (_147_1336)::_147_1335))
in (_147_1338)::_147_1337))
in (let _147_1339 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _147_1340 _147_1339)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _147_1343 = (let _147_1341 = (FStar_Syntax_Syntax.mk_binder a)
in (_147_1341)::[])
in (let _147_1342 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _147_1343 _147_1342)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let _57_2665 = (FStar_Syntax_Util.type_u ())
in (match (_57_2665) with
| (t, _57_2664) -> begin
(

let expected_k = (let _147_1348 = (let _147_1346 = (FStar_Syntax_Syntax.mk_binder a)
in (let _147_1345 = (let _147_1344 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_147_1344)::[])
in (_147_1346)::_147_1345))
in (let _147_1347 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _147_1348 _147_1347)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let t = (let _147_1349 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _147_1349))
in (

let _57_2671 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_57_2671) with
| (univs, t) -> begin
(

let _57_2687 = (match ((let _147_1351 = (let _147_1350 = (FStar_Syntax_Subst.compress t)
in _147_1350.FStar_Syntax_Syntax.n)
in (binders, _147_1351))) with
| ([], _57_2674) -> begin
([], t)
end
| (_57_2677, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _57_2684 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_2687) with
| (binders, signature) -> begin
(

let close = (fun n ts -> (

let ts = (let _147_1356 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _147_1356))
in (

let _57_2692 = ()
in ts)))
in (

let ed = (

let _57_2694 = ed
in (let _147_1367 = (close 0 ret)
in (let _147_1366 = (close 1 bind_wp)
in (let _147_1365 = (close 0 if_then_else)
in (let _147_1364 = (close 0 ite_wp)
in (let _147_1363 = (close 0 wp_binop)
in (let _147_1362 = (close 0 wp_as_type)
in (let _147_1361 = (close 1 close_wp)
in (let _147_1360 = (close 0 assert_p)
in (let _147_1359 = (close 0 assume_p)
in (let _147_1358 = (close 0 null_wp)
in (let _147_1357 = (close 0 trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _57_2694.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2694.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _147_1367; FStar_Syntax_Syntax.bind_wp = _147_1366; FStar_Syntax_Syntax.if_then_else = _147_1365; FStar_Syntax_Syntax.ite_wp = _147_1364; FStar_Syntax_Syntax.wp_binop = _147_1363; FStar_Syntax_Syntax.wp_as_type = _147_1362; FStar_Syntax_Syntax.close_wp = _147_1361; FStar_Syntax_Syntax.assert_p = _147_1360; FStar_Syntax_Syntax.assume_p = _147_1359; FStar_Syntax_Syntax.null_wp = _147_1358; FStar_Syntax_Syntax.trivial = _147_1357}))))))))))))
in (

let _57_2697 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_1368 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _147_1368))
end else begin
()
end
in ed)))
end))
end)))))))))))))))))))
end)))
end))
end))
end))))


let tc_lex_t = (fun env ses quals lids -> (

let _57_2703 = ()
in (

let _57_2711 = ()
in (match (ses) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _57_2740, _57_2742, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _57_2731, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _57_2720, r2))::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
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

let lex_top_t = (let _147_1376 = (let _147_1375 = (let _147_1374 = (let _147_1373 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _147_1373 FStar_Syntax_Syntax.Delta_constant None))
in (_147_1374, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_147_1375))
in (FStar_Syntax_Syntax.mk _147_1376 None r1))
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

let a = (let _147_1377 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _147_1377))
in (

let hd = (let _147_1378 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _147_1378))
in (

let tl = (let _147_1383 = (let _147_1382 = (let _147_1381 = (let _147_1380 = (let _147_1379 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _147_1379 FStar_Syntax_Syntax.Delta_constant None))
in (_147_1380, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_147_1381))
in (FStar_Syntax_Syntax.mk _147_1382 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _147_1383))
in (

let res = (let _147_1387 = (let _147_1386 = (let _147_1385 = (let _147_1384 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _147_1384 FStar_Syntax_Syntax.Delta_constant None))
in (_147_1385, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_147_1386))
in (FStar_Syntax_Syntax.mk _147_1387 None r2))
in (let _147_1388 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _147_1388))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _147_1390 = (let _147_1389 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _147_1389))
in FStar_Syntax_Syntax.Sig_bundle (_147_1390)))))))))))))))
end
| _57_2766 -> begin
(let _147_1392 = (let _147_1391 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _147_1391))
in (FStar_All.failwith _147_1392))
end))))


let tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _57_2776 = (FStar_Syntax_Util.type_u ())
in (match (_57_2776) with
| (k, _57_2775) -> begin
(

let phi = (let _147_1403 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _147_1403 (norm env)))
in (

let _57_2778 = (FStar_TypeChecker_Util.check_uvars r phi)
in FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))))
end))))


let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _147_1417 = (let _147_1416 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _147_1416))
in (FStar_TypeChecker_Errors.diag r _147_1417)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let _57_2801 = ()
in (

let _57_2803 = (warn_positivity tc r)
in (

let _57_2807 = (FStar_Syntax_Subst.open_term tps k)
in (match (_57_2807) with
| (tps, k) -> begin
(

let _57_2811 = (tc_tparams env tps)
in (match (_57_2811) with
| (tps, env_tps, us) -> begin
(

let _57_2814 = (FStar_Syntax_Util.arrow_formals k)
in (match (_57_2814) with
| (indices, t) -> begin
(

let _57_2818 = (tc_tparams env_tps indices)
in (match (_57_2818) with
| (indices, env', us') -> begin
(

let _57_2822 = (tc_trivial_guard env' t)
in (match (_57_2822) with
| (t, _57_2821) -> begin
(

let k = (let _147_1422 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _147_1422))
in (

let _57_2826 = (FStar_Syntax_Util.type_u ())
in (match (_57_2826) with
| (t_type, u) -> begin
(

let _57_2827 = (let _147_1423 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _147_1423))
in (

let t_tc = (let _147_1424 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _147_1424))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _147_1425 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) ([], t_tc))
in (_147_1425, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u)))))))
end)))
end))
end))
end))
end))
end))))
end
| _57_2834 -> begin
(FStar_All.failwith "impossible")
end))
in (

let positive_if_pure = (fun _57_2836 l -> ())
in (

let tc_data = (fun env tcs _57_6 -> (match (_57_6) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let _57_2853 = ()
in (

let _57_2888 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _57_2857 -> (match (_57_2857) with
| (se, u_tc) -> begin
if (let _147_1438 = (let _147_1437 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _147_1437))
in (FStar_Ident.lid_equals tc_lid _147_1438)) then begin
(

let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2859, _57_2861, tps, _57_2864, _57_2866, _57_2868, _57_2870, _57_2872) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _57_2878 -> (match (_57_2878) with
| (x, _57_2877) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _57_2880 -> begin
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
in (match (_57_2888) with
| (tps, u_tc) -> begin
(

let _57_2908 = (match ((let _147_1440 = (FStar_Syntax_Subst.compress t)
in _147_1440.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _57_2896 = (FStar_Util.first_N ntps bs)
in (match (_57_2896) with
| (_57_2894, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _57_2902 -> (match (_57_2902) with
| (x, _57_2901) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _147_1443 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _147_1443))))
end))
end
| _57_2905 -> begin
([], t)
end)
in (match (_57_2908) with
| (arguments, result) -> begin
(

let _57_2909 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_1446 = (FStar_Syntax_Print.lid_to_string c)
in (let _147_1445 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _147_1444 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _147_1446 _147_1445 _147_1444))))
end else begin
()
end
in (

let _57_2914 = (tc_tparams env arguments)
in (match (_57_2914) with
| (arguments, env', us) -> begin
(

let _57_2918 = (tc_trivial_guard env' result)
in (match (_57_2918) with
| (result, _57_2917) -> begin
(

let _57_2922 = (FStar_Syntax_Util.head_and_args result)
in (match (_57_2922) with
| (head, _57_2921) -> begin
(

let _57_2927 = (match ((let _147_1447 = (FStar_Syntax_Subst.compress head)
in _147_1447.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _57_2926 -> begin
(let _147_1451 = (let _147_1450 = (let _147_1449 = (let _147_1448 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _147_1448))
in (_147_1449, r))
in FStar_Syntax_Syntax.Error (_147_1450))
in (Prims.raise _147_1451))
end)
in (

let g = (FStar_List.fold_left2 (fun g _57_2933 u_x -> (match (_57_2933) with
| (x, _57_2932) -> begin
(

let _57_2935 = ()
in (let _147_1455 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _147_1455)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _147_1459 = (let _147_1457 = (FStar_All.pipe_right tps (FStar_List.map (fun _57_2941 -> (match (_57_2941) with
| (x, _57_2940) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _147_1457 arguments))
in (let _147_1458 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _147_1459 _147_1458)))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _57_2944 -> begin
(FStar_All.failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let _57_2950 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_7 -> (match (_57_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2954, _57_2956, tps, k, _57_2960, _57_2962, _57_2964, _57_2966) -> begin
(let _147_1470 = (let _147_1469 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _147_1469))
in (FStar_Syntax_Syntax.null_binder _147_1470))
end
| _57_2970 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _57_8 -> (match (_57_8) with
| FStar_Syntax_Syntax.Sig_datacon (_57_2974, _57_2976, t, _57_2979, _57_2981, _57_2983, _57_2985, _57_2987) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _57_2991 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let t = (let _147_1472 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _147_1472))
in (

let _57_2994 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_1473 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _147_1473))
end else begin
()
end
in (

let _57_2998 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_57_2998) with
| (uvs, t) -> begin
(

let _57_3000 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_1477 = (let _147_1475 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _147_1475 (FStar_String.concat ", ")))
in (let _147_1476 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _147_1477 _147_1476)))
end else begin
()
end
in (

let _57_3004 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_57_3004) with
| (uvs, t) -> begin
(

let _57_3008 = (FStar_Syntax_Util.arrow_formals t)
in (match (_57_3008) with
| (args, _57_3007) -> begin
(

let _57_3011 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_57_3011) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _57_3015 se -> (match (_57_3015) with
| (x, _57_3014) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3019, tps, _57_3022, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let _57_3045 = (match ((let _147_1480 = (FStar_Syntax_Subst.compress ty)
in _147_1480.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _57_3036 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_57_3036) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _57_3039 -> begin
(let _147_1481 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _147_1481 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _57_3042 -> begin
([], ty)
end)
in (match (_57_3045) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _57_3047 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| _57_3051 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _147_1482 -> FStar_Syntax_Syntax.U_name (_147_1482))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_9 -> (match (_57_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3056, _57_3058, _57_3060, _57_3062, _57_3064, _57_3066, _57_3068) -> begin
(tc, uvs_universes)
end
| _57_3072 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _57_3077 d -> (match (_57_3077) with
| (t, _57_3076) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _57_3081, _57_3083, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _147_1486 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _147_1486 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _57_3093 -> begin
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

let _57_3103 = (FStar_All.pipe_right ses (FStar_List.partition (fun _57_10 -> (match (_57_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_3097) -> begin
true
end
| _57_3100 -> begin
false
end))))
in (match (_57_3103) with
| (tys, datas) -> begin
(

let env0 = env
in (

let _57_3120 = (FStar_List.fold_right (fun tc _57_3109 -> (match (_57_3109) with
| (env, all_tcs, g) -> begin
(

let _57_3113 = (tc_tycon env tc)
in (match (_57_3113) with
| (env, tc, tc_u) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (

let _57_3115 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_1490 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _147_1490))
end else begin
()
end
in (let _147_1491 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _147_1491))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_3120) with
| (env, tcs, g) -> begin
(

let _57_3130 = (FStar_List.fold_right (fun se _57_3124 -> (match (_57_3124) with
| (datas, g) -> begin
(

let _57_3127 = (tc_data env tcs se)
in (match (_57_3127) with
| (data, g') -> begin
(let _147_1494 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _147_1494))
end))
end)) datas ([], g))
in (match (_57_3130) with
| (datas, g) -> begin
(

let _57_3133 = (let _147_1495 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _147_1495 datas))
in (match (_57_3133) with
| (tcs, datas) -> begin
(

let sig_bndle = (let _147_1497 = (let _147_1496 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _147_1496))
in FStar_Syntax_Syntax.Sig_bundle (_147_1497))
in (

let split_arrow = (fun t -> (match ((let _147_1500 = (FStar_Syntax_Subst.compress t)
in _147_1500.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(bs, c)
end
| _57_3142 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (_57_3146, _57_3148, t, _57_3151, _57_3153, _57_3155, _57_3157, _57_3159) -> begin
t
end
| _57_3163 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let dr = FStar_Range.dummyRange
in (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_3167, us, _57_3170, _57_3172, _57_3174, _57_3176, _57_3178, _57_3180) -> begin
us
end
| _57_3184 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let _57_3188 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_57_3188) with
| (usubst, us) -> begin
(

let haseq_ty = (fun acc ty -> (

let _57_3212 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _57_3194, bs, t, _57_3198, d_lids, _57_3201, _57_3203) -> begin
(lid, bs, t, d_lids)
end
| _57_3207 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_57_3212) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _147_1507 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _147_1507 t))
in (

let _57_3217 = (FStar_Syntax_Subst.open_term bs t)
in (match (_57_3217) with
| (bs, t) -> begin
(

let ibs = (match ((let _147_1508 = (FStar_Syntax_Subst.compress t)
in _147_1508.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _57_3220) -> begin
ibs
end
| _57_3224 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _147_1511 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _147_1510 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _147_1511 _147_1510)))
in (

let ind = (let _147_1514 = (FStar_List.map (fun _57_3231 -> (match (_57_3231) with
| (bv, aq) -> begin
(let _147_1513 = (FStar_Syntax_Syntax.bv_to_name bv)
in (_147_1513, aq))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _147_1514 None dr))
in (

let ind = (let _147_1517 = (FStar_List.map (fun _57_3235 -> (match (_57_3235) with
| (bv, aq) -> begin
(let _147_1516 = (FStar_Syntax_Syntax.bv_to_name bv)
in (_147_1516, aq))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _147_1517 None dr))
in (

let haseq_ind = (let _147_1519 = (let _147_1518 = (FStar_Syntax_Syntax.as_arg ind)
in (_147_1518)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _147_1519 None dr))
in (

let bs' = (FStar_List.filter (fun b -> (

let _57_3246 = acc
in (match (_57_3246) with
| (_57_3240, en, _57_3243, _57_3245) -> begin
(

let opt = (let _147_1522 = (let _147_1521 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _147_1521))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort _147_1522 false))
in (match (opt) with
| None -> begin
false
end
| Some (_57_3250) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (let _147_1528 = (let _147_1527 = (let _147_1526 = (let _147_1525 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg _147_1525))
in (_147_1526)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _147_1527 None dr))
in (FStar_Syntax_Util.mk_conj t _147_1528))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let _57_3257 = fml
in (let _147_1534 = (let _147_1533 = (let _147_1532 = (let _147_1531 = (let _147_1530 = (let _147_1529 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_147_1529)::[])
in (_147_1530)::[])
in FStar_Syntax_Syntax.Meta_pattern (_147_1531))
in (fml, _147_1532))
in FStar_Syntax_Syntax.Tm_meta (_147_1533))
in {FStar_Syntax_Syntax.n = _147_1534; FStar_Syntax_Syntax.tk = _57_3257.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_3257.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_3257.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _147_1540 = (let _147_1539 = (let _147_1538 = (let _147_1537 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs ((((Prims.fst b), None))::[]) _147_1537 None))
in (FStar_Syntax_Syntax.as_arg _147_1538))
in (_147_1539)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _147_1540 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _147_1546 = (let _147_1545 = (let _147_1544 = (let _147_1543 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs ((((Prims.fst b), None))::[]) _147_1543 None))
in (FStar_Syntax_Syntax.as_arg _147_1544))
in (_147_1545)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _147_1546 None dr))) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let _57_3271 = acc
in (match (_57_3271) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_57_3276, _57_3278, _57_3280, t_lid, _57_3283, _57_3285, _57_3287, _57_3289) -> begin
(t_lid = lid)
end
| _57_3293 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let haseq_data = (fun acc data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (match ((let _147_1552 = (FStar_Syntax_Subst.compress dt)
in _147_1552.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _57_3302) -> begin
(

let dbs = (let _147_1553 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _147_1553))
in (

let dbs = (let _147_1554 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _147_1554 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (let _147_1559 = (let _147_1558 = (let _147_1557 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_147_1557)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _147_1558 None dr))
in (FStar_Syntax_Util.mk_conj t _147_1559))) FStar_Syntax_Util.t_true dbs)
in (

let _57_3313 = acc
in (match (_57_3313) with
| (env, cond') -> begin
(let _147_1561 = (FStar_TypeChecker_Env.push_binders env dbs)
in (let _147_1560 = (FStar_Syntax_Util.mk_conj cond' cond)
in (_147_1561, _147_1560)))
end))))))
end
| _57_3315 -> begin
acc
end))))
in (

let _57_3318 = (FStar_List.fold_left haseq_data (env, FStar_Syntax_Util.t_true) t_datas)
in (match (_57_3318) with
| (env, cond) -> begin
(

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (let _147_1563 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _147_1562 = (FStar_Syntax_Util.mk_conj cond' cond)
in ((FStar_List.append l_axioms (((axiom_lid, fml))::[])), env, _147_1563, _147_1562))))
end))))))
end)))))))))))))))
end))))
end)))
in (

let is_noeq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Noeq)) quals)
in (

let debug_lid = (match ((FStar_List.hd tcs)) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _57_3324, _57_3326, _57_3328, _57_3330, _57_3332, _57_3334, _57_3336) -> begin
lid
end
| _57_3340 -> begin
(FStar_All.failwith "Impossible!")
end)
in (

let _57_3342 = if is_noeq then begin
(FStar_Util.print1 "Skipping this type since noeq:%s\n" debug_lid.FStar_Ident.str)
end else begin
()
end
in if ((not ((FStar_Ident.lid_equals env.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid))) && (not (is_noeq))) then begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _57_3345 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _57_3347 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let _57_3354 = (FStar_List.fold_left haseq_ty ([], env, FStar_Syntax_Util.t_true, FStar_Syntax_Util.t_true) tcs)
in (match (_57_3354) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let _57_3356 = (FStar_Util.print1 "Checking tc_trivial_guard for:\n\n%s\n\n" debug_lid.FStar_Ident.str)
in (

let _57_3361 = (tc_trivial_guard env phi)
in (match (_57_3361) with
| (phi, _57_3360) -> begin
(

let _57_3362 = (let _147_1565 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print1 "Checking haseq soundness for:%s\n" _147_1565))
in (

let _57_3364 = (let _147_1566 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _147_1566))
in (

let _57_3366 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env0 us)
in (

let ses = (FStar_List.fold_left (fun l _57_3372 -> (match (_57_3372) with
| (lid, fml) -> begin
(

let _57_3373 = (let _147_1569 = (FStar_Syntax_Print.term_to_string fml)
in (FStar_Util.print1 "Checking tc_assume for axiom:%s\n" _147_1569))
in (

let se = (tc_assume env lid fml [] dr)
in (FStar_List.append l ((se)::[]))))
end)) [] axioms)
in (let _147_1571 = (let _147_1570 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append (FStar_List.append tcs datas) ses), quals, lids, _147_1570))
in FStar_Syntax_Syntax.Sig_bundle (_147_1571)))))))
end))))
end))))))
end else begin
sig_bndle
end))))
end)))))))
end))
end))
end)))
end)))))))))


let rec tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.env) = (fun env se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let se = (tc_lex_t env ses quals lids)
in (let _147_1576 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _147_1576))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let se = (tc_inductive env ses quals lids)
in (let _147_1577 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _147_1577))))
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

let _57_3414 = (set_options FStar_Options.Set o)
in (se, env))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(

let _57_3418 = (let _147_1582 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _147_1582 Prims.ignore))
in (

let _57_3423 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _57_3425 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (se, env))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(

let ne = (tc_eff_decl env ne ForFree)
in (

let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(

let ne = (tc_eff_decl env ne NotForFree)
in (

let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(

let _57_3447 = (let _147_1583 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _147_1583))
in (match (_57_3447) with
| (a, wp_a_src) -> begin
(

let _57_3450 = (let _147_1584 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _147_1584))
in (match (_57_3450) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _147_1588 = (let _147_1587 = (let _147_1586 = (let _147_1585 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _147_1585))
in FStar_Syntax_Syntax.NT (_147_1586))
in (_147_1587)::[])
in (FStar_Syntax_Subst.subst _147_1588 wp_b_tgt))
in (

let expected_k = (let _147_1593 = (let _147_1591 = (FStar_Syntax_Syntax.mk_binder a)
in (let _147_1590 = (let _147_1589 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_147_1589)::[])
in (_147_1591)::_147_1590))
in (let _147_1592 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _147_1593 _147_1592)))
in (

let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (

let sub = (

let _57_3454 = sub
in {FStar_Syntax_Syntax.source = _57_3454.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _57_3454.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
in (

let se = FStar_Syntax_Syntax.Sig_sub_effect ((sub, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(

let _57_3467 = ()
in (

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _57_3473 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_57_3473) with
| (tps, c) -> begin
(

let _57_3477 = (tc_tparams env tps)
in (match (_57_3477) with
| (tps, env, us) -> begin
(

let _57_3481 = (tc_comp env c)
in (match (_57_3481) with
| (c, u, g) -> begin
(

let _57_3482 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let _57_3488 = (let _147_1594 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _147_1594))
in (match (_57_3488) with
| (uvs, t) -> begin
(

let _57_3507 = (match ((let _147_1596 = (let _147_1595 = (FStar_Syntax_Subst.compress t)
in _147_1595.FStar_Syntax_Syntax.n)
in (tps, _147_1596))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_57_3491, c)) -> begin
([], c)
end
| (_57_3497, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _57_3504 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_3507) with
| (tps, c) -> begin
(

let se = FStar_Syntax_Syntax.Sig_effect_abbrev ((lid, uvs, tps, c, tags, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 se)
in (se, env)))
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

let _57_3518 = ()
in (

let _57_3522 = (let _147_1598 = (let _147_1597 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _147_1597))
in (check_and_gen env t _147_1598))
in (match (_57_3522) with
| (uvs, t) -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(

let se = (tc_assume env lid phi quals r)
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (

let _57_3542 = (tc_term env e)
in (match (_57_3542) with
| (e, c, g1) -> begin
(

let _57_3547 = (let _147_1602 = (let _147_1599 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_147_1599))
in (let _147_1601 = (let _147_1600 = (c.FStar_Syntax_Syntax.comp ())
in (e, _147_1600))
in (check_expected_effect env _147_1602 _147_1601)))
in (match (_57_3547) with
| (e, _57_3545, g) -> begin
(

let _57_3548 = (let _147_1603 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _147_1603))
in (

let se = FStar_Syntax_Syntax.Sig_main ((e, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
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
(let _147_1615 = (let _147_1614 = (let _147_1613 = (let _147_1612 = (FStar_Syntax_Print.lid_to_string l)
in (let _147_1611 = (FStar_Syntax_Print.quals_to_string q)
in (let _147_1610 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _147_1612 _147_1611 _147_1610))))
in (_147_1613, r))
in FStar_Syntax_Syntax.Error (_147_1614))
in (Prims.raise _147_1615))
end
end))
in (

let _57_3592 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _57_3569 lb -> (match (_57_3569) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _57_3588 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (

let _57_3583 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _57_3582 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _147_1618 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _147_1618, quals_opt))))
end)
in (match (_57_3588) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_57_3592) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _57_11 -> (match (_57_11) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _57_3601 -> begin
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

let e = (let _147_1622 = (let _147_1621 = (let _147_1620 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _147_1620))
in FStar_Syntax_Syntax.Tm_let (_147_1621))
in (FStar_Syntax_Syntax.mk _147_1622 None r))
in (

let _57_3635 = (match ((tc_maybe_toplevel_term (

let _57_3605 = env
in {FStar_TypeChecker_Env.solver = _57_3605.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3605.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3605.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3605.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3605.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3605.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3605.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3605.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3605.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3605.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3605.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _57_3605.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _57_3605.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3605.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3605.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3605.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3605.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3605.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3605.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _57_3612; FStar_Syntax_Syntax.pos = _57_3610; FStar_Syntax_Syntax.vars = _57_3608}, _57_3619, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_57_3623, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _57_3629 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _57_3632 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_57_3635) with
| (se, lbs) -> begin
(

let _57_3641 = if (log env) then begin
(let _147_1630 = (let _147_1629 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _147_1626 = (let _147_1625 = (let _147_1624 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _147_1624.FStar_Syntax_Syntax.fv_name)
in _147_1625.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _147_1626))) with
| None -> begin
true
end
| _57_3639 -> begin
false
end)
in if should_log then begin
(let _147_1628 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _147_1627 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _147_1628 _147_1627)))
end else begin
""
end))))
in (FStar_All.pipe_right _147_1629 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _147_1630))
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end))))
end))


let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _57_12 -> (match (_57_12) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _57_3651 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _57_3661 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_57_3663) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _57_3674, _57_3676) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _57_3682 -> (match (_57_3682) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _57_3688, _57_3690, quals, r) -> begin
(

let dec = (let _147_1646 = (let _147_1645 = (let _147_1644 = (let _147_1643 = (let _147_1642 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _147_1642))
in FStar_Syntax_Syntax.Tm_arrow (_147_1643))
in (FStar_Syntax_Syntax.mk _147_1644 None r))
in (l, us, _147_1645, (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_147_1646))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _57_3700, _57_3702, _57_3704, _57_3706, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _57_3712 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_57_3714, _57_3716, quals, _57_3719) -> begin
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
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _57_13 -> (match (_57_13) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _57_3738 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_57_3740) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _57_3759, _57_3761, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
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
(let _147_1653 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _147_1652 = (let _147_1651 = (let _147_1650 = (let _147_1649 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _147_1649.FStar_Syntax_Syntax.fv_name)
in _147_1650.FStar_Syntax_Syntax.v)
in (_147_1651, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_147_1652)))))
in (_147_1653, hidden))
end else begin
((se)::[], hidden)
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let _57_3800 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _57_3781 se -> (match (_57_3781) with
| (ses, exports, env, hidden) -> begin
(

let _57_3783 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_1660 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _147_1660))
end else begin
()
end
in (

let _57_3787 = (tc_decl env se)
in (match (_57_3787) with
| (se, env) -> begin
(

let _57_3788 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _147_1661 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _147_1661))
end else begin
()
end
in (

let _57_3790 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (

let _57_3794 = (for_export hidden se)
in (match (_57_3794) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_57_3800) with
| (ses, exports, env, _57_3799) -> begin
(let _147_1662 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _147_1662, env))
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
in (let _147_1667 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _57_3805.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3805.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3805.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3805.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3805.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3805.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3805.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3805.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3805.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3805.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3805.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3805.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3805.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_3805.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_3805.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3805.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _147_1667; FStar_TypeChecker_Env.type_of = _57_3805.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3805.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3805.FStar_TypeChecker_Env.use_bv_sorts}))
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
in (let _147_1680 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _147_1680 Prims.ignore)))))
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
(let _147_1689 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _147_1689))
end else begin
()
end
in (

let env = (

let _57_3852 = env
in {FStar_TypeChecker_Env.solver = _57_3852.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3852.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3852.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3852.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3852.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3852.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3852.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3852.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3852.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3852.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3852.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3852.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3852.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_3852.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3852.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3852.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3852.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3852.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3852.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3852.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_3868 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _57_3860) -> begin
(let _147_1694 = (let _147_1693 = (let _147_1692 = (FStar_TypeChecker_Env.get_range env)
in ((Prims.strcat "Implicit argument: " msg), _147_1692))
in FStar_Syntax_Syntax.Error (_147_1693))
in (Prims.raise _147_1694))
end
in (match (_57_3868) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(t, c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(let _147_1699 = (let _147_1698 = (let _147_1697 = (let _147_1695 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _147_1695))
in (let _147_1696 = (FStar_TypeChecker_Env.get_range env)
in (_147_1697, _147_1696)))
in FStar_Syntax_Syntax.Error (_147_1698))
in (Prims.raise _147_1699))
end
end)))))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

let _57_3871 = if (FStar_Options.debug_any ()) then begin
(let _147_1704 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _147_1704))
end else begin
()
end
in (

let _57_3875 = (tc_modul env m)
in (match (_57_3875) with
| (m, env) -> begin
(

let _57_3876 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _147_1705 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _147_1705))
end else begin
()
end
in (m, env))
end))))




