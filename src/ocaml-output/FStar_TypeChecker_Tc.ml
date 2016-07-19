
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
in {FStar_TypeChecker_Env.solver = _58_19.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_19.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_19.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_19.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_19.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_19.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_19.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_19.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_19.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _58_19.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_19.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_19.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_19.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_19.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_19.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_19.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_19.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _58_19.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_19.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_19.FStar_TypeChecker_Env.use_bv_sorts}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _58_22 = env
in {FStar_TypeChecker_Env.solver = _58_22.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_22.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_22.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_22.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_22.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_22.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_22.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_22.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_22.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _58_22.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_22.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_22.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_22.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_22.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_22.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_22.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_22.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _58_22.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_22.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_22.FStar_TypeChecker_Env.use_bv_sorts}))


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


let steps : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Normalize.step Prims.list = (fun env -> if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
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

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _150_85 = if (not ((FStar_Syntax_Util.is_pure_or_ghost_function t))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _150_85))
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
(let _150_87 = (FStar_Syntax_Print.term_to_string t)
in (let _150_86 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _150_87 _150_86)))
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
(let _150_89 = (FStar_Syntax_Print.term_to_string t)
in (let _150_88 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _150_89 _150_88)))
end else begin
()
end
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let _58_111 = (let _150_95 = (FStar_All.pipe_left (fun _150_94 -> Some (_150_94)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _150_95 env e lc g))
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
(let _150_96 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _150_96))
end else begin
()
end
in ((e), (lc), (g)))
end)))))


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


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _58_131 -> (match (_58_131) with
| (e, c) -> begin
(

let expected_c_opt = (match (copt) with
| Some (_58_133) -> begin
copt
end
| None -> begin
if ((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Syntax_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) then begin
(let _150_109 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (_150_109))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
if (FStar_Syntax_Util.is_pure_comp c) then begin
(let _150_110 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (_150_110))
end else begin
if (FStar_Syntax_Util.is_pure_or_ghost_comp c) then begin
(let _150_111 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (_150_111))
end else begin
None
end
end
end
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _150_112 = (norm_c env c)
in ((e), (_150_112), (FStar_TypeChecker_Rel.trivial_guard)))
end
| Some (expected_c) -> begin
(

let _58_140 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_115 = (FStar_Syntax_Print.term_to_string e)
in (let _150_114 = (FStar_Syntax_Print.comp_to_string c)
in (let _150_113 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _150_115 _150_114 _150_113))))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _58_143 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_118 = (FStar_Syntax_Print.term_to_string e)
in (let _150_117 = (FStar_Syntax_Print.comp_to_string c)
in (let _150_116 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _150_118 _150_117 _150_116))))
end else begin
()
end
in (

let _58_149 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_58_149) with
| (e, _58_147, g) -> begin
(

let g = (let _150_119 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _150_119 "could not prove post-condition" g))
in (

let _58_151 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_121 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _150_120 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _150_121 _150_120)))
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
(let _150_127 = (let _150_126 = (let _150_125 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _150_124 = (FStar_TypeChecker_Env.get_range env)
in ((_150_125), (_150_124))))
in FStar_Syntax_Syntax.Error (_150_126))
in (Prims.raise _150_127))
end)
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _150_130 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _150_130))
end))


let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _58_182; FStar_Syntax_Syntax.result_typ = _58_180; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, _58_174))::[]; FStar_Syntax_Syntax.flags = _58_171}) -> begin
(

let pat_vars = (FStar_Syntax_Free.names pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _58_189 -> (match (_58_189) with
| (b, _58_188) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _58_193) -> begin
(let _150_137 = (let _150_136 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _150_136))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _150_137))
end))
end
| _58_197 -> begin
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

let _58_204 = env
in {FStar_TypeChecker_Env.solver = _58_204.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_204.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_204.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_204.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_204.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_204.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_204.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_204.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_204.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_204.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_204.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_204.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _58_204.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_204.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_204.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_204.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_204.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _58_204.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_204.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_204.FStar_TypeChecker_Env.use_bv_sorts})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _58_216 -> (match (_58_216) with
| (b, _58_215) -> begin
(

let t = (let _150_151 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _150_151))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _58_225 -> begin
(let _150_152 = (FStar_Syntax_Syntax.bv_to_name b)
in (_150_152)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let _58_231 = (FStar_Syntax_Util.head_and_args dec)
in (match (_58_231) with
| (head, _58_230) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _58_235 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _58_3 -> (match (_58_3) with
| FStar_Syntax_Syntax.DECREASES (_58_239) -> begin
true
end
| _58_242 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _58_247 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| _58_252 -> begin
(mk_lex_list xs)
end))
end)))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun _58_257 -> (match (_58_257) with
| (l, t) -> begin
(match ((let _150_158 = (FStar_Syntax_Subst.compress t)
in _150_158.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _58_264 -> (match (_58_264) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _150_162 = (let _150_161 = (let _150_160 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_150_160))
in (FStar_Syntax_Syntax.new_bv _150_161 x.FStar_Syntax_Syntax.sort))
in ((_150_162), (imp)))
end else begin
((x), (imp))
end
end))))
in (

let _58_268 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_58_268) with
| (formals, c) -> begin
(

let dec = (decreases_clause formals c)
in (

let precedes = (let _150_166 = (let _150_165 = (FStar_Syntax_Syntax.as_arg dec)
in (let _150_164 = (let _150_163 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_150_163)::[])
in (_150_165)::_150_164))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _150_166 None r))
in (

let _58_275 = (FStar_Util.prefix formals)
in (match (_58_275) with
| (bs, (last, imp)) -> begin
(

let last = (

let _58_276 = last
in (let _150_167 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _58_276.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_276.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_167}))
in (

let refined_formals = (FStar_List.append bs ((((last), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (

let _58_281 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_170 = (FStar_Syntax_Print.lbname_to_string l)
in (let _150_169 = (FStar_Syntax_Print.term_to_string t)
in (let _150_168 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _150_170 _150_169 _150_168))))
end else begin
()
end
in ((l), (t'))))))
end))))
end)))
end
| _58_284 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end))


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let _58_287 = env
in {FStar_TypeChecker_Env.solver = _58_287.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_287.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_287.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_287.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_287.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_287.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_287.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_287.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_287.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_287.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_287.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_287.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_287.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_287.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_287.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_287.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_287.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _58_287.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_287.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_287.FStar_TypeChecker_Env.use_bv_sorts}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (

let _58_292 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_240 = (let _150_238 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _150_238))
in (let _150_239 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _150_240 _150_239)))
end else begin
()
end
in (

let top = e
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_58_296) -> begin
(let _150_244 = (FStar_Syntax_Subst.compress e)
in (tc_term env _150_244))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let _58_337 = (tc_tot_or_gtot_term env e)
in (match (_58_337) with
| (e, c, g) -> begin
(

let g = (

let _58_338 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_338.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_338.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_338.FStar_TypeChecker_Env.implicits})
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let _58_348 = (FStar_Syntax_Util.type_u ())
in (match (_58_348) with
| (t, u) -> begin
(

let _58_352 = (tc_check_tot_or_gtot_term env e t)
in (match (_58_352) with
| (e, c, g) -> begin
(

let _58_359 = (

let _58_356 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_356) with
| (env, _58_355) -> begin
(tc_pats env pats)
end))
in (match (_58_359) with
| (pats, g') -> begin
(

let g' = (

let _58_360 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_360.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_360.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_360.FStar_TypeChecker_Env.implicits})
in (let _150_246 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_pattern (pats))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _150_245 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((_150_246), (c), (_150_245)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _150_247 = (FStar_Syntax_Subst.compress e)
in _150_247.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_58_369, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _58_376; FStar_Syntax_Syntax.lbtyp = _58_374; FStar_Syntax_Syntax.lbeff = _58_372; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _58_387 = (let _150_248 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _150_248 e1))
in (match (_58_387) with
| (e1, c1, g1) -> begin
(

let _58_391 = (tc_term env e2)
in (match (_58_391) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((None), (c2)))
in (

let e = (let _150_253 = (let _150_252 = (let _150_251 = (let _150_250 = (let _150_249 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_TypeChecker_Common.t_unit), (e1)))
in (_150_249)::[])
in ((false), (_150_250)))
in ((_150_251), (e2)))
in FStar_Syntax_Syntax.Tm_let (_150_252))
in (FStar_Syntax_Syntax.mk _150_253 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _150_254 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e), (c), (_150_254))))))
end))
end))
end
| _58_396 -> begin
(

let _58_400 = (tc_term env e)
in (match (_58_400) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let _58_409 = (tc_term env e)
in (match (_58_409) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (m)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _58_415) -> begin
(

let _58_421 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_421) with
| (env0, _58_420) -> begin
(

let _58_426 = (tc_comp env0 expected_c)
in (match (_58_426) with
| (expected_c, _58_424, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (

let _58_431 = (let _150_255 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term _150_255 e))
in (match (_58_431) with
| (e, c', g') -> begin
(

let _58_435 = (let _150_257 = (let _150_256 = (c'.FStar_Syntax_Syntax.comp ())
in ((e), (_150_256)))
in (check_expected_effect env0 (Some (expected_c)) _150_257))
in (match (_58_435) with
| (e, expected_c, g'') -> begin
(let _150_260 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t_res)), (Some ((FStar_Syntax_Util.comp_effect_name expected_c)))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _150_259 = (let _150_258 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _150_258))
in ((_150_260), ((FStar_Syntax_Util.lcomp_of_comp expected_c)), (_150_259))))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _58_440) -> begin
(

let _58_445 = (FStar_Syntax_Util.type_u ())
in (match (_58_445) with
| (k, u) -> begin
(

let _58_450 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_450) with
| (t, _58_448, f) -> begin
(

let _58_454 = (let _150_261 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _150_261 e))
in (match (_58_454) with
| (e, c, g) -> begin
(

let _58_458 = (let _150_265 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_455 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _150_265 e c f))
in (match (_58_458) with
| (c, f) -> begin
(

let _58_462 = (let _150_266 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t)), (Some (c.FStar_Syntax_Syntax.eff_name))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _150_266 c))
in (match (_58_462) with
| (e, c, f2) -> begin
(let _150_268 = (let _150_267 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _150_267))
in ((e), (c), (_150_268)))
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

let _58_498 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_498) with
| (unary_op, _58_497) -> begin
(

let head = (let _150_269 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (Prims.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) None _150_269))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), (rest)))) None top.FStar_Syntax_Syntax.pos)
in (tc_term env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _58_506; FStar_Syntax_Syntax.pos = _58_504; FStar_Syntax_Syntax.vars = _58_502}, ((e, aqual))::[]) -> begin
(

let _58_516 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end else begin
()
end
in (

let _58_525 = (

let _58_521 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_521) with
| (env0, _58_520) -> begin
(tc_term env0 e)
end))
in (match (_58_525) with
| (e, c, g) -> begin
(

let _58_529 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_529) with
| (reify_op, _58_528) -> begin
(

let u_c = (

let _58_535 = (tc_term env c.FStar_Syntax_Syntax.res_typ)
in (match (_58_535) with
| (_58_531, c, _58_534) -> begin
(match ((let _150_270 = (FStar_Syntax_Subst.compress c.FStar_Syntax_Syntax.res_typ)
in _150_270.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| _58_539 -> begin
(FStar_All.failwith "Unexpected result type of computation")
end)
end))
in (

let repr = (FStar_TypeChecker_Util.reify_comp env c u_c)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e), (aqual)))::[])))) (Some (repr.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let c = (let _150_271 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right _150_271 FStar_Syntax_Util.lcomp_of_comp))
in (

let _58_547 = (comp_check_expected_typ env e c)
in (match (_58_547) with
| (e, c, g') -> begin
(let _150_272 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), (c), (_150_272)))
end))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.tk = _58_553; FStar_Syntax_Syntax.pos = _58_551; FStar_Syntax_Syntax.vars = _58_549}, ((e, aqual))::[]) -> begin
(

let _58_564 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end else begin
()
end
in (

let no_reflect = (fun _58_567 -> (match (()) with
| () -> begin
(let _150_277 = (let _150_276 = (let _150_275 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((_150_275), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_276))
in (Prims.raise _150_277))
end))
in (

let _58_571 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_571) with
| (reflect_op, _58_570) -> begin
(match ((FStar_TypeChecker_Env.effect_decl_opt env l)) with
| None -> begin
(no_reflect ())
end
| Some (ed) -> begin
if (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable)))) then begin
(no_reflect ())
end else begin
(

let _58_577 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_577) with
| (env_no_ex, topt) -> begin
(

let _58_605 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (let _150_283 = (let _150_282 = (let _150_281 = (let _150_280 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _150_279 = (let _150_278 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (_150_278)::[])
in (_150_280)::_150_279))
in ((repr), (_150_281)))
in FStar_Syntax_Syntax.Tm_app (_150_282))
in (FStar_Syntax_Syntax.mk _150_283 None top.FStar_Syntax_Syntax.pos))
in (

let _58_585 = (let _150_285 = (let _150_284 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _150_284 Prims.fst))
in (tc_tot_or_gtot_term _150_285 t))
in (match (_58_585) with
| (t, _58_583, g) -> begin
(match ((let _150_286 = (FStar_Syntax_Subst.compress t)
in _150_286.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_58_587, ((res, _58_594))::((wp, _58_590))::[]) -> begin
((t), (res), (wp), (g))
end
| _58_600 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))
in (match (_58_605) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let _58_619 = (

let _58_609 = (tc_tot_or_gtot_term env_no_ex e)
in (match (_58_609) with
| (e, c, g) -> begin
(

let _58_610 = if (let _150_287 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation _150_287)) then begin
(FStar_TypeChecker_Errors.add_errors env (((("Expected Tot, got a GTot computation"), (e.FStar_Syntax_Syntax.pos)))::[]))
end else begin
()
end
in (match ((FStar_TypeChecker_Rel.try_teq env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)) with
| None -> begin
(

let _58_613 = (let _150_292 = (let _150_291 = (let _150_290 = (let _150_289 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _150_288 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" _150_289 _150_288)))
in ((_150_290), (e.FStar_Syntax_Syntax.pos)))
in (_150_291)::[])
in (FStar_TypeChecker_Errors.add_errors env _150_292))
in (let _150_293 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e), (_150_293))))
end
| Some (g') -> begin
(let _150_295 = (let _150_294 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' _150_294))
in ((e), (_150_295)))
end))
end))
in (match (_58_619) with
| (e, g) -> begin
(

let c = (let _150_299 = (let _150_298 = (let _150_297 = (let _150_296 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_296)::[])
in {FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = _150_297; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp _150_298))
in (FStar_All.pipe_right _150_299 FStar_Syntax_Util.lcomp_of_comp))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e), (aqual)))::[])))) (Some (res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let _58_625 = (comp_check_expected_typ env e c)
in (match (_58_625) with
| (e, c, g') -> begin
(let _150_300 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e), (c), (_150_300)))
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

let env = (let _150_302 = (let _150_301 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _150_301 Prims.fst))
in (FStar_All.pipe_right _150_302 instantiate_both))
in (

let _58_632 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_304 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _150_303 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _150_304 _150_303)))
end else begin
()
end
in (

let _58_637 = (tc_term (no_inst env) head)
in (match (_58_637) with
| (head, chead, g_head) -> begin
(

let _58_641 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _150_305 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _150_305))
end else begin
(let _150_306 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _150_306))
end
in (match (_58_641) with
| (e, c, g) -> begin
(

let _58_642 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_307 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _150_307))
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

let _58_648 = (comp_check_expected_typ env0 e c)
in (match (_58_648) with
| (e, c, g') -> begin
(

let gimp = (match ((let _150_308 = (FStar_Syntax_Subst.compress head)
in _150_308.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _58_651) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e), (c.FStar_Syntax_Syntax.res_typ), (head.FStar_Syntax_Syntax.pos))
in (

let _58_655 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_655.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_655.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_655.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _58_658 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (

let gres = (let _150_309 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _150_309))
in (

let _58_661 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_311 = (FStar_Syntax_Print.term_to_string e)
in (let _150_310 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" _150_311 _150_310)))
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

let _58_669 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_669) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let _58_674 = (tc_term env1 e1)
in (match (_58_674) with
| (e1, c1, g1) -> begin
(

let _58_685 = (match (topt) with
| Some (t) -> begin
((env), (t))
end
| None -> begin
(

let _58_681 = (FStar_Syntax_Util.type_u ())
in (match (_58_681) with
| (k, _58_680) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _150_312 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in ((_150_312), (res_t))))
end))
end)
in (match (_58_685) with
| (env_branches, res_t) -> begin
(

let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let _58_702 = (

let _58_699 = (FStar_List.fold_right (fun _58_693 _58_696 -> (match (((_58_693), (_58_696))) with
| ((_58_689, f, c, g), (caccum, gaccum)) -> begin
(let _150_315 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (_150_315)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_58_699) with
| (cases, g) -> begin
(let _150_316 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in ((_150_316), (g)))
end))
in (match (_58_702) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (guard_x)), (c_branches)))
in (

let e = (let _150_320 = (let _150_319 = (let _150_318 = (FStar_List.map (fun _58_711 -> (match (_58_711) with
| (f, _58_706, _58_708, _58_710) -> begin
f
end)) t_eqns)
in ((e1), (_150_318)))
in FStar_Syntax_Syntax.Tm_match (_150_319))
in (FStar_Syntax_Syntax.mk _150_320 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (Some (cres.FStar_Syntax_Syntax.eff_name))))) None e.FStar_Syntax_Syntax.pos)
in (

let _58_714 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_323 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _150_322 = (let _150_321 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _150_321))
in (FStar_Util.print2 "(%s) comp type = %s\n" _150_323 _150_322)))
end else begin
()
end
in (let _150_324 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e), (cres), (_150_324)))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_726); FStar_Syntax_Syntax.lbunivs = _58_724; FStar_Syntax_Syntax.lbtyp = _58_722; FStar_Syntax_Syntax.lbeff = _58_720; FStar_Syntax_Syntax.lbdef = _58_718})::[]), _58_732) -> begin
(

let _58_735 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_325 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _150_325))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _58_739), _58_742) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_757); FStar_Syntax_Syntax.lbunivs = _58_755; FStar_Syntax_Syntax.lbtyp = _58_753; FStar_Syntax_Syntax.lbeff = _58_751; FStar_Syntax_Syntax.lbdef = _58_749})::_58_747), _58_763) -> begin
(

let _58_766 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_326 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _150_326))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _58_770), _58_773) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let _58_787 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_787) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _150_340 = (let _150_339 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_339))
in FStar_Util.Inr (_150_340))
end
in (

let is_data_ctor = (fun _58_4 -> (match (_58_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _58_797 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _150_346 = (let _150_345 = (let _150_344 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _150_343 = (FStar_TypeChecker_Env.get_range env)
in ((_150_344), (_150_343))))
in FStar_Syntax_Syntax.Error (_150_345))
in (Prims.raise _150_346))
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

let g = (match ((let _150_347 = (FStar_Syntax_Subst.compress t1)
in _150_347.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_808) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _58_811 -> begin
(

let imp = (("uvar in term"), (env), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let _58_813 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_813.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_813.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_813.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _58_819 = (FStar_Syntax_Util.type_u ())
in (match (_58_819) with
| (k, u) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _58_825 = (FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
in (match (_58_825) with
| (t, _58_823, g0) -> begin
(

let _58_830 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (_58_830) with
| (e, _58_828, g1) -> begin
(let _150_348 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) _150_348))
end))
end)))
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

let _58_834 = x
in {FStar_Syntax_Syntax.ppname = _58_834.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_834.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let _58_840 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_840) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _150_350 = (let _150_349 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_349))
in FStar_Util.Inr (_150_350))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _58_847; FStar_Syntax_Syntax.pos = _58_845; FStar_Syntax_Syntax.vars = _58_843}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let _58_857 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_857) with
| (us', t) -> begin
(

let _58_864 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _150_353 = (let _150_352 = (let _150_351 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (_150_351)))
in FStar_Syntax_Syntax.Error (_150_352))
in (Prims.raise _150_353))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _58_863 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (

let fv' = (

let _58_866 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _58_868 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_868.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_868.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_866.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_866.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _150_356 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_356 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let _58_876 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_876) with
| (us, t) -> begin
(

let fv' = (

let _58_877 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _58_879 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_879.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_879.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_877.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_877.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _150_357 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_357 us))
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

let _58_893 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_893) with
| (bs, c) -> begin
(

let env0 = env
in (

let _58_898 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_898) with
| (env, _58_897) -> begin
(

let _58_903 = (tc_binders env bs)
in (match (_58_903) with
| (bs, env, g, us) -> begin
(

let _58_907 = (tc_comp env c)
in (match (_58_907) with
| (c, uc, f) -> begin
(

let e = (

let _58_908 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _58_908.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_908.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_908.FStar_Syntax_Syntax.vars})
in (

let _58_911 = (check_smt_pat env e bs c)
in (

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _150_358 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _150_358))
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

let _58_927 = (let _150_360 = (let _150_359 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_359)::[])
in (FStar_Syntax_Subst.open_term _150_360 phi))
in (match (_58_927) with
| (x, phi) -> begin
(

let env0 = env
in (

let _58_932 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_932) with
| (env, _58_931) -> begin
(

let _58_937 = (let _150_361 = (FStar_List.hd x)
in (tc_binder env _150_361))
in (match (_58_937) with
| (x, env, f1, u) -> begin
(

let _58_938 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_364 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _150_363 = (FStar_Syntax_Print.term_to_string phi)
in (let _150_362 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _150_364 _150_363 _150_362))))
end else begin
()
end
in (

let _58_943 = (FStar_Syntax_Util.type_u ())
in (match (_58_943) with
| (t_phi, _58_942) -> begin
(

let _58_948 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_58_948) with
| (phi, _58_946, f2) -> begin
(

let e = (

let _58_949 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _58_949.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_949.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_949.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _150_365 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _150_365))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _58_957) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (

let _58_963 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_366 = (FStar_Syntax_Print.term_to_string (

let _58_961 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))); FStar_Syntax_Syntax.tk = _58_961.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _58_961.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_961.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _150_366))
end else begin
()
end
in (

let _58_967 = (FStar_Syntax_Subst.open_term bs body)
in (match (_58_967) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _58_969 -> begin
(let _150_368 = (let _150_367 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _150_367))
in (FStar_All.failwith _150_368))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_58_974) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_58_977, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_58_982, Some (_58_984)) -> begin
(FStar_All.failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (_58_989) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_58_992) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_58_995) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_58_999) -> begin
FStar_TypeChecker_Common.t_range
end
| _58_1002 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(

let _58_1010 = (FStar_Syntax_Util.type_u ())
in (match (_58_1010) with
| (k, u) -> begin
(

let _58_1015 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_1015) with
| (t, _58_1013, g) -> begin
(let _150_373 = (FStar_Syntax_Syntax.mk_Total t)
in ((_150_373), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(

let _58_1020 = (FStar_Syntax_Util.type_u ())
in (match (_58_1020) with
| (k, u) -> begin
(

let _58_1025 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_1025) with
| (t, _58_1023, g) -> begin
(let _150_374 = (FStar_Syntax_Syntax.mk_GTotal t)
in ((_150_374), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (

let tc = (let _150_376 = (let _150_375 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_150_375)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _150_376 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let _58_1034 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_58_1034) with
| (tc, _58_1032, f) -> begin
(

let _58_1038 = (FStar_Syntax_Util.head_and_args tc)
in (match (_58_1038) with
| (_58_1036, args) -> begin
(

let _58_1041 = (let _150_378 = (FStar_List.hd args)
in (let _150_377 = (FStar_List.tl args)
in ((_150_378), (_150_377))))
in (match (_58_1041) with
| (res, args) -> begin
(

let _58_1057 = (let _150_380 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _58_5 -> (match (_58_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _58_1048 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1048) with
| (env, _58_1047) -> begin
(

let _58_1053 = (tc_tot_or_gtot_term env e)
in (match (_58_1053) with
| (e, _58_1051, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e)), (g))
end))
end))
end
| f -> begin
((f), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right _150_380 FStar_List.unzip))
in (match (_58_1057) with
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
| _58_1068 -> begin
(FStar_All.failwith "Impossible:Unexpected sort for computation")
end)))
end
| _58_1070 -> begin
(FStar_All.failwith "Impossible:Unexpected sort for computation")
end)
in (let _150_382 = (FStar_Syntax_Syntax.mk_Comp (

let _58_1072 = c
in {FStar_Syntax_Syntax.effect_name = _58_1072.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _58_1072.FStar_Syntax_Syntax.flags}))
in (let _150_381 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((_150_382), (u), (_150_381)))))
end))
end))
end))
end))))
end)))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_58_1080) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _150_387 = (aux u)
in FStar_Syntax_Syntax.U_succ (_150_387))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _150_388 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_150_388))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _150_392 = (let _150_391 = (let _150_390 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _150_389 = (FStar_TypeChecker_Env.get_range env)
in ((_150_390), (_150_389))))
in FStar_Syntax_Syntax.Error (_150_391))
in (Prims.raise _150_392))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _150_393 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_393 Prims.snd))
end
| _58_1095 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _150_402 = (let _150_401 = (let _150_400 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in ((_150_400), (top.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_401))
in (Prims.raise _150_402)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun _58_1113 bs bs_expected -> (match (_58_1113) with
| (env, out, g, subst) -> begin
(match (((bs), (bs_expected))) with
| ([], []) -> begin
((env), ((FStar_List.rev out)), (None), (g), (subst))
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
(

let _58_1144 = (match (((imp), (imp'))) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _150_419 = (let _150_418 = (let _150_417 = (let _150_415 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _150_415))
in (let _150_416 = (FStar_Syntax_Syntax.range_of_bv hd)
in ((_150_417), (_150_416))))
in FStar_Syntax_Syntax.Error (_150_418))
in (Prims.raise _150_419))
end
| _58_1143 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _58_1161 = (match ((let _150_420 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _150_420.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| _58_1149 -> begin
(

let _58_1150 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_421 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _150_421))
end else begin
()
end
in (

let _58_1156 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_58_1156) with
| (t, _58_1154, g1) -> begin
(

let g2 = (let _150_423 = (FStar_TypeChecker_Env.get_range env)
in (let _150_422 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _150_423 "Type annotation on parameter incompatible with the expected type" _150_422)))
in (

let g = (let _150_424 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _150_424))
in ((t), (g))))
end)))
end)
in (match (_58_1161) with
| (t, g) -> begin
(

let hd = (

let _58_1162 = hd
in {FStar_Syntax_Syntax.ppname = _58_1162.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1162.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env = (push_binding env b)
in (

let subst = (let _150_425 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _150_425))
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

let _58_1183 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _58_1182 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (

let _58_1190 = (tc_binders env bs)
in (match (_58_1190) with
| (bs, envbody, g, _58_1189) -> begin
(

let _58_1208 = (match ((let _150_432 = (FStar_Syntax_Subst.compress body)
in _150_432.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _58_1195) -> begin
(

let _58_1202 = (tc_comp envbody c)
in (match (_58_1202) with
| (c, _58_1200, g') -> begin
(let _150_433 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((Some (c)), (body), (_150_433)))
end))
end
| _58_1204 -> begin
((None), (body), (g))
end)
in (match (_58_1208) with
| (copt, body, g) -> begin
((None), (bs), ([]), (copt), (envbody), (body), (g))
end))
end)))
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm t -> (match ((let _150_438 = (FStar_Syntax_Subst.compress t)
in _150_438.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let _58_1235 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _58_1234 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _58_1242 = (tc_binders env bs)
in (match (_58_1242) with
| (bs, envbody, g, _58_1241) -> begin
(

let _58_1246 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_58_1246) with
| (envbody, _58_1245) -> begin
((Some (((t), (true)))), (bs), ([]), (None), (envbody), (body), (g))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _58_1249) -> begin
(

let _58_1260 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_58_1260) with
| (_58_1253, bs, bs', copt, env, body, g) -> begin
((Some (((t), (false)))), (bs), (bs'), (copt), (env), (body), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _58_1267 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_58_1267) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun _58_1278 c_expected -> (match (_58_1278) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _150_449 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in ((env), (bs), (guard), (_150_449)))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (let _150_450 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _150_450))
in (let _150_451 = (FStar_Syntax_Subst.subst_comp subst c)
in ((env), (bs), (guard), (_150_451))))
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

let _58_1299 = (check_binders env more_bs bs_expected)
in (match (_58_1299) with
| (env, bs', more, guard', subst) -> begin
(let _150_453 = (let _150_452 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env), ((FStar_List.append bs bs')), (more), (_150_452), (subst)))
in (handle_more _150_453 c_expected))
end))
end
| _58_1301 -> begin
(let _150_455 = (let _150_454 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _150_454))
in (fail _150_455 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _150_456 = (check_binders env bs bs_expected)
in (handle_more _150_456 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let _58_1307 = envbody
in {FStar_TypeChecker_Env.solver = _58_1307.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1307.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1307.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1307.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1307.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1307.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1307.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1307.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1307.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1307.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1307.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1307.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _58_1307.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1307.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1307.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1307.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1307.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _58_1307.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1307.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1307.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _58_1312 _58_1315 -> (match (((_58_1312), (_58_1315))) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _58_1321 = (let _150_466 = (let _150_465 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _150_465 Prims.fst))
in (tc_term _150_466 t))
in (match (_58_1321) with
| (t, _58_1318, _58_1320) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l (([]), (t)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _150_467 = (FStar_Syntax_Syntax.mk_binder (

let _58_1325 = x
in {FStar_Syntax_Syntax.ppname = _58_1325.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1325.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_150_467)::letrec_binders)
end
| _58_1328 -> begin
letrec_binders
end)
in ((env), (lb))))
end))
end)) ((envbody), ([])))))))
in (

let _58_1334 = (check_actuals_against_formals env bs bs_expected)
in (match (_58_1334) with
| (envbody, bs, g, c) -> begin
(

let _58_1337 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
((envbody), ([]))
end
in (match (_58_1337) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in ((Some (((t), (false)))), (bs), (letrecs), (Some (c)), (envbody), (body), (g)))
end))
end))))
end))
end
| _58_1340 -> begin
if (not (norm)) then begin
(let _150_468 = (unfold_whnf env t)
in (as_function_typ true _150_468))
end else begin
(

let _58_1350 = (expected_function_typ env None body)
in (match (_58_1350) with
| (_58_1342, bs, _58_1345, c_opt, envbody, body, g) -> begin
((Some (((t), (false)))), (bs), ([]), (c_opt), (envbody), (body), (g))
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let _58_1354 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1354) with
| (env, topt) -> begin
(

let _58_1358 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_469 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _150_469 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (

let _58_1367 = (expected_function_typ env topt body)
in (match (_58_1367) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let _58_1373 = (tc_term (

let _58_1368 = envbody
in {FStar_TypeChecker_Env.solver = _58_1368.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1368.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1368.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1368.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1368.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1368.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1368.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1368.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1368.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1368.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1368.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1368.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1368.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_1368.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1368.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1368.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _58_1368.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1368.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1368.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_58_1373) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _58_1375 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _150_472 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _150_471 = (let _150_470 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _150_470))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _150_472 _150_471)))
end else begin
()
end
in (

let _58_1382 = (let _150_474 = (let _150_473 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body), (_150_473)))
in (check_expected_effect (

let _58_1377 = envbody
in {FStar_TypeChecker_Env.solver = _58_1377.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1377.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1377.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1377.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1377.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1377.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1377.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1377.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1377.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1377.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1377.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1377.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1377.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1377.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1377.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1377.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1377.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _58_1377.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1377.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1377.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _150_474))
in (match (_58_1382) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _150_475 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _150_475))
end else begin
(

let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _150_478 = (let _150_477 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _150_476 -> FStar_Util.Inl (_150_476)))
in Some (_150_477))
in (FStar_Syntax_Util.abs bs body _150_478))
in (

let _58_1405 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_58_1394) -> begin
((e), (t), (guard))
end
| _58_1397 -> begin
(

let _58_1400 = if use_teq then begin
(let _150_479 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in ((e), (_150_479)))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_58_1400) with
| (e, guard') -> begin
(let _150_480 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((e), (t), (_150_480)))
end))
end))
end
| None -> begin
((e), (tfun_computed), (guard))
end)
in (match (_58_1405) with
| (e, tfun, guard) -> begin
(

let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (

let _58_1409 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_58_1409) with
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

let _58_1419 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_489 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _150_488 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _150_489 _150_488)))
end else begin
()
end
in (

let monadic_application = (fun _58_1426 subst arg_comps_rev arg_rets guard fvs bs -> (match (_58_1426) with
| (head, chead, ghead, cres) -> begin
(

let _58_1433 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let _58_1461 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun _58_6 -> (match (_58_6) with
| (_58_1440, _58_1442, None) -> begin
false
end
| (_58_1446, _58_1448, Some (c)) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _150_505 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _150_505 cres))
end else begin
(

let _58_1453 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_508 = (FStar_Syntax_Print.term_to_string head)
in (let _150_507 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _150_506 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _150_508 _150_507 _150_506))))
end else begin
()
end
in cres)
end
in ((cres), (g))))))
end
| _58_1457 -> begin
(

let g = (let _150_509 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right _150_509 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _150_514 = (let _150_513 = (let _150_512 = (let _150_511 = (let _150_510 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _150_510))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _150_511))
in (FStar_Syntax_Syntax.mk_Total _150_512))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_513))
in ((_150_514), (g))))
end)
in (match (_58_1461) with
| (cres, guard) -> begin
(

let _58_1462 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_515 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _150_515))
end else begin
()
end
in (

let _58_1484 = (FStar_List.fold_left (fun _58_1467 _58_1473 -> (match (((_58_1467), (_58_1473))) with
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
in (match (_58_1484) with
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

let _58_1490 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (_58_1490) with
| (comp, g) -> begin
((app), (comp), (g))
end)))))
end)))
end)))
end))
in (

let rec tc_args = (fun head_info _58_1498 bs args -> (match (_58_1498) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args))) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (_58_1504))))::rest, ((_58_1512, None))::_58_1510) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _58_1518 = (check_no_escape (Some (head)) env fvs t)
in (

let _58_1524 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_58_1524) with
| (varg, _58_1522, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst
in (

let arg = (let _150_527 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (_150_527)))
in (let _150_529 = (let _150_528 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst), ((((arg), (None), (None)))::outargs), ((arg)::arg_rets), (_150_528), (fvs)))
in (tc_args head_info _150_529 rest args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
(

let _58_1556 = (match (((aqual), (aq))) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _58_1555 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifier"), (e.FStar_Syntax_Syntax.pos)))))
end)
in (

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let _58_1559 = x
in {FStar_Syntax_Syntax.ppname = _58_1559.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1559.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (

let _58_1562 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_530 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _150_530))
end else begin
()
end
in (

let _58_1564 = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let _58_1567 = env
in {FStar_TypeChecker_Env.solver = _58_1567.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1567.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1567.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1567.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1567.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1567.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1567.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1567.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1567.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1567.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1567.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1567.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1567.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1567.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1567.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _58_1567.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1567.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _58_1567.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1567.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1567.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _58_1570 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_533 = (FStar_Syntax_Print.tag_of_term e)
in (let _150_532 = (FStar_Syntax_Print.term_to_string e)
in (let _150_531 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _150_533 _150_532 _150_531))))
end else begin
()
end
in (

let _58_1575 = (tc_term env e)
in (match (_58_1575) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = ((e), (aq))
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(

let subst = (let _150_534 = (FStar_List.hd bs)
in (maybe_extend_subst subst _150_534 e))
in (tc_args head_info ((subst), ((((arg), (None), (None)))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(

let subst = (let _150_535 = (FStar_List.hd bs)
in (maybe_extend_subst subst _150_535 e))
in (tc_args head_info ((subst), ((((arg), (Some (x)), (Some (c))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (let _150_536 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _150_536)) then begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _150_537 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_537))
in (tc_args head_info ((subst), ((((arg), (Some (newx)), (Some (c))))::outargs), ((arg')::arg_rets), (g), (fvs)) rest rest')))
end else begin
(let _150_541 = (let _150_540 = (let _150_539 = (let _150_538 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _150_538))
in (_150_539)::arg_rets)
in ((subst), ((((arg), (Some (x)), (Some (c))))::outargs), (_150_540), (g), ((x)::fvs)))
in (tc_args head_info _150_541 rest rest'))
end
end
end))
end))))))))))
end
| (_58_1583, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::_58_1588) -> begin
(

let _58_1595 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (_58_1595) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _150_546 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _150_546 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let _58_1606 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (_58_1606) with
| (bs, cres') -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp cres')))
in (

let _58_1608 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_547 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _150_547))
end else begin
()
end
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args)))
end))
end
| _58_1611 when (not (norm)) -> begin
(let _150_548 = (unfold_whnf env tres)
in (aux true _150_548))
end
| _58_1613 -> begin
(let _150_554 = (let _150_553 = (let _150_552 = (let _150_550 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (let _150_549 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _150_550 _150_549)))
in (let _150_551 = (FStar_Syntax_Syntax.argpos arg)
in ((_150_552), (_150_551))))
in FStar_Syntax_Syntax.Error (_150_553))
in (Prims.raise _150_554))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (match ((let _150_559 = (FStar_Syntax_Util.unrefine tf)
in _150_559.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl -> begin
(

let _58_1646 = (tc_term env e)
in (match (_58_1646) with
| (e, c, g_e) -> begin
(

let _58_1650 = (tc_args env tl)
in (match (_58_1650) with
| (args, comps, g_rest) -> begin
(let _150_564 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e), (imp)))::args), ((((e.FStar_Syntax_Syntax.pos), (c)))::comps), (_150_564)))
end))
end))
end))
in (

let _58_1654 = (tc_args env args)
in (match (_58_1654) with
| (args, comps, g_args) -> begin
(

let bs = (let _150_566 = (FStar_All.pipe_right comps (FStar_List.map (fun _58_1658 -> (match (_58_1658) with
| (_58_1656, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks _150_566))
in (

let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _58_1664 -> begin
FStar_Syntax_Util.ml_comp
end)
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _150_581 = (FStar_Syntax_Subst.compress t)
in _150_581.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_58_1670) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _58_1675 -> begin
ml_or_tot
end)
end)
in (

let cres = (let _150_586 = (let _150_585 = (let _150_584 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_584 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _150_585))
in (ml_or_tot _150_586 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (

let _58_1679 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_589 = (FStar_Syntax_Print.term_to_string head)
in (let _150_588 = (FStar_Syntax_Print.term_to_string tf)
in (let _150_587 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _150_589 _150_588 _150_587))))
end else begin
()
end
in (

let _58_1681 = (let _150_590 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _150_590))
in (

let comp = (let _150_593 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _58_1685 out -> (match (_58_1685) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c ((None), (out)))
end)) ((((head.FStar_Syntax_Syntax.pos), (chead)))::comps) _150_593))
in (let _150_595 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _150_594 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((_150_595), (comp), (_150_594))))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _58_1694 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_1694) with
| (bs, c) -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp c)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args))
end))
end
| _58_1697 -> begin
if (not (norm)) then begin
(let _150_596 = (unfold_whnf env tf)
in (check_function_app true _150_596))
end else begin
(let _150_599 = (let _150_598 = (let _150_597 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in ((_150_597), (head.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_598))
in (Prims.raise _150_599))
end
end))
in (let _150_601 = (let _150_600 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _150_600))
in (check_function_app false _150_601))))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let _58_1733 = (FStar_List.fold_left2 (fun _58_1714 _58_1717 _58_1720 -> (match (((_58_1714), (_58_1717), (_58_1720))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(

let _58_1721 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifiers"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _58_1726 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_58_1726) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (let _150_611 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _150_611 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _150_615 = (let _150_613 = (let _150_612 = (FStar_Syntax_Syntax.as_arg e)
in (_150_612)::[])
in (FStar_List.append seen _150_613))
in (let _150_614 = (FStar_TypeChecker_Rel.conj_guard guard g)
in ((_150_615), (_150_614), (ghost)))))))
end)))
end)) (([]), (g_head), (false)) args bs)
in (match (_58_1733) with
| (args, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = if ghost then begin
(let _150_616 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _150_616 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (

let _58_1738 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_58_1738) with
| (c, g) -> begin
((e), (c), (g))
end))))
end)))
end
| _58_1740 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let _58_1747 = (FStar_Syntax_Subst.open_branch branch)
in (match (_58_1747) with
| (pattern, when_clause, branch_exp) -> begin
(

let _58_1752 = branch
in (match (_58_1752) with
| (cpat, _58_1750, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _58_1760 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_58_1760) with
| (pat_bvs, exps, p) -> begin
(

let _58_1761 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_628 = (FStar_Syntax_Print.pat_to_string p0)
in (let _150_627 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _150_628 _150_627)))
end else begin
()
end
in (

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let _58_1767 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_58_1767) with
| (env1, _58_1766) -> begin
(

let env1 = (

let _58_1768 = env1
in {FStar_TypeChecker_Env.solver = _58_1768.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1768.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1768.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1768.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1768.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1768.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1768.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1768.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _58_1768.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1768.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1768.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1768.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1768.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1768.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1768.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1768.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1768.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _58_1768.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1768.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1768.FStar_TypeChecker_Env.use_bv_sorts})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _58_1807 = (let _150_651 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _58_1773 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_631 = (FStar_Syntax_Print.term_to_string e)
in (let _150_630 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _150_631 _150_630)))
end else begin
()
end
in (

let _58_1778 = (tc_term env1 e)
in (match (_58_1778) with
| (e, lc, g) -> begin
(

let _58_1779 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_633 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _150_632 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _150_633 _150_632)))
end else begin
()
end
in (

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let _58_1785 = (let _150_634 = (FStar_TypeChecker_Rel.discharge_guard env (

let _58_1783 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_1783.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_1783.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_1783.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _150_634 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _150_639 = (let _150_638 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _150_638 (FStar_List.map (fun _58_1793 -> (match (_58_1793) with
| (u, _58_1792) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _150_639 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _58_1801 = if (let _150_640 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _150_640)) then begin
(

let unresolved = (let _150_641 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _150_641 FStar_Util.set_elements))
in (let _150_649 = (let _150_648 = (let _150_647 = (let _150_646 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _150_645 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _150_644 = (let _150_643 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _58_1800 -> (match (_58_1800) with
| (u, _58_1799) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _150_643 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _150_646 _150_645 _150_644))))
in ((_150_647), (p.FStar_Syntax_Syntax.p)))
in FStar_Syntax_Syntax.Error (_150_648))
in (Prims.raise _150_649)))
end else begin
()
end
in (

let _58_1803 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_650 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _150_650))
end else begin
()
end
in ((e), (e'))))))))))))
end))))))
in (FStar_All.pipe_right _150_651 FStar_List.unzip))
in (match (_58_1807) with
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

let _58_1814 = (let _150_652 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _150_652 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_58_1814) with
| (scrutinee_env, _58_1813) -> begin
(

let _58_1820 = (tc_pat true pat_t pattern)
in (match (_58_1820) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let _58_1830 = (match (when_clause) with
| None -> begin
((None), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("When clauses are not yet supported in --verify mode; they will be some day"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
(

let _58_1827 = (let _150_653 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _150_653 e))
in (match (_58_1827) with
| (e, c, g) -> begin
((Some (e)), (g))
end))
end
end)
in (match (_58_1830) with
| (when_clause, g_when) -> begin
(

let _58_1834 = (tc_term pat_env branch_exp)
in (match (_58_1834) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _150_655 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _150_654 -> Some (_150_654)) _150_655))
end)
in (

let _58_1890 = (

let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _58_1852 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _150_659 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _150_658 -> Some (_150_658)) _150_659))
end))
end))) None))
in (

let _58_1860 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_58_1860) with
| (c, g_branch) -> begin
(

let _58_1885 = (match (((eqs), (when_condition))) with
| (None, None) -> begin
((c), (g_when))
end
| (Some (f), None) -> begin
(

let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _150_662 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _150_661 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((_150_662), (_150_661))))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (let _150_663 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_150_663))
in (let _150_666 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _150_665 = (let _150_664 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _150_664 g_when))
in ((_150_666), (_150_665))))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _150_667 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in ((_150_667), (g_when)))))
end)
in (match (_58_1885) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _150_669 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _150_668 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in ((_150_669), (_150_668), (g_branch)))))
end))
end)))
in (match (_58_1890) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = (

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> if ((let _150_679 = (let _150_678 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _150_678))
in (FStar_List.length _150_679)) > 1) then begin
(

let disc = (let _150_680 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _150_680 FStar_Syntax_Syntax.Delta_equational None))
in (

let disc = (let _150_682 = (let _150_681 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_150_681)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _150_682 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _150_683 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_150_683)::[])))
end else begin
[]
end)
in (

let fail = (fun _58_1900 -> (match (()) with
| () -> begin
(let _150_689 = (let _150_688 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _150_687 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _150_686 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _150_688 _150_687 _150_686))))
in (FStar_All.failwith _150_689))
end))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _58_1907) -> begin
(head_constructor t)
end
| _58_1911 -> begin
(fail ())
end))
in (

let pat_exp = (let _150_692 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _150_692 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_58_1936) -> begin
(let _150_697 = (let _150_696 = (let _150_695 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _150_694 = (let _150_693 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_150_693)::[])
in (_150_695)::_150_694))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _150_696 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_150_697)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _150_698 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _150_698))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(

let sub_term_guards = (let _150_705 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _58_1954 -> (match (_58_1954) with
| (ei, _58_1953) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _58_1958 -> begin
(

let sub_term = (let _150_704 = (let _150_701 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _150_701 FStar_Syntax_Syntax.Delta_equational None))
in (let _150_703 = (let _150_702 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_150_702)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _150_704 _150_703 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _150_705 FStar_List.flatten))
in (let _150_706 = (discriminate scrutinee_tm f)
in (FStar_List.append _150_706 sub_term_guards)))
end)
end
| _58_1962 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(

let t = (let _150_711 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _150_711))
in (

let _58_1970 = (FStar_Syntax_Util.type_u ())
in (match (_58_1970) with
| (k, _58_1969) -> begin
(

let _58_1976 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_58_1976) with
| (t, _58_1973, _58_1975) -> begin
t
end))
end)))
end)
in (

let branch_guard = (let _150_712 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _150_712 FStar_Syntax_Util.mk_disj_l))
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

let _58_1984 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_713 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _150_713))
end else begin
()
end
in (let _150_714 = (FStar_Syntax_Subst.close_branch ((pattern), (when_clause), (branch_exp)))
in ((_150_714), (branch_guard), (c), (guard))))))
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

let _58_2001 = (check_let_bound_def true env lb)
in (match (_58_2001) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let _58_2013 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
((g1), (e1), (univ_vars), (c1))
end else begin
(

let g1 = (let _150_717 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _150_717 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _58_2008 = (let _150_721 = (let _150_720 = (let _150_719 = (let _150_718 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (_150_718)))
in (_150_719)::[])
in (FStar_TypeChecker_Util.generalize env _150_720))
in (FStar_List.hd _150_721))
in (match (_58_2008) with
| (_58_2004, univs, e1, c1) -> begin
((g1), (e1), (univs), ((FStar_Syntax_Util.lcomp_of_comp c1)))
end)))
end
in (match (_58_2013) with
| (g1, e1, univ_vars, c1) -> begin
(

let _58_2023 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(

let _58_2016 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_58_2016) with
| (ok, c1) -> begin
if ok then begin
((e2), (c1))
end else begin
(

let _58_2017 = if (FStar_Options.warn_top_level_effects ()) then begin
(let _150_722 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _150_722 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _150_723 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) None e2.FStar_Syntax_Syntax.pos)
in ((_150_723), (c1))))
end
end))
end else begin
(

let _58_2019 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _150_724 = (c1.FStar_Syntax_Syntax.comp ())
in ((e2), (_150_724))))
end
in (match (_58_2023) with
| (e2, c1) -> begin
(

let cres = (let _150_725 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_725))
in (

let _58_2025 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _150_726 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((_150_726), (cres), (FStar_TypeChecker_Rel.trivial_guard))))))
end))
end))
end))
end
| _58_2029 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let _58_2040 = env
in {FStar_TypeChecker_Env.solver = _58_2040.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2040.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2040.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2040.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2040.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2040.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2040.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2040.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2040.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2040.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2040.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2040.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2040.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_2040.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2040.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2040.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2040.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _58_2040.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2040.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2040.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _58_2049 = (let _150_730 = (let _150_729 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _150_729 Prims.fst))
in (check_let_bound_def false _150_730 lb))
in (match (_58_2049) with
| (e1, _58_2045, c1, g1, annotated) -> begin
(

let x = (

let _58_2050 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_2050.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2050.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let _58_2056 = (let _150_732 = (let _150_731 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_731)::[])
in (FStar_Syntax_Subst.open_term _150_732 e2))
in (match (_58_2056) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _58_2062 = (let _150_733 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _150_733 e2))
in (match (_58_2062) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (x)), (c2)))
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e2 = (FStar_TypeChecker_Util.maybe_lift env e2 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e = (let _150_736 = (let _150_735 = (let _150_734 = (FStar_Syntax_Subst.close xb e2)
in ((((false), ((lb)::[]))), (_150_734)))
in FStar_Syntax_Syntax.Tm_let (_150_735))
in (FStar_Syntax_Syntax.mk _150_736 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name)
in (

let x_eq_e1 = (let _150_739 = (let _150_738 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _150_738 e1))
in (FStar_All.pipe_left (fun _150_737 -> FStar_TypeChecker_Common.NonTrivial (_150_737)) _150_739))
in (

let g2 = (let _150_741 = (let _150_740 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _150_740 g2))
in (FStar_TypeChecker_Rel.close_guard xb _150_741))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if (let _150_742 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome _150_742)) then begin
((e), (cres), (guard))
end else begin
(

let _58_2071 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in ((e), (cres), (guard)))
end))))))))
end))))
end))))
end)))
end
| _58_2074 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _58_2086 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_58_2086) with
| (lbs, e2) -> begin
(

let _58_2089 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2089) with
| (env0, topt) -> begin
(

let _58_2092 = (build_let_rec_env true env0 lbs)
in (match (_58_2092) with
| (lbs, rec_env) -> begin
(

let _58_2095 = (check_let_recs rec_env lbs)
in (match (_58_2095) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (let _150_745 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _150_745 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _150_748 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _150_748 (fun _150_747 -> Some (_150_747))))
in (

let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(

let ecs = (let _150_752 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _150_751 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (_150_751))))))
in (FStar_TypeChecker_Util.generalize env _150_752))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _58_2106 -> (match (_58_2106) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _150_754 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_754))
in (

let _58_2109 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _58_2113 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_2113) with
| (lbs, e2) -> begin
(let _150_756 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _150_755 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in ((_150_756), (cres), (_150_755))))
end)))))))
end))
end))
end))
end))
end
| _58_2115 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _58_2127 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_58_2127) with
| (lbs, e2) -> begin
(

let _58_2130 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2130) with
| (env0, topt) -> begin
(

let _58_2133 = (build_let_rec_env false env0 lbs)
in (match (_58_2133) with
| (lbs, rec_env) -> begin
(

let _58_2136 = (check_let_recs rec_env lbs)
in (match (_58_2136) with
| (lbs, g_lbs) -> begin
(

let _58_2148 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let _58_2139 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_2139.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2139.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let _58_2142 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _58_2142.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _58_2142.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _58_2142.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _58_2142.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (lb.FStar_Syntax_Syntax.lbtyp)))
in ((env), (lb)))))) env))
in (match (_58_2148) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let _58_2154 = (tc_term env e2)
in (match (_58_2154) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _58_2158 = cres
in {FStar_Syntax_Syntax.eff_name = _58_2158.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _58_2158.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_2158.FStar_Syntax_Syntax.comp})
in (

let _58_2163 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_2163) with
| (lbs, e2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_58_2166) -> begin
((e), (cres), (guard))
end
| None -> begin
(

let _58_2169 = (check_no_escape None env bvs tres)
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
| _58_2172 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let _58_2205 = (FStar_List.fold_left (fun _58_2179 lb -> (match (_58_2179) with
| (lbs, env) -> begin
(

let _58_2184 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_58_2184) with
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

let _58_2193 = (let _150_768 = (let _150_767 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _150_767))
in (tc_check_tot_or_gtot_term (

let _58_2187 = env0
in {FStar_TypeChecker_Env.solver = _58_2187.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2187.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2187.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2187.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2187.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2187.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2187.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2187.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2187.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2187.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2187.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2187.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2187.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2187.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _58_2187.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2187.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2187.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _58_2187.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2187.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2187.FStar_TypeChecker_Env.use_bv_sorts}) t _150_768))
in (match (_58_2193) with
| (t, _58_2191, g) -> begin
(

let _58_2194 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (

let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(

let _58_2197 = env
in {FStar_TypeChecker_Env.solver = _58_2197.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2197.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2197.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2197.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2197.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2197.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2197.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2197.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2197.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2197.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2197.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2197.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t)))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2197.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_2197.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2197.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2197.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2197.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _58_2197.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2197.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2197.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (t)))
end
in (

let lb = (

let _58_2200 = lb
in {FStar_Syntax_Syntax.lbname = _58_2200.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _58_2200.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb)::lbs), (env)))))))
end))
end)) (([]), (env)) lbs)
in (match (_58_2205) with
| (lbs, env) -> begin
(((FStar_List.rev lbs)), (env))
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _58_2218 = (let _150_773 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _58_2212 = (let _150_772 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _150_772 lb.FStar_Syntax_Syntax.lbdef))
in (match (_58_2212) with
| (e, c, g) -> begin
(

let _58_2213 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in ((lb), (g))))
end)))))
in (FStar_All.pipe_right _150_773 FStar_List.unzip))
in (match (_58_2218) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _58_2226 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2226) with
| (env1, _58_2225) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _58_2232 = (check_lbtyp top_level env lb)
in (match (_58_2232) with
| (topt, wf_annot, univ_vars, env1) -> begin
(

let _58_2233 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _58_2240 = (tc_maybe_toplevel_term (

let _58_2235 = env1
in {FStar_TypeChecker_Env.solver = _58_2235.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2235.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2235.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2235.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2235.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2235.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2235.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2235.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2235.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2235.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2235.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2235.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2235.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _58_2235.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2235.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2235.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2235.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _58_2235.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2235.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2235.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_58_2240) with
| (e1, c1, g1) -> begin
(

let _58_2244 = (let _150_780 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_2241 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _150_780 e1 c1 wf_annot))
in (match (_58_2244) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _58_2246 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_781 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _150_781))
end else begin
()
end
in (let _150_782 = (FStar_Option.isSome topt)
in ((e1), (univ_vars), (c1), (g1), (_150_782)))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _58_2253 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in ((None), (FStar_TypeChecker_Rel.trivial_guard), ([]), (env)))
end
| _58_2256 -> begin
(

let _58_2259 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_58_2259) with
| (univ_vars, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _150_786 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars), (_150_786)))
end else begin
(

let _58_2264 = (FStar_Syntax_Util.type_u ())
in (match (_58_2264) with
| (k, _58_2263) -> begin
(

let _58_2269 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_58_2269) with
| (t, _58_2267, g) -> begin
(

let _58_2270 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_789 = (let _150_787 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _150_787))
in (let _150_788 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _150_789 _150_788)))
end else begin
()
end
in (

let t = (norm env1 t)
in (let _150_790 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (g), (univ_vars), (_150_790)))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _58_2276 -> (match (_58_2276) with
| (x, imp) -> begin
(

let _58_2279 = (FStar_Syntax_Util.type_u ())
in (match (_58_2279) with
| (tu, u) -> begin
(

let _58_2284 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_58_2284) with
| (t, _58_2282, g) -> begin
(

let x = (((

let _58_2285 = x
in {FStar_Syntax_Syntax.ppname = _58_2285.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2285.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in (

let _58_2288 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_794 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _150_793 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _150_794 _150_793)))
end else begin
()
end
in (let _150_795 = (push_binding env x)
in ((x), (_150_795), (g), (u)))))
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

let _58_2303 = (tc_binder env b)
in (match (_58_2303) with
| (b, env', g, u) -> begin
(

let _58_2308 = (aux env' bs)
in (match (_58_2308) with
| (bs, env', g', us) -> begin
(let _150_803 = (let _150_802 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _150_802))
in (((b)::bs), (env'), (_150_803), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun _58_2316 _58_2319 -> (match (((_58_2316), (_58_2319))) with
| ((t, imp), (args, g)) -> begin
(

let _58_2324 = (tc_term env t)
in (match (_58_2324) with
| (t, _58_2322, g') -> begin
(let _150_812 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t), (imp)))::args), (_150_812)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p _58_2328 -> (match (_58_2328) with
| (pats, g) -> begin
(

let _58_2331 = (tc_args env p)
in (match (_58_2331) with
| (args, g') -> begin
(let _150_815 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats), (_150_815)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _58_2337 = (tc_maybe_toplevel_term env e)
in (match (_58_2337) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
((e), (c), (g))
end else begin
(

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let _58_2340 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_818 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _150_818))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _58_2345 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _150_819 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in ((_150_819), (false)))
end else begin
(let _150_820 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in ((_150_820), (true)))
end
in (match (_58_2345) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _150_821 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (_150_821)))
end
| _58_2349 -> begin
if allow_ghost then begin
(let _150_824 = (let _150_823 = (let _150_822 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in ((_150_822), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_823))
in (Prims.raise _150_824))
end else begin
(let _150_827 = (let _150_826 = (let _150_825 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in ((_150_825), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_826))
in (Prims.raise _150_827))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let _58_2359 = (tc_tot_or_gtot_term env t)
in (match (_58_2359) with
| (t, c, g) -> begin
(

let _58_2360 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in ((t), (c)))
end)))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let _58_2368 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_2368) with
| (t, c, g) -> begin
(

let _58_2369 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _150_845 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _150_845)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _150_849 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (([]), (_150_849)))))


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let _58_2384 = (tc_binders env tps)
in (match (_58_2384) with
| (tps, env, g, us) -> begin
(

let _58_2385 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in ((tps), (env), (us)))
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (

let fail = (fun _58_2391 -> (match (()) with
| () -> begin
(let _150_864 = (let _150_863 = (let _150_862 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in ((_150_862), ((FStar_Ident.range_of_lid m))))
in FStar_Syntax_Syntax.Error (_150_863))
in (Prims.raise _150_864))
end))
in (

let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _58_2404))::((wp, _58_2400))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _58_2408 -> begin
(fail ())
end))
end
| _58_2410 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let _58_2417 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_58_2417) with
| (uvs, c) -> begin
((uvs), ([]), (c))
end))
end
| _58_2419 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let _58_2423 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_58_2423) with
| (uvs, t') -> begin
(match ((let _150_871 = (FStar_Syntax_Subst.compress t')
in _150_871.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
((uvs), (binders), (c))
end
| _58_2429 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))


let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (

let fail = (fun t -> (let _150_882 = (let _150_881 = (let _150_880 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in ((_150_880), ((FStar_Ident.range_of_lid mname))))
in FStar_Syntax_Syntax.Error (_150_881))
in (Prims.raise _150_882)))
in (match ((let _150_883 = (FStar_Syntax_Subst.compress signature)
in _150_883.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _58_2446))::((wp, _58_2442))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _58_2450 -> begin
(fail signature)
end))
end
| _58_2452 -> begin
(fail signature)
end)))


let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (

let _58_2457 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_58_2457) with
| (a, wp) -> begin
(

let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _58_2460 -> begin
(

let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (

let op = (fun ts -> (

let _58_2464 = ()
in (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in (([]), (t1)))))
in (

let _58_2467 = ed
in (let _150_899 = (op ed.FStar_Syntax_Syntax.ret_wp)
in (let _150_898 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _150_897 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _150_896 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _150_895 = (op ed.FStar_Syntax_Syntax.stronger)
in (let _150_894 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _150_893 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _150_892 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _150_891 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _150_890 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _58_2467.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2467.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _58_2467.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _58_2467.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _58_2467.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _150_899; FStar_Syntax_Syntax.bind_wp = _150_898; FStar_Syntax_Syntax.if_then_else = _150_897; FStar_Syntax_Syntax.ite_wp = _150_896; FStar_Syntax_Syntax.stronger = _150_895; FStar_Syntax_Syntax.close_wp = _150_894; FStar_Syntax_Syntax.assert_p = _150_893; FStar_Syntax_Syntax.assume_p = _150_892; FStar_Syntax_Syntax.null_wp = _150_891; FStar_Syntax_Syntax.trivial = _150_890; FStar_Syntax_Syntax.repr = _58_2467.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _58_2467.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _58_2467.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _58_2467.FStar_Syntax_Syntax.actions})))))))))))))
end)
in ((ed), (a), (wp)))
end)))


let rec tc_real_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  effect_cost  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed is_for_free -> (

let _58_2473 = ()
in (

let _58_2477 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_58_2477) with
| (binders_un, signature_un) -> begin
(

let _58_2482 = (tc_tparams env0 binders_un)
in (match (_58_2482) with
| (binders, env, _58_2481) -> begin
(

let _58_2486 = (tc_trivial_guard env signature_un)
in (match (_58_2486) with
| (signature, _58_2485) -> begin
(

let ed = (

let _58_2487 = ed
in {FStar_Syntax_Syntax.qualifiers = _58_2487.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2487.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _58_2487.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _58_2487.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _58_2487.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _58_2487.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _58_2487.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _58_2487.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _58_2487.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _58_2487.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _58_2487.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _58_2487.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _58_2487.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _58_2487.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _58_2487.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _58_2487.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _58_2487.FStar_Syntax_Syntax.actions})
in (

let _58_2493 = (open_effect_decl env ed)
in (match (_58_2493) with
| (ed, a, wp_a) -> begin
(

let get_effect_signature = (fun _58_2495 -> (match (()) with
| () -> begin
(

let _58_2499 = (tc_trivial_guard env signature_un)
in (match (_58_2499) with
| (signature, _58_2498) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (

let env = (let _150_928 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _150_928))
in (

let _58_2501 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _150_931 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _150_930 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _150_929 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checking effect signature: %s %s : %s\n" _150_931 _150_930 _150_929))))
end else begin
()
end
in (

let check_and_gen' = (fun env _58_2508 k -> (match (_58_2508) with
| (_58_2506, t) -> begin
(check_and_gen env t k)
end))
in (

let _58_2514 = (match (is_for_free) with
| NotForFree -> begin
((env), (ed))
end
| ForFree -> begin
(FStar_TypeChecker_DMFF.gen_wps_for_free env binders a wp_a tc_decl tc_term ed)
end)
in (match (_58_2514) with
| (env, ed) -> begin
(

let return_wp = (

let expected_k = (let _150_943 = (let _150_941 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_940 = (let _150_939 = (let _150_938 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _150_938))
in (_150_939)::[])
in (_150_941)::_150_940))
in (let _150_942 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _150_943 _150_942)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let _58_2519 = (get_effect_signature ())
in (match (_58_2519) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _150_947 = (let _150_945 = (let _150_944 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _150_944))
in (_150_945)::[])
in (let _150_946 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _150_947 _150_946)))
in (

let expected_k = (let _150_958 = (let _150_956 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _150_955 = (let _150_954 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_953 = (let _150_952 = (FStar_Syntax_Syntax.mk_binder b)
in (let _150_951 = (let _150_950 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _150_949 = (let _150_948 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (_150_948)::[])
in (_150_950)::_150_949))
in (_150_952)::_150_951))
in (_150_954)::_150_953))
in (_150_956)::_150_955))
in (let _150_957 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _150_958 _150_957)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (let _150_960 = (let _150_959 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_959 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _150_960))
in (

let expected_k = (let _150_969 = (let _150_967 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_966 = (let _150_965 = (FStar_Syntax_Syntax.mk_binder p)
in (let _150_964 = (let _150_963 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _150_962 = (let _150_961 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_961)::[])
in (_150_963)::_150_962))
in (_150_965)::_150_964))
in (_150_967)::_150_966))
in (let _150_968 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_969 _150_968)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (let _150_974 = (let _150_972 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_971 = (let _150_970 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_970)::[])
in (_150_972)::_150_971))
in (let _150_973 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_974 _150_973)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let _58_2531 = (FStar_Syntax_Util.type_u ())
in (match (_58_2531) with
| (t, _58_2530) -> begin
(

let expected_k = (let _150_981 = (let _150_979 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_978 = (let _150_977 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _150_976 = (let _150_975 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_975)::[])
in (_150_977)::_150_976))
in (_150_979)::_150_978))
in (let _150_980 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _150_981 _150_980)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (let _150_983 = (let _150_982 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_982 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _150_983))
in (

let b_wp_a = (let _150_987 = (let _150_985 = (let _150_984 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _150_984))
in (_150_985)::[])
in (let _150_986 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_987 _150_986)))
in (

let expected_k = (let _150_994 = (let _150_992 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_991 = (let _150_990 = (FStar_Syntax_Syntax.mk_binder b)
in (let _150_989 = (let _150_988 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_150_988)::[])
in (_150_990)::_150_989))
in (_150_992)::_150_991))
in (let _150_993 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_994 _150_993)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (let _150_1003 = (let _150_1001 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1000 = (let _150_999 = (let _150_996 = (let _150_995 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_995 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _150_996))
in (let _150_998 = (let _150_997 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_997)::[])
in (_150_999)::_150_998))
in (_150_1001)::_150_1000))
in (let _150_1002 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_1003 _150_1002)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _150_1012 = (let _150_1010 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1009 = (let _150_1008 = (let _150_1005 = (let _150_1004 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_1004 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _150_1005))
in (let _150_1007 = (let _150_1006 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_1006)::[])
in (_150_1008)::_150_1007))
in (_150_1010)::_150_1009))
in (let _150_1011 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_1012 _150_1011)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _150_1015 = (let _150_1013 = (FStar_Syntax_Syntax.mk_binder a)
in (_150_1013)::[])
in (let _150_1014 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_1015 _150_1014)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let _58_2547 = (FStar_Syntax_Util.type_u ())
in (match (_58_2547) with
| (t, _58_2546) -> begin
(

let expected_k = (let _150_1020 = (let _150_1018 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1017 = (let _150_1016 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_1016)::[])
in (_150_1018)::_150_1017))
in (let _150_1019 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _150_1020 _150_1019)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let _58_2671 = if ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) || (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable))) then begin
(

let repr = (

let _58_2553 = (FStar_Syntax_Util.type_u ())
in (match (_58_2553) with
| (t, _58_2552) -> begin
(

let expected_k = (let _150_1025 = (let _150_1023 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1022 = (let _150_1021 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_1021)::[])
in (_150_1023)::_150_1022))
in (let _150_1024 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _150_1025 _150_1024)))
in (tc_check_trivial_guard env ed.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (let _150_1036 = (let _150_1035 = (let _150_1034 = (FStar_Syntax_Util.un_uinst repr)
in (let _150_1033 = (let _150_1032 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_1031 = (let _150_1030 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_1030)::[])
in (_150_1032)::_150_1031))
in ((_150_1034), (_150_1033))))
in FStar_Syntax_Syntax.Tm_app (_150_1035))
in (FStar_Syntax_Syntax.mk _150_1036 None FStar_Range.dummyRange)))
in (

let mk_repr = (fun a wp -> (let _150_1041 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_repr' _150_1041 wp)))
in (

let destruct_repr = (fun t -> (match ((let _150_1044 = (FStar_Syntax_Subst.compress t)
in _150_1044.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_58_2565, ((t, _58_2572))::((wp, _58_2568))::[]) -> begin
((t), (wp))
end
| _58_2578 -> begin
(FStar_All.failwith "Unexpected repr type")
end))
in (

let bind_repr = (

let r = (let _150_1045 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_0 FStar_Syntax_Syntax.Delta_constant None)
in (FStar_All.pipe_right _150_1045 FStar_Syntax_Syntax.fv_to_tm))
in (

let _58_2582 = (get_effect_signature ())
in (match (_58_2582) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _150_1049 = (let _150_1047 = (let _150_1046 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _150_1046))
in (_150_1047)::[])
in (let _150_1048 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _150_1049 _150_1048)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" None a_wp_b)
in (

let x_a = (let _150_1050 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _150_1050))
in (

let wp_g_x = (let _150_1054 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (let _150_1053 = (let _150_1052 = (let _150_1051 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_1051))
in (_150_1052)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _150_1054 _150_1053 None FStar_Range.dummyRange)))
in (

let res = (

let wp = (let _150_1066 = (let _150_1055 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right _150_1055 Prims.snd))
in (let _150_1065 = (let _150_1064 = (let _150_1063 = (let _150_1062 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_1061 = (let _150_1060 = (FStar_Syntax_Syntax.bv_to_name b)
in (let _150_1059 = (let _150_1058 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (let _150_1057 = (let _150_1056 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (_150_1056)::[])
in (_150_1058)::_150_1057))
in (_150_1060)::_150_1059))
in (_150_1062)::_150_1061))
in (r)::_150_1063)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _150_1064))
in (FStar_Syntax_Syntax.mk_Tm_app _150_1066 _150_1065 None FStar_Range.dummyRange)))
in (mk_repr b wp))
in (

let expected_k = (let _150_1086 = (let _150_1084 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1083 = (let _150_1082 = (FStar_Syntax_Syntax.mk_binder b)
in (let _150_1081 = (let _150_1080 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (let _150_1079 = (let _150_1078 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (let _150_1077 = (let _150_1076 = (let _150_1068 = (let _150_1067 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a _150_1067))
in (FStar_Syntax_Syntax.null_binder _150_1068))
in (let _150_1075 = (let _150_1074 = (let _150_1073 = (let _150_1072 = (let _150_1069 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_150_1069)::[])
in (let _150_1071 = (let _150_1070 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _150_1070))
in (FStar_Syntax_Util.arrow _150_1072 _150_1071)))
in (FStar_Syntax_Syntax.null_binder _150_1073))
in (_150_1074)::[])
in (_150_1076)::_150_1075))
in (_150_1078)::_150_1077))
in (_150_1080)::_150_1079))
in (_150_1082)::_150_1081))
in (_150_1084)::_150_1083))
in (let _150_1085 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _150_1086 _150_1085)))
in (

let _58_2596 = (tc_tot_or_gtot_term env expected_k)
in (match (_58_2596) with
| (expected_k, _58_2593, _58_2595) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_repr expected_k))
end)))))))))
end)))
in (

let return_repr = (

let x_a = (let _150_1087 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _150_1087))
in (

let res = (

let wp = (let _150_1094 = (let _150_1088 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right _150_1088 Prims.snd))
in (let _150_1093 = (let _150_1092 = (let _150_1091 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_1090 = (let _150_1089 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (_150_1089)::[])
in (_150_1091)::_150_1090))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _150_1092))
in (FStar_Syntax_Syntax.mk_Tm_app _150_1094 _150_1093 None FStar_Range.dummyRange)))
in (mk_repr a wp))
in (

let expected_k = (let _150_1099 = (let _150_1097 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1096 = (let _150_1095 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_150_1095)::[])
in (_150_1097)::_150_1096))
in (let _150_1098 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _150_1099 _150_1098)))
in (

let _58_2608 = (tc_tot_or_gtot_term env expected_k)
in (match (_58_2608) with
| (expected_k, _58_2605, _58_2607) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let _58_2612 = (check_and_gen' env ed.FStar_Syntax_Syntax.return_repr expected_k)
in (match (_58_2612) with
| (univs, repr) -> begin
(match (univs) with
| [] -> begin
(([]), (repr))
end
| _58_2615 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected universe-polymorphic return for effect"), (repr.FStar_Syntax_Syntax.pos)))))
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let _58_2622 = (tc_tot_or_gtot_term env act.FStar_Syntax_Syntax.action_defn)
in (match (_58_2622) with
| (act_defn, c, g_a) -> begin
(

let _58_2642 = (match ((let _150_1102 = (FStar_Syntax_Subst.compress c.FStar_Syntax_Syntax.res_typ)
in _150_1102.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _58_2630 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_2630) with
| (bs, _58_2629) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (let _150_1103 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs _150_1103))
in (

let _58_2637 = (tc_tot_or_gtot_term env k)
in (match (_58_2637) with
| (k, _58_2635, g) -> begin
((k), (g))
end))))
end))
end
| _58_2639 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Actions must have function types"), (act_defn.FStar_Syntax_Syntax.pos)))))
end)
in (match (_58_2642) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env c.FStar_Syntax_Syntax.res_typ expected_k)
in (

let _58_2644 = (let _150_1105 = (let _150_1104 = (FStar_TypeChecker_Rel.conj_guard g_k g)
in (FStar_TypeChecker_Rel.conj_guard g_a _150_1104))
in (FStar_TypeChecker_Rel.force_trivial_guard env _150_1105))
in (

let act_ty = (match ((let _150_1106 = (FStar_Syntax_Subst.compress expected_k)
in _150_1106.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _58_2652 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_2652) with
| (bs, c) -> begin
(

let _58_2655 = (destruct_repr (FStar_Syntax_Util.comp_result c))
in (match (_58_2655) with
| (a, wp) -> begin
(

let c = (let _150_1108 = (let _150_1107 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_1107)::[])
in {FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a; FStar_Syntax_Syntax.effect_args = _150_1108; FStar_Syntax_Syntax.flags = []})
in (let _150_1109 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Util.arrow bs _150_1109)))
end))
end))
end
| _58_2658 -> begin
(FStar_All.failwith "")
end)
in (

let _58_2662 = (FStar_TypeChecker_Util.generalize_universes env act_defn)
in (match (_58_2662) with
| (univs, act_defn) -> begin
(

let act_ty = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env act_ty)
in (

let _58_2664 = act
in {FStar_Syntax_Syntax.action_name = _58_2664.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = act_defn; FStar_Syntax_Syntax.action_typ = act_ty}))
end)))))
end))
end)))
in (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.map check_action)))
in ((repr), (bind_repr), (return_repr), (actions)))))))))
end else begin
((ed.FStar_Syntax_Syntax.repr), (ed.FStar_Syntax_Syntax.bind_repr), (ed.FStar_Syntax_Syntax.return_repr), (ed.FStar_Syntax_Syntax.actions))
end
in (match (_58_2671) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t = (let _150_1110 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _150_1110))
in (

let _58_2675 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_58_2675) with
| (univs, t) -> begin
(

let _58_2691 = (match ((let _150_1112 = (let _150_1111 = (FStar_Syntax_Subst.compress t)
in _150_1111.FStar_Syntax_Syntax.n)
in ((binders), (_150_1112)))) with
| ([], _58_2678) -> begin
(([]), (t))
end
| (_58_2681, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
((binders), ((FStar_Syntax_Util.comp_result c)))
end
| _58_2688 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_58_2691) with
| (binders, signature) -> begin
(

let close = (fun n ts -> (

let ts = (let _150_1117 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _150_1117))
in (

let _58_2696 = ()
in ts)))
in (

let close_action = (fun act -> (

let _58_2702 = (close (- (1)) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (_58_2702) with
| (univs, defn) -> begin
(

let _58_2705 = (close (- (1)) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (_58_2705) with
| (univs', typ) -> begin
(

let _58_2706 = ()
in (

let _58_2708 = act
in {FStar_Syntax_Syntax.action_name = _58_2708.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ}))
end))
end)))
in (

let ed = (

let _58_2710 = ed
in (let _150_1134 = (close 0 return_wp)
in (let _150_1133 = (close 1 bind_wp)
in (let _150_1132 = (close 0 if_then_else)
in (let _150_1131 = (close 0 ite_wp)
in (let _150_1130 = (close 0 stronger)
in (let _150_1129 = (close 1 close_wp)
in (let _150_1128 = (close 0 assert_p)
in (let _150_1127 = (close 0 assume_p)
in (let _150_1126 = (close 0 null_wp)
in (let _150_1125 = (close 0 trivial_wp)
in (let _150_1124 = (let _150_1120 = (close 0 (([]), (repr)))
in (Prims.snd _150_1120))
in (let _150_1123 = (close 0 return_repr)
in (let _150_1122 = (close 1 bind_repr)
in (let _150_1121 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.qualifiers = _58_2710.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2710.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _150_1134; FStar_Syntax_Syntax.bind_wp = _150_1133; FStar_Syntax_Syntax.if_then_else = _150_1132; FStar_Syntax_Syntax.ite_wp = _150_1131; FStar_Syntax_Syntax.stronger = _150_1130; FStar_Syntax_Syntax.close_wp = _150_1129; FStar_Syntax_Syntax.assert_p = _150_1128; FStar_Syntax_Syntax.assume_p = _150_1127; FStar_Syntax_Syntax.null_wp = _150_1126; FStar_Syntax_Syntax.trivial = _150_1125; FStar_Syntax_Syntax.repr = _150_1124; FStar_Syntax_Syntax.return_repr = _150_1123; FStar_Syntax_Syntax.bind_repr = _150_1122; FStar_Syntax_Syntax.actions = _150_1121})))))))))))))))
in (

let _58_2715 = if ((FStar_TypeChecker_Env.debug env FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EffDecl")))) then begin
(let _150_1135 = (FStar_Syntax_Print.eff_decl_to_string (match (is_for_free) with
| ForFree -> begin
true
end
| NotForFree -> begin
false
end) ed)
in (FStar_Util.print_string _150_1135))
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
and elaborate_and_star : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (

let _58_2721 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_58_2721) with
| (binders_un, signature_un) -> begin
(

let _58_2726 = (tc_tparams env0 binders_un)
in (match (_58_2726) with
| (binders, env, _58_2725) -> begin
(

let _58_2730 = (tc_trivial_guard env signature_un)
in (match (_58_2730) with
| (signature, _58_2729) -> begin
(

let _58_2743 = (match ((let _150_1138 = (FStar_Syntax_Subst.compress signature)
in _150_1138.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (((a, _58_2733))::[], effect_marker) -> begin
((a), (effect_marker))
end
| _58_2740 -> begin
(FStar_All.failwith "bad shape for effect-for-free signature")
end)
in (match (_58_2743) with
| (a, effect_marker) -> begin
(

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]))
in (

let open_and_reduce = (fun t -> (

let subst = (FStar_Syntax_Subst.opening_of_binders binders)
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (

let _58_2753 = (tc_term env t)
in (match (_58_2753) with
| (t, comp, _58_2752) -> begin
((t), (comp))
end)))))
in (

let recheck_debug = (fun s env t -> (

let _58_2758 = (let _150_1149 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Term has been %s-transformed to:\n%s\n----------\n" s _150_1149))
in (

let _58_2765 = (tc_term env t)
in (match (_58_2765) with
| (t, _58_2762, _58_2764) -> begin
(let _150_1150 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Re-checked; got:\n%s\n----------\n" _150_1150))
end))))
in (

let _58_2768 = (open_and_reduce ed.FStar_Syntax_Syntax.repr)
in (match (_58_2768) with
| (repr, _comp) -> begin
(

let _58_2769 = (let _150_1151 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" _150_1151))
in (

let dmff_env = (FStar_TypeChecker_DMFF.empty env (tc_constant FStar_Range.dummyRange))
in (

let _58_2774 = (FStar_TypeChecker_DMFF.star_type_definition dmff_env repr)
in (match (_58_2774) with
| (dmff_env, wp_type) -> begin
(

let _58_2775 = (recheck_debug "*" env wp_type)
in (

let effect_signature = (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None signature.FStar_Syntax_Syntax.pos))
in (

let wp_a = (let _150_1159 = (let _150_1158 = (let _150_1157 = (let _150_1156 = (let _150_1155 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_1154 = (FStar_Syntax_Syntax.as_implicit false)
in ((_150_1155), (_150_1154))))
in (_150_1156)::[])
in ((wp_type), (_150_1157)))
in FStar_Syntax_Syntax.Tm_app (_150_1158))
in (mk _150_1159))
in (

let wp_a = (normalize env wp_a)
in (

let binders = (let _150_1163 = (let _150_1160 = (FStar_Syntax_Syntax.as_implicit false)
in ((a), (_150_1160)))
in (let _150_1162 = (let _150_1161 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_1161)::[])
in (_150_1163)::_150_1162))
in (

let binders = (FStar_Syntax_Subst.close_binders binders)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (effect_marker))))))))))
in (

let _58_2784 = (recheck_debug "turned into the effect signature" env effect_signature)
in (

let elaborate_and_star = (fun dmff_env item -> (

let _58_2791 = item
in (match (_58_2791) with
| (u_item, item) -> begin
(

let _58_2794 = (open_and_reduce item)
in (match (_58_2794) with
| (item, item_comp) -> begin
(

let _58_2795 = if (not ((FStar_Syntax_Util.is_total_lcomp item_comp))) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Computation for [item] is not total!")))
end else begin
()
end
in (

let _58_2801 = (FStar_TypeChecker_DMFF.star_expr_definition dmff_env item)
in (match (_58_2801) with
| (dmff_env, (item_wp, item_elab)) -> begin
(

let _58_2802 = (recheck_debug "*" env item_wp)
in (

let _58_2804 = (recheck_debug "_" env item_elab)
in ((dmff_env), (item_wp), (item_elab))))
end)))
end))
end)))
in (

let _58_2809 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.bind_repr)
in (match (_58_2809) with
| (dmff_env, bind_wp, bind_elab) -> begin
(

let _58_2813 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.return_repr)
in (match (_58_2813) with
| (dmff_env, return_wp, return_elab) -> begin
(

let return_wp = (match ((let _150_1168 = (FStar_Syntax_Subst.compress return_wp)
in _150_1168.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(let _150_1169 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) _150_1169 (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_GTot_lid)))))
end
| _58_2824 -> begin
(FStar_All.failwith "unexpected shape for return")
end)
in (

let bind_wp = (match ((let _150_1170 = (FStar_Syntax_Subst.compress bind_wp)
in _150_1170.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (let _150_1173 = (let _150_1172 = (let _150_1171 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (r)) None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.null_binder _150_1171))
in (_150_1172)::binders)
in (FStar_Syntax_Util.abs _150_1173 body what)))
end
| _58_2833 -> begin
(FStar_All.failwith "unexpected shape for bind")
end)
in (

let _58_2847 = (FStar_List.fold_left (fun _58_2837 action -> (match (_58_2837) with
| (dmff_env, actions) -> begin
(

let _58_2842 = (elaborate_and_star dmff_env ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (_58_2842) with
| (dmff_env, action_wp, action_elab) -> begin
((dmff_env), (((

let _58_2843 = action
in {FStar_Syntax_Syntax.action_name = _58_2843.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = _58_2843.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = action_elab; FStar_Syntax_Syntax.action_typ = _58_2843.FStar_Syntax_Syntax.action_typ}))::actions))
end))
end)) ((dmff_env), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (_58_2847) with
| (dmff_env, actions) -> begin
(

let actions = (FStar_List.rev actions)
in (

let c = (FStar_Syntax_Subst.close binders)
in (

let ed = (

let _58_2850 = ed
in (let _150_1189 = (FStar_Syntax_Subst.close_binders binders)
in (let _150_1188 = (c effect_signature)
in (let _150_1187 = (let _150_1177 = (c return_wp)
in (([]), (_150_1177)))
in (let _150_1186 = (let _150_1178 = (c bind_wp)
in (([]), (_150_1178)))
in (let _150_1185 = (let _150_1179 = (c return_elab)
in (([]), (_150_1179)))
in (let _150_1184 = (let _150_1180 = (c bind_elab)
in (([]), (_150_1180)))
in (let _150_1183 = (FStar_List.map (fun action -> (

let _58_2853 = action
in (let _150_1182 = (c action.FStar_Syntax_Syntax.action_defn)
in {FStar_Syntax_Syntax.action_name = _58_2853.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = _58_2853.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _150_1182; FStar_Syntax_Syntax.action_typ = _58_2853.FStar_Syntax_Syntax.action_typ}))) actions)
in {FStar_Syntax_Syntax.qualifiers = _58_2850.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2850.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _58_2850.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _150_1189; FStar_Syntax_Syntax.signature = _150_1188; FStar_Syntax_Syntax.ret_wp = _150_1187; FStar_Syntax_Syntax.bind_wp = _150_1186; FStar_Syntax_Syntax.if_then_else = _58_2850.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _58_2850.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _58_2850.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _58_2850.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _58_2850.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _58_2850.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _58_2850.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _58_2850.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _58_2850.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _150_1185; FStar_Syntax_Syntax.bind_repr = _150_1184; FStar_Syntax_Syntax.actions = _150_1183}))))))))
in (

let _58_2856 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _150_1190 = (FStar_Syntax_Print.eff_decl_to_string true ed)
in (FStar_Util.print_string _150_1190))
end else begin
()
end
in ed))))
end))))
end))
end))))))
end))))
end)))))
end))
end))
end))
end)))
and tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  effect_cost  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed is_for_free -> (

let ed = (match (is_for_free) with
| ForFree -> begin
(elaborate_and_star env0 ed)
end
| NotForFree -> begin
ed
end)
in (tc_real_eff_decl env0 ed is_for_free)))
and tc_lex_t : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (

let _58_2868 = ()
in (

let _58_2876 = ()
in (match (ses) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _58_2905, _58_2907, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _58_2896, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _58_2885, r2))::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
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

let lex_top_t = (let _150_1201 = (let _150_1200 = (let _150_1199 = (let _150_1198 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _150_1198 FStar_Syntax_Syntax.Delta_constant None))
in ((_150_1199), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_150_1200))
in (FStar_Syntax_Syntax.mk _150_1201 None r1))
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

let a = (let _150_1202 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _150_1202))
in (

let hd = (let _150_1203 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _150_1203))
in (

let tl = (let _150_1208 = (let _150_1207 = (let _150_1206 = (let _150_1205 = (let _150_1204 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _150_1204 FStar_Syntax_Syntax.Delta_constant None))
in ((_150_1205), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_150_1206))
in (FStar_Syntax_Syntax.mk _150_1207 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _150_1208))
in (

let res = (let _150_1212 = (let _150_1211 = (let _150_1210 = (let _150_1209 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _150_1209 FStar_Syntax_Syntax.Delta_constant None))
in ((_150_1210), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_150_1211))
in (FStar_Syntax_Syntax.mk _150_1212 None r2))
in (let _150_1213 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (Some (FStar_Syntax_Syntax.imp_tag))))::(((hd), (None)))::(((tl), (None)))::[]) _150_1213))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t), (FStar_Syntax_Const.lex_t_lid), (0), ([]), ([]), (r2)))
in (let _150_1215 = (let _150_1214 = (FStar_TypeChecker_Env.get_range env)
in (((tc)::(dc_lextop)::(dc_lexcons)::[]), ([]), (lids), (_150_1214)))
in FStar_Syntax_Syntax.Sig_bundle (_150_1215)))))))))))))))
end
| _58_2931 -> begin
(let _150_1217 = (let _150_1216 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle (((ses), ([]), (lids), (FStar_Range.dummyRange)))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _150_1216))
in (FStar_All.failwith _150_1217))
end))))
and tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _58_2941 = (FStar_Syntax_Util.type_u ())
in (match (_58_2941) with
| (k, _58_2940) -> begin
(

let phi = (let _150_1223 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _150_1223 (norm env)))
in (

let _58_2943 = (FStar_TypeChecker_Util.check_uvars r phi)
in FStar_Syntax_Syntax.Sig_assume (((lid), (phi), (quals), (r)))))
end))))
and tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _150_1233 = (let _150_1232 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _150_1232))
in (FStar_TypeChecker_Errors.diag r _150_1233)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let _58_2966 = ()
in (

let _58_2968 = (warn_positivity tc r)
in (

let _58_2972 = (FStar_Syntax_Subst.open_term tps k)
in (match (_58_2972) with
| (tps, k) -> begin
(

let _58_2977 = (tc_binders env tps)
in (match (_58_2977) with
| (tps, env_tps, guard_params, us) -> begin
(

let _58_2980 = (FStar_Syntax_Util.arrow_formals k)
in (match (_58_2980) with
| (indices, t) -> begin
(

let _58_2985 = (tc_binders env_tps indices)
in (match (_58_2985) with
| (indices, env', guard_indices, us') -> begin
(

let _58_2993 = (

let _58_2990 = (tc_tot_or_gtot_term env' t)
in (match (_58_2990) with
| (t, _58_2988, g) -> begin
(let _150_1240 = (let _150_1239 = (let _150_1238 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params _150_1238))
in (FStar_TypeChecker_Rel.discharge_guard env' _150_1239))
in ((t), (_150_1240)))
end))
in (match (_58_2993) with
| (t, guard) -> begin
(

let k = (let _150_1241 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _150_1241))
in (

let _58_2997 = (FStar_Syntax_Util.type_u ())
in (match (_58_2997) with
| (t_type, u) -> begin
(

let _58_2998 = (let _150_1242 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _150_1242))
in (

let t_tc = (let _150_1243 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _150_1243))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _150_1244 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((_150_1244), (FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps), (k), (mutuals), (data), (quals), (r)))), (u), (guard))))))))
end)))
end))
end))
end))
end))
end))))
end
| _58_3005 -> begin
(FStar_All.failwith "impossible")
end))
in (

let positive_if_pure = (fun _58_3007 l -> ())
in (

let tc_data = (fun env tcs _58_7 -> (match (_58_7) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let _58_3024 = ()
in (

let _58_3059 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _58_3028 -> (match (_58_3028) with
| (se, u_tc) -> begin
if (let _150_1257 = (let _150_1256 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _150_1256))
in (FStar_Ident.lid_equals tc_lid _150_1257)) then begin
(

let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_3030, _58_3032, tps, _58_3035, _58_3037, _58_3039, _58_3041, _58_3043) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _58_3049 -> (match (_58_3049) with
| (x, _58_3048) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
end
| _58_3051 -> begin
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
in (match (_58_3059) with
| (tps, u_tc) -> begin
(

let _58_3079 = (match ((let _150_1259 = (FStar_Syntax_Subst.compress t)
in _150_1259.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _58_3067 = (FStar_Util.first_N ntps bs)
in (match (_58_3067) with
| (_58_3065, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res)))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _58_3073 -> (match (_58_3073) with
| (x, _58_3072) -> begin
FStar_Syntax_Syntax.DB ((((ntps - (1 + i))), (x)))
end))))
in (let _150_1262 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _150_1262))))
end))
end
| _58_3076 -> begin
(([]), (t))
end)
in (match (_58_3079) with
| (arguments, result) -> begin
(

let _58_3080 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1265 = (FStar_Syntax_Print.lid_to_string c)
in (let _150_1264 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _150_1263 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _150_1265 _150_1264 _150_1263))))
end else begin
()
end
in (

let _58_3085 = (tc_tparams env arguments)
in (match (_58_3085) with
| (arguments, env', us) -> begin
(

let _58_3089 = (tc_trivial_guard env' result)
in (match (_58_3089) with
| (result, _58_3088) -> begin
(

let _58_3093 = (FStar_Syntax_Util.head_and_args result)
in (match (_58_3093) with
| (head, _58_3092) -> begin
(

let _58_3098 = (match ((let _150_1266 = (FStar_Syntax_Subst.compress head)
in _150_1266.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _58_3097 -> begin
(let _150_1271 = (let _150_1270 = (let _150_1269 = (let _150_1268 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _150_1267 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _150_1268 _150_1267)))
in ((_150_1269), (r)))
in FStar_Syntax_Syntax.Error (_150_1270))
in (Prims.raise _150_1271))
end)
in (

let g = (FStar_List.fold_left2 (fun g _58_3104 u_x -> (match (_58_3104) with
| (x, _58_3103) -> begin
(

let _58_3106 = ()
in (let _150_1275 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _150_1275)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _150_1279 = (let _150_1277 = (FStar_All.pipe_right tps (FStar_List.map (fun _58_3112 -> (match (_58_3112) with
| (x, _58_3111) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append _150_1277 arguments))
in (let _150_1278 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _150_1279 _150_1278)))
in ((FStar_Syntax_Syntax.Sig_datacon (((c), ([]), (t), (tc_lid), (ntps), (quals), ([]), (r)))), (g)))))
end))
end))
end)))
end))
end)))
end
| _58_3115 -> begin
(FStar_All.failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let _58_3121 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _58_8 -> (match (_58_8) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_3125, _58_3127, tps, k, _58_3131, _58_3133, _58_3135, _58_3137) -> begin
(let _150_1290 = (let _150_1289 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _150_1289))
in (FStar_Syntax_Syntax.null_binder _150_1290))
end
| _58_3141 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _58_9 -> (match (_58_9) with
| FStar_Syntax_Syntax.Sig_datacon (_58_3145, _58_3147, t, _58_3150, _58_3152, _58_3154, _58_3156, _58_3158) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _58_3162 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let t = (let _150_1292 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _150_1292))
in (

let _58_3165 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1293 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _150_1293))
end else begin
()
end
in (

let _58_3169 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_58_3169) with
| (uvs, t) -> begin
(

let _58_3171 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1297 = (let _150_1295 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _150_1295 (FStar_String.concat ", ")))
in (let _150_1296 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _150_1297 _150_1296)))
end else begin
()
end
in (

let _58_3175 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_58_3175) with
| (uvs, t) -> begin
(

let _58_3179 = (FStar_Syntax_Util.arrow_formals t)
in (match (_58_3179) with
| (args, _58_3178) -> begin
(

let _58_3182 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_58_3182) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _58_3186 se -> (match (_58_3186) with
| (x, _58_3185) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _58_3190, tps, _58_3193, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let _58_3216 = (match ((let _150_1300 = (FStar_Syntax_Subst.compress ty)
in _150_1300.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _58_3207 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_58_3207) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _58_3210 -> begin
(let _150_1301 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) _150_1301 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps), (t)))
end))
end
| _58_3213 -> begin
(([]), (ty))
end)
in (match (_58_3216) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs), (tps), (t), (mutuals), (datas), (quals), (r)))
end)))
end
| _58_3218 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| _58_3222 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _150_1302 -> FStar_Syntax_Syntax.U_name (_150_1302))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _58_10 -> (match (_58_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _58_3227, _58_3229, _58_3231, _58_3233, _58_3235, _58_3237, _58_3239) -> begin
((tc), (uvs_universes))
end
| _58_3243 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _58_3248 d -> (match (_58_3248) with
| (t, _58_3247) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _58_3252, _58_3254, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _150_1306 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _150_1306 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon (((l), (uvs), (ty), (tc), (ntps), (quals), (mutuals), (r))))
end
| _58_3264 -> begin
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

let _58_3274 = (FStar_All.pipe_right ses (FStar_List.partition (fun _58_11 -> (match (_58_11) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_3268) -> begin
true
end
| _58_3271 -> begin
false
end))))
in (match (_58_3274) with
| (tys, datas) -> begin
(

let _58_3281 = if (FStar_All.pipe_right datas (FStar_Util.for_some (fun _58_12 -> (match (_58_12) with
| FStar_Syntax_Syntax.Sig_datacon (_58_3277) -> begin
false
end
| _58_3280 -> begin
true
end)))) then begin
(let _150_1311 = (let _150_1310 = (let _150_1309 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (_150_1309)))
in FStar_Syntax_Syntax.Error (_150_1310))
in (Prims.raise _150_1311))
end else begin
()
end
in (

let env0 = env
in (

let _58_3300 = (FStar_List.fold_right (fun tc _58_3288 -> (match (_58_3288) with
| (env, all_tcs, g) -> begin
(

let _58_3293 = (tc_tycon env tc)
in (match (_58_3293) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (

let _58_3295 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1314 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _150_1314))
end else begin
()
end
in (let _150_1316 = (let _150_1315 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g _150_1315))
in ((env), ((((tc), (tc_u)))::all_tcs), (_150_1316)))))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_58_3300) with
| (env, tcs, g) -> begin
(

let _58_3310 = (FStar_List.fold_right (fun se _58_3304 -> (match (_58_3304) with
| (datas, g) -> begin
(

let _58_3307 = (tc_data env tcs se)
in (match (_58_3307) with
| (data, g') -> begin
(let _150_1319 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((data)::datas), (_150_1319)))
end))
end)) datas (([]), (g)))
in (match (_58_3310) with
| (datas, g) -> begin
(

let _58_3313 = (let _150_1320 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _150_1320 datas))
in (match (_58_3313) with
| (tcs, datas) -> begin
(

let sig_bndle = (let _150_1322 = (let _150_1321 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_150_1321)))
in FStar_Syntax_Syntax.Sig_bundle (_150_1322))
in (

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (_58_3318, _58_3320, t, _58_3323, _58_3325, _58_3327, _58_3329, _58_3331) -> begin
t
end
| _58_3335 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let dr = FStar_Range.dummyRange
in (

let haseq_ty = (fun usubst us acc ty -> (

let _58_3362 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _58_3344, bs, t, _58_3348, d_lids, _58_3351, _58_3353) -> begin
((lid), (bs), (t), (d_lids))
end
| _58_3357 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_58_3362) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _150_1333 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _150_1333 t))
in (

let _58_3367 = (FStar_Syntax_Subst.open_term bs t)
in (match (_58_3367) with
| (bs, t) -> begin
(

let ibs = (match ((let _150_1334 = (FStar_Syntax_Subst.compress t)
in _150_1334.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _58_3370) -> begin
ibs
end
| _58_3374 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _150_1337 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _150_1336 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_1337 _150_1336)))
in (

let ind = (let _150_1340 = (FStar_List.map (fun _58_3381 -> (match (_58_3381) with
| (bv, aq) -> begin
(let _150_1339 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_150_1339), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _150_1340 None dr))
in (

let ind = (let _150_1343 = (FStar_List.map (fun _58_3385 -> (match (_58_3385) with
| (bv, aq) -> begin
(let _150_1342 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_150_1342), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _150_1343 None dr))
in (

let haseq_ind = (let _150_1345 = (let _150_1344 = (FStar_Syntax_Syntax.as_arg ind)
in (_150_1344)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _150_1345 None dr))
in (

let bs' = (FStar_List.filter (fun b -> (

let _58_3396 = acc
in (match (_58_3396) with
| (_58_3390, en, _58_3393, _58_3395) -> begin
(

let opt = (let _150_1348 = (let _150_1347 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _150_1347))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort _150_1348 false))
in (match (opt) with
| None -> begin
false
end
| Some (_58_3400) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (let _150_1354 = (let _150_1353 = (let _150_1352 = (let _150_1351 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg _150_1351))
in (_150_1352)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _150_1353 None dr))
in (FStar_Syntax_Util.mk_conj t _150_1354))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let _58_3407 = fml
in (let _150_1360 = (let _150_1359 = (let _150_1358 = (let _150_1357 = (let _150_1356 = (let _150_1355 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_150_1355)::[])
in (_150_1356)::[])
in FStar_Syntax_Syntax.Meta_pattern (_150_1357))
in ((fml), (_150_1358)))
in FStar_Syntax_Syntax.Tm_meta (_150_1359))
in {FStar_Syntax_Syntax.n = _150_1360; FStar_Syntax_Syntax.tk = _58_3407.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _58_3407.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_3407.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _150_1366 = (let _150_1365 = (let _150_1364 = (let _150_1363 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _150_1363 None))
in (FStar_Syntax_Syntax.as_arg _150_1364))
in (_150_1365)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _150_1366 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _150_1372 = (let _150_1371 = (let _150_1370 = (let _150_1369 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _150_1369 None))
in (FStar_Syntax_Syntax.as_arg _150_1370))
in (_150_1371)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _150_1372 None dr))) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let _58_3421 = acc
in (match (_58_3421) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_58_3426, _58_3428, _58_3430, t_lid, _58_3433, _58_3435, _58_3437, _58_3439) -> begin
(t_lid = lid)
end
| _58_3443 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let haseq_data = (fun acc data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (match ((let _150_1378 = (FStar_Syntax_Subst.compress dt)
in _150_1378.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _58_3452) -> begin
(

let dbs = (let _150_1379 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _150_1379))
in (

let dbs = (let _150_1380 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _150_1380 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (let _150_1385 = (let _150_1384 = (let _150_1383 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_150_1383)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _150_1384 None dr))
in (FStar_Syntax_Util.mk_conj t _150_1385))) FStar_Syntax_Util.t_true dbs)
in (

let _58_3463 = acc
in (match (_58_3463) with
| (env, cond') -> begin
(let _150_1387 = (FStar_TypeChecker_Env.push_binders env dbs)
in (let _150_1386 = (FStar_Syntax_Util.mk_conj cond' cond)
in ((_150_1387), (_150_1386))))
end))))))
end
| _58_3465 -> begin
acc
end))))
in (

let _58_3468 = (FStar_List.fold_left haseq_data ((env), (FStar_Syntax_Util.t_true)) t_datas)
in (match (_58_3468) with
| (env, cond) -> begin
(

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (let _150_1389 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _150_1388 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env), (_150_1389), (_150_1388)))))
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
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_3474, us, _58_3477, _58_3479, _58_3481, _58_3483, _58_3485, _58_3487) -> begin
us
end
| _58_3491 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let _58_3495 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_58_3495) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _58_3497 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _58_3499 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let _58_3506 = (FStar_List.fold_left (haseq_ty usubst us) (([]), (env), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (_58_3506) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let _58_3511 = (tc_trivial_guard env phi)
in (match (_58_3511) with
| (phi, _58_3510) -> begin
(

let _58_3512 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(let _150_1391 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _150_1391))
end else begin
()
end
in (

let _58_3514 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env0 us)
in (

let ses = (FStar_List.fold_left (fun l _58_3520 -> (match (_58_3520) with
| (lid, fml) -> begin
(

let se = (tc_assume env lid fml [] dr)
in (FStar_List.append l ((se)::[])))
end)) [] axioms)
in (let _150_1396 = (let _150_1395 = (let _150_1394 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_150_1394)))
in FStar_Syntax_Syntax.Sig_bundle (_150_1395))
in (_150_1396)::ses)))))
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
in (let _150_1399 = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (_150_1399)))))
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
| FStar_Getopt.GoOn -> begin
()
end
| FStar_Getopt.Help -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Failed to process pragma: use \'fstar --help\' to see which options are available"), (r)))))
end
| FStar_Getopt.Die (s) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Failed to process pragma: " s)), (r)))))
end))
in (match (p) with
| FStar_Syntax_Syntax.SetOptions (o) -> begin
(

let _58_3563 = (set_options FStar_Options.Set o)
in (((se)::[]), (env)))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(

let _58_3567 = (let _150_1406 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _150_1406 Prims.ignore))
in (

let _58_3572 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _58_3574 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
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

let _58_3597 = (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun _58_3592 a -> (match (_58_3592) with
| (env, ses) -> begin
(

let se_let = (FStar_Syntax_Util.action_as_lb a)
in (let _150_1409 = (FStar_TypeChecker_Env.push_sigelt env se_let)
in ((_150_1409), ((se_let)::ses))))
end)) ((env), ((se)::[]))))
in (match (_58_3597) with
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

let _58_3606 = (let _150_1410 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _150_1410))
in (match (_58_3606) with
| (a, wp_a_src) -> begin
(

let _58_3609 = (let _150_1411 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _150_1411))
in (match (_58_3609) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _150_1415 = (let _150_1414 = (let _150_1413 = (let _150_1412 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (_150_1412)))
in FStar_Syntax_Syntax.NT (_150_1413))
in (_150_1414)::[])
in (FStar_Syntax_Subst.subst _150_1415 wp_b_tgt))
in (

let expected_k = (let _150_1420 = (let _150_1418 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1417 = (let _150_1416 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_150_1416)::[])
in (_150_1418)::_150_1417))
in (let _150_1419 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _150_1420 _150_1419)))
in (

let lift_wp = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift_wp) expected_k)
in (

let repr_type = (fun eff_name a wp -> (

let no_reify = (fun l -> (let _150_1432 = (let _150_1431 = (let _150_1430 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _150_1429 = (FStar_TypeChecker_Env.get_range env)
in ((_150_1430), (_150_1429))))
in FStar_Syntax_Syntax.Error (_150_1431))
in (Prims.raise _150_1432)))
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
(let _150_1439 = (let _150_1437 = (let _150_1436 = (let _150_1435 = (FStar_Syntax_Syntax.as_arg a)
in (let _150_1434 = (let _150_1433 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_1433)::[])
in (_150_1435)::_150_1434))
in ((repr), (_150_1436)))
in FStar_Syntax_Syntax.Tm_app (_150_1437))
in (let _150_1438 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _150_1439 None _150_1438)))
end)
end)))
in (

let lift = (match (sub.FStar_Syntax_Syntax.lift) with
| None -> begin
None
end
| Some (_58_3625, lift) -> begin
(

let _58_3631 = (let _150_1440 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _150_1440))
in (match (_58_3631) with
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

let lift_wp_a = (let _150_1447 = (let _150_1445 = (let _150_1444 = (let _150_1443 = (FStar_Syntax_Syntax.as_arg a_typ)
in (let _150_1442 = (let _150_1441 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (_150_1441)::[])
in (_150_1443)::_150_1442))
in (((Prims.snd sub.FStar_Syntax_Syntax.lift_wp)), (_150_1444)))
in FStar_Syntax_Syntax.Tm_app (_150_1445))
in (let _150_1446 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _150_1447 None _150_1446)))
in (repr_type sub.FStar_Syntax_Syntax.target a_typ lift_wp_a))
in (

let expected_k = (let _150_1454 = (let _150_1452 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1451 = (let _150_1450 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (let _150_1449 = (let _150_1448 = (FStar_Syntax_Syntax.null_binder repr_f)
in (_150_1448)::[])
in (_150_1450)::_150_1449))
in (_150_1452)::_150_1451))
in (let _150_1453 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow _150_1454 _150_1453)))
in (

let _58_3644 = (tc_tot_or_gtot_term env expected_k)
in (match (_58_3644) with
| (expected_k, _58_3641, _58_3643) -> begin
(

let lift = (check_and_gen env lift expected_k)
in Some (lift))
end))))))))
end))
end)
in (

let sub = (

let _58_3647 = sub
in {FStar_Syntax_Syntax.source = _58_3647.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _58_3647.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift})
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

let _58_3660 = ()
in (

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _58_3666 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_58_3666) with
| (tps, c) -> begin
(

let _58_3670 = (tc_tparams env tps)
in (match (_58_3670) with
| (tps, env, us) -> begin
(

let _58_3674 = (tc_comp env c)
in (match (_58_3674) with
| (c, u, g) -> begin
(

let _58_3675 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let _58_3681 = (let _150_1455 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _150_1455))
in (match (_58_3681) with
| (uvs, t) -> begin
(

let _58_3700 = (match ((let _150_1457 = (let _150_1456 = (FStar_Syntax_Subst.compress t)
in _150_1456.FStar_Syntax_Syntax.n)
in ((tps), (_150_1457)))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_58_3684, c)) -> begin
(([]), (c))
end
| (_58_3690, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
((tps), (c))
end
| _58_3697 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_58_3700) with
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

let _58_3711 = ()
in (

let _58_3715 = (let _150_1459 = (let _150_1458 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _150_1458))
in (check_and_gen env t _150_1459))
in (match (_58_3715) with
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

let _58_3735 = (tc_term env e)
in (match (_58_3735) with
| (e, c, g1) -> begin
(

let _58_3740 = (let _150_1463 = (let _150_1460 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_150_1460))
in (let _150_1462 = (let _150_1461 = (c.FStar_Syntax_Syntax.comp ())
in ((e), (_150_1461)))
in (check_expected_effect env _150_1463 _150_1462)))
in (match (_58_3740) with
| (e, _58_3738, g) -> begin
(

let _58_3741 = (let _150_1464 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _150_1464))
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
(let _150_1476 = (let _150_1475 = (let _150_1474 = (let _150_1473 = (FStar_Syntax_Print.lid_to_string l)
in (let _150_1472 = (FStar_Syntax_Print.quals_to_string q)
in (let _150_1471 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _150_1473 _150_1472 _150_1471))))
in ((_150_1474), (r)))
in FStar_Syntax_Syntax.Error (_150_1475))
in (Prims.raise _150_1476))
end
end))
in (

let _58_3785 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _58_3762 lb -> (match (_58_3762) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _58_3781 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
((gen), (lb), (quals_opt))
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (

let _58_3776 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _58_3775 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _150_1479 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Syntax_Const.effect_ALL_lid), (tval), (lb.FStar_Syntax_Syntax.lbdef)))
in ((false), (_150_1479), (quals_opt)))))
end)
in (match (_58_3781) with
| (gen, lb, quals_opt) -> begin
((gen), ((lb)::lbs), (quals_opt))
end)))
end)) ((true), ([]), (if (quals = []) then begin
None
end else begin
Some (quals)
end))))
in (match (_58_3785) with
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
| _58_3794 -> begin
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

let e = (let _150_1483 = (let _150_1482 = (let _150_1481 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((((Prims.fst lbs)), (lbs'))), (_150_1481)))
in FStar_Syntax_Syntax.Tm_let (_150_1482))
in (FStar_Syntax_Syntax.mk _150_1483 None r))
in (

let _58_3828 = (match ((tc_maybe_toplevel_term (

let _58_3798 = env
in {FStar_TypeChecker_Env.solver = _58_3798.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_3798.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_3798.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_3798.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_3798.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_3798.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_3798.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_3798.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_3798.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_3798.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_3798.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _58_3798.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _58_3798.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_3798.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_3798.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_3798.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _58_3798.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_3798.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_3798.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _58_3805; FStar_Syntax_Syntax.pos = _58_3803; FStar_Syntax_Syntax.vars = _58_3801}, _58_3812, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_58_3816, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _58_3822 -> begin
quals
end)
in ((FStar_Syntax_Syntax.Sig_let (((lbs), (r), (lids), (quals)))), (lbs)))
end
| _58_3825 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_58_3828) with
| (se, lbs) -> begin
(

let _58_3834 = if (log env) then begin
(let _150_1491 = (let _150_1490 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _150_1487 = (let _150_1486 = (let _150_1485 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _150_1485.FStar_Syntax_Syntax.fv_name)
in _150_1486.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _150_1487))) with
| None -> begin
true
end
| _58_3832 -> begin
false
end)
in if should_log then begin
(let _150_1489 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _150_1488 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _150_1489 _150_1488)))
end else begin
""
end))))
in (FStar_All.pipe_right _150_1490 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _150_1491))
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
| _58_3844 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _58_3854 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_58_3856) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _58_3867, _58_3869) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _58_3875 -> (match (_58_3875) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _58_3881, _58_3883, quals, r) -> begin
(

let dec = (let _150_1507 = (let _150_1506 = (let _150_1505 = (let _150_1504 = (let _150_1503 = (FStar_Syntax_Syntax.mk_Total t)
in ((bs), (_150_1503)))
in FStar_Syntax_Syntax.Tm_arrow (_150_1504))
in (FStar_Syntax_Syntax.mk _150_1505 None r))
in ((l), (us), (_150_1506), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_150_1507))
in (((dec)::out), (hidden)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _58_3893, _58_3895, _58_3897, _58_3899, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r)))
in (((dec)::out), ((l)::hidden)))
end
| _58_3905 -> begin
((out), (hidden))
end)
end)) ses (([]), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end
| FStar_Syntax_Syntax.Sig_assume (_58_3907, _58_3909, quals, _58_3912) -> begin
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
| _58_3931 -> begin
false
end)))) then begin
(((se)::[]), (hidden))
end else begin
(([]), (hidden))
end
end
end
| FStar_Syntax_Syntax.Sig_main (_58_3933) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _58_3952, _58_3954, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
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
(let _150_1514 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _150_1513 = (let _150_1512 = (let _150_1511 = (let _150_1510 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _150_1510.FStar_Syntax_Syntax.fv_name)
in _150_1511.FStar_Syntax_Syntax.v)
in ((_150_1512), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_150_1513)))))
in ((_150_1514), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let _58_4001 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _58_3974 se -> (match (_58_3974) with
| (ses, exports, env, hidden) -> begin
(

let _58_3976 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1521 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _150_1521))
end else begin
()
end
in (

let _58_3980 = (tc_decl env se)
in (match (_58_3980) with
| (ses', env) -> begin
(

let _58_3983 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _150_1526 = (FStar_List.fold_left (fun s se -> (let _150_1525 = (let _150_1524 = (FStar_Syntax_Print.sigelt_to_string se)
in (Prims.strcat s _150_1524))
in (Prims.strcat _150_1525 "\n"))) "" ses')
in (FStar_Util.print1 "Checked: %s\n" _150_1526))
end else begin
()
end
in (

let _58_3986 = (FStar_List.iter (fun se -> (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)) ses')
in (

let _58_3995 = (FStar_List.fold_left (fun _58_3990 se -> (match (_58_3990) with
| (le, lh) -> begin
(

let tup = (for_export hidden se)
in (((FStar_List.rev_append (Prims.fst tup) le)), ((FStar_List.rev_append (Prims.snd tup) lh))))
end)) (([]), ([])) ses')
in (match (_58_3995) with
| (exported, hidden) -> begin
(((FStar_List.rev_append ses' ses)), (((FStar_List.rev_append exported []))::exports), (env), (hidden))
end))))
end)))
end)) (([]), ([]), (env), ([]))))
in (match (_58_4001) with
| (ses, exports, env, _58_4000) -> begin
(let _150_1530 = (FStar_All.pipe_right (FStar_List.rev_append exports []) FStar_List.flatten)
in (((FStar_List.rev_append ses [])), (_150_1530), (env)))
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

let _58_4006 = env
in (let _150_1535 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _58_4006.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_4006.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_4006.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_4006.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_4006.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_4006.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_4006.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_4006.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_4006.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_4006.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_4006.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_4006.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_4006.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_4006.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_4006.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_4006.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _150_1535; FStar_TypeChecker_Env.type_of = _58_4006.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_4006.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_4006.FStar_TypeChecker_Env.use_bv_sorts}))
in (

let _58_4009 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let _58_4015 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_58_4015) with
| (ses, exports, env) -> begin
(((

let _58_4016 = modul
in {FStar_Syntax_Syntax.name = _58_4016.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _58_4016.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _58_4016.FStar_Syntax_Syntax.is_interface})), (exports), (env))
end))))))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let _58_4024 = (tc_decls env decls)
in (match (_58_4024) with
| (ses, exports, env) -> begin
(

let modul = (

let _58_4025 = modul
in {FStar_Syntax_Syntax.name = _58_4025.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _58_4025.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _58_4025.FStar_Syntax_Syntax.is_interface})
in ((modul), (exports), (env)))
end)))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul = (

let _58_4031 = modul
in {FStar_Syntax_Syntax.name = _58_4031.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _58_4031.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in (

let _58_4041 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(

let _58_4035 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let _58_4037 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (

let _58_4039 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _150_1548 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _150_1548 Prims.ignore)))))
end else begin
()
end
in ((modul), (env))))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let _58_4048 = (tc_partial_modul env modul)
in (match (_58_4048) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _58_4051 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _150_1557 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _150_1557))
end else begin
()
end
in (

let env = (

let _58_4053 = env
in {FStar_TypeChecker_Env.solver = _58_4053.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_4053.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_4053.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_4053.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_4053.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_4053.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_4053.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_4053.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_4053.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_4053.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_4053.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_4053.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_4053.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_4053.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_4053.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_4053.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_4053.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _58_4053.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_4053.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_4053.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _58_4069 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _58_4061) -> begin
(let _150_1562 = (let _150_1561 = (let _150_1560 = (FStar_TypeChecker_Env.get_range env)
in (((Prims.strcat "Implicit argument: " msg)), (_150_1560)))
in FStar_Syntax_Syntax.Error (_150_1561))
in (Prims.raise _150_1562))
end
in (match (_58_4069) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end else begin
(let _150_1567 = (let _150_1566 = (let _150_1565 = (let _150_1563 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _150_1563))
in (let _150_1564 = (FStar_TypeChecker_Env.get_range env)
in ((_150_1565), (_150_1564))))
in FStar_Syntax_Syntax.Error (_150_1566))
in (Prims.raise _150_1567))
end
end)))))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

let _58_4072 = if (FStar_Options.debug_any ()) then begin
(let _150_1572 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _150_1572))
end else begin
()
end
in (

let _58_4076 = (tc_modul env m)
in (match (_58_4076) with
| (m, env) -> begin
(

let _58_4077 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _150_1573 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _150_1573))
end else begin
()
end
in ((m), (env)))
end))))




