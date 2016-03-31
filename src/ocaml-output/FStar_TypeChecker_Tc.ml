
open Prims

let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_ST.read FStar_Options.log_types) && (not ((let _157_3 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _157_3))))))


let rng : FStar_TypeChecker_Env.env  ->  FStar_Range.range = (fun env -> (FStar_TypeChecker_Env.get_range env))


let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _68_18 = env
in {FStar_TypeChecker_Env.solver = _68_18.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_18.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_18.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_18.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_18.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_18.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_18.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_18.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_18.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _68_18.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_18.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_18.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _68_18.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _68_18.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_18.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_18.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_18.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _68_18.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _68_18.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_18.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_18.FStar_TypeChecker_Env.use_bv_sorts}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _68_21 = env
in {FStar_TypeChecker_Env.solver = _68_21.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_21.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_21.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_21.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_21.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_21.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_21.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_21.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_21.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _68_21.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_21.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_21.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _68_21.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _68_21.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_21.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_21.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_21.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _68_21.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _68_21.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_21.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_21.FStar_TypeChecker_Env.use_bv_sorts}))


let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (

let r = if (tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
v.FStar_Syntax_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos tl.FStar_Syntax_Syntax.pos)
end
in (let _157_17 = (let _157_16 = (FStar_Syntax_Syntax.as_arg v)
in (let _157_15 = (let _157_14 = (FStar_Syntax_Syntax.as_arg tl)
in (_157_14)::[])
in (_157_16)::_157_15))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _157_17 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _68_1 -> (match (_68_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _68_31 -> begin
false
end))


let steps : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Normalize.step Prims.list = (fun env -> if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::[]
end else begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]
end)


let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Beta)::[]) env t))


let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _157_30 = (steps env)
in (FStar_TypeChecker_Normalize.normalize _157_30 env t)))


let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _157_35 = (steps env)
in (FStar_TypeChecker_Normalize.normalize_comp _157_35 env c)))


let check_no_escape : FStar_Syntax_Syntax.term Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun head_opt env fvs kt -> (

let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
()
end
| _68_48 -> begin
(

let fvs' = (let _157_48 = if try_norm then begin
(norm env t)
end else begin
t
end
in (FStar_Syntax_Free.names _157_48))
in (match ((FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)) with
| None -> begin
()
end
| Some (x) -> begin
if (not (try_norm)) then begin
(aux true t)
end else begin
(

let fail = (fun _68_55 -> (match (()) with
| () -> begin
(

let msg = (match (head_opt) with
| None -> begin
(let _157_52 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _157_52))
end
| Some (head) -> begin
(let _157_54 = (FStar_Syntax_Print.bv_to_string x)
in (let _157_53 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _157_54 _157_53)))
end)
in (let _157_57 = (let _157_56 = (let _157_55 = (FStar_TypeChecker_Env.get_range env)
in (msg, _157_55))
in FStar_Syntax_Syntax.Error (_157_56))
in (Prims.raise _157_57)))
end))
in (

let s = (let _157_59 = (let _157_58 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _157_58))
in (FStar_TypeChecker_Util.new_uvar env _157_59))
in (match ((FStar_TypeChecker_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g)
end
| _68_64 -> begin
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

let _68_67 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_65 = (FStar_Syntax_Print.bv_to_string (Prims.fst b))
in (let _157_64 = (FStar_Syntax_Print.term_to_string (Prims.fst b).FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _157_65 _157_64)))
end else begin
()
end
in (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))
end)


let maybe_make_subst = (fun _68_2 -> (match (_68_2) with
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Syntax_Syntax.NT ((x, e)))::[]
end
| _68_76 -> begin
[]
end))


let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.subst_t = (fun s b v -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
s
end else begin
(FStar_Syntax_Syntax.NT (((Prims.fst b), v)))::s
end)


let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (

let _68_82 = lc
in {FStar_Syntax_Syntax.eff_name = _68_82.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _68_82.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _68_84 -> (match (()) with
| () -> begin
(let _157_78 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _157_78 t))
end))}))


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _157_87 = if (not ((FStar_Syntax_Util.is_pure_or_ghost_function t))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _157_87))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _68_116 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, guard)
end
| Some (t') -> begin
(

let _68_98 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_89 = (FStar_Syntax_Print.term_to_string t)
in (let _157_88 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _157_89 _157_88)))
end else begin
()
end
in (

let _68_102 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_68_102) with
| (e, lc) -> begin
(

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _68_106 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_68_106) with
| (e, g) -> begin
(

let _68_107 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_91 = (FStar_Syntax_Print.term_to_string t)
in (let _157_90 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _157_91 _157_90)))
end else begin
()
end
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let _68_112 = (let _157_97 = (FStar_All.pipe_left (fun _157_96 -> Some (_157_96)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _157_97 env e lc g))
in (match (_68_112) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))))
end)))
end)))
end)
in (match (_68_116) with
| (e, lc, g) -> begin
(

let _68_117 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_98 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _157_98))
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

let _68_127 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_68_127) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _68_132 -> (match (_68_132) with
| (e, c) -> begin
(

let expected_c_opt = (match (copt) with
| Some (_68_134) -> begin
copt
end
| None -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
(

let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (match ((FStar_TypeChecker_Env.default_effect env md.FStar_Syntax_Syntax.mname)) with
| None -> begin
None
end
| Some (l) -> begin
(

let flags = if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) then begin
(FStar_Syntax_Syntax.TOTAL)::[]
end else begin
if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_ML_lid) then begin
(FStar_Syntax_Syntax.MLEFFECT)::[]
end else begin
[]
end
end
in (

let def = (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.effect_name = l; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = flags})
in Some (def)))
end)))
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _157_111 = (norm_c env c)
in (e, _157_111, FStar_TypeChecker_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(

let _68_148 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_114 = (FStar_Syntax_Print.term_to_string e)
in (let _157_113 = (FStar_Syntax_Print.comp_to_string c)
in (let _157_112 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _157_114 _157_113 _157_112))))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _68_151 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_117 = (FStar_Syntax_Print.term_to_string e)
in (let _157_116 = (FStar_Syntax_Print.comp_to_string c)
in (let _157_115 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _157_117 _157_116 _157_115))))
end else begin
()
end
in (

let _68_157 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_68_157) with
| (e, _68_155, g) -> begin
(

let g = (let _157_118 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _157_118 "could not prove post-condition" g))
in (

let _68_159 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_120 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _157_119 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _157_120 _157_119)))
end else begin
()
end
in (e, expected_c, g)))
end)))))
end))
end))


let no_logical_guard = (fun env _68_165 -> (match (_68_165) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
(te, kt, f)
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _157_126 = (let _157_125 = (let _157_124 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _157_123 = (FStar_TypeChecker_Env.get_range env)
in (_157_124, _157_123)))
in FStar_Syntax_Syntax.Error (_157_125))
in (Prims.raise _157_126))
end)
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _157_129 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _157_129))
end))


let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _68_189; FStar_Syntax_Syntax.result_typ = _68_187; FStar_Syntax_Syntax.effect_args = _pre::_post::(pats, _68_181)::[]; FStar_Syntax_Syntax.flags = _68_178}) -> begin
(

let pat_vars = (FStar_Syntax_Free.names pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _68_196 -> (match (_68_196) with
| (b, _68_195) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _68_200) -> begin
(let _157_136 = (let _157_135 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _157_135))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _157_136))
end))
end
| _68_204 -> begin
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

let _68_211 = env
in {FStar_TypeChecker_Env.solver = _68_211.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_211.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_211.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_211.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_211.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_211.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_211.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_211.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_211.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_211.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_211.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_211.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _68_211.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _68_211.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_211.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_211.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_211.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _68_211.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _68_211.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_211.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_211.FStar_TypeChecker_Env.use_bv_sorts})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _68_223 -> (match (_68_223) with
| (b, _68_222) -> begin
(

let t = (let _157_150 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _157_150))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _68_232 -> begin
(let _157_151 = (FStar_Syntax_Syntax.bv_to_name b)
in (_157_151)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let _68_238 = (FStar_Syntax_Util.head_and_args dec)
in (match (_68_238) with
| (head, _68_237) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _68_242 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _68_3 -> (match (_68_3) with
| FStar_Syntax_Syntax.DECREASES (_68_246) -> begin
true
end
| _68_249 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _68_254 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| x::[] -> begin
x
end
| _68_259 -> begin
(mk_lex_list xs)
end))
end)))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun _68_264 -> (match (_68_264) with
| (l, t) -> begin
(match ((let _157_157 = (FStar_Syntax_Subst.compress t)
in _157_157.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _68_271 -> (match (_68_271) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _157_161 = (let _157_160 = (let _157_159 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_157_159))
in (FStar_Syntax_Syntax.new_bv _157_160 x.FStar_Syntax_Syntax.sort))
in (_157_161, imp))
end else begin
(x, imp)
end
end))))
in (

let _68_275 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_68_275) with
| (formals, c) -> begin
(

let dec = (decreases_clause formals c)
in (

let precedes = (let _157_165 = (let _157_164 = (FStar_Syntax_Syntax.as_arg dec)
in (let _157_163 = (let _157_162 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_157_162)::[])
in (_157_164)::_157_163))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _157_165 None r))
in (

let _68_282 = (FStar_Util.prefix formals)
in (match (_68_282) with
| (bs, (last, imp)) -> begin
(

let last = (

let _68_283 = last
in (let _157_166 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _68_283.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_283.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _157_166}))
in (

let refined_formals = (FStar_List.append bs (((last, imp))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (

let _68_288 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_169 = (FStar_Syntax_Print.lbname_to_string l)
in (let _157_168 = (FStar_Syntax_Print.term_to_string t)
in (let _157_167 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _157_169 _157_168 _157_167))))
end else begin
()
end
in (l, t')))))
end))))
end)))
end
| _68_291 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end))


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let _68_294 = env
in {FStar_TypeChecker_Env.solver = _68_294.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_294.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_294.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_294.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_294.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_294.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_294.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_294.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_294.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_294.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_294.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_294.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_294.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _68_294.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_294.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_294.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_294.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _68_294.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _68_294.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_294.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_294.FStar_TypeChecker_Env.use_bv_sorts}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (

let _68_299 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_238 = (let _157_236 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _157_236))
in (let _157_237 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _157_238 _157_237)))
end else begin
()
end
in (

let top = e
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_68_303) -> begin
(let _157_242 = (FStar_Syntax_Subst.compress e)
in (tc_term env _157_242))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let _68_344 = (tc_tot_or_gtot_term env e)
in (match (_68_344) with
| (e, c, g) -> begin
(

let g = (

let _68_345 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _68_345.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_345.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_345.FStar_TypeChecker_Env.implicits})
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let _68_355 = (FStar_Syntax_Util.type_u ())
in (match (_68_355) with
| (t, u) -> begin
(

let _68_359 = (tc_check_tot_or_gtot_term env e t)
in (match (_68_359) with
| (e, c, g) -> begin
(

let _68_366 = (

let _68_363 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_68_363) with
| (env, _68_362) -> begin
(tc_pats env pats)
end))
in (match (_68_366) with
| (pats, g') -> begin
(

let g' = (

let _68_367 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _68_367.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_367.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_367.FStar_TypeChecker_Env.implicits})
in (let _157_244 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_pattern (pats)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _157_243 = (FStar_TypeChecker_Rel.conj_guard g g')
in (_157_244, c, _157_243))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _157_245 = (FStar_Syntax_Subst.compress e)
in _157_245.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_68_376, {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _68_383; FStar_Syntax_Syntax.lbtyp = _68_381; FStar_Syntax_Syntax.lbeff = _68_379; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(

let _68_394 = (let _157_246 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _157_246 e1))
in (match (_68_394) with
| (e1, c1, g1) -> begin
(

let _68_398 = (tc_term env e2)
in (match (_68_398) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (None, c2))
in (

let e = (let _157_251 = (let _157_250 = (let _157_249 = (let _157_248 = (let _157_247 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Common.t_unit, e1))
in (_157_247)::[])
in (false, _157_248))
in (_157_249, e2))
in FStar_Syntax_Syntax.Tm_let (_157_250))
in (FStar_Syntax_Syntax.mk _157_251 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _157_252 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _157_252)))))
end))
end))
end
| _68_403 -> begin
(

let _68_407 = (tc_term env e)
in (match (_68_407) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let _68_416 = (tc_term env e)
in (match (_68_416) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, m))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _68_422) -> begin
(

let _68_429 = (tc_comp env expected_c)
in (match (_68_429) with
| (expected_c, _68_427, g) -> begin
(

let _68_433 = (tc_term env e)
in (match (_68_433) with
| (e, c', g') -> begin
(

let _68_437 = (let _157_254 = (let _157_253 = (c'.FStar_Syntax_Syntax.comp ())
in (e, _157_253))
in (check_expected_effect env (Some (expected_c)) _157_254))
in (match (_68_437) with
| (e, expected_c, g'') -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (let _157_257 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t_res), Some ((FStar_Syntax_Util.comp_effect_name expected_c))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _157_256 = (let _157_255 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _157_255))
in (_157_257, (FStar_Syntax_Util.lcomp_of_comp expected_c), _157_256))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _68_443) -> begin
(

let _68_448 = (FStar_Syntax_Util.type_u ())
in (match (_68_448) with
| (k, u) -> begin
(

let _68_453 = (tc_check_tot_or_gtot_term env t k)
in (match (_68_453) with
| (t, _68_451, f) -> begin
(

let _68_457 = (let _157_258 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _157_258 e))
in (match (_68_457) with
| (e, c, g) -> begin
(

let _68_461 = (let _157_262 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _68_458 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _157_262 e c f))
in (match (_68_461) with
| (c, f) -> begin
(

let _68_465 = (let _157_263 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t), Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _157_263 c))
in (match (_68_465) with
| (e, c, f2) -> begin
(let _157_265 = (let _157_264 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _157_264))
in (e, c, _157_265))
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

let env = (let _157_267 = (let _157_266 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _157_266 Prims.fst))
in (FStar_All.pipe_right _157_267 instantiate_both))
in (

let _68_472 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_269 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _157_268 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _157_269 _157_268)))
end else begin
()
end
in (

let _68_477 = (tc_term (no_inst env) head)
in (match (_68_477) with
| (head, chead, g_head) -> begin
(

let _68_481 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _157_270 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _157_270))
end else begin
(let _157_271 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _157_271))
end
in (match (_68_481) with
| (e, c, g) -> begin
(

let _68_482 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _157_272 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _157_272))
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

let _68_489 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_278 = (FStar_Syntax_Print.term_to_string e)
in (let _157_277 = (let _157_273 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _157_273))
in (let _157_276 = (let _157_275 = (FStar_TypeChecker_Env.expected_typ env0)
in (FStar_All.pipe_right _157_275 (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end))))
in (FStar_Util.print3 "(%s) About to check %s against expected typ %s\n" _157_278 _157_277 _157_276))))
end else begin
()
end
in (

let _68_494 = (comp_check_expected_typ env0 e c)
in (match (_68_494) with
| (e, c, g') -> begin
(

let _68_495 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_281 = (FStar_Syntax_Print.term_to_string e)
in (let _157_280 = (let _157_279 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _157_279))
in (FStar_Util.print2 "(%s) checked ... got %s\n" _157_281 _157_280)))
end else begin
()
end
in (

let gimp = (match ((let _157_282 = (FStar_Syntax_Subst.compress head)
in _157_282.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _68_499) -> begin
(

let imp = ("head of application is a uvar", env0, u, e, c.FStar_Syntax_Syntax.res_typ, head.FStar_Syntax_Syntax.pos)
in (

let _68_503 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _68_503.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _68_503.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_503.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _68_506 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (

let gres = (let _157_283 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _157_283))
in (

let _68_509 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _157_284 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print1 "Guard from application node is %s\n" _157_284))
end else begin
()
end
in (e, c, gres)))))
end)))))
end))
end)))))
end
| FStar_Syntax_Syntax.Tm_match (e1, eqns) -> begin
(

let _68_517 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_68_517) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let _68_522 = (tc_term env1 e1)
in (match (_68_522) with
| (e1, c1, g1) -> begin
(

let _68_533 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(

let _68_529 = (FStar_Syntax_Util.type_u ())
in (match (_68_529) with
| (k, _68_528) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _157_285 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_157_285, res_t)))
end))
end)
in (match (_68_533) with
| (env_branches, res_t) -> begin
(

let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let _68_550 = (

let _68_547 = (FStar_List.fold_right (fun _68_541 _68_544 -> (match ((_68_541, _68_544)) with
| ((_68_537, f, c, g), (caccum, gaccum)) -> begin
(let _157_288 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _157_288))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_68_547) with
| (cases, g) -> begin
(let _157_289 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_157_289, g))
end))
in (match (_68_550) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (guard_x), c_branches))
in (

let e = (let _157_293 = (let _157_292 = (let _157_291 = (FStar_List.map (fun _68_559 -> (match (_68_559) with
| (f, _68_554, _68_556, _68_558) -> begin
f
end)) t_eqns)
in (e1, _157_291))
in FStar_Syntax_Syntax.Tm_match (_157_292))
in (FStar_Syntax_Syntax.mk _157_293 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ), Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (

let _68_562 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _157_296 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _157_295 = (let _157_294 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _157_294))
in (FStar_Util.print2 "(%s) comp type = %s\n" _157_296 _157_295)))
end else begin
()
end
in (let _157_297 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _157_297))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_68_574); FStar_Syntax_Syntax.lbunivs = _68_572; FStar_Syntax_Syntax.lbtyp = _68_570; FStar_Syntax_Syntax.lbeff = _68_568; FStar_Syntax_Syntax.lbdef = _68_566}::[]), _68_580) -> begin
(

let _68_583 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_298 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _157_298))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _68_587), _68_590) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_68_605); FStar_Syntax_Syntax.lbunivs = _68_603; FStar_Syntax_Syntax.lbtyp = _68_601; FStar_Syntax_Syntax.lbeff = _68_599; FStar_Syntax_Syntax.lbdef = _68_597}::_68_595), _68_611) -> begin
(

let _68_614 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_299 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _157_299))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _68_618), _68_621) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let _68_635 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_68_635) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _157_313 = (let _157_312 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _157_312))
in FStar_Util.Inr (_157_313))
end
in (

let is_data_ctor = (fun _68_4 -> (match (_68_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _68_645 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _157_319 = (let _157_318 = (let _157_317 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _157_316 = (FStar_TypeChecker_Env.get_range env)
in (_157_317, _157_316)))
in FStar_Syntax_Syntax.Error (_157_318))
in (Prims.raise _157_319))
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

let g = (match ((let _157_320 = (FStar_Syntax_Subst.compress t1)
in _157_320.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_68_656) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _68_659 -> begin
(

let imp = ("uvar in term", env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (

let _68_661 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _68_661.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _68_661.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_661.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _68_667 = (FStar_Syntax_Util.type_u ())
in (match (_68_667) with
| (t, u) -> begin
(

let e = (FStar_TypeChecker_Util.new_uvar env t)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))
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

let _68_672 = x
in {FStar_Syntax_Syntax.ppname = _68_672.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_672.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let _68_678 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_68_678) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _157_322 = (let _157_321 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _157_321))
in FStar_Util.Inr (_157_322))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _68_685; FStar_Syntax_Syntax.pos = _68_683; FStar_Syntax_Syntax.vars = _68_681}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let _68_695 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_68_695) with
| (us', t) -> begin
(

let _68_702 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _157_325 = (let _157_324 = (let _157_323 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _157_323))
in FStar_Syntax_Syntax.Error (_157_324))
in (Prims.raise _157_325))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _68_701 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (

let fv' = (

let _68_704 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _68_706 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _68_706.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _68_706.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _68_704.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _68_704.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _157_328 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _157_328 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let _68_714 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_68_714) with
| (us, t) -> begin
(

let fv' = (

let _68_715 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _68_717 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _68_717.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _68_717.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _68_715.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _68_715.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _157_329 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _157_329 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t)))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let t = (tc_constant env top.FStar_Syntax_Syntax.pos c)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _68_731 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_68_731) with
| (bs, c) -> begin
(

let env0 = env
in (

let _68_736 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_68_736) with
| (env, _68_735) -> begin
(

let _68_741 = (tc_binders env bs)
in (match (_68_741) with
| (bs, env, g, us) -> begin
(

let _68_745 = (tc_comp env c)
in (match (_68_745) with
| (c, uc, f) -> begin
(

let e = (

let _68_746 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _68_746.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _68_746.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _68_746.FStar_Syntax_Syntax.vars})
in (

let _68_749 = (check_smt_pat env e bs c)
in (

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _157_330 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _157_330))
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

let _68_765 = (let _157_332 = (let _157_331 = (FStar_Syntax_Syntax.mk_binder x)
in (_157_331)::[])
in (FStar_Syntax_Subst.open_term _157_332 phi))
in (match (_68_765) with
| (x, phi) -> begin
(

let env0 = env
in (

let _68_770 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_68_770) with
| (env, _68_769) -> begin
(

let _68_775 = (let _157_333 = (FStar_List.hd x)
in (tc_binder env _157_333))
in (match (_68_775) with
| (x, env, f1, u) -> begin
(

let _68_776 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_336 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _157_335 = (FStar_Syntax_Print.term_to_string phi)
in (let _157_334 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _157_336 _157_335 _157_334))))
end else begin
()
end
in (

let _68_781 = (FStar_Syntax_Util.type_u ())
in (match (_68_781) with
| (t_phi, _68_780) -> begin
(

let _68_786 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_68_786) with
| (phi, _68_784, f2) -> begin
(

let e = (

let _68_787 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _68_787.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _68_787.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _68_787.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _157_337 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _157_337))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _68_795) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (

let _68_801 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_338 = (FStar_Syntax_Print.term_to_string (

let _68_799 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _68_799.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _68_799.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _68_799.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _157_338))
end else begin
()
end
in (

let _68_805 = (FStar_Syntax_Subst.open_term bs body)
in (match (_68_805) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _68_807 -> begin
(let _157_340 = (let _157_339 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _157_339))
in (FStar_All.failwith _157_340))
end)))))
and tc_constant : FStar_TypeChecker_Env.env  ->  FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun env r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_68_813) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_68_816, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_68_821, Some (FStar_Const.Unsigned, FStar_Const.Int8)) -> begin
FStar_TypeChecker_Common.t_uint8
end
| FStar_Const.Const_int (_68_829, Some (FStar_Const.Signed, FStar_Const.Int8)) -> begin
FStar_TypeChecker_Common.t_int8
end
| FStar_Const.Const_int (_68_837, Some (FStar_Const.Unsigned, FStar_Const.Int16)) -> begin
FStar_TypeChecker_Common.t_uint16
end
| FStar_Const.Const_int (_68_845, Some (FStar_Const.Signed, FStar_Const.Int16)) -> begin
FStar_TypeChecker_Common.t_int16
end
| FStar_Const.Const_int (_68_853, Some (FStar_Const.Unsigned, FStar_Const.Int32)) -> begin
FStar_TypeChecker_Common.t_uint32
end
| FStar_Const.Const_int (_68_861, Some (FStar_Const.Signed, FStar_Const.Int32)) -> begin
FStar_TypeChecker_Common.t_int32
end
| FStar_Const.Const_int (_68_869, Some (FStar_Const.Unsigned, FStar_Const.Int64)) -> begin
FStar_TypeChecker_Common.t_uint64
end
| FStar_Const.Const_int (_68_877, Some (FStar_Const.Signed, FStar_Const.Int64)) -> begin
FStar_TypeChecker_Common.t_int64
end
| FStar_Const.Const_string (_68_885) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_68_888) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_68_891) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_68_895) -> begin
(

let fail = (fun _68_898 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Range constant cannot be checked in this context; expected an instance of \'range_of\'", r))))
end))
in (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(fail ())
end
| Some (t) -> begin
if (let _157_346 = (FStar_Syntax_Util.destruct t FStar_Syntax_Const.range_of_lid)
in (FStar_Option.isSome _157_346)) then begin
t
end else begin
(fail ())
end
end))
end
| _68_903 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(

let _68_910 = (FStar_Syntax_Util.type_u ())
in (match (_68_910) with
| (k, u) -> begin
(

let _68_915 = (tc_check_tot_or_gtot_term env t k)
in (match (_68_915) with
| (t, _68_913, g) -> begin
(let _157_349 = (FStar_Syntax_Syntax.mk_Total t)
in (_157_349, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(

let _68_920 = (FStar_Syntax_Util.type_u ())
in (match (_68_920) with
| (k, u) -> begin
(

let _68_925 = (tc_check_tot_or_gtot_term env t k)
in (match (_68_925) with
| (t, _68_923, g) -> begin
(let _157_350 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_157_350, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (

let tc = (let _157_352 = (let _157_351 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_157_351)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _157_352 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let _68_934 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_68_934) with
| (tc, _68_932, f) -> begin
(

let _68_938 = (FStar_Syntax_Util.head_and_args tc)
in (match (_68_938) with
| (_68_936, args) -> begin
(

let _68_941 = (let _157_354 = (FStar_List.hd args)
in (let _157_353 = (FStar_List.tl args)
in (_157_354, _157_353)))
in (match (_68_941) with
| (res, args) -> begin
(

let _68_957 = (let _157_356 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _68_5 -> (match (_68_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _68_948 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_68_948) with
| (env, _68_947) -> begin
(

let _68_953 = (tc_tot_or_gtot_term env e)
in (match (_68_953) with
| (e, _68_951, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _157_356 FStar_List.unzip))
in (match (_68_957) with
| (flags, guards) -> begin
(

let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| _68_962 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _157_358 = (FStar_Syntax_Syntax.mk_Comp (

let _68_964 = c
in {FStar_Syntax_Syntax.effect_name = _68_964.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _68_964.FStar_Syntax_Syntax.flags}))
in (let _157_357 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_157_358, u, _157_357))))
end))
end))
end))
end))))
end))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_68_972) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _157_363 = (aux u)
in FStar_Syntax_Syntax.U_succ (_157_363))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _157_364 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_157_364))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _157_368 = (let _157_367 = (let _157_366 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _157_365 = (FStar_TypeChecker_Env.get_range env)
in (_157_366, _157_365)))
in FStar_Syntax_Syntax.Error (_157_367))
in (Prims.raise _157_368))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _157_369 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _157_369 Prims.snd))
end
| _68_987 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _157_378 = (let _157_377 = (let _157_376 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_157_376, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_157_377))
in (Prims.raise _157_378)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun _68_1005 bs bs_expected -> (match (_68_1005) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| ((hd, imp)::bs, (hd_expected, imp')::bs_expected) -> begin
(

let _68_1036 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _157_395 = (let _157_394 = (let _157_393 = (let _157_391 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _157_391))
in (let _157_392 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_157_393, _157_392)))
in FStar_Syntax_Syntax.Error (_157_394))
in (Prims.raise _157_395))
end
| _68_1035 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _68_1053 = (match ((let _157_396 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _157_396.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _68_1041 -> begin
(

let _68_1042 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_397 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _157_397))
end else begin
()
end
in (

let _68_1048 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_68_1048) with
| (t, _68_1046, g1) -> begin
(

let g2 = (let _157_399 = (FStar_TypeChecker_Env.get_range env)
in (let _157_398 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _157_399 "Type annotation on parameter incompatible with the expected type" _157_398)))
in (

let g = (let _157_400 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _157_400))
in (t, g)))
end)))
end)
in (match (_68_1053) with
| (t, g) -> begin
(

let hd = (

let _68_1054 = hd
in {FStar_Syntax_Syntax.ppname = _68_1054.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_1054.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = (hd, imp)
in (

let b_expected = (hd_expected, imp')
in (

let env = (maybe_push_binding env b)
in (

let subst = (let _157_401 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _157_401))
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

let _68_1075 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _68_1074 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (

let _68_1082 = (tc_binders env bs)
in (match (_68_1082) with
| (bs, envbody, g, _68_1081) -> begin
(

let _68_1100 = (match ((let _157_408 = (FStar_Syntax_Subst.compress body)
in _157_408.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _68_1087) -> begin
(

let _68_1094 = (tc_comp envbody c)
in (match (_68_1094) with
| (c, _68_1092, g') -> begin
(let _157_409 = (FStar_TypeChecker_Rel.conj_guard g g')
in (Some (c), body, _157_409))
end))
end
| _68_1096 -> begin
(None, body, g)
end)
in (match (_68_1100) with
| (copt, body, g) -> begin
(None, bs, [], copt, envbody, body, g)
end))
end)))
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm t -> (match ((let _157_414 = (FStar_Syntax_Subst.compress t)
in _157_414.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let _68_1127 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _68_1126 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _68_1134 = (tc_binders env bs)
in (match (_68_1134) with
| (bs, envbody, g, _68_1133) -> begin
(

let _68_1138 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_68_1138) with
| (envbody, _68_1137) -> begin
(Some ((t, true)), bs, [], None, envbody, body, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _68_1141) -> begin
(

let _68_1152 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_68_1152) with
| (_68_1145, bs, bs', copt, env, body, g) -> begin
(Some ((t, false)), bs, bs', copt, env, body, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _68_1159 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_68_1159) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun _68_1170 c_expected -> (match (_68_1170) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _157_425 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _157_425))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (let _157_426 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _157_426))
in (let _157_427 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _157_427)))
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

let _68_1191 = (check_binders env more_bs bs_expected)
in (match (_68_1191) with
| (env, bs', more, guard', subst) -> begin
(let _157_429 = (let _157_428 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _157_428, subst))
in (handle_more _157_429 c_expected))
end))
end
| _68_1193 -> begin
(let _157_431 = (let _157_430 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _157_430))
in (fail _157_431 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _157_432 = (check_binders env bs bs_expected)
in (handle_more _157_432 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let _68_1199 = envbody
in {FStar_TypeChecker_Env.solver = _68_1199.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_1199.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_1199.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_1199.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_1199.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_1199.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_1199.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_1199.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_1199.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_1199.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_1199.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_1199.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _68_1199.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _68_1199.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_1199.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_1199.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_1199.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _68_1199.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _68_1199.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_1199.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_1199.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _68_1204 _68_1207 -> (match ((_68_1204, _68_1207)) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _68_1213 = (let _157_442 = (let _157_441 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _157_441 Prims.fst))
in (tc_term _157_442 t))
in (match (_68_1213) with
| (t, _68_1210, _68_1212) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _157_443 = (FStar_Syntax_Syntax.mk_binder (

let _68_1217 = x
in {FStar_Syntax_Syntax.ppname = _68_1217.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_1217.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_157_443)::letrec_binders)
end
| _68_1220 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (

let _68_1226 = (check_actuals_against_formals env bs bs_expected)
in (match (_68_1226) with
| (envbody, bs, g, c) -> begin
(

let _68_1229 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_68_1229) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, body, g))
end))
end))))
end))
end
| _68_1232 -> begin
if (not (norm)) then begin
(let _157_444 = (unfold_whnf env t)
in (as_function_typ true _157_444))
end else begin
(

let _68_1242 = (expected_function_typ env None body)
in (match (_68_1242) with
| (_68_1234, bs, _68_1237, c_opt, envbody, body, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, body, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let _68_1246 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_68_1246) with
| (env, topt) -> begin
(

let _68_1250 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_445 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _157_445 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (

let _68_1259 = (expected_function_typ env topt body)
in (match (_68_1259) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let _68_1265 = (tc_term (

let _68_1260 = envbody
in {FStar_TypeChecker_Env.solver = _68_1260.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_1260.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_1260.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_1260.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_1260.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_1260.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_1260.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_1260.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_1260.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_1260.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_1260.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_1260.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_1260.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _68_1260.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _68_1260.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_1260.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _68_1260.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _68_1260.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_1260.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_1260.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_68_1265) with
| (body, cbody, guard_body) -> begin
(

let _68_1266 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_449 = (FStar_Syntax_Print.term_to_string body)
in (let _157_448 = (let _157_446 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _157_446))
in (let _157_447 = (FStar_TypeChecker_Rel.guard_to_string env guard_body)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _157_449 _157_448 _157_447))))
end else begin
()
end
in (

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _68_1269 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _157_452 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _157_451 = (let _157_450 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _157_450))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _157_452 _157_451)))
end else begin
()
end
in (

let _68_1276 = (let _157_454 = (let _157_453 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _157_453))
in (check_expected_effect (

let _68_1271 = envbody
in {FStar_TypeChecker_Env.solver = _68_1271.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_1271.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_1271.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_1271.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_1271.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_1271.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_1271.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_1271.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_1271.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_1271.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_1271.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_1271.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_1271.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _68_1271.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _68_1271.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _68_1271.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_1271.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _68_1271.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _68_1271.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_1271.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_1271.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _157_454))
in (match (_68_1276) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _157_455 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _157_455))
end else begin
(

let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (FStar_Syntax_Util.abs bs body (Some ((FStar_Syntax_Util.lcomp_of_comp cbody))))
in (

let _68_1299 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_68_1288) -> begin
(e, t, guard)
end
| _68_1291 -> begin
(

let _68_1294 = if use_teq then begin
(let _157_456 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _157_456))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_68_1294) with
| (e, guard') -> begin
(let _157_457 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _157_457))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_68_1299) with
| (e, tfun, guard) -> begin
(

let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (

let _68_1303 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_68_1303) with
| (c, g) -> begin
(e, c, g)
end)))
end))))))
end)))))
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

let _68_1313 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_466 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _157_465 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _157_466 _157_465)))
end else begin
()
end
in (

let rec check_function_app = (fun norm tf -> (match ((let _157_471 = (FStar_Syntax_Util.unrefine tf)
in _157_471.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| (e, imp)::tl -> begin
(

let _68_1347 = (tc_term env e)
in (match (_68_1347) with
| (e, c, g_e) -> begin
(

let _68_1351 = (tc_args env tl)
in (match (_68_1351) with
| (args, comps, g_rest) -> begin
(let _157_476 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, (c)::comps, _157_476))
end))
end))
end))
in (

let _68_1355 = (tc_args env args)
in (match (_68_1355) with
| (args, comps, g_args) -> begin
(

let bs = (let _157_478 = (FStar_All.pipe_right comps (FStar_List.map (fun c -> (c.FStar_Syntax_Syntax.res_typ, None))))
in (FStar_Syntax_Util.null_binders_of_tks _157_478))
in (

let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _68_1362 -> begin
FStar_Syntax_Util.ml_comp
end)
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _157_493 = (FStar_Syntax_Subst.compress t)
in _157_493.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_68_1368) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _68_1373 -> begin
ml_or_tot
end)
end)
in (

let cres = (let _157_498 = (let _157_497 = (let _157_496 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _157_496 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _157_497))
in (ml_or_tot _157_498 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (

let _68_1377 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _157_501 = (FStar_Syntax_Print.term_to_string head)
in (let _157_500 = (FStar_Syntax_Print.term_to_string tf)
in (let _157_499 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _157_501 _157_500 _157_499))))
end else begin
()
end
in (

let _68_1379 = (let _157_502 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _157_502))
in (

let comp = (let _157_505 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_TypeChecker_Util.bind env None c (None, out))) ((chead)::comps) _157_505))
in (let _157_507 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _157_506 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_157_507, comp, _157_506)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _68_1390 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_68_1390) with
| (bs, c) -> begin
(

let rec tc_args = (fun _68_1398 bs cres args -> (match (_68_1398) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (_68_1405)))::rest, (_68_1413, None)::_68_1411) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _68_1419 = (check_no_escape (Some (head)) env fvs t)
in (

let _68_1425 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_68_1425) with
| (varg, _68_1423, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (

let arg = (let _157_516 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _157_516))
in (let _157_518 = (let _157_517 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _157_517, fvs))
in (tc_args _157_518 rest cres args))))
end))))
end
| ((x, aqual)::rest, (e, aq)::rest') -> begin
(

let _68_1457 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _68_1456 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let _68_1460 = x
in {FStar_Syntax_Syntax.ppname = _68_1460.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_1460.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (

let _68_1463 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _157_519 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _157_519))
end else begin
()
end
in (

let _68_1465 = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let _68_1468 = env
in {FStar_TypeChecker_Env.solver = _68_1468.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_1468.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_1468.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_1468.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_1468.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_1468.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_1468.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_1468.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_1468.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_1468.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_1468.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_1468.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_1468.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _68_1468.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _68_1468.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _68_1468.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_1468.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _68_1468.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _68_1468.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_1468.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_1468.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _68_1471 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_522 = (FStar_Syntax_Print.tag_of_term e)
in (let _157_521 = (FStar_Syntax_Print.term_to_string e)
in (let _157_520 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _157_522 _157_521 _157_520))))
end else begin
()
end
in (

let _68_1476 = (tc_term env e)
in (match (_68_1476) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(

let subst = (let _157_523 = (FStar_List.hd bs)
in (maybe_extend_subst subst _157_523 e))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(

let subst = (let _157_524 = (FStar_List.hd bs)
in (maybe_extend_subst subst _157_524 e))
in (

let _68_1483 = (((Some (x), c))::comps, g)
in (match (_68_1483) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _157_525 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _157_525)) then begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _157_526 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _157_526))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (newx), c))::comps, g, fvs) rest cres rest')))
end else begin
(let _157_530 = (let _157_529 = (let _157_528 = (let _157_527 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _157_527))
in (_157_528)::arg_rets)
in (subst, (arg)::outargs, _157_529, ((Some (x), c))::comps, g, (x)::fvs))
in (tc_args _157_530 rest cres rest'))
end
end
end))
end))))))))))
end
| (_68_1487, []) -> begin
(

let _68_1490 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let _68_1508 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _68_1498 -> (match (_68_1498) with
| (_68_1496, c) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _157_532 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _157_532 cres))
end else begin
(

let _68_1500 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_535 = (FStar_Syntax_Print.term_to_string head)
in (let _157_534 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _157_533 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _157_535 _157_534 _157_533))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _68_1504 -> begin
(

let g = (let _157_536 = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (FStar_All.pipe_right _157_536 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _157_541 = (let _157_540 = (let _157_539 = (let _157_538 = (let _157_537 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _157_537))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _157_538))
in (FStar_Syntax_Syntax.mk_Total _157_539))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _157_540))
in (_157_541, g)))
end)
in (match (_68_1508) with
| (cres, g) -> begin
(

let _68_1509 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_542 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _157_542))
end else begin
()
end
in (

let comp = (FStar_List.fold_left (fun out c -> (FStar_TypeChecker_Util.bind env None (Prims.snd c) ((Prims.fst c), out))) cres comps)
in (

let comp = (FStar_TypeChecker_Util.bind env None chead (None, comp))
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev outargs) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let comp = (FStar_TypeChecker_Util.record_application_site env app comp)
in (

let _68_1519 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp g)
in (match (_68_1519) with
| (comp, g) -> begin
(

let _68_1520 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_548 = (FStar_TypeChecker_Normalize.term_to_string env app)
in (let _157_547 = (let _157_546 = (comp.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Print.comp_to_string _157_546))
in (FStar_Util.print2 "\t Type of app term %s is %s\n" _157_548 _157_547)))
end else begin
()
end
in (app, comp, g))
end)))))))
end)))
end
| ([], arg::_68_1524) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _157_553 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _157_553 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let _68_1536 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_554 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _157_554))
end else begin
()
end
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs (FStar_Syntax_Util.lcomp_of_comp cres') args))
end
| _68_1539 when (not (norm)) -> begin
(let _157_555 = (unfold_whnf env tres)
in (aux true _157_555))
end
| _68_1541 -> begin
(let _157_561 = (let _157_560 = (let _157_559 = (let _157_557 = (FStar_TypeChecker_Normalize.term_to_string env tf)
in (let _157_556 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _157_557 _157_556)))
in (let _157_558 = (FStar_Syntax_Syntax.argpos arg)
in (_157_559, _157_558)))
in FStar_Syntax_Syntax.Error (_157_560))
in (Prims.raise _157_561))
end)))
in (aux false cres.FStar_Syntax_Syntax.res_typ))
end)
end))
in (tc_args ([], [], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs (FStar_Syntax_Util.lcomp_of_comp c) args))
end))
end
| _68_1543 -> begin
if (not (norm)) then begin
(let _157_562 = (unfold_whnf env tf)
in (check_function_app true _157_562))
end else begin
(let _157_565 = (let _157_564 = (let _157_563 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_157_563, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_157_564))
in (Prims.raise _157_565))
end
end))
in (let _157_567 = (let _157_566 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _157_566))
in (check_function_app false _157_567))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let _68_1579 = (FStar_List.fold_left2 (fun _68_1560 _68_1563 _68_1566 -> (match ((_68_1560, _68_1563, _68_1566)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(

let _68_1567 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let _68_1572 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_68_1572) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (let _157_577 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _157_577 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _157_581 = (let _157_579 = (let _157_578 = (FStar_Syntax_Syntax.as_arg e)
in (_157_578)::[])
in (FStar_List.append seen _157_579))
in (let _157_580 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_157_581, _157_580, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_68_1579) with
| (args, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = if ghost then begin
(let _157_582 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _157_582 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (

let _68_1584 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_68_1584) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _68_1586 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let _68_1593 = (FStar_Syntax_Subst.open_branch branch)
in (match (_68_1593) with
| (pattern, when_clause, branch_exp) -> begin
(

let _68_1598 = branch
in (match (_68_1598) with
| (cpat, _68_1596, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _68_1606 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_68_1606) with
| (pat_bvs, exps, p) -> begin
(

let _68_1607 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_594 = (FStar_Syntax_Print.pat_to_string p0)
in (let _157_593 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _157_594 _157_593)))
end else begin
()
end
in (

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let _68_1613 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_68_1613) with
| (env1, _68_1612) -> begin
(

let env1 = (

let _68_1614 = env1
in {FStar_TypeChecker_Env.solver = _68_1614.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_1614.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_1614.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_1614.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_1614.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_1614.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_1614.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_1614.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _68_1614.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_1614.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_1614.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_1614.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _68_1614.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _68_1614.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_1614.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_1614.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_1614.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _68_1614.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _68_1614.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_1614.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_1614.FStar_TypeChecker_Env.use_bv_sorts})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _68_1653 = (let _157_617 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _68_1619 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_597 = (FStar_Syntax_Print.term_to_string e)
in (let _157_596 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _157_597 _157_596)))
end else begin
()
end
in (

let _68_1624 = (tc_term env1 e)
in (match (_68_1624) with
| (e, lc, g) -> begin
(

let _68_1625 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_599 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _157_598 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _157_599 _157_598)))
end else begin
()
end
in (

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let _68_1631 = (let _157_600 = (FStar_TypeChecker_Rel.discharge_guard env (

let _68_1629 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _68_1629.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_1629.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_1629.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _157_600 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _157_605 = (let _157_604 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _157_604 (FStar_List.map (fun _68_1639 -> (match (_68_1639) with
| (u, _68_1638) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _157_605 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _68_1647 = if (let _157_606 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _157_606)) then begin
(

let unresolved = (let _157_607 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _157_607 FStar_Util.set_elements))
in (let _157_615 = (let _157_614 = (let _157_613 = (let _157_612 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _157_611 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _157_610 = (let _157_609 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _68_1646 -> (match (_68_1646) with
| (u, _68_1645) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _157_609 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _157_612 _157_611 _157_610))))
in (_157_613, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_157_614))
in (Prims.raise _157_615)))
end else begin
()
end
in (

let _68_1649 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_616 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _157_616))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _157_617 FStar_List.unzip))
in (match (_68_1653) with
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

let _68_1660 = (let _157_618 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _157_618 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_68_1660) with
| (scrutinee_env, _68_1659) -> begin
(

let _68_1666 = (tc_pat true pat_t pattern)
in (match (_68_1666) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let _68_1676 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(

let _68_1673 = (let _157_619 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _157_619 e))
in (match (_68_1673) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_68_1676) with
| (when_clause, g_when) -> begin
(

let _68_1680 = (tc_term pat_env branch_exp)
in (match (_68_1680) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _157_621 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _157_620 -> Some (_157_620)) _157_621))
end)
in (

let _68_1736 = (

let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _68_1698 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _157_625 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _157_624 -> Some (_157_624)) _157_625))
end))
end))) None))
in (

let _68_1706 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_68_1706) with
| (c, g_branch) -> begin
(

let _68_1731 = (match ((eqs, when_condition)) with
| (None, None) -> begin
(c, g_when)
end
| (Some (f), None) -> begin
(

let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _157_628 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _157_627 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_157_628, _157_627)))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (let _157_629 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_157_629))
in (let _157_632 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _157_631 = (let _157_630 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _157_630 g_when))
in (_157_632, _157_631)))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _157_633 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_157_633, g_when))))
end)
in (match (_68_1731) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _157_635 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _157_634 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_157_635, _157_634, g_branch))))
end))
end)))
in (match (_68_1736) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = (

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> if ((let _157_645 = (let _157_644 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _157_644))
in (FStar_List.length _157_645)) > 1) then begin
(

let disc = (let _157_646 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _157_646 FStar_Syntax_Syntax.Delta_equational None))
in (

let disc = (let _157_648 = (let _157_647 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_157_647)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _157_648 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _157_649 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_157_649)::[])))
end else begin
[]
end)
in (

let fail = (fun _68_1746 -> (match (()) with
| () -> begin
(let _157_655 = (let _157_654 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _157_653 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _157_652 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _157_654 _157_653 _157_652))))
in (FStar_All.failwith _157_655))
end))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _68_1753) -> begin
(head_constructor t)
end
| _68_1757 -> begin
(fail ())
end))
in (

let pat_exp = (let _157_658 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _157_658 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_68_1782) -> begin
(let _157_663 = (let _157_662 = (let _157_661 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _157_660 = (let _157_659 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_157_659)::[])
in (_157_661)::_157_660))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _157_662 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_157_663)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _157_664 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _157_664))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(

let sub_term_guards = (let _157_671 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _68_1800 -> (match (_68_1800) with
| (ei, _68_1799) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _68_1804 -> begin
(

let sub_term = (let _157_670 = (let _157_667 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _157_667 FStar_Syntax_Syntax.Delta_equational None))
in (let _157_669 = (let _157_668 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_157_668)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _157_670 _157_669 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _157_671 FStar_List.flatten))
in (let _157_672 = (discriminate scrutinee_tm f)
in (FStar_List.append _157_672 sub_term_guards)))
end)
end
| _68_1808 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(

let t = (let _157_677 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _157_677))
in (

let _68_1816 = (FStar_Syntax_Util.type_u ())
in (match (_68_1816) with
| (k, _68_1815) -> begin
(

let _68_1822 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_68_1822) with
| (t, _68_1819, _68_1821) -> begin
t
end))
end)))
end)
in (

let branch_guard = (let _157_678 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _157_678 FStar_Syntax_Util.mk_disj_l))
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

let _68_1830 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_679 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _157_679))
end else begin
()
end
in (let _157_680 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_157_680, branch_guard, c, guard)))))
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
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(

let _68_1847 = (check_let_bound_def true env lb)
in (match (_68_1847) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let _68_1859 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(

let g1 = (let _157_683 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _157_683 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _68_1854 = (let _157_687 = (let _157_686 = (let _157_685 = (let _157_684 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _157_684))
in (_157_685)::[])
in (FStar_TypeChecker_Util.generalize env _157_686))
in (FStar_List.hd _157_687))
in (match (_68_1854) with
| (_68_1850, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_68_1859) with
| (g1, e1, univ_vars, c1) -> begin
(

let _68_1869 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(

let _68_1862 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_68_1862) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(

let _68_1863 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _157_688 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _157_688 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _157_689 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_157_689, c1)))
end
end))
end else begin
(

let _68_1865 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _157_690 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _157_690)))
end
in (match (_68_1869) with
| (e2, c1) -> begin
(

let cres = (let _157_691 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _157_691))
in (

let _68_1871 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _157_692 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_157_692, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _68_1875 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(

let env = (

let _68_1886 = env
in {FStar_TypeChecker_Env.solver = _68_1886.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_1886.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_1886.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_1886.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_1886.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_1886.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_1886.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_1886.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_1886.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_1886.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_1886.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_1886.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_1886.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _68_1886.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_1886.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_1886.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_1886.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _68_1886.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _68_1886.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_1886.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_1886.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _68_1895 = (let _157_696 = (let _157_695 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _157_695 Prims.fst))
in (check_let_bound_def false _157_696 lb))
in (match (_68_1895) with
| (e1, _68_1891, c1, g1, annotated) -> begin
(

let x = (

let _68_1896 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _68_1896.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_1896.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let _68_1902 = (let _157_698 = (let _157_697 = (FStar_Syntax_Syntax.mk_binder x)
in (_157_697)::[])
in (FStar_Syntax_Subst.open_term _157_698 e2))
in (match (_68_1902) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _68_1908 = (let _157_699 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _157_699 e2))
in (match (_68_1908) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (x), c2))
in (

let e = (let _157_702 = (let _157_701 = (let _157_700 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _157_700))
in FStar_Syntax_Syntax.Tm_let (_157_701))
in (FStar_Syntax_Syntax.mk _157_702 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let x_eq_e1 = (let _157_705 = (let _157_704 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _157_704 e1))
in (FStar_All.pipe_left (fun _157_703 -> FStar_TypeChecker_Common.NonTrivial (_157_703)) _157_705))
in (

let g2 = (let _157_707 = (let _157_706 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _157_706 g2))
in (FStar_TypeChecker_Rel.close_guard xb _157_707))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if annotated then begin
(e, cres, guard)
end else begin
(

let _68_1914 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end)))))
end))))
end))))
end)))
end
| _68_1917 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _68_1929 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_68_1929) with
| (lbs, e2) -> begin
(

let _68_1932 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_68_1932) with
| (env0, topt) -> begin
(

let _68_1935 = (build_let_rec_env true env0 lbs)
in (match (_68_1935) with
| (lbs, rec_env) -> begin
(

let _68_1938 = (check_let_recs rec_env lbs)
in (match (_68_1938) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (let _157_710 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _157_710 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _157_713 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _157_713 (fun _157_712 -> Some (_157_712))))
in (

let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(

let ecs = (let _157_717 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _157_716 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _157_716)))))
in (FStar_TypeChecker_Util.generalize env _157_717))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _68_1949 -> (match (_68_1949) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _157_719 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _157_719))
in (

let _68_1952 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _68_1956 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_68_1956) with
| (lbs, e2) -> begin
(let _157_721 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _157_720 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_157_721, cres, _157_720)))
end)))))))
end))
end))
end))
end))
end
| _68_1958 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _68_1970 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_68_1970) with
| (lbs, e2) -> begin
(

let _68_1973 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_68_1973) with
| (env0, topt) -> begin
(

let _68_1976 = (build_let_rec_env false env0 lbs)
in (match (_68_1976) with
| (lbs, rec_env) -> begin
(

let _68_1979 = (check_let_recs rec_env lbs)
in (match (_68_1979) with
| (lbs, g_lbs) -> begin
(

let _68_1991 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let _68_1982 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _68_1982.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_1982.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let _68_1985 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _68_1985.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _68_1985.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _68_1985.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _68_1985.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], lb.FStar_Syntax_Syntax.lbtyp))
in (env, lb))))) env))
in (match (_68_1991) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let _68_1997 = (tc_term env e2)
in (match (_68_1997) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _68_2001 = cres
in {FStar_Syntax_Syntax.eff_name = _68_2001.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _68_2001.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _68_2001.FStar_Syntax_Syntax.comp})
in (

let _68_2006 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_68_2006) with
| (lbs, e2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_68_2009) -> begin
(e, cres, guard)
end
| None -> begin
(

let _68_2012 = (check_no_escape None env bvs tres)
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
| _68_2015 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let _68_2048 = (FStar_List.fold_left (fun _68_2022 lb -> (match (_68_2022) with
| (lbs, env) -> begin
(

let _68_2027 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_68_2027) with
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

let _68_2036 = (let _157_733 = (let _157_732 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _157_732))
in (tc_check_tot_or_gtot_term (

let _68_2030 = env0
in {FStar_TypeChecker_Env.solver = _68_2030.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_2030.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_2030.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_2030.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_2030.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_2030.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_2030.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_2030.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_2030.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_2030.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_2030.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_2030.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_2030.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _68_2030.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _68_2030.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_2030.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_2030.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _68_2030.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _68_2030.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_2030.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_2030.FStar_TypeChecker_Env.use_bv_sorts}) t _157_733))
in (match (_68_2036) with
| (t, _68_2034, g) -> begin
(

let _68_2037 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (

let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(

let _68_2040 = env
in {FStar_TypeChecker_Env.solver = _68_2040.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_2040.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_2040.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_2040.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_2040.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_2040.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_2040.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_2040.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_2040.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_2040.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_2040.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_2040.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _68_2040.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _68_2040.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_2040.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_2040.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_2040.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _68_2040.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _68_2040.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_2040.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_2040.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (

let lb = (

let _68_2043 = lb
in {FStar_Syntax_Syntax.lbname = _68_2043.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _68_2043.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_68_2048) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _68_2061 = (let _157_738 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _68_2055 = (let _157_737 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _157_737 lb.FStar_Syntax_Syntax.lbdef))
in (match (_68_2055) with
| (e, c, g) -> begin
(

let _68_2056 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _157_738 FStar_List.unzip))
in (match (_68_2061) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _68_2069 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_68_2069) with
| (env1, _68_2068) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _68_2075 = (check_lbtyp top_level env lb)
in (match (_68_2075) with
| (topt, wf_annot, univ_vars, env1) -> begin
(

let _68_2076 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let _68_2083 = (tc_maybe_toplevel_term (

let _68_2078 = env1
in {FStar_TypeChecker_Env.solver = _68_2078.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_2078.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_2078.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_2078.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_2078.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_2078.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_2078.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_2078.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_2078.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_2078.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_2078.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_2078.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_2078.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _68_2078.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_2078.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_2078.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_2078.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _68_2078.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _68_2078.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_2078.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_2078.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_68_2083) with
| (e1, c1, g1) -> begin
(

let _68_2087 = (let _157_745 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _68_2084 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _157_745 e1 c1 wf_annot))
in (match (_68_2087) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _68_2089 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _157_746 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _157_746))
end else begin
()
end
in (let _157_747 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _157_747))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _68_2096 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _68_2099 -> begin
(

let _68_2102 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_68_2102) with
| (univ_vars, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _157_751 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _157_751))
end else begin
(

let _68_2107 = (FStar_Syntax_Util.type_u ())
in (match (_68_2107) with
| (k, _68_2106) -> begin
(

let _68_2112 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_68_2112) with
| (t, _68_2110, g) -> begin
(

let _68_2113 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _157_754 = (let _157_752 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _157_752))
in (let _157_753 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _157_754 _157_753)))
end else begin
()
end
in (

let t = (norm env1 t)
in (let _157_755 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _157_755))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _68_2119 -> (match (_68_2119) with
| (x, imp) -> begin
(

let _68_2122 = (FStar_Syntax_Util.type_u ())
in (match (_68_2122) with
| (tu, u) -> begin
(

let _68_2127 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_68_2127) with
| (t, _68_2125, g) -> begin
(

let x = ((

let _68_2128 = x
in {FStar_Syntax_Syntax.ppname = _68_2128.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_2128.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (

let _68_2131 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_759 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _157_758 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _157_759 _157_758)))
end else begin
()
end
in (let _157_760 = (maybe_push_binding env x)
in (x, _157_760, g, u))))
end))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe Prims.list) = (fun env bs -> (

let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_TypeChecker_Rel.trivial_guard, [])
end
| b::bs -> begin
(

let _68_2146 = (tc_binder env b)
in (match (_68_2146) with
| (b, env', g, u) -> begin
(

let _68_2151 = (aux env' bs)
in (match (_68_2151) with
| (bs, env', g', us) -> begin
(let _157_768 = (let _157_767 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _157_767))
in ((b)::bs, env', _157_768, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun _68_2159 _68_2162 -> (match ((_68_2159, _68_2162)) with
| ((t, imp), (args, g)) -> begin
(

let _68_2167 = (tc_term env t)
in (match (_68_2167) with
| (t, _68_2165, g') -> begin
(let _157_777 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _157_777))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _68_2171 -> (match (_68_2171) with
| (pats, g) -> begin
(

let _68_2174 = (tc_args env p)
in (match (_68_2174) with
| (args, g') -> begin
(let _157_780 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _157_780))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _68_2180 = (tc_maybe_toplevel_term env e)
in (match (_68_2180) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let _68_2183 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_783 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _157_783))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _68_2188 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _157_784 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_157_784, false))
end else begin
(let _157_785 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_157_785, true))
end
in (match (_68_2188) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _157_786 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _157_786))
end
| _68_2192 -> begin
if allow_ghost then begin
(let _157_789 = (let _157_788 = (let _157_787 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_157_787, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_157_788))
in (Prims.raise _157_789))
end else begin
(let _157_792 = (let _157_791 = (let _157_790 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_157_790, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_157_791))
in (Prims.raise _157_792))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))


let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let _68_2202 = (tc_tot_or_gtot_term env t)
in (match (_68_2202) with
| (t, c, g) -> begin
(

let _68_2203 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let _68_2211 = (tc_check_tot_or_gtot_term env t k)
in (match (_68_2211) with
| (t, c, g) -> begin
(

let _68_2212 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _157_812 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _157_812)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _157_816 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _157_816))))


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let _68_2227 = (tc_binders env tps)
in (match (_68_2227) with
| (tps, env, g, us) -> begin
(

let _68_2228 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (

let fail = (fun _68_2234 -> (match (()) with
| () -> begin
(let _157_831 = (let _157_830 = (let _157_829 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_157_829, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_157_830))
in (Prims.raise _157_831))
end))
in (

let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _68_2251)::(wp, _68_2247)::(_wlp, _68_2243)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _68_2255 -> begin
(fail ())
end))
end
| _68_2257 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let _68_2264 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_68_2264) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _68_2266 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let _68_2270 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_68_2270) with
| (uvs, t') -> begin
(match ((let _157_838 = (FStar_Syntax_Subst.compress t')
in _157_838.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _68_2276 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))


let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (

let fail = (fun t -> (let _157_849 = (let _157_848 = (let _157_847 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_157_847, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_157_848))
in (Prims.raise _157_849)))
in (match ((let _157_850 = (FStar_Syntax_Subst.compress signature)
in _157_850.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _68_2297)::(wp, _68_2293)::(_wlp, _68_2289)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _68_2301 -> begin
(fail signature)
end))
end
| _68_2303 -> begin
(fail signature)
end)))


let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (

let _68_2308 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_68_2308) with
| (a, wp) -> begin
(

let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _68_2311 -> begin
(

let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (

let op = (fun ts -> (

let _68_2315 = ()
in (

let t0 = (Prims.snd ts)
in (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (

let _68_2319 = ed
in (let _157_869 = (op ed.FStar_Syntax_Syntax.ret)
in (let _157_868 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _157_867 = (op ed.FStar_Syntax_Syntax.bind_wlp)
in (let _157_866 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _157_865 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _157_864 = (op ed.FStar_Syntax_Syntax.ite_wlp)
in (let _157_863 = (op ed.FStar_Syntax_Syntax.wp_binop)
in (let _157_862 = (op ed.FStar_Syntax_Syntax.wp_as_type)
in (let _157_861 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _157_860 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _157_859 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _157_858 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _157_857 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _68_2319.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _68_2319.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _68_2319.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _68_2319.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _68_2319.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _157_869; FStar_Syntax_Syntax.bind_wp = _157_868; FStar_Syntax_Syntax.bind_wlp = _157_867; FStar_Syntax_Syntax.if_then_else = _157_866; FStar_Syntax_Syntax.ite_wp = _157_865; FStar_Syntax_Syntax.ite_wlp = _157_864; FStar_Syntax_Syntax.wp_binop = _157_863; FStar_Syntax_Syntax.wp_as_type = _157_862; FStar_Syntax_Syntax.close_wp = _157_861; FStar_Syntax_Syntax.assert_p = _157_860; FStar_Syntax_Syntax.assume_p = _157_859; FStar_Syntax_Syntax.null_wp = _157_858; FStar_Syntax_Syntax.trivial = _157_857}))))))))))))))))
end)
in (ed, a, wp))
end)))


let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (

let _68_2324 = ()
in (

let _68_2328 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_68_2328) with
| (binders_un, signature_un) -> begin
(

let _68_2333 = (tc_tparams env0 binders_un)
in (match (_68_2333) with
| (binders, env, _68_2332) -> begin
(

let _68_2337 = (tc_trivial_guard env signature_un)
in (match (_68_2337) with
| (signature, _68_2336) -> begin
(

let ed = (

let _68_2338 = ed
in {FStar_Syntax_Syntax.qualifiers = _68_2338.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _68_2338.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _68_2338.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _68_2338.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _68_2338.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _68_2338.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = _68_2338.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _68_2338.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _68_2338.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = _68_2338.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _68_2338.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _68_2338.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _68_2338.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _68_2338.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _68_2338.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _68_2338.FStar_Syntax_Syntax.trivial})
in (

let _68_2344 = (open_effect_decl env ed)
in (match (_68_2344) with
| (ed, a, wp_a) -> begin
(

let get_effect_signature = (fun _68_2346 -> (match (()) with
| () -> begin
(

let _68_2350 = (tc_trivial_guard env signature_un)
in (match (_68_2350) with
| (signature, _68_2349) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (

let env = (let _157_876 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _157_876))
in (

let _68_2352 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _157_879 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _157_878 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _157_877 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checked effect signature: %s %s : %s\n" _157_879 _157_878 _157_877))))
end else begin
()
end
in (

let check_and_gen' = (fun env _68_2359 k -> (match (_68_2359) with
| (_68_2357, t) -> begin
(check_and_gen env t k)
end))
in (

let ret = (

let expected_k = (let _157_891 = (let _157_889 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_888 = (let _157_887 = (let _157_886 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _157_886))
in (_157_887)::[])
in (_157_889)::_157_888))
in (let _157_890 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _157_891 _157_890)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (

let bind_wp = (

let wlp_a = wp_a
in (

let _68_2366 = (get_effect_signature ())
in (match (_68_2366) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _157_895 = (let _157_893 = (let _157_892 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _157_892))
in (_157_893)::[])
in (let _157_894 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _157_895 _157_894)))
in (

let a_wlp_b = a_wp_b
in (

let expected_k = (let _157_908 = (let _157_906 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_905 = (let _157_904 = (FStar_Syntax_Syntax.mk_binder b)
in (let _157_903 = (let _157_902 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _157_901 = (let _157_900 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _157_899 = (let _157_898 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (let _157_897 = (let _157_896 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_157_896)::[])
in (_157_898)::_157_897))
in (_157_900)::_157_899))
in (_157_902)::_157_901))
in (_157_904)::_157_903))
in (_157_906)::_157_905))
in (let _157_907 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _157_908 _157_907)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k))))
end)))
in (

let bind_wlp = (

let wlp_a = wp_a
in (

let _68_2374 = (get_effect_signature ())
in (match (_68_2374) with
| (b, wlp_b) -> begin
(

let a_wlp_b = (let _157_912 = (let _157_910 = (let _157_909 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _157_909))
in (_157_910)::[])
in (let _157_911 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _157_912 _157_911)))
in (

let expected_k = (let _157_921 = (let _157_919 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_918 = (let _157_917 = (FStar_Syntax_Syntax.mk_binder b)
in (let _157_916 = (let _157_915 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _157_914 = (let _157_913 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_157_913)::[])
in (_157_915)::_157_914))
in (_157_917)::_157_916))
in (_157_919)::_157_918))
in (let _157_920 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _157_921 _157_920)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wlp expected_k)))
end)))
in (

let if_then_else = (

let p = (let _157_923 = (let _157_922 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _157_922 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _157_923))
in (

let expected_k = (let _157_932 = (let _157_930 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_929 = (let _157_928 = (FStar_Syntax_Syntax.mk_binder p)
in (let _157_927 = (let _157_926 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _157_925 = (let _157_924 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_157_924)::[])
in (_157_926)::_157_925))
in (_157_928)::_157_927))
in (_157_930)::_157_929))
in (let _157_931 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _157_932 _157_931)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let wlp_a = wp_a
in (

let expected_k = (let _157_939 = (let _157_937 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_936 = (let _157_935 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _157_934 = (let _157_933 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_157_933)::[])
in (_157_935)::_157_934))
in (_157_937)::_157_936))
in (let _157_938 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _157_939 _157_938)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k)))
in (

let ite_wlp = (

let wlp_a = wp_a
in (

let expected_k = (let _157_944 = (let _157_942 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_941 = (let _157_940 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (_157_940)::[])
in (_157_942)::_157_941))
in (let _157_943 = (FStar_Syntax_Syntax.mk_Total wlp_a)
in (FStar_Syntax_Util.arrow _157_944 _157_943)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wlp expected_k)))
in (

let wp_binop = (

let bin_op = (

let _68_2389 = (FStar_Syntax_Util.type_u ())
in (match (_68_2389) with
| (t1, u1) -> begin
(

let _68_2392 = (FStar_Syntax_Util.type_u ())
in (match (_68_2392) with
| (t2, u2) -> begin
(

let t = (let _157_945 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_max ((u1)::(u2)::[]))) None _157_945))
in (let _157_950 = (let _157_948 = (FStar_Syntax_Syntax.null_binder t1)
in (let _157_947 = (let _157_946 = (FStar_Syntax_Syntax.null_binder t2)
in (_157_946)::[])
in (_157_948)::_157_947))
in (let _157_949 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _157_950 _157_949))))
end))
end))
in (

let expected_k = (let _157_959 = (let _157_957 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_956 = (let _157_955 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _157_954 = (let _157_953 = (FStar_Syntax_Syntax.null_binder bin_op)
in (let _157_952 = (let _157_951 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_157_951)::[])
in (_157_953)::_157_952))
in (_157_955)::_157_954))
in (_157_957)::_157_956))
in (let _157_958 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _157_959 _157_958)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_binop expected_k)))
in (

let wp_as_type = (

let _68_2400 = (FStar_Syntax_Util.type_u ())
in (match (_68_2400) with
| (t, _68_2399) -> begin
(

let expected_k = (let _157_964 = (let _157_962 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_961 = (let _157_960 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_157_960)::[])
in (_157_962)::_157_961))
in (let _157_963 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _157_964 _157_963)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (

let close_wp = (

let b = (let _157_966 = (let _157_965 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _157_965 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _157_966))
in (

let b_wp_a = (let _157_970 = (let _157_968 = (let _157_967 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _157_967))
in (_157_968)::[])
in (let _157_969 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _157_970 _157_969)))
in (

let expected_k = (let _157_977 = (let _157_975 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_974 = (let _157_973 = (FStar_Syntax_Syntax.mk_binder b)
in (let _157_972 = (let _157_971 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_157_971)::[])
in (_157_973)::_157_972))
in (_157_975)::_157_974))
in (let _157_976 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _157_977 _157_976)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (let _157_986 = (let _157_984 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_983 = (let _157_982 = (let _157_979 = (let _157_978 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _157_978 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _157_979))
in (let _157_981 = (let _157_980 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_157_980)::[])
in (_157_982)::_157_981))
in (_157_984)::_157_983))
in (let _157_985 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _157_986 _157_985)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _157_995 = (let _157_993 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_992 = (let _157_991 = (let _157_988 = (let _157_987 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _157_987 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _157_988))
in (let _157_990 = (let _157_989 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_157_989)::[])
in (_157_991)::_157_990))
in (_157_993)::_157_992))
in (let _157_994 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _157_995 _157_994)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _157_998 = (let _157_996 = (FStar_Syntax_Syntax.mk_binder a)
in (_157_996)::[])
in (let _157_997 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _157_998 _157_997)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let _68_2416 = (FStar_Syntax_Util.type_u ())
in (match (_68_2416) with
| (t, _68_2415) -> begin
(

let expected_k = (let _157_1003 = (let _157_1001 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_1000 = (let _157_999 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_157_999)::[])
in (_157_1001)::_157_1000))
in (let _157_1002 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _157_1003 _157_1002)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let t = (let _157_1004 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _157_1004))
in (

let _68_2422 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_68_2422) with
| (univs, t) -> begin
(

let _68_2438 = (match ((let _157_1006 = (let _157_1005 = (FStar_Syntax_Subst.compress t)
in _157_1005.FStar_Syntax_Syntax.n)
in (binders, _157_1006))) with
| ([], _68_2425) -> begin
([], t)
end
| (_68_2428, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _68_2435 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_68_2438) with
| (binders, signature) -> begin
(

let close = (fun ts -> (let _157_1009 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _157_1009)))
in (

let ed = (

let _68_2441 = ed
in (let _157_1022 = (close ret)
in (let _157_1021 = (close bind_wp)
in (let _157_1020 = (close bind_wlp)
in (let _157_1019 = (close if_then_else)
in (let _157_1018 = (close ite_wp)
in (let _157_1017 = (close ite_wlp)
in (let _157_1016 = (close wp_binop)
in (let _157_1015 = (close wp_as_type)
in (let _157_1014 = (close close_wp)
in (let _157_1013 = (close assert_p)
in (let _157_1012 = (close assume_p)
in (let _157_1011 = (close null_wp)
in (let _157_1010 = (close trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _68_2441.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _68_2441.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _157_1022; FStar_Syntax_Syntax.bind_wp = _157_1021; FStar_Syntax_Syntax.bind_wlp = _157_1020; FStar_Syntax_Syntax.if_then_else = _157_1019; FStar_Syntax_Syntax.ite_wp = _157_1018; FStar_Syntax_Syntax.ite_wlp = _157_1017; FStar_Syntax_Syntax.wp_binop = _157_1016; FStar_Syntax_Syntax.wp_as_type = _157_1015; FStar_Syntax_Syntax.close_wp = _157_1014; FStar_Syntax_Syntax.assert_p = _157_1013; FStar_Syntax_Syntax.assume_p = _157_1012; FStar_Syntax_Syntax.null_wp = _157_1011; FStar_Syntax_Syntax.trivial = _157_1010}))))))))))))))
in (

let _68_2444 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_1023 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _157_1023))
end else begin
()
end
in ed)))
end))
end))))))))))))))))))))
end)))
end))
end))
end))))


let tc_lex_t = (fun env ses quals lids -> (

let _68_2450 = ()
in (

let _68_2458 = ()
in (match (ses) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _68_2487, _68_2489, [], r)::FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _68_2478, r1)::FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _68_2467, r2)::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
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

let lex_top_t = (let _157_1031 = (let _157_1030 = (let _157_1029 = (let _157_1028 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _157_1028 FStar_Syntax_Syntax.Delta_constant None))
in (_157_1029, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_157_1030))
in (FStar_Syntax_Syntax.mk _157_1031 None r1))
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

let a = (let _157_1032 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _157_1032))
in (

let hd = (let _157_1033 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _157_1033))
in (

let tl = (let _157_1038 = (let _157_1037 = (let _157_1036 = (let _157_1035 = (let _157_1034 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _157_1034 FStar_Syntax_Syntax.Delta_constant None))
in (_157_1035, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_157_1036))
in (FStar_Syntax_Syntax.mk _157_1037 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _157_1038))
in (

let res = (let _157_1042 = (let _157_1041 = (let _157_1040 = (let _157_1039 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _157_1039 FStar_Syntax_Syntax.Delta_constant None))
in (_157_1040, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_157_1041))
in (FStar_Syntax_Syntax.mk _157_1042 None r2))
in (let _157_1043 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _157_1043))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _157_1045 = (let _157_1044 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _157_1044))
in FStar_Syntax_Syntax.Sig_bundle (_157_1045)))))))))))))))
end
| _68_2513 -> begin
(let _157_1047 = (let _157_1046 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _157_1046))
in (FStar_All.failwith _157_1047))
end))))


let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _157_1061 = (let _157_1060 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _157_1060))
in (FStar_TypeChecker_Errors.diag r _157_1061)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let _68_2535 = ()
in (

let _68_2537 = (warn_positivity tc r)
in (

let _68_2541 = (FStar_Syntax_Subst.open_term tps k)
in (match (_68_2541) with
| (tps, k) -> begin
(

let _68_2545 = (tc_tparams env tps)
in (match (_68_2545) with
| (tps, env_tps, us) -> begin
(

let _68_2548 = (FStar_Syntax_Util.arrow_formals k)
in (match (_68_2548) with
| (indices, t) -> begin
(

let _68_2552 = (tc_tparams env_tps indices)
in (match (_68_2552) with
| (indices, env', us') -> begin
(

let _68_2556 = (tc_trivial_guard env' t)
in (match (_68_2556) with
| (t, _68_2555) -> begin
(

let k = (let _157_1066 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _157_1066))
in (

let _68_2560 = (FStar_Syntax_Util.type_u ())
in (match (_68_2560) with
| (t_type, u) -> begin
(

let _68_2561 = (let _157_1067 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _157_1067))
in (

let t_tc = (let _157_1068 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _157_1068))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _157_1069 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) ([], t_tc))
in (_157_1069, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u)))))))
end)))
end))
end))
end))
end))
end))))
end
| _68_2568 -> begin
(FStar_All.failwith "impossible")
end))
in (

let positive_if_pure = (fun _68_2570 l -> ())
in (

let tc_data = (fun env tcs _68_6 -> (match (_68_6) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let _68_2587 = ()
in (

let _68_2622 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _68_2591 -> (match (_68_2591) with
| (se, u_tc) -> begin
if (let _157_1082 = (let _157_1081 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _157_1081))
in (FStar_Ident.lid_equals tc_lid _157_1082)) then begin
(

let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_68_2593, _68_2595, tps, _68_2598, _68_2600, _68_2602, _68_2604, _68_2606) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _68_2612 -> (match (_68_2612) with
| (x, _68_2611) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _68_2614 -> begin
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
in (match (_68_2622) with
| (tps, u_tc) -> begin
(

let _68_2642 = (match ((let _157_1084 = (FStar_Syntax_Subst.compress t)
in _157_1084.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _68_2630 = (FStar_Util.first_N ntps bs)
in (match (_68_2630) with
| (_68_2628, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _68_2636 -> (match (_68_2636) with
| (x, _68_2635) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _157_1087 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _157_1087))))
end))
end
| _68_2639 -> begin
([], t)
end)
in (match (_68_2642) with
| (arguments, result) -> begin
(

let _68_2643 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_1090 = (FStar_Syntax_Print.lid_to_string c)
in (let _157_1089 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _157_1088 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _157_1090 _157_1089 _157_1088))))
end else begin
()
end
in (

let _68_2648 = (tc_tparams env arguments)
in (match (_68_2648) with
| (arguments, env', us) -> begin
(

let _68_2652 = (tc_trivial_guard env' result)
in (match (_68_2652) with
| (result, _68_2651) -> begin
(

let _68_2656 = (FStar_Syntax_Util.head_and_args result)
in (match (_68_2656) with
| (head, _68_2655) -> begin
(

let _68_2661 = (match ((let _157_1091 = (FStar_Syntax_Subst.compress head)
in _157_1091.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _68_2660 -> begin
(let _157_1095 = (let _157_1094 = (let _157_1093 = (let _157_1092 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _157_1092))
in (_157_1093, r))
in FStar_Syntax_Syntax.Error (_157_1094))
in (Prims.raise _157_1095))
end)
in (

let g = (FStar_List.fold_left2 (fun g _68_2667 u_x -> (match (_68_2667) with
| (x, _68_2666) -> begin
(

let _68_2669 = ()
in (let _157_1099 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _157_1099)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _157_1103 = (let _157_1101 = (FStar_All.pipe_right tps (FStar_List.map (fun _68_2675 -> (match (_68_2675) with
| (x, _68_2674) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _157_1101 arguments))
in (let _157_1102 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _157_1103 _157_1102)))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _68_2678 -> begin
(FStar_All.failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let _68_2684 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _68_7 -> (match (_68_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_68_2688, _68_2690, tps, k, _68_2694, _68_2696, _68_2698, _68_2700) -> begin
(let _157_1114 = (let _157_1113 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _157_1113))
in (FStar_Syntax_Syntax.null_binder _157_1114))
end
| _68_2704 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _68_8 -> (match (_68_8) with
| FStar_Syntax_Syntax.Sig_datacon (_68_2708, _68_2710, t, _68_2713, _68_2715, _68_2717, _68_2719, _68_2721) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _68_2725 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let t = (let _157_1116 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _157_1116))
in (

let _68_2728 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_1117 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _157_1117))
end else begin
()
end
in (

let _68_2732 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_68_2732) with
| (uvs, t) -> begin
(

let _68_2734 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_1121 = (let _157_1119 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _157_1119 (FStar_String.concat ", ")))
in (let _157_1120 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _157_1121 _157_1120)))
end else begin
()
end
in (

let _68_2738 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_68_2738) with
| (uvs, t) -> begin
(

let _68_2742 = (FStar_Syntax_Util.arrow_formals t)
in (match (_68_2742) with
| (args, _68_2741) -> begin
(

let _68_2745 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_68_2745) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _68_2749 se -> (match (_68_2749) with
| (x, _68_2748) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _68_2753, tps, _68_2756, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let _68_2779 = (match ((let _157_1124 = (FStar_Syntax_Subst.compress ty)
in _157_1124.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _68_2770 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_68_2770) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _68_2773 -> begin
(let _157_1125 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _157_1125 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _68_2776 -> begin
([], ty)
end)
in (match (_68_2779) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _68_2781 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| _68_2785 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _157_1126 -> FStar_Syntax_Syntax.U_name (_157_1126))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _68_9 -> (match (_68_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _68_2790, _68_2792, _68_2794, _68_2796, _68_2798, _68_2800, _68_2802) -> begin
(tc, uvs_universes)
end
| _68_2806 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _68_2811 d -> (match (_68_2811) with
| (t, _68_2810) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _68_2815, _68_2817, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _157_1130 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _157_1130 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _68_2827 -> begin
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

let _68_2837 = (FStar_All.pipe_right ses (FStar_List.partition (fun _68_10 -> (match (_68_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_68_2831) -> begin
true
end
| _68_2834 -> begin
false
end))))
in (match (_68_2837) with
| (tys, datas) -> begin
(

let env0 = env
in (

let _68_2854 = (FStar_List.fold_right (fun tc _68_2843 -> (match (_68_2843) with
| (env, all_tcs, g) -> begin
(

let _68_2847 = (tc_tycon env tc)
in (match (_68_2847) with
| (env, tc, tc_u) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (

let _68_2849 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_1134 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _157_1134))
end else begin
()
end
in (let _157_1135 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _157_1135))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_68_2854) with
| (env, tcs, g) -> begin
(

let _68_2864 = (FStar_List.fold_right (fun se _68_2858 -> (match (_68_2858) with
| (datas, g) -> begin
(

let _68_2861 = (tc_data env tcs se)
in (match (_68_2861) with
| (data, g') -> begin
(let _157_1138 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _157_1138))
end))
end)) datas ([], g))
in (match (_68_2864) with
| (datas, g) -> begin
(

let _68_2867 = (let _157_1139 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _157_1139 datas))
in (match (_68_2867) with
| (tcs, datas) -> begin
(let _157_1141 = (let _157_1140 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _157_1140))
in FStar_Syntax_Syntax.Sig_bundle (_157_1141))
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
in (let _157_1146 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _157_1146))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let se = (tc_inductive env ses quals lids)
in (let _157_1147 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _157_1147))))
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

let _68_2905 = (set_options FStar_Options.Set o)
in (se, env))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(

let _68_2909 = (let _157_1152 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _157_1152 Prims.ignore))
in (

let _68_2914 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _68_2916 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (se, env))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(

let ne = (tc_eff_decl env ne)
in (

let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(

let _68_2931 = (let _157_1153 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _157_1153))
in (match (_68_2931) with
| (a, wp_a_src) -> begin
(

let _68_2934 = (let _157_1154 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _157_1154))
in (match (_68_2934) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _157_1158 = (let _157_1157 = (let _157_1156 = (let _157_1155 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _157_1155))
in FStar_Syntax_Syntax.NT (_157_1156))
in (_157_1157)::[])
in (FStar_Syntax_Subst.subst _157_1158 wp_b_tgt))
in (

let expected_k = (let _157_1163 = (let _157_1161 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_1160 = (let _157_1159 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_157_1159)::[])
in (_157_1161)::_157_1160))
in (let _157_1162 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _157_1163 _157_1162)))
in (

let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (

let sub = (

let _68_2938 = sub
in {FStar_Syntax_Syntax.source = _68_2938.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _68_2938.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
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

let _68_2951 = ()
in (

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _68_2957 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_68_2957) with
| (tps, c) -> begin
(

let _68_2961 = (tc_tparams env tps)
in (match (_68_2961) with
| (tps, env, us) -> begin
(

let _68_2965 = (tc_comp env c)
in (match (_68_2965) with
| (c, u, g) -> begin
(

let _68_2966 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let tags = (FStar_All.pipe_right tags (FStar_List.map (fun _68_11 -> (match (_68_11) with
| FStar_Syntax_Syntax.DefaultEffect (None) -> begin
(

let c' = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let _157_1166 = (FStar_All.pipe_right c'.FStar_Syntax_Syntax.effect_name (fun _157_1165 -> Some (_157_1165)))
in FStar_Syntax_Syntax.DefaultEffect (_157_1166)))
end
| t -> begin
t
end))))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let _68_2978 = (let _157_1167 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _157_1167))
in (match (_68_2978) with
| (uvs, t) -> begin
(

let _68_2997 = (match ((let _157_1169 = (let _157_1168 = (FStar_Syntax_Subst.compress t)
in _157_1168.FStar_Syntax_Syntax.n)
in (tps, _157_1169))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_68_2981, c)) -> begin
([], c)
end
| (_68_2987, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _68_2994 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_68_2997) with
| (tps, c) -> begin
(

let se = FStar_Syntax_Syntax.Sig_effect_abbrev ((lid, uvs, tps, c, tags, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 se)
in (se, env)))
end))
end))))))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t, quals, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _68_3008 = ()
in (

let k = (let _157_1170 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _157_1170))
in (

let _68_3013 = (check_and_gen env t k)
in (match (_68_3013) with
| (uvs, t) -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _68_3026 = (FStar_Syntax_Util.type_u ())
in (match (_68_3026) with
| (k, _68_3025) -> begin
(

let phi = (let _157_1171 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _157_1171 (norm env)))
in (

let _68_3028 = (FStar_TypeChecker_Util.check_uvars r phi)
in (

let se = FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (

let _68_3041 = (tc_term env e)
in (match (_68_3041) with
| (e, c, g1) -> begin
(

let _68_3046 = (let _157_1175 = (let _157_1172 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_157_1172))
in (let _157_1174 = (let _157_1173 = (c.FStar_Syntax_Syntax.comp ())
in (e, _157_1173))
in (check_expected_effect env _157_1175 _157_1174)))
in (match (_68_3046) with
| (e, _68_3044, g) -> begin
(

let _68_3047 = (let _157_1176 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _157_1176))
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
(let _157_1188 = (let _157_1187 = (let _157_1186 = (let _157_1185 = (FStar_Syntax_Print.lid_to_string l)
in (let _157_1184 = (FStar_Syntax_Print.quals_to_string q)
in (let _157_1183 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _157_1185 _157_1184 _157_1183))))
in (_157_1186, r))
in FStar_Syntax_Syntax.Error (_157_1187))
in (Prims.raise _157_1188))
end
end))
in (

let _68_3091 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _68_3068 lb -> (match (_68_3068) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _68_3087 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (

let _68_3082 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _68_3081 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _157_1191 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _157_1191, quals_opt))))
end)
in (match (_68_3087) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_68_3091) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _68_12 -> (match (_68_12) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _68_3100 -> begin
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

let e = (let _157_1195 = (let _157_1194 = (let _157_1193 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _157_1193))
in FStar_Syntax_Syntax.Tm_let (_157_1194))
in (FStar_Syntax_Syntax.mk _157_1195 None r))
in (

let _68_3134 = (match ((tc_maybe_toplevel_term (

let _68_3104 = env
in {FStar_TypeChecker_Env.solver = _68_3104.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_3104.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_3104.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_3104.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_3104.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_3104.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_3104.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_3104.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_3104.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_3104.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_3104.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _68_3104.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _68_3104.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_3104.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_3104.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_3104.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _68_3104.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _68_3104.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_3104.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_3104.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _68_3111; FStar_Syntax_Syntax.pos = _68_3109; FStar_Syntax_Syntax.vars = _68_3107}, _68_3118, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_68_3122, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _68_3128 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _68_3131 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_68_3134) with
| (se, lbs) -> begin
(

let _68_3140 = if (log env) then begin
(let _157_1203 = (let _157_1202 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _157_1199 = (let _157_1198 = (let _157_1197 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _157_1197.FStar_Syntax_Syntax.fv_name)
in _157_1198.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _157_1199))) with
| None -> begin
true
end
| _68_3138 -> begin
false
end)
in if should_log then begin
(let _157_1201 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _157_1200 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _157_1201 _157_1200)))
end else begin
""
end))))
in (FStar_All.pipe_right _157_1202 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _157_1203))
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

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _68_13 -> (match (_68_13) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _68_3150 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _68_3160 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_68_3162) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _68_3173, _68_3175) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _68_3181 -> (match (_68_3181) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _68_3187, _68_3189, quals, r) -> begin
(

let dec = (let _157_1219 = (let _157_1218 = (let _157_1217 = (let _157_1216 = (let _157_1215 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _157_1215))
in FStar_Syntax_Syntax.Tm_arrow (_157_1216))
in (FStar_Syntax_Syntax.mk _157_1217 None r))
in (l, us, _157_1218, (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_157_1219))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _68_3199, _68_3201, _68_3203, _68_3205, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _68_3211 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_68_3213, _68_3215, quals, _68_3218) -> begin
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
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _68_14 -> (match (_68_14) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _68_3237 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_68_3239) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _68_3255, _68_3257, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
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
(let _157_1226 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _157_1225 = (let _157_1224 = (let _157_1223 = (let _157_1222 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _157_1222.FStar_Syntax_Syntax.fv_name)
in _157_1223.FStar_Syntax_Syntax.v)
in (_157_1224, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_157_1225)))))
in (_157_1226, hidden))
end else begin
((se)::[], hidden)
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let _68_3296 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _68_3277 se -> (match (_68_3277) with
| (ses, exports, env, hidden) -> begin
(

let _68_3279 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_1233 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _157_1233))
end else begin
()
end
in (

let _68_3283 = (tc_decl env se)
in (match (_68_3283) with
| (se, env) -> begin
(

let _68_3284 = if ((FStar_ST.read FStar_Options.log_types) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _157_1234 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _157_1234))
end else begin
()
end
in (

let _68_3286 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (

let _68_3290 = (for_export hidden se)
in (match (_68_3290) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_68_3296) with
| (ses, exports, env, _68_3295) -> begin
(let _157_1235 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _157_1235, env))
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

let _68_3301 = env
in (let _157_1240 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _68_3301.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_3301.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_3301.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_3301.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_3301.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_3301.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_3301.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_3301.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_3301.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_3301.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_3301.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_3301.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_3301.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _68_3301.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _68_3301.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_3301.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _157_1240; FStar_TypeChecker_Env.default_effects = _68_3301.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _68_3301.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_3301.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_3301.FStar_TypeChecker_Env.use_bv_sorts}))
in (

let _68_3304 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let _68_3310 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_68_3310) with
| (ses, exports, env) -> begin
((

let _68_3311 = modul
in {FStar_Syntax_Syntax.name = _68_3311.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _68_3311.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _68_3311.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let _68_3319 = (tc_decls env decls)
in (match (_68_3319) with
| (ses, exports, env) -> begin
(

let modul = (

let _68_3320 = modul
in {FStar_Syntax_Syntax.name = _68_3320.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _68_3320.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _68_3320.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul = (

let _68_3326 = modul
in {FStar_Syntax_Syntax.name = _68_3326.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _68_3326.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in (

let _68_3336 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(

let _68_3330 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let _68_3332 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (

let _68_3334 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _157_1253 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _157_1253 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let _68_3343 = (tc_partial_modul env modul)
in (match (_68_3343) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _68_3346 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _157_1262 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _157_1262))
end else begin
()
end
in (

let env = (

let _68_3348 = env
in {FStar_TypeChecker_Env.solver = _68_3348.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_3348.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_3348.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_3348.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_3348.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_3348.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_3348.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_3348.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_3348.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_3348.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_3348.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_3348.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_3348.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _68_3348.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_3348.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_3348.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_3348.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _68_3348.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _68_3348.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_3348.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_3348.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _68_3364 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _68_3356) -> begin
(let _157_1267 = (let _157_1266 = (let _157_1265 = (FStar_TypeChecker_Env.get_range env)
in ((Prims.strcat "Implicit argument: " msg), _157_1265))
in FStar_Syntax_Syntax.Error (_157_1266))
in (Prims.raise _157_1267))
end
in (match (_68_3364) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(t, c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(let _157_1272 = (let _157_1271 = (let _157_1270 = (let _157_1268 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _157_1268))
in (let _157_1269 = (FStar_TypeChecker_Env.get_range env)
in (_157_1270, _157_1269)))
in FStar_Syntax_Syntax.Error (_157_1271))
in (Prims.raise _157_1272))
end
end)))))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

let _68_3367 = if ((let _157_1277 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _157_1277)) <> 0) then begin
(let _157_1278 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _157_1278))
end else begin
()
end
in (

let _68_3371 = (tc_modul env m)
in (match (_68_3371) with
| (m, env) -> begin
(

let _68_3372 = if (FStar_Options.should_dump m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _157_1279 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _157_1279))
end else begin
()
end
in (m, env))
end))))




