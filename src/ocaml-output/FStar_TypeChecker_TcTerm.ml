
open Prims

let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _58_7 = env
in {FStar_TypeChecker_Env.solver = _58_7.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_7.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_7.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_7.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_7.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_7.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_7.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_7.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_7.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _58_7.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_7.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_7.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_7.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_7.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_7.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_7.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_7.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_7.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_7.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_7.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_7.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_7.FStar_TypeChecker_Env.qname_and_index}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _58_10 = env
in {FStar_TypeChecker_Env.solver = _58_10.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_10.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_10.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_10.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_10.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_10.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_10.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_10.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_10.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _58_10.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_10.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_10.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_10.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_10.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_10.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_10.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_10.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_10.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_10.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_10.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_10.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_10.FStar_TypeChecker_Env.qname_and_index}))


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


let check_no_escape : FStar_Syntax_Syntax.term Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun head_opt env fvs kt -> (

let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
()
end
| _58_37 -> begin
(

let fvs' = (let _152_40 = if try_norm then begin
(norm env t)
end else begin
t
end
in (FStar_Syntax_Free.names _152_40))
in (match ((FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)) with
| None -> begin
()
end
| Some (x) -> begin
if (not (try_norm)) then begin
(aux true t)
end else begin
(

let fail = (fun _58_44 -> (match (()) with
| () -> begin
(

let msg = (match (head_opt) with
| None -> begin
(let _152_44 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _152_44))
end
| Some (head) -> begin
(let _152_46 = (FStar_Syntax_Print.bv_to_string x)
in (let _152_45 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _152_46 _152_45)))
end)
in (let _152_49 = (let _152_48 = (let _152_47 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (_152_47)))
in FStar_Syntax_Syntax.Error (_152_48))
in (Prims.raise _152_49)))
end))
in (

let s = (let _152_51 = (let _152_50 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _152_50))
in (FStar_TypeChecker_Util.new_uvar env _152_51))
in (match ((FStar_TypeChecker_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g)
end
| _58_53 -> begin
(fail ())
end)))
end
end))
end))
in (aux false kt)))


let push_binding = (fun env b -> (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))


let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.subst_t = (fun s b v -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
s
end else begin
(FStar_Syntax_Syntax.NT ((((Prims.fst b)), (v))))::s
end)


let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (

let _58_61 = lc
in {FStar_Syntax_Syntax.eff_name = _58_61.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_61.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _58_63 -> (match (()) with
| () -> begin
(let _152_65 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _152_65 t))
end))}))


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let should_return = (fun t -> (match ((let _152_76 = (FStar_Syntax_Subst.compress t)
in _152_76.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_71, c) -> begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(

let t = (FStar_All.pipe_left FStar_Syntax_Util.unrefine (FStar_Syntax_Util.comp_result c))
in (match ((let _152_77 = (FStar_Syntax_Subst.compress t)
in _152_77.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (_58_79) -> begin
false
end
| _58_82 -> begin
true
end))
end else begin
false
end
end
| _58_84 -> begin
true
end))
in (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _152_78 = if ((not ((should_return t))) || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _152_78))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _58_112 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
((e), (lc), (guard))
end
| Some (t') -> begin
(

let _58_94 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_80 = (FStar_Syntax_Print.term_to_string t)
in (let _152_79 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _152_80 _152_79)))
end else begin
()
end
in (

let _58_98 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_58_98) with
| (e, lc) -> begin
(

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _58_102 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_58_102) with
| (e, g) -> begin
(

let _58_103 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_82 = (FStar_Syntax_Print.term_to_string t)
in (let _152_81 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _152_82 _152_81)))
end else begin
()
end
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let _58_108 = (let _152_88 = (FStar_All.pipe_left (fun _152_87 -> Some (_152_87)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _152_88 env e lc g))
in (match (_58_108) with
| (lc, g) -> begin
((e), ((set_lcomp_result lc t')), (g))
end))))
end)))
end)))
end)
in (match (_58_112) with
| (e, lc, g) -> begin
(

let _58_113 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_89 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _152_89))
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

let _58_123 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_58_123) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _58_128 -> (match (_58_128) with
| (e, c) -> begin
(

let expected_c_opt = (match (copt) with
| Some (_58_130) -> begin
copt
end
| None -> begin
if ((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Syntax_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) then begin
(let _152_102 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (_152_102))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
if (FStar_Syntax_Util.is_pure_comp c) then begin
(let _152_103 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (_152_103))
end else begin
if (FStar_Syntax_Util.is_pure_or_ghost_comp c) then begin
(let _152_104 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (_152_104))
end else begin
None
end
end
end
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _152_105 = (norm_c env c)
in ((e), (_152_105), (FStar_TypeChecker_Rel.trivial_guard)))
end
| Some (expected_c) -> begin
(

let _58_137 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_108 = (FStar_Syntax_Print.term_to_string e)
in (let _152_107 = (FStar_Syntax_Print.comp_to_string c)
in (let _152_106 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _152_108 _152_107 _152_106))))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _58_140 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_111 = (FStar_Syntax_Print.term_to_string e)
in (let _152_110 = (FStar_Syntax_Print.comp_to_string c)
in (let _152_109 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _152_111 _152_110 _152_109))))
end else begin
()
end
in (

let _58_146 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_58_146) with
| (e, _58_144, g) -> begin
(

let g = (let _152_112 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _152_112 "could not prove post-condition" g))
in (

let _58_148 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_114 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _152_113 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _152_114 _152_113)))
end else begin
()
end
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e (FStar_Syntax_Util.comp_effect_name c) (FStar_Syntax_Util.comp_effect_name expected_c))
in ((e), (expected_c), (g)))))
end)))))
end))
end))


let no_logical_guard = (fun env _58_155 -> (match (_58_155) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
((te), (kt), (f))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _152_120 = (let _152_119 = (let _152_118 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _152_117 = (FStar_TypeChecker_Env.get_range env)
in ((_152_118), (_152_117))))
in FStar_Syntax_Syntax.Error (_152_119))
in (Prims.raise _152_120))
end)
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _152_123 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _152_123))
end))


let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _58_179; FStar_Syntax_Syntax.result_typ = _58_177; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, _58_171))::[]; FStar_Syntax_Syntax.flags = _58_168}) -> begin
(

let pat_vars = (FStar_Syntax_Free.names pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _58_186 -> (match (_58_186) with
| (b, _58_185) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _58_190) -> begin
(let _152_130 = (let _152_129 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _152_129))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _152_130))
end))
end
| _58_194 -> begin
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

let _58_201 = env
in {FStar_TypeChecker_Env.solver = _58_201.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_201.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_201.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_201.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_201.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_201.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_201.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_201.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_201.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_201.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_201.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_201.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _58_201.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_201.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_201.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_201.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_201.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_201.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_201.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_201.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_201.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_201.FStar_TypeChecker_Env.qname_and_index})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _58_213 -> (match (_58_213) with
| (b, _58_212) -> begin
(

let t = (let _152_144 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _152_144))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _58_222 -> begin
(let _152_145 = (FStar_Syntax_Syntax.bv_to_name b)
in (_152_145)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let _58_228 = (FStar_Syntax_Util.head_and_args dec)
in (match (_58_228) with
| (head, _58_227) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _58_232 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _58_2 -> (match (_58_2) with
| FStar_Syntax_Syntax.DECREASES (_58_236) -> begin
true
end
| _58_239 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _58_244 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| _58_249 -> begin
(mk_lex_list xs)
end))
end)))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun _58_254 -> (match (_58_254) with
| (l, t) -> begin
(match ((let _152_151 = (FStar_Syntax_Subst.compress t)
in _152_151.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _58_261 -> (match (_58_261) with
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

let _58_265 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_58_265) with
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

let _58_272 = (FStar_Util.prefix formals)
in (match (_58_272) with
| (bs, (last, imp)) -> begin
(

let last = (

let _58_273 = last
in (let _152_160 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _58_273.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_273.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_160}))
in (

let refined_formals = (FStar_List.append bs ((((last), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (

let _58_278 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
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
| _58_281 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end)
end)


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let _58_284 = env
in {FStar_TypeChecker_Env.solver = _58_284.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_284.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_284.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_284.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_284.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_284.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_284.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_284.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_284.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_284.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_284.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_284.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_284.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_284.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_284.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_284.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_284.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_284.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_284.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_284.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_284.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_284.FStar_TypeChecker_Env.qname_and_index}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (

let _58_289 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
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
| FStar_Syntax_Syntax.Tm_delayed (_58_293) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let _58_334 = (tc_tot_or_gtot_term env e)
in (match (_58_334) with
| (e, c, g) -> begin
(

let g = (

let _58_335 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_335.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_335.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_335.FStar_TypeChecker_Env.implicits})
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let _58_345 = (FStar_Syntax_Util.type_u ())
in (match (_58_345) with
| (t, u) -> begin
(

let _58_349 = (tc_check_tot_or_gtot_term env e t)
in (match (_58_349) with
| (e, c, g) -> begin
(

let _58_356 = (

let _58_353 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_353) with
| (env, _58_352) -> begin
(tc_pats env pats)
end))
in (match (_58_356) with
| (pats, g') -> begin
(

let g' = (

let _58_357 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_357.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_357.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_357.FStar_TypeChecker_Env.implicits})
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
| FStar_Syntax_Syntax.Tm_let ((_58_366, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _58_373; FStar_Syntax_Syntax.lbtyp = _58_371; FStar_Syntax_Syntax.lbeff = _58_369; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _58_384 = (let _152_240 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _152_240 e1))
in (match (_58_384) with
| (e1, c1, g1) -> begin
(

let _58_388 = (tc_term env e2)
in (match (_58_388) with
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
| _58_393 -> begin
(

let _58_397 = (tc_term env e)
in (match (_58_397) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (_58_401)) -> begin
(tc_term env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let _58_412 = (tc_term env e)
in (match (_58_412) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (m)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _58_418) -> begin
(

let _58_424 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_424) with
| (env0, _58_423) -> begin
(

let _58_429 = (tc_comp env0 expected_c)
in (match (_58_429) with
| (expected_c, _58_427, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (

let _58_434 = (let _152_247 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term _152_247 e))
in (match (_58_434) with
| (e, c', g') -> begin
(

let _58_438 = (let _152_249 = (let _152_248 = (c'.FStar_Syntax_Syntax.comp ())
in ((e), (_152_248)))
in (check_expected_effect env0 (Some (expected_c)) _152_249))
in (match (_58_438) with
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
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _58_443) -> begin
(

let _58_448 = (FStar_Syntax_Util.type_u ())
in (match (_58_448) with
| (k, u) -> begin
(

let _58_453 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_453) with
| (t, _58_451, f) -> begin
(

let _58_457 = (let _152_253 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _152_253 e))
in (match (_58_457) with
| (e, c, g) -> begin
(

let _58_461 = (let _152_257 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_458 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _152_257 e c f))
in (match (_58_461) with
| (c, f) -> begin
(

let _58_465 = (let _152_258 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t)), (Some (c.FStar_Syntax_Syntax.eff_name))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _152_258 c))
in (match (_58_465) with
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

let _58_501 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_501) with
| (unary_op, _58_500) -> begin
(

let head = (let _152_261 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (Prims.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) None _152_261))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), (rest)))) None top.FStar_Syntax_Syntax.pos)
in (tc_term env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _58_509; FStar_Syntax_Syntax.pos = _58_507; FStar_Syntax_Syntax.vars = _58_505}, ((e, aqual))::[]) -> begin
(

let _58_519 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end else begin
()
end
in (

let _58_528 = (

let _58_524 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_524) with
| (env0, _58_523) -> begin
(tc_term env0 e)
end))
in (match (_58_528) with
| (e, c, g) -> begin
(

let _58_532 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_532) with
| (reify_op, _58_531) -> begin
(

let u_c = (

let _58_538 = (tc_term env c.FStar_Syntax_Syntax.res_typ)
in (match (_58_538) with
| (_58_534, c, _58_537) -> begin
(match ((let _152_262 = (FStar_Syntax_Subst.compress c.FStar_Syntax_Syntax.res_typ)
in _152_262.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| _58_542 -> begin
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

let _58_550 = (comp_check_expected_typ env e c)
in (match (_58_550) with
| (e, c, g') -> begin
(let _152_264 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), (c), (_152_264)))
end))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.tk = _58_556; FStar_Syntax_Syntax.pos = _58_554; FStar_Syntax_Syntax.vars = _58_552}, ((e, aqual))::[]) -> begin
(

let _58_567 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end else begin
()
end
in (

let no_reflect = (fun _58_570 -> (match (()) with
| () -> begin
(let _152_269 = (let _152_268 = (let _152_267 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((_152_267), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_152_268))
in (Prims.raise _152_269))
end))
in (

let _58_574 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_574) with
| (reflect_op, _58_573) -> begin
(match ((FStar_TypeChecker_Env.effect_decl_opt env l)) with
| None -> begin
(no_reflect ())
end
| Some (ed) -> begin
if (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable)))) then begin
(no_reflect ())
end else begin
(

let _58_580 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_580) with
| (env_no_ex, topt) -> begin
(

let _58_608 = (

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

let _58_588 = (let _152_277 = (let _152_276 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _152_276 Prims.fst))
in (tc_tot_or_gtot_term _152_277 t))
in (match (_58_588) with
| (t, _58_586, g) -> begin
(match ((let _152_278 = (FStar_Syntax_Subst.compress t)
in _152_278.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_58_590, ((res, _58_597))::((wp, _58_593))::[]) -> begin
((t), (res), (wp), (g))
end
| _58_603 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))
in (match (_58_608) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let _58_622 = (

let _58_612 = (tc_tot_or_gtot_term env_no_ex e)
in (match (_58_612) with
| (e, c, g) -> begin
(

let _58_613 = if (let _152_279 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation _152_279)) then begin
(FStar_TypeChecker_Errors.add_errors env (((("Expected Tot, got a GTot computation"), (e.FStar_Syntax_Syntax.pos)))::[]))
end else begin
()
end
in (match ((FStar_TypeChecker_Rel.try_teq env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)) with
| None -> begin
(

let _58_616 = (let _152_284 = (let _152_283 = (let _152_282 = (let _152_281 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
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
in (match (_58_622) with
| (e, g) -> begin
(

let c = (let _152_291 = (let _152_290 = (let _152_289 = (let _152_288 = (FStar_Syntax_Syntax.as_arg wp)
in (_152_288)::[])
in {FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = _152_289; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp _152_290))
in (FStar_All.pipe_right _152_291 FStar_Syntax_Util.lcomp_of_comp))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e), (aqual)))::[])))) (Some (res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let _58_628 = (comp_check_expected_typ env e c)
in (match (_58_628) with
| (e, c, g') -> begin
(let _152_292 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e), (c), (_152_292)))
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

let env = (let _152_294 = (let _152_293 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _152_293 Prims.fst))
in (FStar_All.pipe_right _152_294 instantiate_both))
in (

let _58_635 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_296 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _152_295 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _152_296 _152_295)))
end else begin
()
end
in (

let _58_640 = (tc_term (no_inst env) head)
in (match (_58_640) with
| (head, chead, g_head) -> begin
(

let _58_644 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _152_297 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _152_297))
end else begin
(let _152_298 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _152_298))
end
in (match (_58_644) with
| (e, c, g) -> begin
(

let _58_645 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_299 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _152_299))
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

let _58_651 = (comp_check_expected_typ env0 e c)
in (match (_58_651) with
| (e, c, g') -> begin
(

let gimp = (match ((let _152_300 = (FStar_Syntax_Subst.compress head)
in _152_300.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _58_654) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e), (c.FStar_Syntax_Syntax.res_typ), (head.FStar_Syntax_Syntax.pos))
in (

let _58_658 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_658.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_658.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_658.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _58_661 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (

let gres = (let _152_301 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _152_301))
in (

let _58_664 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_303 = (FStar_Syntax_Print.term_to_string e)
in (let _152_302 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" _152_303 _152_302)))
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

let _58_672 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_672) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let _58_677 = (tc_term env1 e1)
in (match (_58_677) with
| (e1, c1, g1) -> begin
(

let _58_688 = (match (topt) with
| Some (t) -> begin
((env), (t))
end
| None -> begin
(

let _58_684 = (FStar_Syntax_Util.type_u ())
in (match (_58_684) with
| (k, _58_683) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _152_304 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in ((_152_304), (res_t))))
end))
end)
in (match (_58_688) with
| (env_branches, res_t) -> begin
(

let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let _58_705 = (

let _58_702 = (FStar_List.fold_right (fun _58_696 _58_699 -> (match (((_58_696), (_58_699))) with
| ((_58_692, f, c, g), (caccum, gaccum)) -> begin
(let _152_307 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (_152_307)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_58_702) with
| (cases, g) -> begin
(let _152_308 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in ((_152_308), (g)))
end))
in (match (_58_705) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (guard_x)), (c_branches)))
in (

let e = (

let mk_match = (fun scrutinee -> (

let branches = (FStar_List.map (fun _58_716 -> (match (_58_716) with
| (f, _58_711, _58_713, _58_715) -> begin
f
end)) t_eqns)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (Some (cres.FStar_Syntax_Syntax.eff_name))))) None e.FStar_Syntax_Syntax.pos))))
in if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c1.FStar_Syntax_Syntax.eff_name) then begin
(mk_match e1)
end else begin
(

let e_match = (let _152_312 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match _152_312))
in (

let lb = (let _152_313 = (FStar_TypeChecker_Env.norm_eff_name env c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = _152_313; FStar_Syntax_Syntax.lbdef = e1})
in (let _152_318 = (let _152_317 = (let _152_316 = (let _152_315 = (let _152_314 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (_152_314)::[])
in (FStar_Syntax_Subst.close _152_315 e_match))
in ((((false), ((lb)::[]))), (_152_316)))
in FStar_Syntax_Syntax.Tm_let (_152_317))
in (FStar_Syntax_Syntax.mk _152_318 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))))
end)
in (

let _58_722 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_321 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _152_320 = (let _152_319 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _152_319))
in (FStar_Util.print2 "(%s) comp type = %s\n" _152_321 _152_320)))
end else begin
()
end
in (let _152_322 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e), (cres), (_152_322))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_734); FStar_Syntax_Syntax.lbunivs = _58_732; FStar_Syntax_Syntax.lbtyp = _58_730; FStar_Syntax_Syntax.lbeff = _58_728; FStar_Syntax_Syntax.lbdef = _58_726})::[]), _58_740) -> begin
(

let _58_743 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_323 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _152_323))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _58_747), _58_750) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_765); FStar_Syntax_Syntax.lbunivs = _58_763; FStar_Syntax_Syntax.lbtyp = _58_761; FStar_Syntax_Syntax.lbeff = _58_759; FStar_Syntax_Syntax.lbdef = _58_757})::_58_755), _58_771) -> begin
(

let _58_774 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_324 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _152_324))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _58_778), _58_781) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let _58_795 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_795) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _152_338 = (let _152_337 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_337))
in FStar_Util.Inr (_152_338))
end
in (

let is_data_ctor = (fun _58_3 -> (match (_58_3) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _58_805 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _152_344 = (let _152_343 = (let _152_342 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _152_341 = (FStar_TypeChecker_Env.get_range env)
in ((_152_342), (_152_341))))
in FStar_Syntax_Syntax.Error (_152_343))
in (Prims.raise _152_344))
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
(let _152_346 = (let _152_345 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" _152_345))
in (FStar_All.failwith _152_346))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (match ((let _152_347 = (FStar_Syntax_Subst.compress t1)
in _152_347.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_816) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _58_819 -> begin
(

let imp = (("uvar in term"), (env), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let _58_821 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_821.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_821.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_821.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _58_836 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(

let _58_829 = (FStar_Syntax_Util.type_u ())
in (match (_58_829) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
end))
end
| Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end)
in (match (_58_836) with
| (t, _58_834, g0) -> begin
(

let _58_841 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (_58_841) with
| (e, _58_839, g1) -> begin
(let _152_350 = (let _152_348 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right _152_348 FStar_Syntax_Util.lcomp_of_comp))
in (let _152_349 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e), (_152_350), (_152_349))))
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

let _58_845 = x
in {FStar_Syntax_Syntax.ppname = _58_845.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_845.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let _58_851 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_851) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _152_352 = (let _152_351 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_351))
in FStar_Util.Inr (_152_352))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _58_858; FStar_Syntax_Syntax.pos = _58_856; FStar_Syntax_Syntax.vars = _58_854}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let _58_868 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_868) with
| (us', t) -> begin
(

let _58_875 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _152_355 = (let _152_354 = (let _152_353 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (_152_353)))
in FStar_Syntax_Syntax.Error (_152_354))
in (Prims.raise _152_355))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _58_874 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (

let fv' = (

let _58_877 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _58_879 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_879.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_879.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_877.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_877.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _152_358 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _152_358 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let _58_887 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_887) with
| (us, t) -> begin
(

let fv' = (

let _58_888 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _58_890 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_890.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_890.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_888.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_888.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _152_359 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _152_359 us))
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

let _58_904 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_904) with
| (bs, c) -> begin
(

let env0 = env
in (

let _58_909 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_909) with
| (env, _58_908) -> begin
(

let _58_914 = (tc_binders env bs)
in (match (_58_914) with
| (bs, env, g, us) -> begin
(

let _58_918 = (tc_comp env c)
in (match (_58_918) with
| (c, uc, f) -> begin
(

let e = (

let _58_919 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _58_919.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_919.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_919.FStar_Syntax_Syntax.vars})
in (

let _58_922 = (check_smt_pat env e bs c)
in (

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _152_360 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _152_360))
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

let _58_938 = (let _152_362 = (let _152_361 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_361)::[])
in (FStar_Syntax_Subst.open_term _152_362 phi))
in (match (_58_938) with
| (x, phi) -> begin
(

let env0 = env
in (

let _58_943 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_943) with
| (env, _58_942) -> begin
(

let _58_948 = (let _152_363 = (FStar_List.hd x)
in (tc_binder env _152_363))
in (match (_58_948) with
| (x, env, f1, u) -> begin
(

let _58_949 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_366 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _152_365 = (FStar_Syntax_Print.term_to_string phi)
in (let _152_364 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _152_366 _152_365 _152_364))))
end else begin
()
end
in (

let _58_954 = (FStar_Syntax_Util.type_u ())
in (match (_58_954) with
| (t_phi, _58_953) -> begin
(

let _58_959 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_58_959) with
| (phi, _58_957, f2) -> begin
(

let e = (

let _58_960 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _58_960.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_960.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_960.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _152_367 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _152_367))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _58_968) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (

let _58_974 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_368 = (FStar_Syntax_Print.term_to_string (

let _58_972 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))); FStar_Syntax_Syntax.tk = _58_972.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _58_972.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_972.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _152_368))
end else begin
()
end
in (

let _58_978 = (FStar_Syntax_Subst.open_term bs body)
in (match (_58_978) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _58_980 -> begin
(let _152_371 = (let _152_370 = (FStar_Syntax_Print.term_to_string top)
in (let _152_369 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" _152_370 _152_369)))
in (FStar_All.failwith _152_371))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_58_985) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_58_988, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_58_993, Some (_58_995)) -> begin
(FStar_All.failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (_58_1000) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_58_1003) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_58_1006) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_58_1010) -> begin
FStar_TypeChecker_Common.t_range
end
| _58_1013 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(

let _58_1021 = (FStar_Syntax_Util.type_u ())
in (match (_58_1021) with
| (k, u) -> begin
(

let _58_1026 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_1026) with
| (t, _58_1024, g) -> begin
(let _152_376 = (FStar_Syntax_Syntax.mk_Total t)
in ((_152_376), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(

let _58_1031 = (FStar_Syntax_Util.type_u ())
in (match (_58_1031) with
| (k, u) -> begin
(

let _58_1036 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_1036) with
| (t, _58_1034, g) -> begin
(let _152_377 = (FStar_Syntax_Syntax.mk_GTotal t)
in ((_152_377), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (

let tc = (let _152_379 = (let _152_378 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_152_378)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _152_379 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let _58_1045 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_58_1045) with
| (tc, _58_1043, f) -> begin
(

let _58_1049 = (FStar_Syntax_Util.head_and_args tc)
in (match (_58_1049) with
| (_58_1047, args) -> begin
(

let _58_1052 = (let _152_381 = (FStar_List.hd args)
in (let _152_380 = (FStar_List.tl args)
in ((_152_381), (_152_380))))
in (match (_58_1052) with
| (res, args) -> begin
(

let _58_1068 = (let _152_383 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _58_4 -> (match (_58_4) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _58_1059 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1059) with
| (env, _58_1058) -> begin
(

let _58_1064 = (tc_tot_or_gtot_term env e)
in (match (_58_1064) with
| (e, _58_1062, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e)), (g))
end))
end))
end
| f -> begin
((f), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right _152_383 FStar_List.unzip))
in (match (_58_1068) with
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
| _58_1079 -> begin
(FStar_All.failwith "Impossible:Unexpected sort for computation")
end)))
end
| _58_1081 -> begin
(FStar_All.failwith "Impossible:Unexpected sort for computation")
end)
in (

let c = (FStar_Syntax_Syntax.mk_Comp (

let _58_1083 = c
in {FStar_Syntax_Syntax.effect_name = _58_1083.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _58_1083.FStar_Syntax_Syntax.flags}))
in (

let u_c = (match ((FStar_TypeChecker_Util.effect_repr env c u)) with
| None -> begin
u
end
| Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end)
in (let _152_384 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((c), (u_c), (_152_384))))))
end))
end))
end))
end))))
end)))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_58_1096) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _152_389 = (aux u)
in FStar_Syntax_Syntax.U_succ (_152_389))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _152_390 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_152_390))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _152_394 = (let _152_393 = (let _152_392 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _152_391 = (FStar_TypeChecker_Env.get_range env)
in ((_152_392), (_152_391))))
in FStar_Syntax_Syntax.Error (_152_393))
in (Prims.raise _152_394))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _152_395 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _152_395 Prims.snd))
end
| _58_1111 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _152_404 = (let _152_403 = (let _152_402 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in ((_152_402), (top.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_152_403))
in (Prims.raise _152_404)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun _58_1129 bs bs_expected -> (match (_58_1129) with
| (env, out, g, subst) -> begin
(match (((bs), (bs_expected))) with
| ([], []) -> begin
((env), ((FStar_List.rev out)), (None), (g), (subst))
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
(

let _58_1160 = (match (((imp), (imp'))) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _152_421 = (let _152_420 = (let _152_419 = (let _152_417 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _152_417))
in (let _152_418 = (FStar_Syntax_Syntax.range_of_bv hd)
in ((_152_419), (_152_418))))
in FStar_Syntax_Syntax.Error (_152_420))
in (Prims.raise _152_421))
end
| _58_1159 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _58_1177 = (match ((let _152_422 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _152_422.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| _58_1165 -> begin
(

let _58_1166 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_423 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _152_423))
end else begin
()
end
in (

let _58_1172 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_58_1172) with
| (t, _58_1170, g1) -> begin
(

let g2 = (let _152_425 = (FStar_TypeChecker_Env.get_range env)
in (let _152_424 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _152_425 "Type annotation on parameter incompatible with the expected type" _152_424)))
in (

let g = (let _152_426 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _152_426))
in ((t), (g))))
end)))
end)
in (match (_58_1177) with
| (t, g) -> begin
(

let hd = (

let _58_1178 = hd
in {FStar_Syntax_Syntax.ppname = _58_1178.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1178.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env = (push_binding env b)
in (

let subst = (let _152_427 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _152_427))
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

let _58_1199 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _58_1198 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (

let _58_1206 = (tc_binders env bs)
in (match (_58_1206) with
| (bs, envbody, g, _58_1205) -> begin
(

let _58_1224 = (match ((let _152_434 = (FStar_Syntax_Subst.compress body)
in _152_434.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _58_1211) -> begin
(

let _58_1218 = (tc_comp envbody c)
in (match (_58_1218) with
| (c, _58_1216, g') -> begin
(let _152_435 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((Some (c)), (body), (_152_435)))
end))
end
| _58_1220 -> begin
((None), (body), (g))
end)
in (match (_58_1224) with
| (copt, body, g) -> begin
((None), (bs), ([]), (copt), (envbody), (body), (g))
end))
end)))
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm t -> (match ((let _152_440 = (FStar_Syntax_Subst.compress t)
in _152_440.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let _58_1251 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _58_1250 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _58_1258 = (tc_binders env bs)
in (match (_58_1258) with
| (bs, envbody, g, _58_1257) -> begin
(

let _58_1262 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_58_1262) with
| (envbody, _58_1261) -> begin
((Some (((t), (true)))), (bs), ([]), (None), (envbody), (body), (g))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _58_1265) -> begin
(

let _58_1276 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_58_1276) with
| (_58_1269, bs, bs', copt, env, body, g) -> begin
((Some (((t), (false)))), (bs), (bs'), (copt), (env), (body), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _58_1283 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_58_1283) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun _58_1294 c_expected -> (match (_58_1294) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _152_451 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in ((env), (bs), (guard), (_152_451)))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (let _152_452 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _152_452))
in (let _152_453 = (FStar_Syntax_Subst.subst_comp subst c)
in ((env), (bs), (guard), (_152_453))))
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

let _58_1315 = (check_binders env more_bs bs_expected)
in (match (_58_1315) with
| (env, bs', more, guard', subst) -> begin
(let _152_455 = (let _152_454 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env), ((FStar_List.append bs bs')), (more), (_152_454), (subst)))
in (handle_more _152_455 c_expected))
end))
end
| _58_1317 -> begin
(let _152_457 = (let _152_456 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _152_456))
in (fail _152_457 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _152_458 = (check_binders env bs bs_expected)
in (handle_more _152_458 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let _58_1323 = envbody
in {FStar_TypeChecker_Env.solver = _58_1323.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1323.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1323.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1323.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1323.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1323.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1323.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1323.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1323.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1323.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1323.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1323.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _58_1323.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1323.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1323.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1323.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1323.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1323.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1323.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1323.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1323.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1323.FStar_TypeChecker_Env.qname_and_index})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _58_1328 _58_1331 -> (match (((_58_1328), (_58_1331))) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _58_1337 = (let _152_468 = (let _152_467 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _152_467 Prims.fst))
in (tc_term _152_468 t))
in (match (_58_1337) with
| (t, _58_1334, _58_1336) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l (([]), (t)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _152_469 = (FStar_Syntax_Syntax.mk_binder (

let _58_1341 = x
in {FStar_Syntax_Syntax.ppname = _58_1341.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1341.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_152_469)::letrec_binders)
end
| _58_1344 -> begin
letrec_binders
end)
in ((env), (lb))))
end))
end)) ((envbody), ([])))))))
in (

let _58_1350 = (check_actuals_against_formals env bs bs_expected)
in (match (_58_1350) with
| (envbody, bs, g, c) -> begin
(

let _58_1353 = if (FStar_TypeChecker_Env.should_verify env) then begin
(mk_letrec_env envbody bs c)
end else begin
((envbody), ([]))
end
in (match (_58_1353) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in ((Some (((t), (false)))), (bs), (letrecs), (Some (c)), (envbody), (body), (g)))
end))
end))))
end))
end
| _58_1356 -> begin
if (not (norm)) then begin
(let _152_470 = (unfold_whnf env t)
in (as_function_typ true _152_470))
end else begin
(

let _58_1366 = (expected_function_typ env None body)
in (match (_58_1366) with
| (_58_1358, bs, _58_1361, c_opt, envbody, body, g) -> begin
((Some (((t), (false)))), (bs), ([]), (c_opt), (envbody), (body), (g))
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let _58_1370 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1370) with
| (env, topt) -> begin
(

let _58_1374 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_471 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _152_471 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (

let _58_1383 = (expected_function_typ env topt body)
in (match (_58_1383) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let _58_1389 = (tc_term (

let _58_1384 = envbody
in {FStar_TypeChecker_Env.solver = _58_1384.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1384.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1384.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1384.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1384.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1384.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1384.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1384.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1384.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1384.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1384.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1384.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1384.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_1384.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1384.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1384.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1384.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1384.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1384.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1384.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1384.FStar_TypeChecker_Env.qname_and_index}) body)
in (match (_58_1389) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _58_1391 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _152_474 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _152_473 = (let _152_472 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _152_472))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _152_474 _152_473)))
end else begin
()
end
in (

let _58_1398 = (let _152_476 = (let _152_475 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body), (_152_475)))
in (check_expected_effect (

let _58_1393 = envbody
in {FStar_TypeChecker_Env.solver = _58_1393.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1393.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1393.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1393.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1393.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1393.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1393.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1393.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1393.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1393.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1393.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1393.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1393.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1393.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1393.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1393.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1393.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1393.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1393.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1393.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1393.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1393.FStar_TypeChecker_Env.qname_and_index}) c_opt _152_476))
in (match (_58_1398) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(let _152_477 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _152_477))
end else begin
(

let guard = (let _152_478 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) _152_478))
in guard)
end
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _152_481 = (let _152_480 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _152_479 -> FStar_Util.Inl (_152_479)))
in Some (_152_480))
in (FStar_Syntax_Util.abs bs body _152_481))
in (

let _58_1421 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_58_1410) -> begin
((e), (t), (guard))
end
| _58_1413 -> begin
(

let _58_1416 = if use_teq then begin
(let _152_482 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in ((e), (_152_482)))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_58_1416) with
| (e, guard') -> begin
(let _152_483 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((e), (t), (_152_483)))
end))
end))
end
| None -> begin
((e), (tfun_computed), (guard))
end)
in (match (_58_1421) with
| (e, tfun, guard) -> begin
(

let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (

let _58_1425 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_58_1425) with
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

let _58_1435 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_492 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _152_491 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _152_492 _152_491)))
end else begin
()
end
in (

let monadic_application = (fun _58_1442 subst arg_comps_rev arg_rets guard fvs bs -> (match (_58_1442) with
| (head, chead, ghead, cres) -> begin
(

let _58_1449 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let _58_1477 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun _58_5 -> (match (_58_5) with
| (_58_1456, _58_1458, None) -> begin
false
end
| (_58_1462, _58_1464, Some (c)) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _152_508 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _152_508 cres))
end else begin
(

let _58_1469 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_511 = (FStar_Syntax_Print.term_to_string head)
in (let _152_510 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _152_509 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _152_511 _152_510 _152_509))))
end else begin
()
end
in cres)
end
in ((cres), (g))))))
end
| _58_1473 -> begin
(

let g = (let _152_512 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right _152_512 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _152_517 = (let _152_516 = (let _152_515 = (let _152_514 = (let _152_513 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _152_513))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _152_514))
in (FStar_Syntax_Syntax.mk_Total _152_515))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_516))
in ((_152_517), (g))))
end)
in (match (_58_1477) with
| (cres, guard) -> begin
(

let _58_1478 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_518 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _152_518))
end else begin
()
end
in (

let _58_1500 = (FStar_List.fold_left (fun _58_1483 _58_1489 -> (match (((_58_1483), (_58_1489))) with
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
in (match (_58_1500) with
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

let _58_1506 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (_58_1506) with
| (comp, g) -> begin
((app), (comp), (g))
end)))))
end)))
end)))
end))
in (

let rec tc_args = (fun head_info _58_1514 bs args -> (match (_58_1514) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args))) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (_58_1520))))::rest, ((_58_1528, None))::_58_1526) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _58_1534 = (check_no_escape (Some (head)) env fvs t)
in (

let _58_1540 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_58_1540) with
| (varg, _58_1538, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst
in (

let arg = (let _152_530 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (_152_530)))
in (let _152_532 = (let _152_531 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst), ((((arg), (None), (None)))::outargs), ((arg)::arg_rets), (_152_531), (fvs)))
in (tc_args head_info _152_532 rest args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
(

let _58_1572 = (match (((aqual), (aq))) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _58_1571 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifier"), (e.FStar_Syntax_Syntax.pos)))))
end)
in (

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let _58_1575 = x
in {FStar_Syntax_Syntax.ppname = _58_1575.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1575.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (

let _58_1578 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_533 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _152_533))
end else begin
()
end
in (

let _58_1580 = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let _58_1583 = env
in {FStar_TypeChecker_Env.solver = _58_1583.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1583.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1583.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1583.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1583.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1583.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1583.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1583.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1583.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1583.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1583.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1583.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1583.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1583.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1583.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _58_1583.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1583.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1583.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1583.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1583.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1583.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1583.FStar_TypeChecker_Env.qname_and_index})
in (

let _58_1586 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_536 = (FStar_Syntax_Print.tag_of_term e)
in (let _152_535 = (FStar_Syntax_Print.term_to_string e)
in (let _152_534 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _152_536 _152_535 _152_534))))
end else begin
()
end
in (

let _58_1591 = (tc_term env e)
in (match (_58_1591) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = ((e), (aq))
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(

let subst = (let _152_537 = (FStar_List.hd bs)
in (maybe_extend_subst subst _152_537 e))
in (tc_args head_info ((subst), ((((arg), (None), (None)))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(

let subst = (let _152_538 = (FStar_List.hd bs)
in (maybe_extend_subst subst _152_538 e))
in (tc_args head_info ((subst), ((((arg), (Some (x)), (Some (c))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (let _152_539 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _152_539)) then begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _152_540 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _152_540))
in (tc_args head_info ((subst), ((((arg), (Some (newx)), (Some (c))))::outargs), ((arg')::arg_rets), (g), (fvs)) rest rest')))
end else begin
(let _152_544 = (let _152_543 = (let _152_542 = (let _152_541 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _152_541))
in (_152_542)::arg_rets)
in ((subst), ((((arg), (Some (x)), (Some (c))))::outargs), (_152_543), (g), ((x)::fvs)))
in (tc_args head_info _152_544 rest rest'))
end
end
end))
end))))))))))
end
| (_58_1599, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::_58_1604) -> begin
(

let _58_1611 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (_58_1611) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _152_549 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _152_549 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let _58_1622 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (_58_1622) with
| (bs, cres') -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp cres')))
in (

let _58_1624 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_550 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _152_550))
end else begin
()
end
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args)))
end))
end
| _58_1627 when (not (norm)) -> begin
(let _152_551 = (unfold_whnf env tres)
in (aux true _152_551))
end
| _58_1629 -> begin
(let _152_557 = (let _152_556 = (let _152_555 = (let _152_553 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (let _152_552 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _152_553 _152_552)))
in (let _152_554 = (FStar_Syntax_Syntax.argpos arg)
in ((_152_555), (_152_554))))
in FStar_Syntax_Syntax.Error (_152_556))
in (Prims.raise _152_557))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (match ((let _152_562 = (FStar_Syntax_Util.unrefine tf)
in _152_562.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl -> begin
(

let _58_1662 = (tc_term env e)
in (match (_58_1662) with
| (e, c, g_e) -> begin
(

let _58_1666 = (tc_args env tl)
in (match (_58_1666) with
| (args, comps, g_rest) -> begin
(let _152_567 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e), (imp)))::args), ((((e.FStar_Syntax_Syntax.pos), (c)))::comps), (_152_567)))
end))
end))
end))
in (

let _58_1670 = (tc_args env args)
in (match (_58_1670) with
| (args, comps, g_args) -> begin
(

let bs = (let _152_569 = (FStar_All.pipe_right comps (FStar_List.map (fun _58_1674 -> (match (_58_1674) with
| (_58_1672, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks _152_569))
in (

let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _58_1680 -> begin
FStar_Syntax_Util.ml_comp
end)
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _152_584 = (FStar_Syntax_Subst.compress t)
in _152_584.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_58_1686) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _58_1691 -> begin
ml_or_tot
end)
end)
in (

let cres = (let _152_589 = (let _152_588 = (let _152_587 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _152_587 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _152_588))
in (ml_or_tot _152_589 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (

let _58_1695 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _152_592 = (FStar_Syntax_Print.term_to_string head)
in (let _152_591 = (FStar_Syntax_Print.term_to_string tf)
in (let _152_590 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _152_592 _152_591 _152_590))))
end else begin
()
end
in (

let _58_1697 = (let _152_593 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _152_593))
in (

let comp = (let _152_596 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _58_1701 out -> (match (_58_1701) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c ((None), (out)))
end)) ((((head.FStar_Syntax_Syntax.pos), (chead)))::comps) _152_596))
in (let _152_598 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _152_597 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((_152_598), (comp), (_152_597))))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _58_1710 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_1710) with
| (bs, c) -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp c)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args))
end))
end
| _58_1713 -> begin
if (not (norm)) then begin
(let _152_599 = (unfold_whnf env tf)
in (check_function_app true _152_599))
end else begin
(let _152_602 = (let _152_601 = (let _152_600 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in ((_152_600), (head.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_152_601))
in (Prims.raise _152_602))
end
end))
in (let _152_604 = (let _152_603 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _152_603))
in (check_function_app false _152_604))))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let _58_1749 = (FStar_List.fold_left2 (fun _58_1730 _58_1733 _58_1736 -> (match (((_58_1730), (_58_1733), (_58_1736))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(

let _58_1737 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifiers"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _58_1742 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_58_1742) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (let _152_614 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _152_614 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _152_618 = (let _152_616 = (let _152_615 = (FStar_Syntax_Syntax.as_arg e)
in (_152_615)::[])
in (FStar_List.append seen _152_616))
in (let _152_617 = (FStar_TypeChecker_Rel.conj_guard guard g)
in ((_152_618), (_152_617), (ghost)))))))
end)))
end)) (([]), (g_head), (false)) args bs)
in (match (_58_1749) with
| (args, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = if ghost then begin
(let _152_619 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _152_619 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (

let _58_1754 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_58_1754) with
| (c, g) -> begin
((e), (c), (g))
end))))
end)))
end
| _58_1756 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let _58_1763 = (FStar_Syntax_Subst.open_branch branch)
in (match (_58_1763) with
| (pattern, when_clause, branch_exp) -> begin
(

let _58_1768 = branch
in (match (_58_1768) with
| (cpat, _58_1766, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _58_1776 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_58_1776) with
| (pat_bvs, exps, p) -> begin
(

let _58_1777 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_631 = (FStar_Syntax_Print.pat_to_string p0)
in (let _152_630 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _152_631 _152_630)))
end else begin
()
end
in (

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let _58_1783 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_58_1783) with
| (env1, _58_1782) -> begin
(

let env1 = (

let _58_1784 = env1
in {FStar_TypeChecker_Env.solver = _58_1784.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1784.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1784.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1784.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1784.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1784.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1784.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1784.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _58_1784.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1784.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1784.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1784.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1784.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1784.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1784.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1784.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1784.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1784.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1784.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1784.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1784.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1784.FStar_TypeChecker_Env.qname_and_index})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _58_1823 = (let _152_654 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _58_1789 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_634 = (FStar_Syntax_Print.term_to_string e)
in (let _152_633 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _152_634 _152_633)))
end else begin
()
end
in (

let _58_1794 = (tc_term env1 e)
in (match (_58_1794) with
| (e, lc, g) -> begin
(

let _58_1795 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_636 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _152_635 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _152_636 _152_635)))
end else begin
()
end
in (

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let _58_1801 = (let _152_637 = (FStar_TypeChecker_Rel.discharge_guard env (

let _58_1799 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_1799.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_1799.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_1799.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _152_637 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _152_642 = (let _152_641 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _152_641 (FStar_List.map (fun _58_1809 -> (match (_58_1809) with
| (u, _58_1808) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _152_642 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _58_1817 = if (let _152_643 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _152_643)) then begin
(

let unresolved = (let _152_644 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _152_644 FStar_Util.set_elements))
in (let _152_652 = (let _152_651 = (let _152_650 = (let _152_649 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _152_648 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _152_647 = (let _152_646 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _58_1816 -> (match (_58_1816) with
| (u, _58_1815) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _152_646 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _152_649 _152_648 _152_647))))
in ((_152_650), (p.FStar_Syntax_Syntax.p)))
in FStar_Syntax_Syntax.Error (_152_651))
in (Prims.raise _152_652)))
end else begin
()
end
in (

let _58_1819 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_653 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _152_653))
end else begin
()
end
in ((e), (e'))))))))))))
end))))))
in (FStar_All.pipe_right _152_654 FStar_List.unzip))
in (match (_58_1823) with
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

let _58_1830 = (let _152_655 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _152_655 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_58_1830) with
| (scrutinee_env, _58_1829) -> begin
(

let _58_1836 = (tc_pat true pat_t pattern)
in (match (_58_1836) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let _58_1846 = (match (when_clause) with
| None -> begin
((None), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (e) -> begin
if (FStar_TypeChecker_Env.should_verify env) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("When clauses are not yet supported in --verify mode; they will be some day"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
(

let _58_1843 = (let _152_656 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _152_656 e))
in (match (_58_1843) with
| (e, c, g) -> begin
((Some (e)), (g))
end))
end
end)
in (match (_58_1846) with
| (when_clause, g_when) -> begin
(

let _58_1850 = (tc_term pat_env branch_exp)
in (match (_58_1850) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _152_658 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _152_657 -> Some (_152_657)) _152_658))
end)
in (

let _58_1908 = (

let eqs = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
None
end else begin
(FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _58_1868 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _152_662 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _152_661 -> Some (_152_661)) _152_662))
end))
end))) None))
end
in (

let _58_1876 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_58_1876) with
| (c, g_branch) -> begin
(

let _58_1903 = (match (((eqs), (when_condition))) with
| _58_1878 when (not ((FStar_TypeChecker_Env.should_verify env))) -> begin
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
in (let _152_665 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _152_664 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((_152_665), (_152_664))))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (let _152_666 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_152_666))
in (let _152_669 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _152_668 = (let _152_667 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _152_667 g_when))
in ((_152_669), (_152_668))))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _152_670 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in ((_152_670), (g_when)))))
end)
in (match (_58_1903) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _152_672 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _152_671 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in ((_152_672), (_152_671), (g_branch)))))
end))
end)))
in (match (_58_1908) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
FStar_Syntax_Util.t_true
end else begin
(

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> if ((let _152_682 = (let _152_681 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _152_681))
in (FStar_List.length _152_682)) > (Prims.parse_int "1")) then begin
(

let disc = (let _152_683 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _152_683 FStar_Syntax_Syntax.Delta_equational None))
in (

let disc = (let _152_685 = (let _152_684 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_152_684)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _152_685 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _152_686 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_152_686)::[])))
end else begin
[]
end)
in (

let fail = (fun _58_1918 -> (match (()) with
| () -> begin
(let _152_692 = (let _152_691 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _152_690 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _152_689 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _152_691 _152_690 _152_689))))
in (FStar_All.failwith _152_692))
end))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _58_1925) -> begin
(head_constructor t)
end
| _58_1929 -> begin
(fail ())
end))
in (

let pat_exp = (let _152_695 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _152_695 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_58_1954) -> begin
(let _152_700 = (let _152_699 = (let _152_698 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _152_697 = (let _152_696 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_152_696)::[])
in (_152_698)::_152_697))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _152_699 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_152_700)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _152_701 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _152_701))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(

let sub_term_guards = (let _152_708 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _58_1972 -> (match (_58_1972) with
| (ei, _58_1971) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _58_1976 -> begin
(

let sub_term = (let _152_707 = (let _152_704 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _152_704 FStar_Syntax_Syntax.Delta_equational None))
in (let _152_706 = (let _152_705 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_152_705)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _152_707 _152_706 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _152_708 FStar_List.flatten))
in (let _152_709 = (discriminate scrutinee_tm f)
in (FStar_List.append _152_709 sub_term_guards)))
end)
end
| _58_1980 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(

let t = (let _152_714 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _152_714))
in (

let _58_1988 = (FStar_Syntax_Util.type_u ())
in (match (_58_1988) with
| (k, _58_1987) -> begin
(

let _58_1994 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_58_1994) with
| (t, _58_1991, _58_1993) -> begin
t
end))
end)))
end)
in (

let branch_guard = (let _152_715 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _152_715 FStar_Syntax_Util.mk_disj_l))
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

let _58_2002 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_716 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _152_716))
end else begin
()
end
in (let _152_717 = (FStar_Syntax_Subst.close_branch ((pattern), (when_clause), (branch_exp)))
in ((_152_717), (branch_guard), (c), (guard))))))
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

let _58_2019 = (check_let_bound_def true env lb)
in (match (_58_2019) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let _58_2031 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
((g1), (e1), (univ_vars), (c1))
end else begin
(

let g1 = (let _152_720 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _152_720 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _58_2026 = (let _152_724 = (let _152_723 = (let _152_722 = (let _152_721 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (_152_721)))
in (_152_722)::[])
in (FStar_TypeChecker_Util.generalize env _152_723))
in (FStar_List.hd _152_724))
in (match (_58_2026) with
| (_58_2022, univs, e1, c1) -> begin
((g1), (e1), (univs), ((FStar_Syntax_Util.lcomp_of_comp c1)))
end)))
end
in (match (_58_2031) with
| (g1, e1, univ_vars, c1) -> begin
(

let _58_2041 = if (FStar_TypeChecker_Env.should_verify env) then begin
(

let _58_2034 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_58_2034) with
| (ok, c1) -> begin
if ok then begin
((e2), (c1))
end else begin
(

let _58_2035 = if (FStar_Options.warn_top_level_effects ()) then begin
(let _152_725 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _152_725 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _152_726 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) None e2.FStar_Syntax_Syntax.pos)
in ((_152_726), (c1))))
end
end))
end else begin
(

let _58_2037 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _152_727 = (c1.FStar_Syntax_Syntax.comp ())
in ((e2), (_152_727))))
end
in (match (_58_2041) with
| (e2, c1) -> begin
(

let cres = (let _152_728 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_728))
in (

let _58_2043 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _152_729 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((_152_729), (cres), (FStar_TypeChecker_Rel.trivial_guard))))))
end))
end))
end))
end
| _58_2047 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let _58_2058 = env
in {FStar_TypeChecker_Env.solver = _58_2058.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2058.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2058.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2058.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2058.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2058.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2058.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2058.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2058.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2058.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2058.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2058.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2058.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_2058.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2058.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2058.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2058.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2058.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2058.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2058.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2058.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2058.FStar_TypeChecker_Env.qname_and_index})
in (

let _58_2067 = (let _152_733 = (let _152_732 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _152_732 Prims.fst))
in (check_let_bound_def false _152_733 lb))
in (match (_58_2067) with
| (e1, _58_2063, c1, g1, annotated) -> begin
(

let x = (

let _58_2068 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_2068.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2068.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let _58_2074 = (let _152_735 = (let _152_734 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_734)::[])
in (FStar_Syntax_Subst.open_term _152_735 e2))
in (match (_58_2074) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _58_2080 = (let _152_736 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _152_736 e2))
in (match (_58_2080) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (x)), (c2)))
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e2 = (FStar_TypeChecker_Util.maybe_lift env e2 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e = (let _152_739 = (let _152_738 = (let _152_737 = (FStar_Syntax_Subst.close xb e2)
in ((((false), ((lb)::[]))), (_152_737)))
in FStar_Syntax_Syntax.Tm_let (_152_738))
in (FStar_Syntax_Syntax.mk _152_739 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (let _152_742 = (let _152_741 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _152_741 e1))
in (FStar_All.pipe_left (fun _152_740 -> FStar_TypeChecker_Common.NonTrivial (_152_740)) _152_742))
in (

let g2 = (let _152_744 = (let _152_743 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _152_743 g2))
in (FStar_TypeChecker_Rel.close_guard xb _152_744))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if (let _152_745 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome _152_745)) then begin
((e), (cres), (guard))
end else begin
(

let _58_2089 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in ((e), (cres), (guard)))
end))))))))
end))))
end))))
end)))
end
| _58_2092 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _58_2104 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_58_2104) with
| (lbs, e2) -> begin
(

let _58_2107 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2107) with
| (env0, topt) -> begin
(

let _58_2110 = (build_let_rec_env true env0 lbs)
in (match (_58_2110) with
| (lbs, rec_env) -> begin
(

let _58_2113 = (check_let_recs rec_env lbs)
in (match (_58_2113) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (let _152_748 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _152_748 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _152_751 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _152_751 (fun _152_750 -> Some (_152_750))))
in (

let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(

let ecs = (let _152_755 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _152_754 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (_152_754))))))
in (FStar_TypeChecker_Util.generalize env _152_755))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _58_2124 -> (match (_58_2124) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _152_757 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_757))
in (

let _58_2127 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _58_2131 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_2131) with
| (lbs, e2) -> begin
(let _152_759 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _152_758 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in ((_152_759), (cres), (_152_758))))
end)))))))
end))
end))
end))
end))
end
| _58_2133 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

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

let _58_2151 = (build_let_rec_env false env0 lbs)
in (match (_58_2151) with
| (lbs, rec_env) -> begin
(

let _58_2154 = (check_let_recs rec_env lbs)
in (match (_58_2154) with
| (lbs, g_lbs) -> begin
(

let _58_2166 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let _58_2157 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_2157.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2157.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let _58_2160 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _58_2160.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _58_2160.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _58_2160.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _58_2160.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (lb.FStar_Syntax_Syntax.lbtyp)))
in ((env), (lb)))))) env))
in (match (_58_2166) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let _58_2172 = (tc_term env e2)
in (match (_58_2172) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _58_2176 = cres
in {FStar_Syntax_Syntax.eff_name = _58_2176.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _58_2176.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_2176.FStar_Syntax_Syntax.comp})
in (

let _58_2181 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_2181) with
| (lbs, e2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_58_2184) -> begin
((e), (cres), (guard))
end
| None -> begin
(

let _58_2187 = (check_no_escape None env bvs tres)
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
| _58_2190 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun t -> (

let _58_2200 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (_58_2200) with
| (_58_2198, c) -> begin
(

let quals = (FStar_TypeChecker_Env.lookup_effect_quals env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
end)))
in (

let _58_2230 = (FStar_List.fold_left (fun _58_2204 lb -> (match (_58_2204) with
| (lbs, env) -> begin
(

let _58_2209 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_58_2209) with
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

let _58_2218 = (let _152_773 = (let _152_772 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _152_772))
in (tc_check_tot_or_gtot_term (

let _58_2212 = env0
in {FStar_TypeChecker_Env.solver = _58_2212.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2212.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2212.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2212.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2212.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2212.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2212.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2212.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2212.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2212.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2212.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2212.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2212.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2212.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _58_2212.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2212.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2212.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2212.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2212.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2212.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2212.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2212.FStar_TypeChecker_Env.qname_and_index}) t _152_773))
in (match (_58_2218) with
| (t, _58_2216, g) -> begin
(

let _58_2219 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (

let env = if ((termination_check_enabled t) && (FStar_TypeChecker_Env.should_verify env)) then begin
(

let _58_2222 = env
in {FStar_TypeChecker_Env.solver = _58_2222.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2222.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2222.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2222.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2222.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2222.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2222.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2222.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2222.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2222.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2222.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2222.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t)))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2222.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_2222.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2222.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2222.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2222.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2222.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2222.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2222.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2222.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2222.FStar_TypeChecker_Env.qname_and_index})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (t)))
end
in (

let lb = (

let _58_2225 = lb
in {FStar_Syntax_Syntax.lbname = _58_2225.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _58_2225.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb)::lbs), (env)))))))
end))
end)) (([]), (env)) lbs)
in (match (_58_2230) with
| (lbs, env) -> begin
(((FStar_List.rev lbs)), (env))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _58_2243 = (let _152_778 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _58_2237 = (let _152_777 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _152_777 lb.FStar_Syntax_Syntax.lbdef))
in (match (_58_2237) with
| (e, c, g) -> begin
(

let _58_2238 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in ((lb), (g))))
end)))))
in (FStar_All.pipe_right _152_778 FStar_List.unzip))
in (match (_58_2243) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _58_2251 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2251) with
| (env1, _58_2250) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _58_2257 = (check_lbtyp top_level env lb)
in (match (_58_2257) with
| (topt, wf_annot, univ_vars, env1) -> begin
(

let _58_2258 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _58_2265 = (tc_maybe_toplevel_term (

let _58_2260 = env1
in {FStar_TypeChecker_Env.solver = _58_2260.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2260.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2260.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2260.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2260.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2260.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2260.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2260.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2260.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2260.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2260.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2260.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2260.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _58_2260.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2260.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2260.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2260.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2260.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2260.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2260.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2260.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2260.FStar_TypeChecker_Env.qname_and_index}) e1)
in (match (_58_2265) with
| (e1, c1, g1) -> begin
(

let _58_2269 = (let _152_785 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_2266 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _152_785 e1 c1 wf_annot))
in (match (_58_2269) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _58_2271 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_786 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _152_786))
end else begin
()
end
in (let _152_787 = (FStar_Option.isSome topt)
in ((e1), (univ_vars), (c1), (g1), (_152_787)))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _58_2278 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in ((None), (FStar_TypeChecker_Rel.trivial_guard), ([]), (env)))
end
| _58_2281 -> begin
(

let _58_2284 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_58_2284) with
| (univ_vars, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _152_791 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars), (_152_791)))
end else begin
(

let _58_2289 = (FStar_Syntax_Util.type_u ())
in (match (_58_2289) with
| (k, _58_2288) -> begin
(

let _58_2294 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_58_2294) with
| (t, _58_2292, g) -> begin
(

let _58_2295 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _152_794 = (let _152_792 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _152_792))
in (let _152_793 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _152_794 _152_793)))
end else begin
()
end
in (

let t = (norm env1 t)
in (let _152_795 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (g), (univ_vars), (_152_795)))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _58_2301 -> (match (_58_2301) with
| (x, imp) -> begin
(

let _58_2304 = (FStar_Syntax_Util.type_u ())
in (match (_58_2304) with
| (tu, u) -> begin
(

let _58_2305 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_800 = (FStar_Syntax_Print.bv_to_string x)
in (let _152_799 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _152_798 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binders %s:%s at type %s\n" _152_800 _152_799 _152_798))))
end else begin
()
end
in (

let _58_2311 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_58_2311) with
| (t, _58_2309, g) -> begin
(

let x = (((

let _58_2312 = x
in {FStar_Syntax_Syntax.ppname = _58_2312.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2312.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in (

let _58_2315 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_802 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _152_801 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _152_802 _152_801)))
end else begin
()
end
in (let _152_803 = (push_binding env x)
in ((x), (_152_803), (g), (u)))))
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

let _58_2330 = (tc_binder env b)
in (match (_58_2330) with
| (b, env', g, u) -> begin
(

let _58_2335 = (aux env' bs)
in (match (_58_2335) with
| (bs, env', g', us) -> begin
(let _152_811 = (let _152_810 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _152_810))
in (((b)::bs), (env'), (_152_811), ((u)::us)))
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
(let _152_820 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t), (imp)))::args), (_152_820)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p _58_2355 -> (match (_58_2355) with
| (pats, g) -> begin
(

let _58_2358 = (tc_args env p)
in (match (_58_2358) with
| (args, g') -> begin
(let _152_823 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats), (_152_823)))
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
(let _152_826 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in ((_152_826), (false)))
end else begin
(let _152_827 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in ((_152_827), (true)))
end
in (match (_58_2370) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _152_828 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (_152_828)))
end
| _58_2374 -> begin
if allow_ghost then begin
(let _152_831 = (let _152_830 = (let _152_829 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in ((_152_829), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_152_830))
in (Prims.raise _152_831))
end else begin
(let _152_834 = (let _152_833 = (let _152_832 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in ((_152_832), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_152_833))
in (Prims.raise _152_834))
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


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _58_2389 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _152_844 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _152_844))
end else begin
()
end
in (

let env = (

let _58_2391 = env
in {FStar_TypeChecker_Env.solver = _58_2391.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2391.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2391.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2391.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2391.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2391.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2391.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2391.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2391.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2391.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2391.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2391.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2391.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_2391.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2391.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2391.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2391.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2391.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2391.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2391.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2391.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2391.FStar_TypeChecker_Env.qname_and_index})
in (

let _58_2407 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _58_2399) -> begin
(let _152_849 = (let _152_848 = (let _152_847 = (FStar_TypeChecker_Env.get_range env)
in (((Prims.strcat "Implicit argument: " msg)), (_152_847)))
in FStar_Syntax_Syntax.Error (_152_848))
in (Prims.raise _152_849))
end
in (match (_58_2407) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end else begin
(let _152_854 = (let _152_853 = (let _152_852 = (let _152_850 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _152_850))
in (let _152_851 = (FStar_TypeChecker_Env.get_range env)
in ((_152_852), (_152_851))))
in FStar_Syntax_Syntax.Error (_152_853))
in (Prims.raise _152_854))
end
end)))))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
FStar_Syntax_Syntax.U_zero
end else begin
(

let _58_2413 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2413) with
| (env, _58_2412) -> begin
(

let env = (

let _58_2414 = env
in {FStar_TypeChecker_Env.solver = _58_2414.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2414.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2414.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2414.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2414.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2414.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2414.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2414.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2414.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2414.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2414.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2414.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2414.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_2414.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2414.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2414.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2414.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _58_2414.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2414.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _58_2414.FStar_TypeChecker_Env.qname_and_index})
in (

let fail = (fun e t -> (let _152_868 = (let _152_867 = (let _152_866 = (let _152_864 = (FStar_Syntax_Print.term_to_string e)
in (let _152_863 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" _152_864 _152_863)))
in (let _152_865 = (FStar_TypeChecker_Env.get_range env)
in ((_152_866), (_152_865))))
in FStar_Syntax_Syntax.Error (_152_867))
in (Prims.raise _152_868)))
in (

let ok = (fun u -> (

let _58_2422 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_872 = (FStar_Syntax_Print.tag_of_term e)
in (let _152_871 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.print2 "<end> universe_of %s is %s\n" _152_872 _152_871)))
end else begin
()
end
in u))
in (

let universe_of_type = (fun e t -> (match ((let _152_877 = (FStar_Syntax_Util.unrefine t)
in _152_877.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(ok u)
end
| _58_2430 -> begin
(fail e t)
end))
in (

let _58_2433 = (FStar_Syntax_Util.head_and_args e)
in (match (_58_2433) with
| (head, args) -> begin
(match ((let _152_878 = (FStar_Syntax_Subst.compress head)
in _152_878.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_58_2435, t) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _152_879 = (FStar_Syntax_Subst.compress t)
in _152_879.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_2441, t) -> begin
(universe_of_type e (FStar_Syntax_Util.comp_result t))
end
| _58_2446 -> begin
(universe_of_type e t)
end))
end
| _58_2448 -> begin
(match ((FStar_ST.read e.FStar_Syntax_Syntax.tk)) with
| (None) | (Some (FStar_Syntax_Syntax.Tm_unknown)) -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoInline)::[]) env e)
in (

let _58_2464 = (tc_term env e)
in (match (_58_2464) with
| (_58_2454, {FStar_Syntax_Syntax.eff_name = _58_2461; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_2458; FStar_Syntax_Syntax.comp = _58_2456}, g) -> begin
(

let _58_2465 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (let _152_881 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (FStar_All.pipe_left (universe_of_type e) _152_881)))
end)))
end
| Some (t) -> begin
(let _152_883 = (let _152_882 = (FStar_Syntax_Syntax.mk t None e.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env _152_882))
in (FStar_All.pipe_left (universe_of_type e) _152_883))
end)
end)
end))))))
end))
end)




