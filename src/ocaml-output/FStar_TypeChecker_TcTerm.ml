
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


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

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
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = _58_181; FStar_Syntax_Syntax.effect_name = _58_179; FStar_Syntax_Syntax.result_typ = _58_177; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, _58_171))::[]; FStar_Syntax_Syntax.flags = _58_168}) -> begin
(

let pat_vars = (let _152_128 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env pats)
in (FStar_Syntax_Free.names _152_128))
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _58_188 -> (match (_58_188) with
| (b, _58_187) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _58_192) -> begin
(let _152_131 = (let _152_130 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _152_130))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _152_131))
end))
end
| _58_196 -> begin
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

let _58_203 = env
in {FStar_TypeChecker_Env.solver = _58_203.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_203.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_203.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_203.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_203.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_203.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_203.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_203.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_203.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_203.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_203.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_203.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _58_203.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_203.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_203.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_203.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_203.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_203.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_203.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_203.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_203.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_203.FStar_TypeChecker_Env.qname_and_index})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _58_215 -> (match (_58_215) with
| (b, _58_214) -> begin
(

let t = (let _152_145 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _152_145))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _58_224 -> begin
(let _152_146 = (FStar_Syntax_Syntax.bv_to_name b)
in (_152_146)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let _58_230 = (FStar_Syntax_Util.head_and_args dec)
in (match (_58_230) with
| (head, _58_229) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _58_234 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let cflags = (FStar_Syntax_Util.comp_flags c)
in (match ((FStar_All.pipe_right cflags (FStar_List.tryFind (fun _58_2 -> (match (_58_2) with
| FStar_Syntax_Syntax.DECREASES (_58_238) -> begin
true
end
| _58_241 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _58_246 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| _58_251 -> begin
(mk_lex_list xs)
end))
end)))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun _58_256 -> (match (_58_256) with
| (l, t) -> begin
(match ((let _152_152 = (FStar_Syntax_Subst.compress t)
in _152_152.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _58_263 -> (match (_58_263) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _152_156 = (let _152_155 = (let _152_154 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_152_154))
in (FStar_Syntax_Syntax.new_bv _152_155 x.FStar_Syntax_Syntax.sort))
in ((_152_156), (imp)))
end else begin
((x), (imp))
end
end))))
in (

let _58_267 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_58_267) with
| (formals, c) -> begin
(

let dec = (decreases_clause formals c)
in (

let precedes = (let _152_160 = (let _152_159 = (FStar_Syntax_Syntax.as_arg dec)
in (let _152_158 = (let _152_157 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_152_157)::[])
in (_152_159)::_152_158))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _152_160 None r))
in (

let _58_274 = (FStar_Util.prefix formals)
in (match (_58_274) with
| (bs, (last, imp)) -> begin
(

let last = (

let _58_275 = last
in (let _152_161 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _58_275.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_275.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_161}))
in (

let refined_formals = (FStar_List.append bs ((((last), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (

let _58_280 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_164 = (FStar_Syntax_Print.lbname_to_string l)
in (let _152_163 = (FStar_Syntax_Print.term_to_string t)
in (let _152_162 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _152_164 _152_163 _152_162))))
end else begin
()
end
in ((l), (t'))))))
end))))
end)))
end
| _58_283 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end)
end)


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let _58_286 = env
in {FStar_TypeChecker_Env.solver = _58_286.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_286.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_286.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_286.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_286.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_286.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_286.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_286.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_286.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_286.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_286.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_286.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_286.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_286.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_286.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_286.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_286.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_286.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_286.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_286.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_286.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_286.FStar_TypeChecker_Env.qname_and_index}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (

let _58_291 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_234 = (let _152_232 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _152_232))
in (let _152_233 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _152_234 _152_233)))
end else begin
()
end
in (

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_58_295) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let _58_336 = (tc_tot_or_gtot_term env e)
in (match (_58_336) with
| (e, c, g) -> begin
(

let g = (

let _58_337 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_337.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_337.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_337.FStar_TypeChecker_Env.implicits})
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let _58_347 = (FStar_Syntax_Util.type_u ())
in (match (_58_347) with
| (t, u) -> begin
(

let _58_351 = (tc_check_tot_or_gtot_term env e t)
in (match (_58_351) with
| (e, c, g) -> begin
(

let _58_358 = (

let _58_355 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_355) with
| (env, _58_354) -> begin
(tc_pats env pats)
end))
in (match (_58_358) with
| (pats, g') -> begin
(

let g' = (

let _58_359 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_359.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_359.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_359.FStar_TypeChecker_Env.implicits})
in (let _152_239 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_pattern (pats))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _152_238 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((_152_239), (c), (_152_238)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _152_240 = (FStar_Syntax_Subst.compress e)
in _152_240.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_58_368, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _58_375; FStar_Syntax_Syntax.lbtyp = _58_373; FStar_Syntax_Syntax.lbeff = _58_371; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _58_386 = (let _152_241 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _152_241 e1))
in (match (_58_386) with
| (e1, c1, g1) -> begin
(

let _58_390 = (tc_term env e2)
in (match (_58_390) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((None), (c2)))
in (

let e = (let _152_246 = (let _152_245 = (let _152_244 = (let _152_243 = (let _152_242 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_TypeChecker_Common.t_unit), (e1)))
in (_152_242)::[])
in ((false), (_152_243)))
in ((_152_244), (e2)))
in FStar_Syntax_Syntax.Tm_let (_152_245))
in (FStar_Syntax_Syntax.mk _152_246 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _152_247 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e), (c), (_152_247))))))
end))
end))
end
| _58_395 -> begin
(

let _58_399 = (tc_term env e)
in (match (_58_399) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (_58_403)) -> begin
(tc_term env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let _58_414 = (tc_term env e)
in (match (_58_414) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (m)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _58_420) -> begin
(

let _58_426 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_426) with
| (env0, _58_425) -> begin
(

let _58_431 = (tc_comp env0 expected_c)
in (match (_58_431) with
| (expected_c, _58_429, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (

let _58_436 = (let _152_248 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term _152_248 e))
in (match (_58_436) with
| (e, c', g') -> begin
(

let _58_440 = (let _152_250 = (let _152_249 = (c'.FStar_Syntax_Syntax.comp ())
in ((e), (_152_249)))
in (check_expected_effect env0 (Some (expected_c)) _152_250))
in (match (_58_440) with
| (e, expected_c, g'') -> begin
(let _152_253 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t_res)), (Some ((FStar_Syntax_Util.comp_effect_name expected_c)))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _152_252 = (let _152_251 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _152_251))
in ((_152_253), ((FStar_Syntax_Util.lcomp_of_comp expected_c)), (_152_252))))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _58_445) -> begin
(

let _58_450 = (FStar_Syntax_Util.type_u ())
in (match (_58_450) with
| (k, u) -> begin
(

let _58_455 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_455) with
| (t, _58_453, f) -> begin
(

let _58_459 = (let _152_254 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _152_254 e))
in (match (_58_459) with
| (e, c, g) -> begin
(

let _58_463 = (let _152_258 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_460 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _152_258 e c f))
in (match (_58_463) with
| (c, f) -> begin
(

let _58_467 = (let _152_259 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t)), (Some (c.FStar_Syntax_Syntax.eff_name))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _152_259 c))
in (match (_58_467) with
| (e, c, f2) -> begin
(let _152_261 = (let _152_260 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _152_260))
in ((e), (c), (_152_261)))
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

let _58_503 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_503) with
| (unary_op, _58_502) -> begin
(

let head = (let _152_262 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (Prims.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) None _152_262))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), (rest)))) None top.FStar_Syntax_Syntax.pos)
in (tc_term env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _58_511; FStar_Syntax_Syntax.pos = _58_509; FStar_Syntax_Syntax.vars = _58_507}, ((e, aqual))::[]) -> begin
(

let _58_521 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end else begin
()
end
in (

let _58_530 = (

let _58_526 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_526) with
| (env0, _58_525) -> begin
(tc_term env0 e)
end))
in (match (_58_530) with
| (e, c, g) -> begin
(

let _58_534 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_534) with
| (reify_op, _58_533) -> begin
(

let u_c = (

let _58_540 = (tc_term env c.FStar_Syntax_Syntax.res_typ)
in (match (_58_540) with
| (_58_536, c, _58_539) -> begin
(match ((let _152_263 = (FStar_Syntax_Subst.compress c.FStar_Syntax_Syntax.res_typ)
in _152_263.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| _58_544 -> begin
(FStar_All.failwith "Unexpected result type of computation")
end)
end))
in (

let repr = (FStar_TypeChecker_Util.reify_comp env c u_c)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e), (aqual)))::[])))) (Some (repr.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let c = (let _152_264 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right _152_264 FStar_Syntax_Util.lcomp_of_comp))
in (

let _58_552 = (comp_check_expected_typ env e c)
in (match (_58_552) with
| (e, c, g') -> begin
(let _152_265 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), (c), (_152_265)))
end))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.tk = _58_558; FStar_Syntax_Syntax.pos = _58_556; FStar_Syntax_Syntax.vars = _58_554}, ((e, aqual))::[]) -> begin
(

let _58_569 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end else begin
()
end
in (

let no_reflect = (fun _58_572 -> (match (()) with
| () -> begin
(let _152_270 = (let _152_269 = (let _152_268 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((_152_268), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_152_269))
in (Prims.raise _152_270))
end))
in (

let _58_576 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_576) with
| (reflect_op, _58_575) -> begin
(match ((FStar_TypeChecker_Env.effect_decl_opt env l)) with
| None -> begin
(no_reflect ())
end
| Some (ed) -> begin
if (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable)))) then begin
(no_reflect ())
end else begin
(

let _58_582 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_582) with
| (env_no_ex, topt) -> begin
(

let _58_610 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (let _152_276 = (let _152_275 = (let _152_274 = (let _152_273 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _152_272 = (let _152_271 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (_152_271)::[])
in (_152_273)::_152_272))
in ((repr), (_152_274)))
in FStar_Syntax_Syntax.Tm_app (_152_275))
in (FStar_Syntax_Syntax.mk _152_276 None top.FStar_Syntax_Syntax.pos))
in (

let _58_590 = (let _152_278 = (let _152_277 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _152_277 Prims.fst))
in (tc_tot_or_gtot_term _152_278 t))
in (match (_58_590) with
| (t, _58_588, g) -> begin
(match ((let _152_279 = (FStar_Syntax_Subst.compress t)
in _152_279.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_58_592, ((res, _58_599))::((wp, _58_595))::[]) -> begin
((t), (res), (wp), (g))
end
| _58_605 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))
in (match (_58_610) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let _58_624 = (

let _58_614 = (tc_tot_or_gtot_term env_no_ex e)
in (match (_58_614) with
| (e, c, g) -> begin
(

let _58_615 = if (let _152_280 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation _152_280)) then begin
(FStar_TypeChecker_Errors.add_errors env (((("Expected Tot, got a GTot computation"), (e.FStar_Syntax_Syntax.pos)))::[]))
end else begin
()
end
in (match ((FStar_TypeChecker_Rel.try_teq env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)) with
| None -> begin
(

let _58_618 = (let _152_285 = (let _152_284 = (let _152_283 = (let _152_282 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _152_281 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" _152_282 _152_281)))
in ((_152_283), (e.FStar_Syntax_Syntax.pos)))
in (_152_284)::[])
in (FStar_TypeChecker_Errors.add_errors env _152_285))
in (let _152_286 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e), (_152_286))))
end
| Some (g') -> begin
(let _152_288 = (let _152_287 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' _152_287))
in ((e), (_152_288)))
end))
end))
in (match (_58_624) with
| (e, g) -> begin
(

let c = (let _152_294 = (let _152_293 = (let _152_292 = (let _152_289 = (env.FStar_TypeChecker_Env.universe_of env res_typ)
in (_152_289)::[])
in (let _152_291 = (let _152_290 = (FStar_Syntax_Syntax.as_arg wp)
in (_152_290)::[])
in {FStar_Syntax_Syntax.comp_univs = _152_292; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = _152_291; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp _152_293))
in (FStar_All.pipe_right _152_294 FStar_Syntax_Util.lcomp_of_comp))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e), (aqual)))::[])))) (Some (res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let _58_630 = (comp_check_expected_typ env e c)
in (match (_58_630) with
| (e, c, g') -> begin
(let _152_295 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e), (c), (_152_295)))
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

let env = (let _152_297 = (let _152_296 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _152_296 Prims.fst))
in (FStar_All.pipe_right _152_297 instantiate_both))
in (

let _58_637 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_299 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _152_298 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _152_299 _152_298)))
end else begin
()
end
in (

let _58_642 = (tc_term (no_inst env) head)
in (match (_58_642) with
| (head, chead, g_head) -> begin
(

let _58_646 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _152_300 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _152_300))
end else begin
(let _152_301 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _152_301))
end
in (match (_58_646) with
| (e, c, g) -> begin
(

let _58_647 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_302 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _152_302))
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

let _58_653 = (comp_check_expected_typ env0 e c)
in (match (_58_653) with
| (e, c, g') -> begin
(

let gimp = (match ((let _152_303 = (FStar_Syntax_Subst.compress head)
in _152_303.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _58_656) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e), (c.FStar_Syntax_Syntax.res_typ), (head.FStar_Syntax_Syntax.pos))
in (

let _58_660 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_660.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_660.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_660.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _58_663 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (

let gres = (let _152_304 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _152_304))
in (

let _58_666 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_306 = (FStar_Syntax_Print.term_to_string e)
in (let _152_305 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" _152_306 _152_305)))
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

let _58_674 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_674) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let _58_679 = (tc_term env1 e1)
in (match (_58_679) with
| (e1, c1, g1) -> begin
(

let _58_690 = (match (topt) with
| Some (t) -> begin
((env), (t))
end
| None -> begin
(

let _58_686 = (FStar_Syntax_Util.type_u ())
in (match (_58_686) with
| (k, _58_685) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _152_307 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in ((_152_307), (res_t))))
end))
end)
in (match (_58_690) with
| (env_branches, res_t) -> begin
(

let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let _58_707 = (

let _58_704 = (FStar_List.fold_right (fun _58_698 _58_701 -> (match (((_58_698), (_58_701))) with
| ((_58_694, f, c, g), (caccum, gaccum)) -> begin
(let _152_310 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (_152_310)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_58_704) with
| (cases, g) -> begin
(let _152_311 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in ((_152_311), (g)))
end))
in (match (_58_707) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (guard_x)), (c_branches)))
in (

let e = (

let mk_match = (fun scrutinee -> (

let branches = (FStar_List.map (fun _58_718 -> (match (_58_718) with
| (f, _58_713, _58_715, _58_717) -> begin
f
end)) t_eqns)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (Some (cres.FStar_Syntax_Syntax.eff_name))))) None e.FStar_Syntax_Syntax.pos))))
in if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c1.FStar_Syntax_Syntax.eff_name) then begin
(mk_match e1)
end else begin
(

let e_match = (let _152_315 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match _152_315))
in (

let lb = (let _152_316 = (FStar_TypeChecker_Env.norm_eff_name env c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = _152_316; FStar_Syntax_Syntax.lbdef = e1})
in (let _152_321 = (let _152_320 = (let _152_319 = (let _152_318 = (let _152_317 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (_152_317)::[])
in (FStar_Syntax_Subst.close _152_318 e_match))
in ((((false), ((lb)::[]))), (_152_319)))
in FStar_Syntax_Syntax.Tm_let (_152_320))
in (FStar_Syntax_Syntax.mk _152_321 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))))
end)
in (

let _58_724 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_324 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _152_323 = (let _152_322 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _152_322))
in (FStar_Util.print2 "(%s) comp type = %s\n" _152_324 _152_323)))
end else begin
()
end
in (let _152_325 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e), (cres), (_152_325))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_736); FStar_Syntax_Syntax.lbunivs = _58_734; FStar_Syntax_Syntax.lbtyp = _58_732; FStar_Syntax_Syntax.lbeff = _58_730; FStar_Syntax_Syntax.lbdef = _58_728})::[]), _58_742) -> begin
(

let _58_745 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_326 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _152_326))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _58_749), _58_752) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_767); FStar_Syntax_Syntax.lbunivs = _58_765; FStar_Syntax_Syntax.lbtyp = _58_763; FStar_Syntax_Syntax.lbeff = _58_761; FStar_Syntax_Syntax.lbdef = _58_759})::_58_757), _58_773) -> begin
(

let _58_776 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_327 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _152_327))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _58_780), _58_783) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let _58_797 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_797) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _152_341 = (let _152_340 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_340))
in FStar_Util.Inr (_152_341))
end
in (

let is_data_ctor = (fun _58_3 -> (match (_58_3) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _58_807 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _152_347 = (let _152_346 = (let _152_345 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _152_344 = (FStar_TypeChecker_Env.get_range env)
in ((_152_345), (_152_344))))
in FStar_Syntax_Syntax.Error (_152_346))
in (Prims.raise _152_347))
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
(let _152_349 = (let _152_348 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" _152_348))
in (FStar_All.failwith _152_349))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (match ((let _152_350 = (FStar_Syntax_Subst.compress t1)
in _152_350.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_818) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _58_821 -> begin
(

let imp = (("uvar in term"), (env), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let _58_823 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_823.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_823.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_823.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _58_838 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(

let _58_831 = (FStar_Syntax_Util.type_u ())
in (match (_58_831) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
end))
end
| Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end)
in (match (_58_838) with
| (t, _58_836, g0) -> begin
(

let _58_843 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (_58_843) with
| (e, _58_841, g1) -> begin
(let _152_353 = (let _152_351 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right _152_351 FStar_Syntax_Util.lcomp_of_comp))
in (let _152_352 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e), (_152_353), (_152_352))))
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

let _58_847 = x
in {FStar_Syntax_Syntax.ppname = _58_847.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_847.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let _58_853 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_853) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _152_355 = (let _152_354 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_354))
in FStar_Util.Inr (_152_355))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _58_860; FStar_Syntax_Syntax.pos = _58_858; FStar_Syntax_Syntax.vars = _58_856}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let _58_870 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_870) with
| (us', t) -> begin
(

let _58_877 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _152_358 = (let _152_357 = (let _152_356 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (_152_356)))
in FStar_Syntax_Syntax.Error (_152_357))
in (Prims.raise _152_358))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _58_876 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (

let fv' = (

let _58_879 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _58_881 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_881.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_881.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_879.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_879.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _152_361 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _152_361 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let _58_889 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_889) with
| (us, t) -> begin
(

let fv' = (

let _58_890 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _58_892 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_892.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_892.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_890.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_890.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _152_362 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _152_362 us))
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

let _58_906 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_906) with
| (bs, c) -> begin
(

let env0 = env
in (

let _58_911 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_911) with
| (env, _58_910) -> begin
(

let _58_916 = (tc_binders env bs)
in (match (_58_916) with
| (bs, env, g, us) -> begin
(

let _58_920 = (tc_comp env c)
in (match (_58_920) with
| (c, uc, f) -> begin
(

let e = (

let _58_921 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _58_921.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_921.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_921.FStar_Syntax_Syntax.vars})
in (

let _58_924 = (check_smt_pat env e bs c)
in (

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _152_363 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _152_363))
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

let _58_940 = (let _152_365 = (let _152_364 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_364)::[])
in (FStar_Syntax_Subst.open_term _152_365 phi))
in (match (_58_940) with
| (x, phi) -> begin
(

let env0 = env
in (

let _58_945 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_945) with
| (env, _58_944) -> begin
(

let _58_950 = (let _152_366 = (FStar_List.hd x)
in (tc_binder env _152_366))
in (match (_58_950) with
| (x, env, f1, u) -> begin
(

let _58_951 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_369 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _152_368 = (FStar_Syntax_Print.term_to_string phi)
in (let _152_367 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _152_369 _152_368 _152_367))))
end else begin
()
end
in (

let _58_956 = (FStar_Syntax_Util.type_u ())
in (match (_58_956) with
| (t_phi, _58_955) -> begin
(

let _58_961 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_58_961) with
| (phi, _58_959, f2) -> begin
(

let e = (

let _58_962 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _58_962.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_962.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_962.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _152_370 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _152_370))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _58_970) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (

let _58_976 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_371 = (FStar_Syntax_Print.term_to_string (

let _58_974 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))); FStar_Syntax_Syntax.tk = _58_974.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _58_974.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_974.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _152_371))
end else begin
()
end
in (

let _58_980 = (FStar_Syntax_Subst.open_term bs body)
in (match (_58_980) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _58_982 -> begin
(let _152_374 = (let _152_373 = (FStar_Syntax_Print.term_to_string top)
in (let _152_372 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" _152_373 _152_372)))
in (FStar_All.failwith _152_374))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_58_987) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_58_990, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_58_995, Some (_58_997)) -> begin
(FStar_All.failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (_58_1002) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_58_1005) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_58_1008) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_58_1012) -> begin
FStar_TypeChecker_Common.t_range
end
| _58_1015 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _58_1021) -> begin
(

let _58_1026 = (FStar_Syntax_Util.type_u ())
in (match (_58_1026) with
| (k, u) -> begin
(

let _58_1031 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_1031) with
| (t, _58_1029, g) -> begin
(let _152_379 = (FStar_Syntax_Syntax.mk_Total' t (Some (u)))
in ((_152_379), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t, _58_1034) -> begin
(

let _58_1039 = (FStar_Syntax_Util.type_u ())
in (match (_58_1039) with
| (k, u) -> begin
(

let _58_1044 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_1044) with
| (t, _58_1042, g) -> begin
(let _152_380 = (FStar_Syntax_Syntax.mk_GTotal' t (Some (u)))
in ((_152_380), (u), (g)))
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

let tc = (let _152_382 = (let _152_381 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_152_381)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _152_382 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let _58_1056 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_58_1056) with
| (tc, _58_1054, f) -> begin
(

let _58_1059 = (FStar_Syntax_Util.head_and_args tc)
in (match (_58_1059) with
| (head, args) -> begin
(

let comp_univs = (match ((let _152_383 = (FStar_Syntax_Subst.compress head)
in _152_383.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (_58_1061, us) -> begin
us
end
| _58_1066 -> begin
[]
end)
in (

let _58_1071 = (FStar_Syntax_Util.head_and_args tc)
in (match (_58_1071) with
| (_58_1069, args) -> begin
(

let _58_1074 = (let _152_385 = (FStar_List.hd args)
in (let _152_384 = (FStar_List.tl args)
in ((_152_385), (_152_384))))
in (match (_58_1074) with
| (res, args) -> begin
(

let _58_1090 = (let _152_387 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _58_4 -> (match (_58_4) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _58_1081 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1081) with
| (env, _58_1080) -> begin
(

let _58_1086 = (tc_tot_or_gtot_term env e)
in (match (_58_1086) with
| (e, _58_1084, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e)), (g))
end))
end))
end
| f -> begin
((f), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right _152_387 FStar_List.unzip))
in (match (_58_1090) with
| (flags, guards) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (Prims.fst res))
in (

let c = (FStar_Syntax_Syntax.mk_Comp (

let _58_1092 = c
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = _58_1092.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _58_1092.FStar_Syntax_Syntax.flags}))
in (

let u_c = (match ((FStar_TypeChecker_Util.effect_repr env c u)) with
| None -> begin
u
end
| Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end)
in (let _152_388 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((c), (u_c), (_152_388))))))
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
(let _152_393 = (aux u)
in FStar_Syntax_Syntax.U_succ (_152_393))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _152_394 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_152_394))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _152_398 = (let _152_397 = (let _152_396 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _152_395 = (FStar_TypeChecker_Env.get_range env)
in ((_152_396), (_152_395))))
in FStar_Syntax_Syntax.Error (_152_397))
in (Prims.raise _152_398))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _152_399 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _152_399 Prims.snd))
end
| _58_1120 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _152_408 = (let _152_407 = (let _152_406 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in ((_152_406), (top.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_152_407))
in (Prims.raise _152_408)))
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
(let _152_425 = (let _152_424 = (let _152_423 = (let _152_421 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _152_421))
in (let _152_422 = (FStar_Syntax_Syntax.range_of_bv hd)
in ((_152_423), (_152_422))))
in FStar_Syntax_Syntax.Error (_152_424))
in (Prims.raise _152_425))
end
| _58_1168 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _58_1186 = (match ((let _152_426 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _152_426.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| _58_1174 -> begin
(

let _58_1175 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_427 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _152_427))
end else begin
()
end
in (

let _58_1181 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_58_1181) with
| (t, _58_1179, g1) -> begin
(

let g2 = (let _152_429 = (FStar_TypeChecker_Env.get_range env)
in (let _152_428 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _152_429 "Type annotation on parameter incompatible with the expected type" _152_428)))
in (

let g = (let _152_430 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _152_430))
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

let subst = (let _152_431 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _152_431))
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

let _58_1233 = (match ((let _152_438 = (FStar_Syntax_Subst.compress body)
in _152_438.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _58_1220) -> begin
(

let _58_1227 = (tc_comp envbody c)
in (match (_58_1227) with
| (c, _58_1225, g') -> begin
(let _152_439 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((Some (c)), (body), (_152_439)))
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

let rec as_function_typ = (fun norm t -> (match ((let _152_444 = (FStar_Syntax_Subst.compress t)
in _152_444.FStar_Syntax_Syntax.n)) with
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
(let _152_455 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in ((env), (bs), (guard), (_152_455)))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (let _152_456 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _152_456))
in (let _152_457 = (FStar_Syntax_Subst.subst_comp subst c)
in ((env), (bs), (guard), (_152_457))))
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
(let _152_459 = (let _152_458 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env), ((FStar_List.append bs bs')), (more), (_152_458), (subst)))
in (handle_more _152_459 c_expected))
end))
end
| _58_1326 -> begin
(let _152_461 = (let _152_460 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _152_460))
in (fail _152_461 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _152_462 = (check_binders env bs bs_expected)
in (handle_more _152_462 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let _58_1332 = envbody
in {FStar_TypeChecker_Env.solver = _58_1332.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1332.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1332.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1332.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1332.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1332.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1332.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1332.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1332.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1332.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1332.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1332.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _58_1332.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1332.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1332.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1332.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1332.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1332.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1332.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1332.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1332.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1332.FStar_TypeChecker_Env.qname_and_index})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _58_1337 _58_1340 -> (match (((_58_1337), (_58_1340))) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _58_1346 = (let _152_472 = (let _152_471 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _152_471 Prims.fst))
in (tc_term _152_472 t))
in (match (_58_1346) with
| (t, _58_1343, _58_1345) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l (([]), (t)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _152_473 = (FStar_Syntax_Syntax.mk_binder (

let _58_1350 = x
in {FStar_Syntax_Syntax.ppname = _58_1350.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1350.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_152_473)::letrec_binders)
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
(let _152_474 = (unfold_whnf env t)
in (as_function_typ true _152_474))
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
(let _152_475 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _152_475 (if env.FStar_TypeChecker_Env.top_level then begin
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
in {FStar_TypeChecker_Env.solver = _58_1393.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1393.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1393.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1393.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1393.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1393.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1393.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1393.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1393.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1393.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1393.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1393.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1393.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_1393.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1393.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1393.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1393.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1393.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1393.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1393.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1393.FStar_TypeChecker_Env.qname_and_index}) body)
in (match (_58_1398) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _58_1400 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _152_478 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _152_477 = (let _152_476 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _152_476))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _152_478 _152_477)))
end else begin
()
end
in (

let _58_1407 = (let _152_480 = (let _152_479 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body), (_152_479)))
in (check_expected_effect (

let _58_1402 = envbody
in {FStar_TypeChecker_Env.solver = _58_1402.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1402.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1402.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1402.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1402.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1402.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1402.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1402.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1402.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1402.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1402.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1402.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1402.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1402.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1402.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1402.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1402.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1402.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1402.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1402.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1402.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1402.FStar_TypeChecker_Env.qname_and_index}) c_opt _152_480))
in (match (_58_1407) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(let _152_481 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _152_481))
end else begin
(

let guard = (let _152_482 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) _152_482))
in guard)
end
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _152_485 = (let _152_484 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _152_483 -> FStar_Util.Inl (_152_483)))
in Some (_152_484))
in (FStar_Syntax_Util.abs bs body _152_485))
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
(let _152_486 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in ((e), (_152_486)))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_58_1425) with
| (e, guard') -> begin
(let _152_487 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((e), (t), (_152_487)))
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
(let _152_496 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _152_495 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _152_496 _152_495)))
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

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun _58_5 -> (match (_58_5) with
| (_58_1465, _58_1467, None) -> begin
false
end
| (_58_1471, _58_1473, Some (c)) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _152_512 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _152_512 cres))
end else begin
(

let _58_1478 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_515 = (FStar_Syntax_Print.term_to_string head)
in (let _152_514 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _152_513 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _152_515 _152_514 _152_513))))
end else begin
()
end
in cres)
end
in ((cres), (g))))))
end
| _58_1482 -> begin
(

let g = (let _152_516 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right _152_516 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _152_521 = (let _152_520 = (let _152_519 = (let _152_518 = (let _152_517 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _152_517))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _152_518))
in (FStar_Syntax_Syntax.mk_Total _152_519))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_520))
in ((_152_521), (g))))
end)
in (match (_58_1486) with
| (cres, guard) -> begin
(

let _58_1487 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_522 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _152_522))
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

let e = (FStar_TypeChecker_Util.maybe_monadic env e c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
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
(FStar_TypeChecker_Util.maybe_monadic env app comp.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.res_typ)
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

let arg = (let _152_534 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (_152_534)))
in (let _152_536 = (let _152_535 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst), ((((arg), (None), (None)))::outargs), ((arg)::arg_rets), (_152_535), (fvs)))
in (tc_args head_info _152_536 rest args))))
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
(let _152_537 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _152_537))
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
in {FStar_TypeChecker_Env.solver = _58_1592.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1592.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1592.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1592.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1592.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1592.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1592.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1592.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1592.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1592.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1592.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1592.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1592.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1592.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1592.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _58_1592.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1592.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1592.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1592.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1592.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1592.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1592.FStar_TypeChecker_Env.qname_and_index})
in (

let _58_1595 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_540 = (FStar_Syntax_Print.tag_of_term e)
in (let _152_539 = (FStar_Syntax_Print.term_to_string e)
in (let _152_538 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _152_540 _152_539 _152_538))))
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

let subst = (let _152_541 = (FStar_List.hd bs)
in (maybe_extend_subst subst _152_541 e))
in (tc_args head_info ((subst), ((((arg), (None), (None)))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(

let subst = (let _152_542 = (FStar_List.hd bs)
in (maybe_extend_subst subst _152_542 e))
in (tc_args head_info ((subst), ((((arg), (Some (x)), (Some (c))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (let _152_543 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _152_543)) then begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _152_544 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _152_544))
in (tc_args head_info ((subst), ((((arg), (Some (newx)), (Some (c))))::outargs), ((arg')::arg_rets), (g), (fvs)) rest rest')))
end else begin
(let _152_548 = (let _152_547 = (let _152_546 = (let _152_545 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _152_545))
in (_152_546)::arg_rets)
in ((subst), ((((arg), (Some (x)), (Some (c))))::outargs), (_152_547), (g), ((x)::fvs)))
in (tc_args head_info _152_548 rest rest'))
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

let tres = (let _152_553 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _152_553 FStar_Syntax_Util.unrefine))
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
(let _152_554 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _152_554))
end else begin
()
end
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args)))
end))
end
| _58_1636 when (not (norm)) -> begin
(let _152_555 = (unfold_whnf env tres)
in (aux true _152_555))
end
| _58_1638 -> begin
(let _152_561 = (let _152_560 = (let _152_559 = (let _152_557 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (let _152_556 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _152_557 _152_556)))
in (let _152_558 = (FStar_Syntax_Syntax.argpos arg)
in ((_152_559), (_152_558))))
in FStar_Syntax_Syntax.Error (_152_560))
in (Prims.raise _152_561))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (match ((let _152_566 = (FStar_Syntax_Util.unrefine tf)
in _152_566.FStar_Syntax_Syntax.n)) with
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
(let _152_571 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e), (imp)))::args), ((((e.FStar_Syntax_Syntax.pos), (c)))::comps), (_152_571)))
end))
end))
end))
in (

let _58_1679 = (tc_args env args)
in (match (_58_1679) with
| (args, comps, g_args) -> begin
(

let bs = (let _152_573 = (FStar_All.pipe_right comps (FStar_List.map (fun _58_1683 -> (match (_58_1683) with
| (_58_1681, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks _152_573))
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
(match ((let _152_588 = (FStar_Syntax_Subst.compress t)
in _152_588.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_58_1695) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _58_1700 -> begin
ml_or_tot
end)
end)
in (

let cres = (let _152_593 = (let _152_592 = (let _152_591 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _152_591 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _152_592))
in (ml_or_tot _152_593 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (

let _58_1704 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _152_596 = (FStar_Syntax_Print.term_to_string head)
in (let _152_595 = (FStar_Syntax_Print.term_to_string tf)
in (let _152_594 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _152_596 _152_595 _152_594))))
end else begin
()
end
in (

let _58_1706 = (let _152_597 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _152_597))
in (

let comp = (let _152_600 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _58_1710 out -> (match (_58_1710) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c ((None), (out)))
end)) ((((head.FStar_Syntax_Syntax.pos), (chead)))::comps) _152_600))
in (let _152_602 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _152_601 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((_152_602), (comp), (_152_601))))))))))))
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
(let _152_603 = (unfold_whnf env tf)
in (check_function_app true _152_603))
end else begin
(let _152_606 = (let _152_605 = (let _152_604 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in ((_152_604), (head.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_152_605))
in (Prims.raise _152_606))
end
end))
in (let _152_608 = (let _152_607 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _152_607))
in (check_function_app false _152_608))))))))))
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

let g = (let _152_618 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _152_618 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _152_622 = (let _152_620 = (let _152_619 = (FStar_Syntax_Syntax.as_arg e)
in (_152_619)::[])
in (FStar_List.append seen _152_620))
in (let _152_621 = (FStar_TypeChecker_Rel.conj_guard guard g)
in ((_152_622), (_152_621), (ghost)))))))
end)))
end)) (([]), (g_head), (false)) args bs)
in (match (_58_1758) with
| (args, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = if ghost then begin
(let _152_623 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _152_623 FStar_Syntax_Util.lcomp_of_comp))
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
(let _152_635 = (FStar_Syntax_Print.pat_to_string p0)
in (let _152_634 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _152_635 _152_634)))
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
in {FStar_TypeChecker_Env.solver = _58_1793.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1793.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1793.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1793.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1793.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1793.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1793.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1793.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _58_1793.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1793.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1793.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1793.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1793.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1793.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1793.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1793.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1793.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1793.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1793.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1793.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1793.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1793.FStar_TypeChecker_Env.qname_and_index})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _58_1832 = (let _152_658 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _58_1798 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_638 = (FStar_Syntax_Print.term_to_string e)
in (let _152_637 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _152_638 _152_637)))
end else begin
()
end
in (

let _58_1803 = (tc_term env1 e)
in (match (_58_1803) with
| (e, lc, g) -> begin
(

let _58_1804 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_640 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _152_639 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _152_640 _152_639)))
end else begin
()
end
in (

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let _58_1810 = (let _152_641 = (FStar_TypeChecker_Rel.discharge_guard env (

let _58_1808 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_1808.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_1808.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_1808.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _152_641 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _152_646 = (let _152_645 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _152_645 (FStar_List.map (fun _58_1818 -> (match (_58_1818) with
| (u, _58_1817) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _152_646 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _58_1826 = if (let _152_647 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _152_647)) then begin
(

let unresolved = (let _152_648 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _152_648 FStar_Util.set_elements))
in (let _152_656 = (let _152_655 = (let _152_654 = (let _152_653 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _152_652 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _152_651 = (let _152_650 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _58_1825 -> (match (_58_1825) with
| (u, _58_1824) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _152_650 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _152_653 _152_652 _152_651))))
in ((_152_654), (p.FStar_Syntax_Syntax.p)))
in FStar_Syntax_Syntax.Error (_152_655))
in (Prims.raise _152_656)))
end else begin
()
end
in (

let _58_1828 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_657 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _152_657))
end else begin
()
end
in ((e), (e'))))))))))))
end))))))
in (FStar_All.pipe_right _152_658 FStar_List.unzip))
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

let _58_1839 = (let _152_659 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _152_659 FStar_TypeChecker_Env.clear_expected_typ))
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

let _58_1852 = (let _152_660 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _152_660 e))
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
(let _152_662 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _152_661 -> Some (_152_661)) _152_662))
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
(let _152_666 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _152_665 -> Some (_152_665)) _152_666))
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
in (let _152_669 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _152_668 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((_152_669), (_152_668))))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (let _152_670 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_152_670))
in (let _152_673 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _152_672 = (let _152_671 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _152_671 g_when))
in ((_152_673), (_152_672))))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _152_674 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in ((_152_674), (g_when)))))
end)
in (match (_58_1912) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _152_676 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _152_675 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in ((_152_676), (_152_675), (g_branch)))))
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

let discriminate = (fun scrutinee_tm f -> if ((let _152_686 = (let _152_685 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _152_685))
in (FStar_List.length _152_686)) > (Prims.parse_int "1")) then begin
(

let disc = (let _152_687 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _152_687 FStar_Syntax_Syntax.Delta_equational None))
in (

let disc = (let _152_689 = (let _152_688 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_152_688)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _152_689 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _152_690 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_152_690)::[])))
end else begin
[]
end)
in (

let fail = (fun _58_1927 -> (match (()) with
| () -> begin
(let _152_696 = (let _152_695 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _152_694 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _152_693 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _152_695 _152_694 _152_693))))
in (FStar_All.failwith _152_696))
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

let pat_exp = (let _152_699 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _152_699 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_58_1963) -> begin
(let _152_704 = (let _152_703 = (let _152_702 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _152_701 = (let _152_700 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_152_700)::[])
in (_152_702)::_152_701))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _152_703 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_152_704)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _152_705 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _152_705))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(

let sub_term_guards = (let _152_712 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _58_1981 -> (match (_58_1981) with
| (ei, _58_1980) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _58_1985 -> begin
(

let sub_term = (let _152_711 = (let _152_708 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _152_708 FStar_Syntax_Syntax.Delta_equational None))
in (let _152_710 = (let _152_709 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_152_709)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _152_711 _152_710 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _152_712 FStar_List.flatten))
in (let _152_713 = (discriminate scrutinee_tm f)
in (FStar_List.append _152_713 sub_term_guards)))
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

let t = (let _152_718 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _152_718))
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

let branch_guard = (let _152_719 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _152_719 FStar_Syntax_Util.mk_disj_l))
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
(let _152_720 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _152_720))
end else begin
()
end
in (let _152_721 = (FStar_Syntax_Subst.close_branch ((pattern), (when_clause), (branch_exp)))
in ((_152_721), (branch_guard), (c), (guard))))))
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

let g1 = (let _152_724 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _152_724 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _58_2035 = (let _152_728 = (let _152_727 = (let _152_726 = (let _152_725 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (_152_725)))
in (_152_726)::[])
in (FStar_TypeChecker_Util.generalize env _152_727))
in (FStar_List.hd _152_728))
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
(let _152_729 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _152_729 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _152_730 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) None e2.FStar_Syntax_Syntax.pos)
in ((_152_730), (c1))))
end
end))
end else begin
(

let _58_2046 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _152_731 = (c1.FStar_Syntax_Syntax.comp ())
in ((e2), (_152_731))))
end
in (match (_58_2050) with
| (e2, c1) -> begin
(

let cres = (let _152_732 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_732))
in (

let _58_2052 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _152_733 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((_152_733), (cres), (FStar_TypeChecker_Rel.trivial_guard))))))
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
in {FStar_TypeChecker_Env.solver = _58_2067.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2067.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2067.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2067.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2067.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2067.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2067.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2067.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2067.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2067.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2067.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2067.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2067.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_2067.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2067.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2067.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2067.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2067.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2067.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2067.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2067.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2067.FStar_TypeChecker_Env.qname_and_index})
in (

let _58_2076 = (let _152_737 = (let _152_736 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _152_736 Prims.fst))
in (check_let_bound_def false _152_737 lb))
in (match (_58_2076) with
| (e1, _58_2072, c1, g1, annotated) -> begin
(

let x = (

let _58_2077 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_2077.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2077.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let _58_2083 = (let _152_739 = (let _152_738 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_738)::[])
in (FStar_Syntax_Subst.open_term _152_739 e2))
in (match (_58_2083) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _58_2089 = (let _152_740 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _152_740 e2))
in (match (_58_2089) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (x)), (c2)))
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e2 = (FStar_TypeChecker_Util.maybe_lift env e2 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e = (let _152_743 = (let _152_742 = (let _152_741 = (FStar_Syntax_Subst.close xb e2)
in ((((false), ((lb)::[]))), (_152_741)))
in FStar_Syntax_Syntax.Tm_let (_152_742))
in (FStar_Syntax_Syntax.mk _152_743 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (let _152_746 = (let _152_745 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _152_745 e1))
in (FStar_All.pipe_left (fun _152_744 -> FStar_TypeChecker_Common.NonTrivial (_152_744)) _152_746))
in (

let g2 = (let _152_748 = (let _152_747 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _152_747 g2))
in (FStar_TypeChecker_Rel.close_guard xb _152_748))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if (let _152_749 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome _152_749)) then begin
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

let g_lbs = (let _152_752 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _152_752 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _152_755 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _152_755 (fun _152_754 -> Some (_152_754))))
in (

let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(

let ecs = (let _152_759 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _152_758 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (_152_758))))))
in (FStar_TypeChecker_Util.generalize env _152_759))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _58_2133 -> (match (_58_2133) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _152_761 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_761))
in (

let _58_2136 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _58_2140 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_2140) with
| (lbs, e2) -> begin
(let _152_763 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _152_762 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in ((_152_763), (cres), (_152_762))))
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

let termination_check_enabled = (fun t -> (

let _58_2209 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (_58_2209) with
| (_58_2207, c) -> begin
(

let quals = (FStar_TypeChecker_Env.lookup_effect_quals env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
end)))
in (

let _58_2239 = (FStar_List.fold_left (fun _58_2213 lb -> (match (_58_2213) with
| (lbs, env) -> begin
(

let _58_2218 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_58_2218) with
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

let _58_2227 = (let _152_777 = (let _152_776 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _152_776))
in (tc_check_tot_or_gtot_term (

let _58_2221 = env0
in {FStar_TypeChecker_Env.solver = _58_2221.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2221.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2221.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2221.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2221.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2221.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2221.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2221.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2221.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2221.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2221.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2221.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2221.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2221.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _58_2221.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2221.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2221.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2221.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2221.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2221.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2221.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2221.FStar_TypeChecker_Env.qname_and_index}) t _152_777))
in (match (_58_2227) with
| (t, _58_2225, g) -> begin
(

let _58_2228 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (

let env = if ((termination_check_enabled t) && (FStar_TypeChecker_Env.should_verify env)) then begin
(

let _58_2231 = env
in {FStar_TypeChecker_Env.solver = _58_2231.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2231.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2231.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2231.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2231.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2231.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2231.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2231.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2231.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2231.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2231.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2231.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t)))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2231.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_2231.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2231.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2231.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2231.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2231.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2231.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2231.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2231.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2231.FStar_TypeChecker_Env.qname_and_index})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (t)))
end
in (

let lb = (

let _58_2234 = lb
in {FStar_Syntax_Syntax.lbname = _58_2234.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _58_2234.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb)::lbs), (env)))))))
end))
end)) (([]), (env)) lbs)
in (match (_58_2239) with
| (lbs, env) -> begin
(((FStar_List.rev lbs)), (env))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _58_2252 = (let _152_782 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _58_2246 = (let _152_781 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _152_781 lb.FStar_Syntax_Syntax.lbdef))
in (match (_58_2246) with
| (e, c, g) -> begin
(

let _58_2247 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in ((lb), (g))))
end)))))
in (FStar_All.pipe_right _152_782 FStar_List.unzip))
in (match (_58_2252) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _58_2260 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2260) with
| (env1, _58_2259) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _58_2266 = (check_lbtyp top_level env lb)
in (match (_58_2266) with
| (topt, wf_annot, univ_vars, env1) -> begin
(

let _58_2267 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _58_2274 = (tc_maybe_toplevel_term (

let _58_2269 = env1
in {FStar_TypeChecker_Env.solver = _58_2269.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2269.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2269.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2269.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2269.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2269.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2269.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2269.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2269.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2269.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2269.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2269.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2269.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _58_2269.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2269.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2269.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2269.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2269.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2269.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2269.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2269.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2269.FStar_TypeChecker_Env.qname_and_index}) e1)
in (match (_58_2274) with
| (e1, c1, g1) -> begin
(

let _58_2278 = (let _152_789 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_2275 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _152_789 e1 c1 wf_annot))
in (match (_58_2278) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _58_2280 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_790 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _152_790))
end else begin
()
end
in (let _152_791 = (FStar_Option.isSome topt)
in ((e1), (univ_vars), (c1), (g1), (_152_791)))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _58_2287 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in ((None), (FStar_TypeChecker_Rel.trivial_guard), ([]), (env)))
end
| _58_2290 -> begin
(

let _58_2293 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_58_2293) with
| (univ_vars, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _152_795 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars), (_152_795)))
end else begin
(

let _58_2298 = (FStar_Syntax_Util.type_u ())
in (match (_58_2298) with
| (k, _58_2297) -> begin
(

let _58_2303 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_58_2303) with
| (t, _58_2301, g) -> begin
(

let _58_2304 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _152_798 = (let _152_796 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _152_796))
in (let _152_797 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _152_798 _152_797)))
end else begin
()
end
in (

let t = (norm env1 t)
in (let _152_799 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (g), (univ_vars), (_152_799)))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _58_2310 -> (match (_58_2310) with
| (x, imp) -> begin
(

let _58_2313 = (FStar_Syntax_Util.type_u ())
in (match (_58_2313) with
| (tu, u) -> begin
(

let _58_2314 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_804 = (FStar_Syntax_Print.bv_to_string x)
in (let _152_803 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _152_802 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binders %s:%s at type %s\n" _152_804 _152_803 _152_802))))
end else begin
()
end
in (

let _58_2320 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_58_2320) with
| (t, _58_2318, g) -> begin
(

let x = (((

let _58_2321 = x
in {FStar_Syntax_Syntax.ppname = _58_2321.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2321.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in (

let _58_2324 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_806 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _152_805 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _152_806 _152_805)))
end else begin
()
end
in (let _152_807 = (push_binding env x)
in ((x), (_152_807), (g), (u)))))
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

let _58_2339 = (tc_binder env b)
in (match (_58_2339) with
| (b, env', g, u) -> begin
(

let _58_2344 = (aux env' bs)
in (match (_58_2344) with
| (bs, env', g', us) -> begin
(let _152_815 = (let _152_814 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _152_814))
in (((b)::bs), (env'), (_152_815), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun _58_2352 _58_2355 -> (match (((_58_2352), (_58_2355))) with
| ((t, imp), (args, g)) -> begin
(

let _58_2360 = (tc_term env t)
in (match (_58_2360) with
| (t, _58_2358, g') -> begin
(let _152_824 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t), (imp)))::args), (_152_824)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p _58_2364 -> (match (_58_2364) with
| (pats, g) -> begin
(

let _58_2367 = (tc_args env p)
in (match (_58_2367) with
| (args, g') -> begin
(let _152_827 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats), (_152_827)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _58_2373 = (tc_maybe_toplevel_term env e)
in (match (_58_2373) with
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

let _58_2379 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _152_830 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in ((_152_830), (false)))
end else begin
(let _152_831 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in ((_152_831), (true)))
end
in (match (_58_2379) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _152_832 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (_152_832)))
end
| _58_2383 -> begin
if allow_ghost then begin
(let _152_835 = (let _152_834 = (let _152_833 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in ((_152_833), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_152_834))
in (Prims.raise _152_835))
end else begin
(let _152_838 = (let _152_837 = (let _152_836 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in ((_152_836), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_152_837))
in (Prims.raise _152_838))
end
end)
end)))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let _58_2393 = (tc_tot_or_gtot_term env t)
in (match (_58_2393) with
| (t, c, g) -> begin
(

let _58_2394 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in ((t), (c)))
end)))


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _58_2398 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _152_848 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _152_848))
end else begin
()
end
in (

let env = (

let _58_2400 = env
in {FStar_TypeChecker_Env.solver = _58_2400.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2400.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2400.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2400.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2400.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2400.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2400.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2400.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2400.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2400.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2400.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2400.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2400.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_2400.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2400.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2400.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2400.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2400.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2400.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2400.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2400.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2400.FStar_TypeChecker_Env.qname_and_index})
in (

let _58_2416 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _58_2408) -> begin
(let _152_853 = (let _152_852 = (let _152_851 = (FStar_TypeChecker_Env.get_range env)
in (((Prims.strcat "Implicit argument: " msg)), (_152_851)))
in FStar_Syntax_Syntax.Error (_152_852))
in (Prims.raise _152_853))
end
in (match (_58_2416) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end else begin
(let _152_858 = (let _152_857 = (let _152_856 = (let _152_854 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _152_854))
in (let _152_855 = (FStar_TypeChecker_Env.get_range env)
in ((_152_856), (_152_855))))
in FStar_Syntax_Syntax.Error (_152_857))
in (Prims.raise _152_858))
end
end)))))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
FStar_Syntax_Syntax.U_zero
end else begin
(

let _58_2422 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2422) with
| (env, _58_2421) -> begin
(

let env = (

let _58_2423 = env
in {FStar_TypeChecker_Env.solver = _58_2423.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2423.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2423.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2423.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2423.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2423.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2423.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2423.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2423.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2423.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2423.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2423.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2423.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_2423.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2423.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2423.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2423.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _58_2423.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2423.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _58_2423.FStar_TypeChecker_Env.qname_and_index})
in (

let fail = (fun e t -> (let _152_872 = (let _152_871 = (let _152_870 = (let _152_868 = (FStar_Syntax_Print.term_to_string e)
in (let _152_867 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" _152_868 _152_867)))
in (let _152_869 = (FStar_TypeChecker_Env.get_range env)
in ((_152_870), (_152_869))))
in FStar_Syntax_Syntax.Error (_152_871))
in (Prims.raise _152_872)))
in (

let ok = (fun u -> (

let _58_2431 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_876 = (FStar_Syntax_Print.tag_of_term e)
in (let _152_875 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.print2 "<end> universe_of %s is %s\n" _152_876 _152_875)))
end else begin
()
end
in u))
in (

let universe_of_type = (fun e t -> (match ((let _152_881 = (FStar_Syntax_Util.unrefine t)
in _152_881.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(ok u)
end
| _58_2439 -> begin
(fail e t)
end))
in (

let _58_2442 = (FStar_Syntax_Util.head_and_args e)
in (match (_58_2442) with
| (head, args) -> begin
(match ((let _152_882 = (FStar_Syntax_Subst.compress head)
in _152_882.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_58_2444, t) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _152_883 = (FStar_Syntax_Subst.compress t)
in _152_883.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_2450, t) -> begin
(universe_of_type e (FStar_Syntax_Util.comp_result t))
end
| _58_2455 -> begin
(universe_of_type e t)
end))
end
| _58_2457 -> begin
(

let t = (match ((FStar_ST.read e.FStar_Syntax_Syntax.tk)) with
| (None) | (Some (FStar_Syntax_Syntax.Tm_unknown)) -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoInline)::[]) env e)
in (

let _58_2473 = (tc_term env e)
in (match (_58_2473) with
| (_58_2463, {FStar_Syntax_Syntax.eff_name = _58_2470; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_2467; FStar_Syntax_Syntax.comp = _58_2465}, g) -> begin
(

let _58_2474 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in t)
end)))
end
| Some (t) -> begin
(FStar_Syntax_Syntax.mk t None e.FStar_Syntax_Syntax.pos)
end)
in (let _152_885 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (FStar_All.pipe_left (universe_of_type e) _152_885)))
end)
end))))))
end))
end)




