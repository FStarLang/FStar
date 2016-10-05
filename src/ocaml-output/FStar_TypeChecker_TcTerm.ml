
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


let memo_tk : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun e t -> (

let _58_69 = (FStar_ST.op_Colon_Equals e.FStar_Syntax_Syntax.tk (Some (t.FStar_Syntax_Syntax.n)))
in e))


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let should_return = (fun t -> (match ((let _152_79 = (FStar_Syntax_Subst.compress t)
in _152_79.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_78, c) -> begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(

let t = (FStar_All.pipe_left FStar_Syntax_Util.unrefine (FStar_Syntax_Util.comp_result c))
in (match ((let _152_80 = (FStar_Syntax_Subst.compress t)
in _152_80.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (_58_86) -> begin
false
end
| _58_89 -> begin
true
end))
end else begin
false
end
end
| _58_91 -> begin
true
end))
in (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _152_81 = if ((not ((should_return t))) || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _152_81))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _58_119 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(let _152_82 = (memo_tk e t)
in ((_152_82), (lc), (guard)))
end
| Some (t') -> begin
(

let _58_101 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_84 = (FStar_Syntax_Print.term_to_string t)
in (let _152_83 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _152_84 _152_83)))
end else begin
()
end
in (

let _58_105 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_58_105) with
| (e, lc) -> begin
(

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _58_109 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_58_109) with
| (e, g) -> begin
(

let _58_110 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_86 = (FStar_Syntax_Print.term_to_string t)
in (let _152_85 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _152_86 _152_85)))
end else begin
()
end
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let _58_115 = (let _152_92 = (FStar_All.pipe_left (fun _152_91 -> Some (_152_91)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _152_92 env e lc g))
in (match (_58_115) with
| (lc, g) -> begin
(let _152_93 = (memo_tk e t')
in ((_152_93), ((set_lcomp_result lc t')), (g)))
end))))
end)))
end)))
end)
in (match (_58_119) with
| (e, lc, g) -> begin
(

let _58_120 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_94 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _152_94))
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

let _58_130 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_58_130) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _58_135 -> (match (_58_135) with
| (e, c) -> begin
(

let expected_c_opt = (match (copt) with
| Some (_58_137) -> begin
copt
end
| None -> begin
if ((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Syntax_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) then begin
(let _152_107 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (_152_107))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
if (FStar_Syntax_Util.is_pure_comp c) then begin
(let _152_108 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (_152_108))
end else begin
if (FStar_Syntax_Util.is_pure_or_ghost_comp c) then begin
(let _152_109 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (_152_109))
end else begin
None
end
end
end
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _152_110 = (norm_c env c)
in ((e), (_152_110), (FStar_TypeChecker_Rel.trivial_guard)))
end
| Some (expected_c) -> begin
(

let _58_144 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_113 = (FStar_Syntax_Print.term_to_string e)
in (let _152_112 = (FStar_Syntax_Print.comp_to_string c)
in (let _152_111 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _152_113 _152_112 _152_111))))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _58_147 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_116 = (FStar_Syntax_Print.term_to_string e)
in (let _152_115 = (FStar_Syntax_Print.comp_to_string c)
in (let _152_114 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _152_116 _152_115 _152_114))))
end else begin
()
end
in (

let _58_153 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_58_153) with
| (e, _58_151, g) -> begin
(

let g = (let _152_117 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _152_117 "could not prove post-condition" g))
in (

let _58_155 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_119 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _152_118 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _152_119 _152_118)))
end else begin
()
end
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e (FStar_Syntax_Util.comp_effect_name c) (FStar_Syntax_Util.comp_effect_name expected_c))
in ((e), (expected_c), (g)))))
end)))))
end))
end))


let no_logical_guard = (fun env _58_162 -> (match (_58_162) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
((te), (kt), (f))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _152_125 = (let _152_124 = (let _152_123 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _152_122 = (FStar_TypeChecker_Env.get_range env)
in ((_152_123), (_152_122))))
in FStar_Syntax_Syntax.Error (_152_124))
in (Prims.raise _152_125))
end)
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _152_128 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _152_128))
end))


let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = _58_188; FStar_Syntax_Syntax.effect_name = _58_186; FStar_Syntax_Syntax.result_typ = _58_184; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, _58_178))::[]; FStar_Syntax_Syntax.flags = _58_175}) -> begin
(

let pat_vars = (let _152_133 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env pats)
in (FStar_Syntax_Free.names _152_133))
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _58_195 -> (match (_58_195) with
| (b, _58_194) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _58_199) -> begin
(let _152_136 = (let _152_135 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" _152_135))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _152_136))
end))
end
| _58_203 -> begin
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

let _58_210 = env
in {FStar_TypeChecker_Env.solver = _58_210.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_210.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_210.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_210.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_210.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_210.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_210.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_210.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_210.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_210.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_210.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_210.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _58_210.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_210.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_210.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_210.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_210.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_210.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_210.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_210.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_210.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_210.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_210.FStar_TypeChecker_Env.qname_and_index})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _58_222 -> (match (_58_222) with
| (b, _58_221) -> begin
(

let t = (let _152_150 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _152_150))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _58_231 -> begin
(let _152_151 = (FStar_Syntax_Syntax.bv_to_name b)
in (_152_151)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let _58_237 = (FStar_Syntax_Util.head_and_args dec)
in (match (_58_237) with
| (head, _58_236) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _58_241 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let cflags = (FStar_Syntax_Util.comp_flags c)
in (match ((FStar_All.pipe_right cflags (FStar_List.tryFind (fun _58_2 -> (match (_58_2) with
| FStar_Syntax_Syntax.DECREASES (_58_245) -> begin
true
end
| _58_248 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _58_253 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| _58_258 -> begin
(mk_lex_list xs)
end))
end)))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun _58_263 -> (match (_58_263) with
| (l, t) -> begin
(match ((let _152_157 = (FStar_Syntax_Subst.compress t)
in _152_157.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _58_270 -> (match (_58_270) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _152_161 = (let _152_160 = (let _152_159 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_152_159))
in (FStar_Syntax_Syntax.new_bv _152_160 x.FStar_Syntax_Syntax.sort))
in ((_152_161), (imp)))
end else begin
((x), (imp))
end
end))))
in (

let _58_274 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_58_274) with
| (formals, c) -> begin
(

let dec = (decreases_clause formals c)
in (

let precedes = (let _152_165 = (let _152_164 = (FStar_Syntax_Syntax.as_arg dec)
in (let _152_163 = (let _152_162 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_152_162)::[])
in (_152_164)::_152_163))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _152_165 None r))
in (

let _58_281 = (FStar_Util.prefix formals)
in (match (_58_281) with
| (bs, (last, imp)) -> begin
(

let last = (

let _58_282 = last
in (let _152_166 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _58_282.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_282.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_166}))
in (

let refined_formals = (FStar_List.append bs ((((last), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (

let _58_287 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_169 = (FStar_Syntax_Print.lbname_to_string l)
in (let _152_168 = (FStar_Syntax_Print.term_to_string t)
in (let _152_167 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _152_169 _152_168 _152_167))))
end else begin
()
end
in ((l), (t'))))))
end))))
end)))
end
| _58_290 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Annotated type of \'let rec\' must be an arrow"), (t.FStar_Syntax_Syntax.pos)))))
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end)
end)


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let _58_293 = env
in {FStar_TypeChecker_Env.solver = _58_293.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_293.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_293.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_293.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_293.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_293.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_293.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_293.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_293.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_293.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_293.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_293.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_293.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_293.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_293.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_293.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_293.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_293.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_293.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_293.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_293.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_293.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_293.FStar_TypeChecker_Env.qname_and_index}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (

let _58_298 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_239 = (let _152_237 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _152_237))
in (let _152_238 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _152_239 _152_238)))
end else begin
()
end
in (

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_58_302) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let _58_343 = (tc_tot_or_gtot_term env e)
in (match (_58_343) with
| (e, c, g) -> begin
(

let g = (

let _58_344 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_344.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_344.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_344.FStar_TypeChecker_Env.implicits})
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let _58_354 = (FStar_Syntax_Util.type_u ())
in (match (_58_354) with
| (t, u) -> begin
(

let _58_358 = (tc_check_tot_or_gtot_term env e t)
in (match (_58_358) with
| (e, c, g) -> begin
(

let _58_365 = (

let _58_362 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_362) with
| (env, _58_361) -> begin
(tc_pats env pats)
end))
in (match (_58_365) with
| (pats, g') -> begin
(

let g' = (

let _58_366 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_366.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_366.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_366.FStar_TypeChecker_Env.implicits})
in (let _152_244 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_pattern (pats))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _152_243 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((_152_244), (c), (_152_243)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _152_245 = (FStar_Syntax_Subst.compress e)
in _152_245.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_58_375, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _58_382; FStar_Syntax_Syntax.lbtyp = _58_380; FStar_Syntax_Syntax.lbeff = _58_378; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _58_393 = (let _152_246 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _152_246 e1))
in (match (_58_393) with
| (e1, c1, g1) -> begin
(

let _58_397 = (tc_term env e2)
in (match (_58_397) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((None), (c2)))
in (

let e = (let _152_251 = (let _152_250 = (let _152_249 = (let _152_248 = (let _152_247 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_TypeChecker_Common.t_unit), (e1)))
in (_152_247)::[])
in ((false), (_152_248)))
in ((_152_249), (e2)))
in FStar_Syntax_Syntax.Tm_let (_152_250))
in (FStar_Syntax_Syntax.mk _152_251 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _152_252 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e), (c), (_152_252))))))
end))
end))
end
| _58_402 -> begin
(

let _58_406 = (tc_term env e)
in (match (_58_406) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (_58_410)) -> begin
(tc_term env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let _58_421 = (tc_term env e)
in (match (_58_421) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (m)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _58_427) -> begin
(

let _58_433 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_433) with
| (env0, _58_432) -> begin
(

let _58_438 = (tc_comp env0 expected_c)
in (match (_58_438) with
| (expected_c, _58_436, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (

let _58_443 = (let _152_253 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term _152_253 e))
in (match (_58_443) with
| (e, c', g') -> begin
(

let _58_447 = (let _152_255 = (let _152_254 = (c'.FStar_Syntax_Syntax.comp ())
in ((e), (_152_254)))
in (check_expected_effect env0 (Some (expected_c)) _152_255))
in (match (_58_447) with
| (e, expected_c, g'') -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t_res)), (Some ((FStar_Syntax_Util.comp_effect_name expected_c)))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let lc = (FStar_Syntax_Util.lcomp_of_comp expected_c)
in (

let f = (let _152_256 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _152_256))
in (

let _58_454 = (comp_check_expected_typ env e lc)
in (match (_58_454) with
| (e, c, f2) -> begin
(let _152_257 = (FStar_TypeChecker_Rel.conj_guard f f2)
in ((e), (c), (_152_257)))
end)))))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _58_459) -> begin
(

let _58_464 = (FStar_Syntax_Util.type_u ())
in (match (_58_464) with
| (k, u) -> begin
(

let _58_469 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_469) with
| (t, _58_467, f) -> begin
(

let _58_473 = (let _152_258 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _152_258 e))
in (match (_58_473) with
| (e, c, g) -> begin
(

let _58_477 = (let _152_262 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_474 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _152_262 e c f))
in (match (_58_477) with
| (c, f) -> begin
(

let _58_481 = (let _152_263 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t)), (Some (c.FStar_Syntax_Syntax.eff_name))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _152_263 c))
in (match (_58_481) with
| (e, c, f2) -> begin
(let _152_265 = (let _152_264 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _152_264))
in ((e), (c), (_152_265)))
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

let _58_517 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_517) with
| (unary_op, _58_516) -> begin
(

let head = (let _152_266 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (Prims.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) None _152_266))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), (rest)))) None top.FStar_Syntax_Syntax.pos)
in (tc_term env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _58_525; FStar_Syntax_Syntax.pos = _58_523; FStar_Syntax_Syntax.vars = _58_521}, ((e, aqual))::[]) -> begin
(

let _58_535 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end else begin
()
end
in (

let _58_544 = (

let _58_540 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_540) with
| (env0, _58_539) -> begin
(tc_term env0 e)
end))
in (match (_58_544) with
| (e, c, g) -> begin
(

let _58_548 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_548) with
| (reify_op, _58_547) -> begin
(

let u_c = (

let _58_554 = (tc_term env c.FStar_Syntax_Syntax.res_typ)
in (match (_58_554) with
| (_58_550, c, _58_553) -> begin
(match ((let _152_267 = (FStar_Syntax_Subst.compress c.FStar_Syntax_Syntax.res_typ)
in _152_267.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| _58_558 -> begin
(FStar_All.failwith "Unexpected result type of computation")
end)
end))
in (

let repr = (FStar_TypeChecker_Util.reify_comp env c u_c)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e), (aqual)))::[])))) (Some (repr.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let c = (let _152_268 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right _152_268 FStar_Syntax_Util.lcomp_of_comp))
in (

let _58_566 = (comp_check_expected_typ env e c)
in (match (_58_566) with
| (e, c, g') -> begin
(let _152_269 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), (c), (_152_269)))
end))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.tk = _58_572; FStar_Syntax_Syntax.pos = _58_570; FStar_Syntax_Syntax.vars = _58_568}, ((e, aqual))::[]) -> begin
(

let _58_583 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end else begin
()
end
in (

let no_reflect = (fun _58_586 -> (match (()) with
| () -> begin
(let _152_274 = (let _152_273 = (let _152_272 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((_152_272), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_152_273))
in (Prims.raise _152_274))
end))
in (

let _58_590 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_590) with
| (reflect_op, _58_589) -> begin
(match ((FStar_TypeChecker_Env.effect_decl_opt env l)) with
| None -> begin
(no_reflect ())
end
| Some (ed) -> begin
if (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable)))) then begin
(no_reflect ())
end else begin
(

let _58_596 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_596) with
| (env_no_ex, topt) -> begin
(

let _58_624 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (let _152_280 = (let _152_279 = (let _152_278 = (let _152_277 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _152_276 = (let _152_275 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (_152_275)::[])
in (_152_277)::_152_276))
in ((repr), (_152_278)))
in FStar_Syntax_Syntax.Tm_app (_152_279))
in (FStar_Syntax_Syntax.mk _152_280 None top.FStar_Syntax_Syntax.pos))
in (

let _58_604 = (let _152_282 = (let _152_281 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _152_281 Prims.fst))
in (tc_tot_or_gtot_term _152_282 t))
in (match (_58_604) with
| (t, _58_602, g) -> begin
(match ((let _152_283 = (FStar_Syntax_Subst.compress t)
in _152_283.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_58_606, ((res, _58_613))::((wp, _58_609))::[]) -> begin
((t), (res), (wp), (g))
end
| _58_619 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))
in (match (_58_624) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let _58_638 = (

let _58_628 = (tc_tot_or_gtot_term env_no_ex e)
in (match (_58_628) with
| (e, c, g) -> begin
(

let _58_629 = if (let _152_284 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation _152_284)) then begin
(FStar_TypeChecker_Errors.add_errors env (((("Expected Tot, got a GTot computation"), (e.FStar_Syntax_Syntax.pos)))::[]))
end else begin
()
end
in (match ((FStar_TypeChecker_Rel.try_teq env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)) with
| None -> begin
(

let _58_632 = (let _152_289 = (let _152_288 = (let _152_287 = (let _152_286 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _152_285 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" _152_286 _152_285)))
in ((_152_287), (e.FStar_Syntax_Syntax.pos)))
in (_152_288)::[])
in (FStar_TypeChecker_Errors.add_errors env _152_289))
in (let _152_290 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e), (_152_290))))
end
| Some (g') -> begin
(let _152_292 = (let _152_291 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' _152_291))
in ((e), (_152_292)))
end))
end))
in (match (_58_638) with
| (e, g) -> begin
(

let c = (let _152_298 = (let _152_297 = (let _152_296 = (let _152_293 = (env.FStar_TypeChecker_Env.universe_of env res_typ)
in (_152_293)::[])
in (let _152_295 = (let _152_294 = (FStar_Syntax_Syntax.as_arg wp)
in (_152_294)::[])
in {FStar_Syntax_Syntax.comp_univs = _152_296; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = _152_295; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp _152_297))
in (FStar_All.pipe_right _152_298 FStar_Syntax_Util.lcomp_of_comp))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e), (aqual)))::[])))) (Some (res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let _58_644 = (comp_check_expected_typ env e c)
in (match (_58_644) with
| (e, c, g') -> begin
(let _152_299 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e), (c), (_152_299)))
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

let env = (let _152_301 = (let _152_300 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _152_300 Prims.fst))
in (FStar_All.pipe_right _152_301 instantiate_both))
in (

let _58_651 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_303 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _152_302 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _152_303 _152_302)))
end else begin
()
end
in (

let _58_656 = (tc_term (no_inst env) head)
in (match (_58_656) with
| (head, chead, g_head) -> begin
(

let _58_660 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _152_304 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _152_304))
end else begin
(let _152_305 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _152_305))
end
in (match (_58_660) with
| (e, c, g) -> begin
(

let _58_661 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_306 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _152_306))
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

let _58_667 = (comp_check_expected_typ env0 e c)
in (match (_58_667) with
| (e, c, g') -> begin
(

let gimp = (match ((let _152_307 = (FStar_Syntax_Subst.compress head)
in _152_307.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _58_670) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e), (c.FStar_Syntax_Syntax.res_typ), (head.FStar_Syntax_Syntax.pos))
in (

let _58_674 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_674.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_674.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_674.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _58_677 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (

let gres = (let _152_308 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _152_308))
in (

let _58_680 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_310 = (FStar_Syntax_Print.term_to_string e)
in (let _152_309 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" _152_310 _152_309)))
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

let _58_688 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_688) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let _58_693 = (tc_term env1 e1)
in (match (_58_693) with
| (e1, c1, g1) -> begin
(

let _58_704 = (match (topt) with
| Some (t) -> begin
((env), (t))
end
| None -> begin
(

let _58_700 = (FStar_Syntax_Util.type_u ())
in (match (_58_700) with
| (k, _58_699) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _152_311 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in ((_152_311), (res_t))))
end))
end)
in (match (_58_704) with
| (env_branches, res_t) -> begin
(

let _58_705 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_312 = (FStar_Syntax_Print.term_to_string res_t)
in (FStar_Util.print1 "Tm_match: expected type of branches is %s\n" _152_312))
end else begin
()
end
in (

let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let _58_723 = (

let _58_720 = (FStar_List.fold_right (fun _58_714 _58_717 -> (match (((_58_714), (_58_717))) with
| ((_58_710, f, c, g), (caccum, gaccum)) -> begin
(let _152_315 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (_152_315)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_58_720) with
| (cases, g) -> begin
(let _152_316 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in ((_152_316), (g)))
end))
in (match (_58_723) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (guard_x)), (c_branches)))
in (

let e = (

let mk_match = (fun scrutinee -> (

let scrutinee = (FStar_TypeChecker_Util.maybe_lift env scrutinee c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let branches = (FStar_All.pipe_right t_eqns (FStar_List.map (fun _58_737 -> (match (_58_737) with
| ((pat, wopt, br), _58_733, lc, _58_736) -> begin
(let _152_320 = (FStar_TypeChecker_Util.maybe_lift env br lc.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in ((pat), (wopt), (_152_320)))
end))))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (Some (cres.FStar_Syntax_Syntax.eff_name))))) None e.FStar_Syntax_Syntax.pos)))))
in if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c1.FStar_Syntax_Syntax.eff_name) then begin
(mk_match e1)
end else begin
(

let e_match = (let _152_321 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match _152_321))
in (

let lb = (let _152_322 = (FStar_TypeChecker_Env.norm_eff_name env c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = _152_322; FStar_Syntax_Syntax.lbdef = e1})
in (

let e = (let _152_327 = (let _152_326 = (let _152_325 = (let _152_324 = (let _152_323 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (_152_323)::[])
in (FStar_Syntax_Subst.close _152_324 e_match))
in ((((false), ((lb)::[]))), (_152_325)))
in FStar_Syntax_Syntax.Tm_let (_152_326))
in (FStar_Syntax_Syntax.mk _152_327 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ))))
end)
in (

let _58_744 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_330 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _152_329 = (let _152_328 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _152_328))
in (FStar_Util.print2 "(%s) comp type = %s\n" _152_330 _152_329)))
end else begin
()
end
in (let _152_331 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e), (cres), (_152_331))))))
end)))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_756); FStar_Syntax_Syntax.lbunivs = _58_754; FStar_Syntax_Syntax.lbtyp = _58_752; FStar_Syntax_Syntax.lbeff = _58_750; FStar_Syntax_Syntax.lbdef = _58_748})::[]), _58_762) -> begin
(

let _58_765 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_332 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _152_332))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _58_769), _58_772) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_787); FStar_Syntax_Syntax.lbunivs = _58_785; FStar_Syntax_Syntax.lbtyp = _58_783; FStar_Syntax_Syntax.lbeff = _58_781; FStar_Syntax_Syntax.lbdef = _58_779})::_58_777), _58_793) -> begin
(

let _58_796 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_333 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _152_333))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _58_800), _58_803) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let _58_817 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_817) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _152_347 = (let _152_346 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_346))
in FStar_Util.Inr (_152_347))
end
in (

let is_data_ctor = (fun _58_3 -> (match (_58_3) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _58_827 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _152_353 = (let _152_352 = (let _152_351 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _152_350 = (FStar_TypeChecker_Env.get_range env)
in ((_152_351), (_152_350))))
in FStar_Syntax_Syntax.Error (_152_352))
in (Prims.raise _152_353))
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
(let _152_355 = (let _152_354 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" _152_354))
in (FStar_All.failwith _152_355))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (match ((let _152_356 = (FStar_Syntax_Subst.compress t1)
in _152_356.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_838) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _58_841 -> begin
(

let imp = (("uvar in term"), (env), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let _58_843 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_843.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_843.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_843.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _58_858 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(

let _58_851 = (FStar_Syntax_Util.type_u ())
in (match (_58_851) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
end))
end
| Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end)
in (match (_58_858) with
| (t, _58_856, g0) -> begin
(

let _58_863 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (_58_863) with
| (e, _58_861, g1) -> begin
(let _152_359 = (let _152_357 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right _152_357 FStar_Syntax_Util.lcomp_of_comp))
in (let _152_358 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e), (_152_359), (_152_358))))
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

let _58_867 = x
in {FStar_Syntax_Syntax.ppname = _58_867.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_867.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let _58_873 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_873) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _152_361 = (let _152_360 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_360))
in FStar_Util.Inr (_152_361))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _58_880; FStar_Syntax_Syntax.pos = _58_878; FStar_Syntax_Syntax.vars = _58_876}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let _58_890 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_890) with
| (us', t) -> begin
(

let _58_897 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _152_364 = (let _152_363 = (let _152_362 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (_152_362)))
in FStar_Syntax_Syntax.Error (_152_363))
in (Prims.raise _152_364))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _58_896 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (

let fv' = (

let _58_899 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _58_901 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_901.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_901.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_899.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_899.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _152_367 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _152_367 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let _58_909 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_909) with
| (us, t) -> begin
(

let fv' = (

let _58_910 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _58_912 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_912.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_912.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_910.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_910.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _152_368 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _152_368 us))
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

let _58_926 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_926) with
| (bs, c) -> begin
(

let env0 = env
in (

let _58_931 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_931) with
| (env, _58_930) -> begin
(

let _58_936 = (tc_binders env bs)
in (match (_58_936) with
| (bs, env, g, us) -> begin
(

let _58_940 = (tc_comp env c)
in (match (_58_940) with
| (c, uc, f) -> begin
(

let e = (

let _58_941 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _58_941.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_941.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_941.FStar_Syntax_Syntax.vars})
in (

let _58_944 = (check_smt_pat env e bs c)
in (

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _152_369 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _152_369))
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

let _58_960 = (let _152_371 = (let _152_370 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_370)::[])
in (FStar_Syntax_Subst.open_term _152_371 phi))
in (match (_58_960) with
| (x, phi) -> begin
(

let env0 = env
in (

let _58_965 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_965) with
| (env, _58_964) -> begin
(

let _58_970 = (let _152_372 = (FStar_List.hd x)
in (tc_binder env _152_372))
in (match (_58_970) with
| (x, env, f1, u) -> begin
(

let _58_971 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_375 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _152_374 = (FStar_Syntax_Print.term_to_string phi)
in (let _152_373 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _152_375 _152_374 _152_373))))
end else begin
()
end
in (

let _58_976 = (FStar_Syntax_Util.type_u ())
in (match (_58_976) with
| (t_phi, _58_975) -> begin
(

let _58_981 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_58_981) with
| (phi, _58_979, f2) -> begin
(

let e = (

let _58_982 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _58_982.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_982.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_982.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _152_376 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _152_376))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _58_990) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (

let _58_996 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_377 = (FStar_Syntax_Print.term_to_string (

let _58_994 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))); FStar_Syntax_Syntax.tk = _58_994.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _58_994.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_994.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _152_377))
end else begin
()
end
in (

let _58_1000 = (FStar_Syntax_Subst.open_term bs body)
in (match (_58_1000) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _58_1002 -> begin
(let _152_380 = (let _152_379 = (FStar_Syntax_Print.term_to_string top)
in (let _152_378 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" _152_379 _152_378)))
in (FStar_All.failwith _152_380))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_58_1007) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_58_1010, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_58_1015, Some (_58_1017)) -> begin
(FStar_All.failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (_58_1022) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_58_1025) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_58_1028) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_58_1032) -> begin
FStar_TypeChecker_Common.t_range
end
| _58_1035 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _58_1041) -> begin
(

let _58_1046 = (FStar_Syntax_Util.type_u ())
in (match (_58_1046) with
| (k, u) -> begin
(

let _58_1051 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_1051) with
| (t, _58_1049, g) -> begin
(let _152_385 = (FStar_Syntax_Syntax.mk_Total' t (Some (u)))
in ((_152_385), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t, _58_1054) -> begin
(

let _58_1059 = (FStar_Syntax_Util.type_u ())
in (match (_58_1059) with
| (k, u) -> begin
(

let _58_1064 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_1064) with
| (t, _58_1062, g) -> begin
(let _152_386 = (FStar_Syntax_Syntax.mk_GTotal' t (Some (u)))
in ((_152_386), (u), (g)))
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

let tc = (let _152_388 = (let _152_387 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_152_387)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _152_388 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let _58_1076 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_58_1076) with
| (tc, _58_1074, f) -> begin
(

let _58_1079 = (FStar_Syntax_Util.head_and_args tc)
in (match (_58_1079) with
| (head, args) -> begin
(

let comp_univs = (match ((let _152_389 = (FStar_Syntax_Subst.compress head)
in _152_389.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (_58_1081, us) -> begin
us
end
| _58_1086 -> begin
[]
end)
in (

let _58_1091 = (FStar_Syntax_Util.head_and_args tc)
in (match (_58_1091) with
| (_58_1089, args) -> begin
(

let _58_1094 = (let _152_391 = (FStar_List.hd args)
in (let _152_390 = (FStar_List.tl args)
in ((_152_391), (_152_390))))
in (match (_58_1094) with
| (res, args) -> begin
(

let _58_1110 = (let _152_393 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _58_4 -> (match (_58_4) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _58_1101 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1101) with
| (env, _58_1100) -> begin
(

let _58_1106 = (tc_tot_or_gtot_term env e)
in (match (_58_1106) with
| (e, _58_1104, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e)), (g))
end))
end))
end
| f -> begin
((f), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right _152_393 FStar_List.unzip))
in (match (_58_1110) with
| (flags, guards) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (Prims.fst res))
in (

let c = (FStar_Syntax_Syntax.mk_Comp (

let _58_1112 = c
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = _58_1112.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _58_1112.FStar_Syntax_Syntax.flags}))
in (

let u_c = (match ((FStar_TypeChecker_Util.effect_repr env c u)) with
| None -> begin
u
end
| Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end)
in (let _152_394 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((c), (u_c), (_152_394))))))
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
| FStar_Syntax_Syntax.U_bvar (_58_1125) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _152_399 = (aux u)
in FStar_Syntax_Syntax.U_succ (_152_399))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _152_400 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_152_400))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _152_404 = (let _152_403 = (let _152_402 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _152_401 = (FStar_TypeChecker_Env.get_range env)
in ((_152_402), (_152_401))))
in FStar_Syntax_Syntax.Error (_152_403))
in (Prims.raise _152_404))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _152_405 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _152_405 Prims.snd))
end
| _58_1140 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _152_414 = (let _152_413 = (let _152_412 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in ((_152_412), (top.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_152_413))
in (Prims.raise _152_414)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun _58_1158 bs bs_expected -> (match (_58_1158) with
| (env, out, g, subst) -> begin
(match (((bs), (bs_expected))) with
| ([], []) -> begin
((env), ((FStar_List.rev out)), (None), (g), (subst))
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
(

let _58_1189 = (match (((imp), (imp'))) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _152_431 = (let _152_430 = (let _152_429 = (let _152_427 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _152_427))
in (let _152_428 = (FStar_Syntax_Syntax.range_of_bv hd)
in ((_152_429), (_152_428))))
in FStar_Syntax_Syntax.Error (_152_430))
in (Prims.raise _152_431))
end
| _58_1188 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _58_1206 = (match ((let _152_432 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _152_432.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| _58_1194 -> begin
(

let _58_1195 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_433 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _152_433))
end else begin
()
end
in (

let _58_1201 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_58_1201) with
| (t, _58_1199, g1) -> begin
(

let g2 = (let _152_435 = (FStar_TypeChecker_Env.get_range env)
in (let _152_434 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _152_435 "Type annotation on parameter incompatible with the expected type" _152_434)))
in (

let g = (let _152_436 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _152_436))
in ((t), (g))))
end)))
end)
in (match (_58_1206) with
| (t, g) -> begin
(

let hd = (

let _58_1207 = hd
in {FStar_Syntax_Syntax.ppname = _58_1207.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1207.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env = (push_binding env b)
in (

let subst = (let _152_437 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _152_437))
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

let _58_1228 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _58_1227 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (

let _58_1235 = (tc_binders env bs)
in (match (_58_1235) with
| (bs, envbody, g, _58_1234) -> begin
(

let _58_1253 = (match ((let _152_444 = (FStar_Syntax_Subst.compress body)
in _152_444.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _58_1240) -> begin
(

let _58_1247 = (tc_comp envbody c)
in (match (_58_1247) with
| (c, _58_1245, g') -> begin
(let _152_445 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((Some (c)), (body), (_152_445)))
end))
end
| _58_1249 -> begin
((None), (body), (g))
end)
in (match (_58_1253) with
| (copt, body, g) -> begin
((None), (bs), ([]), (copt), (envbody), (body), (g))
end))
end)))
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm t -> (match ((let _152_450 = (FStar_Syntax_Subst.compress t)
in _152_450.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let _58_1280 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _58_1279 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _58_1287 = (tc_binders env bs)
in (match (_58_1287) with
| (bs, envbody, g, _58_1286) -> begin
(

let _58_1291 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_58_1291) with
| (envbody, _58_1290) -> begin
((Some (((t), (true)))), (bs), ([]), (None), (envbody), (body), (g))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _58_1294) -> begin
(

let _58_1305 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_58_1305) with
| (_58_1298, bs, bs', copt, env, body, g) -> begin
((Some (((t), (false)))), (bs), (bs'), (copt), (env), (body), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _58_1312 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_58_1312) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun _58_1323 c_expected -> (match (_58_1323) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _152_461 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in ((env), (bs), (guard), (_152_461)))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (let _152_462 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _152_462))
in (let _152_463 = (FStar_Syntax_Subst.subst_comp subst c)
in ((env), (bs), (guard), (_152_463))))
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

let _58_1344 = (check_binders env more_bs bs_expected)
in (match (_58_1344) with
| (env, bs', more, guard', subst) -> begin
(let _152_465 = (let _152_464 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env), ((FStar_List.append bs bs')), (more), (_152_464), (subst)))
in (handle_more _152_465 c_expected))
end))
end
| _58_1346 -> begin
(let _152_467 = (let _152_466 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _152_466))
in (fail _152_467 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _152_468 = (check_binders env bs bs_expected)
in (handle_more _152_468 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let _58_1352 = envbody
in {FStar_TypeChecker_Env.solver = _58_1352.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1352.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1352.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1352.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1352.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1352.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1352.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1352.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1352.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1352.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1352.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1352.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _58_1352.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1352.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1352.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1352.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1352.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1352.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_1352.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_1352.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1352.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1352.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1352.FStar_TypeChecker_Env.qname_and_index})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _58_1357 _58_1360 -> (match (((_58_1357), (_58_1360))) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _58_1366 = (let _152_478 = (let _152_477 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _152_477 Prims.fst))
in (tc_term _152_478 t))
in (match (_58_1366) with
| (t, _58_1363, _58_1365) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l (([]), (t)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _152_479 = (FStar_Syntax_Syntax.mk_binder (

let _58_1370 = x
in {FStar_Syntax_Syntax.ppname = _58_1370.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1370.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_152_479)::letrec_binders)
end
| _58_1373 -> begin
letrec_binders
end)
in ((env), (lb))))
end))
end)) ((envbody), ([])))))))
in (

let _58_1379 = (check_actuals_against_formals env bs bs_expected)
in (match (_58_1379) with
| (envbody, bs, g, c) -> begin
(

let _58_1382 = if (FStar_TypeChecker_Env.should_verify env) then begin
(mk_letrec_env envbody bs c)
end else begin
((envbody), ([]))
end
in (match (_58_1382) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in ((Some (((t), (false)))), (bs), (letrecs), (Some (c)), (envbody), (body), (g)))
end))
end))))
end))
end
| _58_1385 -> begin
if (not (norm)) then begin
(let _152_480 = (unfold_whnf env t)
in (as_function_typ true _152_480))
end else begin
(

let _58_1395 = (expected_function_typ env None body)
in (match (_58_1395) with
| (_58_1387, bs, _58_1390, c_opt, envbody, body, g) -> begin
((Some (((t), (false)))), (bs), ([]), (c_opt), (envbody), (body), (g))
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let _58_1399 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1399) with
| (env, topt) -> begin
(

let _58_1403 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_481 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _152_481 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (

let _58_1412 = (expected_function_typ env topt body)
in (match (_58_1412) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let _58_1418 = (tc_term (

let _58_1413 = envbody
in {FStar_TypeChecker_Env.solver = _58_1413.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1413.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1413.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1413.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1413.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1413.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1413.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1413.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1413.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1413.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1413.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1413.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1413.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_1413.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1413.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1413.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1413.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_1413.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_1413.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1413.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1413.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1413.FStar_TypeChecker_Env.qname_and_index}) body)
in (match (_58_1418) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _58_1420 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _152_484 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _152_483 = (let _152_482 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _152_482))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _152_484 _152_483)))
end else begin
()
end
in (

let _58_1427 = (let _152_486 = (let _152_485 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body), (_152_485)))
in (check_expected_effect (

let _58_1422 = envbody
in {FStar_TypeChecker_Env.solver = _58_1422.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1422.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1422.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1422.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1422.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1422.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1422.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1422.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1422.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1422.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1422.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1422.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1422.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1422.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1422.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1422.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1422.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1422.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_1422.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_1422.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1422.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1422.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1422.FStar_TypeChecker_Env.qname_and_index}) c_opt _152_486))
in (match (_58_1427) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(let _152_487 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _152_487))
end else begin
(

let guard = (let _152_488 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) _152_488))
in guard)
end
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _152_491 = (let _152_490 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _152_489 -> FStar_Util.Inl (_152_489)))
in Some (_152_490))
in (FStar_Syntax_Util.abs bs body _152_491))
in (

let _58_1450 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_58_1439) -> begin
((e), (t), (guard))
end
| _58_1442 -> begin
(

let _58_1445 = if use_teq then begin
(let _152_492 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in ((e), (_152_492)))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_58_1445) with
| (e, guard') -> begin
(let _152_493 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((e), (t), (_152_493)))
end))
end))
end
| None -> begin
((e), (tfun_computed), (guard))
end)
in (match (_58_1450) with
| (e, tfun, guard) -> begin
(

let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (

let _58_1454 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_58_1454) with
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

let _58_1464 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_502 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _152_501 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _152_502 _152_501)))
end else begin
()
end
in (

let monadic_application = (fun _58_1471 subst arg_comps_rev arg_rets guard fvs bs -> (match (_58_1471) with
| (head, chead, ghead, cres) -> begin
(

let rt = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _58_1479 = cres
in {FStar_Syntax_Syntax.eff_name = _58_1479.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = rt; FStar_Syntax_Syntax.cflags = _58_1479.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_1479.FStar_Syntax_Syntax.comp})
in (

let _58_1508 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun _58_5 -> (match (_58_5) with
| (_58_1487, _58_1489, None) -> begin
false
end
| (_58_1493, _58_1495, Some (c)) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _152_518 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _152_518 cres))
end else begin
(

let _58_1500 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_521 = (FStar_Syntax_Print.term_to_string head)
in (let _152_520 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _152_519 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _152_521 _152_520 _152_519))))
end else begin
()
end
in cres)
end
in ((cres), (g))))))
end
| _58_1504 -> begin
(

let g = (let _152_522 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right _152_522 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _152_527 = (let _152_526 = (let _152_525 = (let _152_524 = (let _152_523 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _152_523))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _152_524))
in (FStar_Syntax_Syntax.mk_Total _152_525))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_526))
in ((_152_527), (g))))
end)
in (match (_58_1508) with
| (cres, guard) -> begin
(

let _58_1509 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_528 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _152_528))
end else begin
()
end
in (

let _58_1531 = (FStar_List.fold_left (fun _58_1514 _58_1520 -> (match (((_58_1514), (_58_1520))) with
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
in (match (_58_1531) with
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

let _58_1537 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (_58_1537) with
| (comp, g) -> begin
((app), (comp), (g))
end)))))
end)))
end))))
end))
in (

let rec tc_args = (fun head_info _58_1545 bs args -> (match (_58_1545) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args))) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (_58_1551))))::rest, ((_58_1559, None))::_58_1557) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let t = (check_no_escape (Some (head)) env fvs t)
in (

let _58_1570 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_58_1570) with
| (varg, _58_1568, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst
in (

let arg = (let _152_540 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (_152_540)))
in (let _152_542 = (let _152_541 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst), ((((arg), (None), (None)))::outargs), ((arg)::arg_rets), (_152_541), (fvs)))
in (tc_args head_info _152_542 rest args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
(

let _58_1602 = (match (((aqual), (aq))) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _58_1601 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifier"), (e.FStar_Syntax_Syntax.pos)))))
end)
in (

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let _58_1605 = x
in {FStar_Syntax_Syntax.ppname = _58_1605.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1605.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (

let _58_1608 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_543 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _152_543))
end else begin
()
end
in (

let targ = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let _58_1612 = env
in {FStar_TypeChecker_Env.solver = _58_1612.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1612.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1612.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1612.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1612.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1612.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1612.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1612.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1612.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1612.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1612.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1612.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1612.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1612.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1612.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _58_1612.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1612.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1612.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_1612.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_1612.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1612.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1612.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1612.FStar_TypeChecker_Env.qname_and_index})
in (

let _58_1615 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_546 = (FStar_Syntax_Print.tag_of_term e)
in (let _152_545 = (FStar_Syntax_Print.term_to_string e)
in (let _152_544 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _152_546 _152_545 _152_544))))
end else begin
()
end
in (

let _58_1620 = (tc_term env e)
in (match (_58_1620) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = ((e), (aq))
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(

let subst = (let _152_547 = (FStar_List.hd bs)
in (maybe_extend_subst subst _152_547 e))
in (tc_args head_info ((subst), ((((arg), (None), (None)))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(

let subst = (let _152_548 = (FStar_List.hd bs)
in (maybe_extend_subst subst _152_548 e))
in (tc_args head_info ((subst), ((((arg), (Some (x)), (Some (c))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (let _152_549 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _152_549)) then begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _152_550 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _152_550))
in (tc_args head_info ((subst), ((((arg), (Some (newx)), (Some (c))))::outargs), ((arg')::arg_rets), (g), (fvs)) rest rest')))
end else begin
(let _152_554 = (let _152_553 = (let _152_552 = (let _152_551 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _152_551))
in (_152_552)::arg_rets)
in ((subst), ((((arg), (Some (x)), (Some (c))))::outargs), (_152_553), (g), ((x)::fvs)))
in (tc_args head_info _152_554 rest rest'))
end
end
end))
end))))))))))
end
| (_58_1628, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::_58_1633) -> begin
(

let _58_1640 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (_58_1640) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _152_559 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _152_559 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let _58_1651 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (_58_1651) with
| (bs, cres') -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp cres')))
in (

let _58_1653 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_560 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _152_560))
end else begin
()
end
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args)))
end))
end
| _58_1656 when (not (norm)) -> begin
(let _152_561 = (unfold_whnf env tres)
in (aux true _152_561))
end
| _58_1658 -> begin
(let _152_567 = (let _152_566 = (let _152_565 = (let _152_563 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (let _152_562 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _152_563 _152_562)))
in (let _152_564 = (FStar_Syntax_Syntax.argpos arg)
in ((_152_565), (_152_564))))
in FStar_Syntax_Syntax.Error (_152_566))
in (Prims.raise _152_567))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (match ((let _152_572 = (FStar_Syntax_Util.unrefine tf)
in _152_572.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl -> begin
(

let _58_1691 = (tc_term env e)
in (match (_58_1691) with
| (e, c, g_e) -> begin
(

let _58_1695 = (tc_args env tl)
in (match (_58_1695) with
| (args, comps, g_rest) -> begin
(let _152_577 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e), (imp)))::args), ((((e.FStar_Syntax_Syntax.pos), (c)))::comps), (_152_577)))
end))
end))
end))
in (

let _58_1699 = (tc_args env args)
in (match (_58_1699) with
| (args, comps, g_args) -> begin
(

let bs = (let _152_579 = (FStar_All.pipe_right comps (FStar_List.map (fun _58_1703 -> (match (_58_1703) with
| (_58_1701, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks _152_579))
in (

let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _58_1709 -> begin
FStar_Syntax_Util.ml_comp
end)
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _152_594 = (FStar_Syntax_Subst.compress t)
in _152_594.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_58_1715) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _58_1720 -> begin
ml_or_tot
end)
end)
in (

let cres = (let _152_599 = (let _152_598 = (let _152_597 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _152_597 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _152_598))
in (ml_or_tot _152_599 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (

let _58_1724 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _152_602 = (FStar_Syntax_Print.term_to_string head)
in (let _152_601 = (FStar_Syntax_Print.term_to_string tf)
in (let _152_600 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _152_602 _152_601 _152_600))))
end else begin
()
end
in (

let _58_1726 = (let _152_603 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _152_603))
in (

let comp = (let _152_606 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _58_1730 out -> (match (_58_1730) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c ((None), (out)))
end)) ((((head.FStar_Syntax_Syntax.pos), (chead)))::comps) _152_606))
in (let _152_608 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _152_607 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((_152_608), (comp), (_152_607))))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _58_1739 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_1739) with
| (bs, c) -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp c)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args))
end))
end
| _58_1742 -> begin
if (not (norm)) then begin
(let _152_609 = (unfold_whnf env tf)
in (check_function_app true _152_609))
end else begin
(let _152_612 = (let _152_611 = (let _152_610 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in ((_152_610), (head.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_152_611))
in (Prims.raise _152_612))
end
end))
in (let _152_614 = (let _152_613 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _152_613))
in (check_function_app false _152_614))))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let _58_1778 = (FStar_List.fold_left2 (fun _58_1759 _58_1762 _58_1765 -> (match (((_58_1759), (_58_1762), (_58_1765))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(

let _58_1766 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifiers"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _58_1771 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_58_1771) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (let _152_624 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _152_624 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _152_628 = (let _152_626 = (let _152_625 = (FStar_Syntax_Syntax.as_arg e)
in (_152_625)::[])
in (FStar_List.append seen _152_626))
in (let _152_627 = (FStar_TypeChecker_Rel.conj_guard guard g)
in ((_152_628), (_152_627), (ghost)))))))
end)))
end)) (([]), (g_head), (false)) args bs)
in (match (_58_1778) with
| (args, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = if ghost then begin
(let _152_629 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _152_629 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (

let _58_1783 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_58_1783) with
| (c, g) -> begin
((e), (c), (g))
end))))
end)))
end
| _58_1785 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let _58_1792 = (FStar_Syntax_Subst.open_branch branch)
in (match (_58_1792) with
| (pattern, when_clause, branch_exp) -> begin
(

let _58_1797 = branch
in (match (_58_1797) with
| (cpat, _58_1795, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _58_1805 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_58_1805) with
| (pat_bvs, exps, p) -> begin
(

let _58_1806 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_641 = (FStar_Syntax_Print.pat_to_string p0)
in (let _152_640 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _152_641 _152_640)))
end else begin
()
end
in (

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let _58_1812 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_58_1812) with
| (env1, _58_1811) -> begin
(

let env1 = (

let _58_1813 = env1
in {FStar_TypeChecker_Env.solver = _58_1813.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1813.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1813.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1813.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1813.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1813.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1813.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1813.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _58_1813.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1813.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1813.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1813.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1813.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1813.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1813.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1813.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1813.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1813.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_1813.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_1813.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1813.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1813.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1813.FStar_TypeChecker_Env.qname_and_index})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _58_1852 = (let _152_664 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _58_1818 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_644 = (FStar_Syntax_Print.term_to_string e)
in (let _152_643 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _152_644 _152_643)))
end else begin
()
end
in (

let _58_1823 = (tc_term env1 e)
in (match (_58_1823) with
| (e, lc, g) -> begin
(

let _58_1824 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_646 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _152_645 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _152_646 _152_645)))
end else begin
()
end
in (

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let _58_1830 = (let _152_647 = (FStar_TypeChecker_Rel.discharge_guard env (

let _58_1828 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_1828.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_1828.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_1828.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _152_647 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _152_652 = (let _152_651 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _152_651 (FStar_List.map (fun _58_1838 -> (match (_58_1838) with
| (u, _58_1837) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _152_652 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _58_1846 = if (let _152_653 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _152_653)) then begin
(

let unresolved = (let _152_654 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _152_654 FStar_Util.set_elements))
in (let _152_662 = (let _152_661 = (let _152_660 = (let _152_659 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _152_658 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _152_657 = (let _152_656 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _58_1845 -> (match (_58_1845) with
| (u, _58_1844) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _152_656 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _152_659 _152_658 _152_657))))
in ((_152_660), (p.FStar_Syntax_Syntax.p)))
in FStar_Syntax_Syntax.Error (_152_661))
in (Prims.raise _152_662)))
end else begin
()
end
in (

let _58_1848 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_663 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _152_663))
end else begin
()
end
in ((e), (e'))))))))))))
end))))))
in (FStar_All.pipe_right _152_664 FStar_List.unzip))
in (match (_58_1852) with
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

let _58_1859 = (let _152_665 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _152_665 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_58_1859) with
| (scrutinee_env, _58_1858) -> begin
(

let _58_1865 = (tc_pat true pat_t pattern)
in (match (_58_1865) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let _58_1875 = (match (when_clause) with
| None -> begin
((None), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (e) -> begin
if (FStar_TypeChecker_Env.should_verify env) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("When clauses are not yet supported in --verify mode; they will be some day"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
(

let _58_1872 = (let _152_666 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _152_666 e))
in (match (_58_1872) with
| (e, c, g) -> begin
((Some (e)), (g))
end))
end
end)
in (match (_58_1875) with
| (when_clause, g_when) -> begin
(

let _58_1879 = (tc_term pat_env branch_exp)
in (match (_58_1879) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _152_668 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _152_667 -> Some (_152_667)) _152_668))
end)
in (

let _58_1937 = (

let eqs = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
None
end else begin
(FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _58_1897 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _152_672 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _152_671 -> Some (_152_671)) _152_672))
end))
end))) None))
end
in (

let _58_1905 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_58_1905) with
| (c, g_branch) -> begin
(

let _58_1932 = (match (((eqs), (when_condition))) with
| _58_1907 when (not ((FStar_TypeChecker_Env.should_verify env))) -> begin
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
in (let _152_675 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _152_674 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((_152_675), (_152_674))))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (let _152_676 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_152_676))
in (let _152_679 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _152_678 = (let _152_677 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _152_677 g_when))
in ((_152_679), (_152_678))))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _152_680 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in ((_152_680), (g_when)))))
end)
in (match (_58_1932) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _152_682 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _152_681 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in ((_152_682), (_152_681), (g_branch)))))
end))
end)))
in (match (_58_1937) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
FStar_Syntax_Util.t_true
end else begin
(

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> if ((let _152_692 = (let _152_691 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _152_691))
in (FStar_List.length _152_692)) > (Prims.parse_int "1")) then begin
(

let disc = (let _152_693 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _152_693 FStar_Syntax_Syntax.Delta_equational None))
in (

let disc = (let _152_695 = (let _152_694 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_152_694)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _152_695 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _152_696 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_152_696)::[])))
end else begin
[]
end)
in (

let fail = (fun _58_1947 -> (match (()) with
| () -> begin
(let _152_702 = (let _152_701 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _152_700 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _152_699 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _152_701 _152_700 _152_699))))
in (FStar_All.failwith _152_702))
end))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _58_1954) -> begin
(head_constructor t)
end
| _58_1958 -> begin
(fail ())
end))
in (

let pat_exp = (let _152_705 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _152_705 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_58_1983) -> begin
(let _152_710 = (let _152_709 = (let _152_708 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _152_707 = (let _152_706 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_152_706)::[])
in (_152_708)::_152_707))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _152_709 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_152_710)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _152_711 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _152_711))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(

let sub_term_guards = (let _152_718 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _58_2001 -> (match (_58_2001) with
| (ei, _58_2000) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _58_2005 -> begin
(

let sub_term = (let _152_717 = (let _152_714 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _152_714 FStar_Syntax_Syntax.Delta_equational None))
in (let _152_716 = (let _152_715 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_152_715)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _152_717 _152_716 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _152_718 FStar_List.flatten))
in (let _152_719 = (discriminate scrutinee_tm f)
in (FStar_List.append _152_719 sub_term_guards)))
end)
end
| _58_2009 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(

let t = (let _152_724 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _152_724))
in (

let _58_2017 = (FStar_Syntax_Util.type_u ())
in (match (_58_2017) with
| (k, _58_2016) -> begin
(

let _58_2023 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_58_2023) with
| (t, _58_2020, _58_2022) -> begin
t
end))
end)))
end)
in (

let branch_guard = (let _152_725 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _152_725 FStar_Syntax_Util.mk_disj_l))
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

let _58_2031 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_726 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _152_726))
end else begin
()
end
in (let _152_727 = (FStar_Syntax_Subst.close_branch ((pattern), (when_clause), (branch_exp)))
in ((_152_727), (branch_guard), (c), (guard))))))
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

let _58_2048 = (check_let_bound_def true env lb)
in (match (_58_2048) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let _58_2060 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
((g1), (e1), (univ_vars), (c1))
end else begin
(

let g1 = (let _152_730 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _152_730 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _58_2055 = (let _152_734 = (let _152_733 = (let _152_732 = (let _152_731 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (_152_731)))
in (_152_732)::[])
in (FStar_TypeChecker_Util.generalize env _152_733))
in (FStar_List.hd _152_734))
in (match (_58_2055) with
| (_58_2051, univs, e1, c1) -> begin
((g1), (e1), (univs), ((FStar_Syntax_Util.lcomp_of_comp c1)))
end)))
end
in (match (_58_2060) with
| (g1, e1, univ_vars, c1) -> begin
(

let _58_2071 = if (FStar_TypeChecker_Env.should_verify env) then begin
(

let _58_2063 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_58_2063) with
| (ok, c1) -> begin
if ok then begin
((e2), (c1))
end else begin
(

let _58_2064 = if (FStar_Options.warn_top_level_effects ()) then begin
(let _152_735 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _152_735 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _152_736 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) None e2.FStar_Syntax_Syntax.pos)
in ((_152_736), (c1))))
end
end))
end else begin
(

let _58_2066 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (

let c = (let _152_737 = (c1.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_right _152_737 (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env)))
in ((e2), (c))))
end
in (match (_58_2071) with
| (e2, c1) -> begin
(

let cres = (let _152_738 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_738))
in (

let _58_2073 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _152_739 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((_152_739), (cres), (FStar_TypeChecker_Rel.trivial_guard))))))
end))
end))
end))
end
| _58_2077 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let _58_2088 = env
in {FStar_TypeChecker_Env.solver = _58_2088.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2088.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2088.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2088.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2088.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2088.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2088.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2088.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2088.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2088.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2088.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2088.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2088.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_2088.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2088.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2088.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2088.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2088.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_2088.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_2088.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2088.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2088.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2088.FStar_TypeChecker_Env.qname_and_index})
in (

let _58_2097 = (let _152_743 = (let _152_742 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _152_742 Prims.fst))
in (check_let_bound_def false _152_743 lb))
in (match (_58_2097) with
| (e1, _58_2093, c1, g1, annotated) -> begin
(

let x = (

let _58_2098 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_2098.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2098.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let _58_2103 = (let _152_745 = (let _152_744 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_744)::[])
in (FStar_Syntax_Subst.open_term _152_745 e2))
in (match (_58_2103) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _58_2109 = (let _152_746 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _152_746 e2))
in (match (_58_2109) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (x)), (c2)))
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e2 = (FStar_TypeChecker_Util.maybe_lift env e2 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let e = (let _152_749 = (let _152_748 = (let _152_747 = (FStar_Syntax_Subst.close xb e2)
in ((((false), ((lb)::[]))), (_152_747)))
in FStar_Syntax_Syntax.Tm_let (_152_748))
in (FStar_Syntax_Syntax.mk _152_749 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (let _152_752 = (let _152_751 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _152_751 e1))
in (FStar_All.pipe_left (fun _152_750 -> FStar_TypeChecker_Common.NonTrivial (_152_750)) _152_752))
in (

let g2 = (let _152_754 = (let _152_753 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _152_753 g2))
in (FStar_TypeChecker_Rel.close_guard xb _152_754))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if (let _152_755 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome _152_755)) then begin
(

let tt = (let _152_756 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_All.pipe_right _152_756 FStar_Option.get))
in (

let _58_2120 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Exports"))) then begin
(let _152_758 = (FStar_Syntax_Print.term_to_string tt)
in (let _152_757 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Got expected type from env %s\ncres.res_typ=%s\n" _152_758 _152_757)))
end else begin
()
end
in ((e), (cres), (guard))))
end else begin
(

let t = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (

let _58_2123 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Exports"))) then begin
(let _152_760 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (let _152_759 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checked %s has no escaping types; normalized to %s\n" _152_760 _152_759)))
end else begin
()
end
in ((e), ((

let _58_2125 = cres
in {FStar_Syntax_Syntax.eff_name = _58_2125.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_2125.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_2125.FStar_Syntax_Syntax.comp})), (guard))))
end)))))))))
end))))
end)))
end)))
end
| _58_2128 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _58_2140 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_58_2140) with
| (lbs, e2) -> begin
(

let _58_2143 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2143) with
| (env0, topt) -> begin
(

let _58_2146 = (build_let_rec_env true env0 lbs)
in (match (_58_2146) with
| (lbs, rec_env) -> begin
(

let _58_2149 = (check_let_recs rec_env lbs)
in (match (_58_2149) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (let _152_763 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _152_763 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _152_766 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _152_766 (fun _152_765 -> Some (_152_765))))
in (

let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(

let ecs = (let _152_770 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _152_769 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (_152_769))))))
in (FStar_TypeChecker_Util.generalize env _152_770))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _58_2160 -> (match (_58_2160) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _152_772 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_772))
in (

let _58_2163 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _58_2167 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_2167) with
| (lbs, e2) -> begin
(let _152_774 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _152_773 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in ((_152_774), (cres), (_152_773))))
end)))))))
end))
end))
end))
end))
end
| _58_2169 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _58_2181 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_58_2181) with
| (lbs, e2) -> begin
(

let _58_2184 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2184) with
| (env0, topt) -> begin
(

let _58_2187 = (build_let_rec_env false env0 lbs)
in (match (_58_2187) with
| (lbs, rec_env) -> begin
(

let _58_2190 = (check_let_recs rec_env lbs)
in (match (_58_2190) with
| (lbs, g_lbs) -> begin
(

let _58_2202 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let _58_2193 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_2193.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2193.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let _58_2196 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _58_2196.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _58_2196.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _58_2196.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _58_2196.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (lb.FStar_Syntax_Syntax.lbtyp)))
in ((env), (lb)))))) env))
in (match (_58_2202) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let _58_2208 = (tc_term env e2)
in (match (_58_2208) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _58_2212 = cres
in {FStar_Syntax_Syntax.eff_name = _58_2212.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _58_2212.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_2212.FStar_Syntax_Syntax.comp})
in (

let _58_2217 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_2217) with
| (lbs, e2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_58_2220) -> begin
((e), (cres), (guard))
end
| None -> begin
(

let tres = (check_no_escape None env bvs tres)
in (

let cres = (

let _58_2224 = cres
in {FStar_Syntax_Syntax.eff_name = _58_2224.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _58_2224.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_2224.FStar_Syntax_Syntax.comp})
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
| _58_2228 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun t -> (

let _58_2238 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (_58_2238) with
| (_58_2236, c) -> begin
(

let quals = (FStar_TypeChecker_Env.lookup_effect_quals env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
end)))
in (

let _58_2268 = (FStar_List.fold_left (fun _58_2242 lb -> (match (_58_2242) with
| (lbs, env) -> begin
(

let _58_2247 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_58_2247) with
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

let _58_2256 = (let _152_788 = (let _152_787 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _152_787))
in (tc_check_tot_or_gtot_term (

let _58_2250 = env0
in {FStar_TypeChecker_Env.solver = _58_2250.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2250.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2250.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2250.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2250.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2250.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2250.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2250.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2250.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2250.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2250.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2250.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2250.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2250.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _58_2250.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2250.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2250.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2250.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_2250.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_2250.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2250.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2250.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2250.FStar_TypeChecker_Env.qname_and_index}) t _152_788))
in (match (_58_2256) with
| (t, _58_2254, g) -> begin
(

let _58_2257 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (

let env = if ((termination_check_enabled t) && (FStar_TypeChecker_Env.should_verify env)) then begin
(

let _58_2260 = env
in {FStar_TypeChecker_Env.solver = _58_2260.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2260.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2260.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2260.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2260.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2260.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2260.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2260.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2260.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2260.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2260.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2260.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t)))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2260.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_2260.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2260.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2260.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2260.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2260.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_2260.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_2260.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2260.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2260.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2260.FStar_TypeChecker_Env.qname_and_index})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (t)))
end
in (

let lb = (

let _58_2263 = lb
in {FStar_Syntax_Syntax.lbname = _58_2263.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _58_2263.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb)::lbs), (env)))))))
end))
end)) (([]), (env)) lbs)
in (match (_58_2268) with
| (lbs, env) -> begin
(((FStar_List.rev lbs)), (env))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _58_2281 = (let _152_793 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _58_2275 = (let _152_792 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _152_792 lb.FStar_Syntax_Syntax.lbdef))
in (match (_58_2275) with
| (e, c, g) -> begin
(

let _58_2276 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in ((lb), (g))))
end)))))
in (FStar_All.pipe_right _152_793 FStar_List.unzip))
in (match (_58_2281) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _58_2289 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2289) with
| (env1, _58_2288) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _58_2295 = (check_lbtyp top_level env lb)
in (match (_58_2295) with
| (topt, wf_annot, univ_vars, env1) -> begin
(

let _58_2296 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _58_2303 = (tc_maybe_toplevel_term (

let _58_2298 = env1
in {FStar_TypeChecker_Env.solver = _58_2298.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2298.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2298.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2298.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2298.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2298.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2298.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2298.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2298.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2298.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2298.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2298.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2298.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _58_2298.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2298.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2298.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2298.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2298.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_2298.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_2298.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2298.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2298.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2298.FStar_TypeChecker_Env.qname_and_index}) e1)
in (match (_58_2303) with
| (e1, c1, g1) -> begin
(

let _58_2307 = (let _152_800 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_2304 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _152_800 e1 c1 wf_annot))
in (match (_58_2307) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _58_2309 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_803 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _152_802 = (FStar_Syntax_Print.term_to_string c1.FStar_Syntax_Syntax.res_typ)
in (let _152_801 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print3 "checked top-level def %s, result type is %s, guard is %s\n" _152_803 _152_802 _152_801))))
end else begin
()
end
in (let _152_804 = (FStar_Option.isSome topt)
in ((e1), (univ_vars), (c1), (g1), (_152_804)))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _58_2316 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in ((None), (FStar_TypeChecker_Rel.trivial_guard), ([]), (env)))
end
| _58_2319 -> begin
(

let _58_2322 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_58_2322) with
| (univ_vars, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _152_808 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars), (_152_808)))
end else begin
(

let _58_2327 = (FStar_Syntax_Util.type_u ())
in (match (_58_2327) with
| (k, _58_2326) -> begin
(

let _58_2332 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_58_2332) with
| (t, _58_2330, g) -> begin
(

let _58_2333 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _152_811 = (let _152_809 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _152_809))
in (let _152_810 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _152_811 _152_810)))
end else begin
()
end
in (

let t = (norm env1 t)
in (let _152_812 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (g), (univ_vars), (_152_812)))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _58_2339 -> (match (_58_2339) with
| (x, imp) -> begin
(

let _58_2342 = (FStar_Syntax_Util.type_u ())
in (match (_58_2342) with
| (tu, u) -> begin
(

let _58_2343 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_817 = (FStar_Syntax_Print.bv_to_string x)
in (let _152_816 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _152_815 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binders %s:%s at type %s\n" _152_817 _152_816 _152_815))))
end else begin
()
end
in (

let _58_2349 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_58_2349) with
| (t, _58_2347, g) -> begin
(

let x = (((

let _58_2350 = x
in {FStar_Syntax_Syntax.ppname = _58_2350.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2350.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in (

let _58_2353 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_819 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _152_818 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _152_819 _152_818)))
end else begin
()
end
in (let _152_820 = (push_binding env x)
in ((x), (_152_820), (g), (u)))))
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

let _58_2368 = (tc_binder env b)
in (match (_58_2368) with
| (b, env', g, u) -> begin
(

let _58_2373 = (aux env' bs)
in (match (_58_2373) with
| (bs, env', g', us) -> begin
(let _152_828 = (let _152_827 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _152_827))
in (((b)::bs), (env'), (_152_828), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun _58_2381 _58_2384 -> (match (((_58_2381), (_58_2384))) with
| ((t, imp), (args, g)) -> begin
(

let _58_2389 = (tc_term env t)
in (match (_58_2389) with
| (t, _58_2387, g') -> begin
(let _152_837 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t), (imp)))::args), (_152_837)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p _58_2393 -> (match (_58_2393) with
| (pats, g) -> begin
(

let _58_2396 = (tc_args env p)
in (match (_58_2396) with
| (args, g') -> begin
(let _152_840 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats), (_152_840)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _58_2402 = (tc_maybe_toplevel_term env e)
in (match (_58_2402) with
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

let _58_2408 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _152_843 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in ((_152_843), (false)))
end else begin
(let _152_844 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in ((_152_844), (true)))
end
in (match (_58_2408) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _152_845 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (_152_845)))
end
| _58_2412 -> begin
if allow_ghost then begin
(let _152_848 = (let _152_847 = (let _152_846 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in ((_152_846), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_152_847))
in (Prims.raise _152_848))
end else begin
(let _152_851 = (let _152_850 = (let _152_849 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in ((_152_849), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_152_850))
in (Prims.raise _152_851))
end
end)
end)))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let _58_2422 = (tc_tot_or_gtot_term env t)
in (match (_58_2422) with
| (t, c, g) -> begin
(

let _58_2423 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in ((t), (c)))
end)))


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _58_2427 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _152_861 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _152_861))
end else begin
()
end
in (

let env = (

let _58_2429 = env
in {FStar_TypeChecker_Env.solver = _58_2429.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2429.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2429.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2429.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2429.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2429.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2429.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2429.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2429.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2429.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2429.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2429.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2429.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_2429.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2429.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2429.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2429.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2429.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_2429.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_2429.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2429.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2429.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2429.FStar_TypeChecker_Env.qname_and_index})
in (

let _58_2445 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _58_2437) -> begin
(let _152_866 = (let _152_865 = (let _152_864 = (FStar_TypeChecker_Env.get_range env)
in (((Prims.strcat "Implicit argument: " msg)), (_152_864)))
in FStar_Syntax_Syntax.Error (_152_865))
in (Prims.raise _152_866))
end
in (match (_58_2445) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end else begin
(let _152_871 = (let _152_870 = (let _152_869 = (let _152_867 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _152_867))
in (let _152_868 = (FStar_TypeChecker_Env.get_range env)
in ((_152_869), (_152_868))))
in FStar_Syntax_Syntax.Error (_152_870))
in (Prims.raise _152_871))
end
end)))))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> (

let _58_2448 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_876 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "<start> universe_of %s\n" _152_876))
end else begin
()
end
in (

let _58_2453 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2453) with
| (env, _58_2452) -> begin
(

let env = (

let _58_2454 = env
in {FStar_TypeChecker_Env.solver = _58_2454.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2454.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2454.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2454.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2454.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2454.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2454.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2454.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2454.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2454.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2454.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2454.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2454.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_2454.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2454.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2454.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2454.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _58_2454.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_2454.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2454.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _58_2454.FStar_TypeChecker_Env.qname_and_index})
in (

let fail = (fun e t -> (let _152_886 = (let _152_885 = (let _152_884 = (let _152_882 = (FStar_Syntax_Print.term_to_string e)
in (let _152_881 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" _152_882 _152_881)))
in (let _152_883 = (FStar_TypeChecker_Env.get_range env)
in ((_152_884), (_152_883))))
in FStar_Syntax_Syntax.Error (_152_885))
in (Prims.raise _152_886)))
in (

let ok = (fun u -> (

let _58_2462 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_891 = (FStar_Syntax_Print.tag_of_term e)
in (let _152_890 = (FStar_Syntax_Print.term_to_string e)
in (let _152_889 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.print3 "<end> universe_of (%s) %s is %s\n" _152_891 _152_890 _152_889))))
end else begin
()
end
in u))
in (

let universe_of_type = (fun e t -> (match ((let _152_896 = (FStar_Syntax_Util.unrefine t)
in _152_896.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(ok u)
end
| _58_2470 -> begin
(fail e t)
end))
in (

let _58_2473 = (FStar_Syntax_Util.head_and_args e)
in (match (_58_2473) with
| (head, args) -> begin
(match ((let _152_897 = (FStar_Syntax_Subst.compress head)
in _152_897.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_58_2475, t) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _152_898 = (FStar_Syntax_Subst.compress t)
in _152_898.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_2481, t) -> begin
(universe_of_type e (FStar_Syntax_Util.comp_result t))
end
| _58_2486 -> begin
(universe_of_type e t)
end))
end
| _58_2488 -> begin
(

let t = (match ((FStar_ST.read e.FStar_Syntax_Syntax.tk)) with
| (None) | (Some (FStar_Syntax_Syntax.Tm_unknown)) -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoInline)::[]) env e)
in (

let _58_2504 = (tc_term env e)
in (match (_58_2504) with
| (_58_2494, {FStar_Syntax_Syntax.eff_name = _58_2501; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_2498; FStar_Syntax_Syntax.comp = _58_2496}, g) -> begin
(

let _58_2505 = (let _152_900 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (FStar_All.pipe_right _152_900 Prims.ignore))
in t)
end)))
end
| Some (t) -> begin
(FStar_Syntax_Syntax.mk t None e.FStar_Syntax_Syntax.pos)
end)
in (let _152_901 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (FStar_All.pipe_left (universe_of_type e) _152_901)))
end)
end))))))
end))))




