
open Prims

let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _61_2 = env
in {FStar_TypeChecker_Env.solver = _61_2.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_2.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_2.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_2.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_2.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_2.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_2.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_2.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _61_2.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _61_2.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _61_2.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _61_2.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _61_2.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _61_2.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _61_2.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _61_2.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _61_2.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _61_2.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _61_2.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _61_2.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_2.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _61_2.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _61_2.FStar_TypeChecker_Env.qname_and_index}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _61_5 = env
in {FStar_TypeChecker_Env.solver = _61_5.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_5.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_5.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_5.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_5.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_5.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_5.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_5.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _61_5.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _61_5.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _61_5.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _61_5.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _61_5.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _61_5.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _61_5.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _61_5.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _61_5.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _61_5.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _61_5.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _61_5.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_5.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _61_5.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _61_5.FStar_TypeChecker_Env.qname_and_index}))


let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (

let r = if (tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
v.FStar_Syntax_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos tl.FStar_Syntax_Syntax.pos)
end
in (let _162_12 = (let _162_11 = (FStar_Syntax_Syntax.as_arg v)
in (let _162_10 = (let _162_9 = (FStar_Syntax_Syntax.as_arg tl)
in (_162_9)::[])
in (_162_11)::_162_10))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _162_12 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun uu___334 -> (match (uu___334) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _61_15 -> begin
false
end))


let steps = (fun env -> (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[])


let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Beta)::[]) env t))


let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize (steps env) env t))


let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (FStar_TypeChecker_Normalize.normalize_comp (steps env) env c))


let check_no_escape : FStar_Syntax_Syntax.term Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun head_opt env fvs kt -> (

let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
t
end
| _61_32 -> begin
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

let fail = (fun _61_40 -> (match (()) with
| () -> begin
(

let msg = (match (head_opt) with
| None -> begin
(let _162_43 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _162_43))
end
| Some (head) -> begin
(let _162_45 = (FStar_Syntax_Print.bv_to_string x)
in (let _162_44 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _162_45 _162_44)))
end)
in (let _162_48 = (let _162_47 = (let _162_46 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (_162_46)))
in FStar_Errors.Error (_162_47))
in (Prims.raise _162_48)))
end))
in (

let s = (let _162_50 = (let _162_49 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _162_49))
in (FStar_TypeChecker_Util.new_uvar env _162_50))
in (match ((FStar_TypeChecker_Rel.try_teq env t s)) with
| Some (g) -> begin
(

let _61_48 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in s)
end
| _61_51 -> begin
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

let _61_59 = lc
in {FStar_Syntax_Syntax.eff_name = _61_59.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _61_59.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _61_61 -> (match (()) with
| () -> begin
(let _162_64 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _162_64 t))
end))}))


let memo_tk : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun e t -> (

let _61_64 = (FStar_ST.op_Colon_Equals e.FStar_Syntax_Syntax.tk (Some (t.FStar_Syntax_Syntax.n)))
in e))


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let should_return = (fun t -> (match ((let _162_79 = (FStar_Syntax_Subst.compress t)
in _162_79.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_61_73, c) -> begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(

let t = (FStar_All.pipe_left FStar_Syntax_Util.unrefine (FStar_Syntax_Util.comp_result c))
in (match ((let _162_80 = (FStar_Syntax_Subst.compress t)
in _162_80.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (_61_81) -> begin
false
end
| _61_84 -> begin
true
end))
end else begin
false
end
end
| _61_86 -> begin
true
end))
in (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _162_81 = if ((not ((should_return t))) || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _162_81))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _61_115 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(let _162_82 = (memo_tk e t)
in ((_162_82), (lc), (guard)))
end
| Some (t') -> begin
(

let _61_96 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _162_84 = (FStar_Syntax_Print.term_to_string t)
in (let _162_83 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _162_84 _162_83)))
end else begin
()
end
in (

let _61_100 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_61_100) with
| (e, lc) -> begin
(

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _61_104 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_61_104) with
| (e, g) -> begin
(

let _61_105 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _162_88 = (FStar_Syntax_Print.term_to_string t)
in (let _162_87 = (FStar_Syntax_Print.term_to_string t')
in (let _162_86 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (let _162_85 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_Util.print4 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n" _162_88 _162_87 _162_86 _162_85)))))
end else begin
()
end
in (

let msg = if (FStar_TypeChecker_Rel.is_trivial g) then begin
None
end else begin
(FStar_All.pipe_left (fun _162_98 -> Some (_162_98)) (FStar_TypeChecker_Err.subtyping_failed env t t'))
end
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let _61_111 = (FStar_TypeChecker_Util.strengthen_precondition msg env e lc g)
in (match (_61_111) with
| (lc, g) -> begin
(let _162_99 = (memo_tk e t')
in ((_162_99), ((set_lcomp_result lc t')), (g)))
end)))))
end)))
end)))
end)
in (match (_61_115) with
| (e, lc, g) -> begin
(

let _61_116 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _162_100 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _162_100))
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

let _61_126 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_61_126) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _61_131 -> (match (_61_131) with
| (e, c) -> begin
(

let expected_c_opt = (match (copt) with
| Some (_61_133) -> begin
copt
end
| None -> begin
if (((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Syntax_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) || (((FStar_Options.ml_ish ()) && env.FStar_TypeChecker_Env.lax) && (not ((FStar_Syntax_Util.is_pure_or_ghost_comp c))))) then begin
(let _162_113 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (_162_113))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
if (FStar_Syntax_Util.is_pure_comp c) then begin
(let _162_114 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (_162_114))
end else begin
if (FStar_Syntax_Util.is_pure_or_ghost_comp c) then begin
(let _162_115 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (_162_115))
end else begin
None
end
end
end
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _162_116 = (norm_c env c)
in ((e), (_162_116), (FStar_TypeChecker_Rel.trivial_guard)))
end
| Some (expected_c) -> begin
(

let _61_140 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _162_119 = (FStar_Syntax_Print.term_to_string e)
in (let _162_118 = (FStar_Syntax_Print.comp_to_string c)
in (let _162_117 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _162_119 _162_118 _162_117))))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _61_143 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _162_122 = (FStar_Syntax_Print.term_to_string e)
in (let _162_121 = (FStar_Syntax_Print.comp_to_string c)
in (let _162_120 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _162_122 _162_121 _162_120))))
end else begin
()
end
in (

let _61_149 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_61_149) with
| (e, _61_147, g) -> begin
(

let g = (let _162_123 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _162_123 "could not prove post-condition" g))
in (

let _61_151 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _162_125 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _162_124 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _162_125 _162_124)))
end else begin
()
end
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e (FStar_Syntax_Util.comp_effect_name c) (FStar_Syntax_Util.comp_effect_name expected_c) (FStar_Syntax_Util.comp_result c))
in ((e), (expected_c), (g)))))
end)))))
end))
end))


let no_logical_guard = (fun env _61_158 -> (match (_61_158) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
((te), (kt), (f))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _162_131 = (let _162_130 = (let _162_129 = (FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term env f)
in (let _162_128 = (FStar_TypeChecker_Env.get_range env)
in ((_162_129), (_162_128))))
in FStar_Errors.Error (_162_130))
in (Prims.raise _162_131))
end)
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _162_134 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _162_134))
end))


let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = _61_184; FStar_Syntax_Syntax.effect_name = _61_182; FStar_Syntax_Syntax.result_typ = _61_180; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, _61_174))::[]; FStar_Syntax_Syntax.flags = _61_171}) -> begin
(

let pat_vars = (let _162_139 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env pats)
in (FStar_Syntax_Free.names _162_139))
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _61_191 -> (match (_61_191) with
| (b, _61_190) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _61_195) -> begin
(let _162_142 = (let _162_141 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" _162_141))
in (FStar_Errors.warn t.FStar_Syntax_Syntax.pos _162_142))
end))
end
| _61_199 -> begin
(failwith "Impossible")
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

let _61_206 = env
in {FStar_TypeChecker_Env.solver = _61_206.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_206.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_206.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_206.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_206.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_206.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_206.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_206.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _61_206.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _61_206.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _61_206.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _61_206.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _61_206.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _61_206.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _61_206.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _61_206.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _61_206.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _61_206.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _61_206.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _61_206.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_206.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _61_206.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _61_206.FStar_TypeChecker_Env.qname_and_index})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _61_218 -> (match (_61_218) with
| (b, _61_217) -> begin
(

let t = (let _162_156 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _162_156))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _61_227 -> begin
(let _162_157 = (FStar_Syntax_Syntax.bv_to_name b)
in (_162_157)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let _61_233 = (FStar_Syntax_Util.head_and_args dec)
in (match (_61_233) with
| (head, _61_232) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _61_237 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let cflags = (FStar_Syntax_Util.comp_flags c)
in (match ((FStar_All.pipe_right cflags (FStar_List.tryFind (fun uu___335 -> (match (uu___335) with
| FStar_Syntax_Syntax.DECREASES (_61_241) -> begin
true
end
| _61_244 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _61_249 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| _61_254 -> begin
(mk_lex_list xs)
end))
end)))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun _61_259 -> (match (_61_259) with
| (l, t) -> begin
(match ((let _162_163 = (FStar_Syntax_Subst.compress t)
in _162_163.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _61_266 -> (match (_61_266) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _162_167 = (let _162_166 = (let _162_165 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_162_165))
in (FStar_Syntax_Syntax.new_bv _162_166 x.FStar_Syntax_Syntax.sort))
in ((_162_167), (imp)))
end else begin
((x), (imp))
end
end))))
in (

let _61_270 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_61_270) with
| (formals, c) -> begin
(

let dec = (decreases_clause formals c)
in (

let precedes = (let _162_171 = (let _162_170 = (FStar_Syntax_Syntax.as_arg dec)
in (let _162_169 = (let _162_168 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_162_168)::[])
in (_162_170)::_162_169))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _162_171 None r))
in (

let _61_277 = (FStar_Util.prefix formals)
in (match (_61_277) with
| (bs, (last, imp)) -> begin
(

let last = (

let _61_278 = last
in (let _162_172 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _61_278.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _61_278.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _162_172}))
in (

let refined_formals = (FStar_List.append bs ((((last), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (

let _61_283 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _162_175 = (FStar_Syntax_Print.lbname_to_string l)
in (let _162_174 = (FStar_Syntax_Print.term_to_string t)
in (let _162_173 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _162_175 _162_174 _162_173))))
end else begin
()
end
in ((l), (t'))))))
end))))
end)))
end
| _61_286 -> begin
(Prims.raise (FStar_Errors.Error ((("Annotated type of \'let rec\' must be an arrow"), (t.FStar_Syntax_Syntax.pos)))))
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end)
end)


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let _61_289 = env
in {FStar_TypeChecker_Env.solver = _61_289.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_289.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_289.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_289.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_289.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_289.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_289.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_289.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _61_289.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _61_289.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _61_289.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _61_289.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _61_289.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _61_289.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _61_289.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _61_289.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _61_289.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _61_289.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _61_289.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _61_289.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_289.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _61_289.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _61_289.FStar_TypeChecker_Env.qname_and_index}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (

let _61_294 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _162_245 = (let _162_243 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _162_243))
in (let _162_244 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _162_245 _162_244)))
end else begin
()
end
in (

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_61_298) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let _61_339 = (tc_tot_or_gtot_term env e)
in (match (_61_339) with
| (e, c, g) -> begin
(

let g = (

let _61_340 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _61_340.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _61_340.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _61_340.FStar_TypeChecker_Env.implicits})
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let _61_350 = (FStar_Syntax_Util.type_u ())
in (match (_61_350) with
| (t, u) -> begin
(

let _61_354 = (tc_check_tot_or_gtot_term env e t)
in (match (_61_354) with
| (e, c, g) -> begin
(

let _61_361 = (

let _61_358 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_61_358) with
| (env, _61_357) -> begin
(tc_pats env pats)
end))
in (match (_61_361) with
| (pats, g') -> begin
(

let g' = (

let _61_362 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _61_362.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _61_362.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _61_362.FStar_TypeChecker_Env.implicits})
in (let _162_250 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_pattern (pats))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _162_249 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((_162_250), (c), (_162_249)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _162_251 = (FStar_Syntax_Subst.compress e)
in _162_251.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_61_371, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _61_378; FStar_Syntax_Syntax.lbtyp = _61_376; FStar_Syntax_Syntax.lbeff = _61_374; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _61_389 = (let _162_252 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _162_252 e1))
in (match (_61_389) with
| (e1, c1, g1) -> begin
(

let _61_393 = (tc_term env e2)
in (match (_61_393) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((None), (c2)))
in (

let e = (let _162_257 = (let _162_256 = (let _162_255 = (let _162_254 = (let _162_253 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_TypeChecker_Common.t_unit), (e1)))
in (_162_253)::[])
in ((false), (_162_254)))
in ((_162_255), (e2)))
in FStar_Syntax_Syntax.Tm_let (_162_256))
in (FStar_Syntax_Syntax.mk _162_257 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _162_258 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e), (c), (_162_258))))))
end))
end))
end
| _61_398 -> begin
(

let _61_402 = (tc_term env e)
in (match (_61_402) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (_61_406)) -> begin
(tc_term env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let _61_417 = (tc_term env e)
in (match (_61_417) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (m)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _61_423) -> begin
(

let _61_429 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_61_429) with
| (env0, _61_428) -> begin
(

let _61_434 = (tc_comp env0 expected_c)
in (match (_61_434) with
| (expected_c, _61_432, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (

let _61_439 = (let _162_259 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term _162_259 e))
in (match (_61_439) with
| (e, c', g') -> begin
(

let _61_443 = (let _162_261 = (let _162_260 = (c'.FStar_Syntax_Syntax.comp ())
in ((e), (_162_260)))
in (check_expected_effect env0 (Some (expected_c)) _162_261))
in (match (_61_443) with
| (e, expected_c, g'') -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t_res)), (Some ((FStar_Syntax_Util.comp_effect_name expected_c)))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let lc = (FStar_Syntax_Util.lcomp_of_comp expected_c)
in (

let f = (let _162_262 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _162_262))
in (

let _61_450 = (comp_check_expected_typ env e lc)
in (match (_61_450) with
| (e, c, f2) -> begin
(let _162_263 = (FStar_TypeChecker_Rel.conj_guard f f2)
in ((e), (c), (_162_263)))
end)))))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _61_455) -> begin
(

let _61_460 = (FStar_Syntax_Util.type_u ())
in (match (_61_460) with
| (k, u) -> begin
(

let _61_465 = (tc_check_tot_or_gtot_term env t k)
in (match (_61_465) with
| (t, _61_463, f) -> begin
(

let _61_469 = (let _162_264 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _162_264 e))
in (match (_61_469) with
| (e, c, g) -> begin
(

let _61_473 = (let _162_268 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _61_470 -> (match (()) with
| () -> begin
FStar_TypeChecker_Err.ill_kinded_type
end)))) _162_268 e c f))
in (match (_61_473) with
| (c, f) -> begin
(

let _61_477 = (let _162_269 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t)), (Some (c.FStar_Syntax_Syntax.eff_name))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _162_269 c))
in (match (_61_477) with
| (e, c, f2) -> begin
(let _162_271 = (let _162_270 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _162_270))
in ((e), (c), (_162_271)))
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

let _61_513 = (FStar_Syntax_Util.head_and_args top)
in (match (_61_513) with
| (unary_op, _61_512) -> begin
(

let head = (let _162_272 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (Prims.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) None _162_272))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), (rest)))) None top.FStar_Syntax_Syntax.pos)
in (tc_term env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _61_521; FStar_Syntax_Syntax.pos = _61_519; FStar_Syntax_Syntax.vars = _61_517}, ((e, aqual))::[]) -> begin
(

let _61_531 = if (FStar_Option.isSome aqual) then begin
(FStar_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end else begin
()
end
in (

let _61_540 = (

let _61_536 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_61_536) with
| (env0, _61_535) -> begin
(tc_term env0 e)
end))
in (match (_61_540) with
| (e, c, g) -> begin
(

let _61_544 = (FStar_Syntax_Util.head_and_args top)
in (match (_61_544) with
| (reify_op, _61_543) -> begin
(

let u_c = (

let _61_550 = (tc_term env c.FStar_Syntax_Syntax.res_typ)
in (match (_61_550) with
| (_61_546, c, _61_549) -> begin
(match ((let _162_273 = (FStar_Syntax_Subst.compress c.FStar_Syntax_Syntax.res_typ)
in _162_273.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| _61_554 -> begin
(failwith "Unexpected result type of computation")
end)
end))
in (

let repr = (FStar_TypeChecker_Util.reify_comp env c u_c)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e), (aqual)))::[])))) (Some (repr.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let c = (let _162_274 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right _162_274 FStar_Syntax_Util.lcomp_of_comp))
in (

let _61_562 = (comp_check_expected_typ env e c)
in (match (_61_562) with
| (e, c, g') -> begin
(let _162_275 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), (c), (_162_275)))
end))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.tk = _61_568; FStar_Syntax_Syntax.pos = _61_566; FStar_Syntax_Syntax.vars = _61_564}, ((e, aqual))::[]) -> begin
(

let _61_579 = if (FStar_Option.isSome aqual) then begin
(FStar_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end else begin
()
end
in (

let no_reflect = (fun _61_582 -> (match (()) with
| () -> begin
(let _162_280 = (let _162_279 = (let _162_278 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((_162_278), (e.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (_162_279))
in (Prims.raise _162_280))
end))
in (

let _61_586 = (FStar_Syntax_Util.head_and_args top)
in (match (_61_586) with
| (reflect_op, _61_585) -> begin
(match ((FStar_TypeChecker_Env.effect_decl_opt env l)) with
| None -> begin
(no_reflect ())
end
| Some (ed) -> begin
if (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers FStar_Syntax_Syntax.contains_reflectable))) then begin
(no_reflect ())
end else begin
(

let _61_592 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_61_592) with
| (env_no_ex, topt) -> begin
(

let _61_620 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (let _162_286 = (let _162_285 = (let _162_284 = (let _162_283 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _162_282 = (let _162_281 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (_162_281)::[])
in (_162_283)::_162_282))
in ((repr), (_162_284)))
in FStar_Syntax_Syntax.Tm_app (_162_285))
in (FStar_Syntax_Syntax.mk _162_286 None top.FStar_Syntax_Syntax.pos))
in (

let _61_600 = (let _162_288 = (let _162_287 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _162_287 Prims.fst))
in (tc_tot_or_gtot_term _162_288 t))
in (match (_61_600) with
| (t, _61_598, g) -> begin
(match ((let _162_289 = (FStar_Syntax_Subst.compress t)
in _162_289.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_61_602, ((res, _61_609))::((wp, _61_605))::[]) -> begin
((t), (res), (wp), (g))
end
| _61_615 -> begin
(failwith "Impossible")
end)
end)))))
in (match (_61_620) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let _61_634 = (

let _61_624 = (tc_tot_or_gtot_term env_no_ex e)
in (match (_61_624) with
| (e, c, g) -> begin
(

let _61_625 = if (let _162_290 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation _162_290)) then begin
(FStar_TypeChecker_Err.add_errors env (((("Expected Tot, got a GTot computation"), (e.FStar_Syntax_Syntax.pos)))::[]))
end else begin
()
end
in (match ((FStar_TypeChecker_Rel.try_teq env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)) with
| None -> begin
(

let _61_628 = (let _162_295 = (let _162_294 = (let _162_293 = (let _162_292 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _162_291 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" _162_292 _162_291)))
in ((_162_293), (e.FStar_Syntax_Syntax.pos)))
in (_162_294)::[])
in (FStar_TypeChecker_Err.add_errors env _162_295))
in (let _162_296 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e), (_162_296))))
end
| Some (g') -> begin
(let _162_298 = (let _162_297 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' _162_297))
in ((e), (_162_298)))
end))
end))
in (match (_61_634) with
| (e, g) -> begin
(

let c = (let _162_304 = (let _162_303 = (let _162_302 = (let _162_299 = (env.FStar_TypeChecker_Env.universe_of env res_typ)
in (_162_299)::[])
in (let _162_301 = (let _162_300 = (FStar_Syntax_Syntax.as_arg wp)
in (_162_300)::[])
in {FStar_Syntax_Syntax.comp_univs = _162_302; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = _162_301; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp _162_303))
in (FStar_All.pipe_right _162_304 FStar_Syntax_Util.lcomp_of_comp))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e), (aqual)))::[])))) (Some (res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let _61_640 = (comp_check_expected_typ env e c)
in (match (_61_640) with
| (e, c, g') -> begin
(let _162_305 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e), (c), (_162_305)))
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

let env = (let _162_307 = (let _162_306 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _162_306 Prims.fst))
in (FStar_All.pipe_right _162_307 instantiate_both))
in (

let _61_647 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _162_309 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _162_308 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _162_309 _162_308)))
end else begin
()
end
in (

let _61_652 = (tc_term (no_inst env) head)
in (match (_61_652) with
| (head, chead, g_head) -> begin
(

let _61_656 = if ((not (env.FStar_TypeChecker_Env.lax)) && (FStar_TypeChecker_Util.short_circuit_head head)) then begin
(let _162_310 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _162_310))
end else begin
(let _162_311 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _162_311))
end
in (match (_61_656) with
| (e, c, g) -> begin
(

let _61_657 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _162_312 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _162_312))
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

let _61_663 = (comp_check_expected_typ env0 e c)
in (match (_61_663) with
| (e, c, g') -> begin
(

let gimp = (match ((let _162_313 = (FStar_Syntax_Subst.compress head)
in _162_313.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _61_666) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e), (c.FStar_Syntax_Syntax.res_typ), (head.FStar_Syntax_Syntax.pos))
in (

let _61_670 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _61_670.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _61_670.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _61_670.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _61_673 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (

let gres = (let _162_314 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _162_314))
in (

let _61_676 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _162_316 = (FStar_Syntax_Print.term_to_string e)
in (let _162_315 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" _162_316 _162_315)))
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

let _61_684 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_61_684) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let _61_689 = (tc_term env1 e1)
in (match (_61_689) with
| (e1, c1, g1) -> begin
(

let _61_700 = (match (topt) with
| Some (t) -> begin
((env), (t))
end
| None -> begin
(

let _61_696 = (FStar_Syntax_Util.type_u ())
in (match (_61_696) with
| (k, _61_695) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _162_317 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in ((_162_317), (res_t))))
end))
end)
in (match (_61_700) with
| (env_branches, res_t) -> begin
(

let _61_701 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _162_318 = (FStar_Syntax_Print.term_to_string res_t)
in (FStar_Util.print1 "Tm_match: expected type of branches is %s\n" _162_318))
end else begin
()
end
in (

let guard_x = (FStar_Syntax_Syntax.new_bv (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let _61_719 = (

let _61_716 = (FStar_List.fold_right (fun _61_710 _61_713 -> (match (((_61_710), (_61_713))) with
| ((_61_706, f, c, g), (caccum, gaccum)) -> begin
(let _162_321 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (_162_321)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_61_716) with
| (cases, g) -> begin
(let _162_322 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in ((_162_322), (g)))
end))
in (match (_61_719) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (guard_x)), (c_branches)))
in (

let e = (

let mk_match = (fun scrutinee -> (

let scrutinee = (FStar_TypeChecker_Util.maybe_lift env scrutinee c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let branches = (FStar_All.pipe_right t_eqns (FStar_List.map (fun _61_733 -> (match (_61_733) with
| ((pat, wopt, br), _61_729, lc, _61_732) -> begin
(let _162_326 = (FStar_TypeChecker_Util.maybe_lift env br lc.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name lc.FStar_Syntax_Syntax.res_typ)
in ((pat), (wopt), (_162_326)))
end))))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (Some (cres.FStar_Syntax_Syntax.eff_name))))) None e.FStar_Syntax_Syntax.pos)))))
in if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c1.FStar_Syntax_Syntax.eff_name) then begin
(mk_match e1)
end else begin
(

let e_match = (let _162_327 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match _162_327))
in (

let lb = (let _162_328 = (FStar_TypeChecker_Env.norm_eff_name env c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = _162_328; FStar_Syntax_Syntax.lbdef = e1})
in (

let e = (let _162_333 = (let _162_332 = (let _162_331 = (let _162_330 = (let _162_329 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (_162_329)::[])
in (FStar_Syntax_Subst.close _162_330 e_match))
in ((((false), ((lb)::[]))), (_162_331)))
in FStar_Syntax_Syntax.Tm_let (_162_332))
in (FStar_Syntax_Syntax.mk _162_333 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ))))
end)
in (

let _61_740 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _162_336 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _162_335 = (let _162_334 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _162_334))
in (FStar_Util.print2 "(%s) comp type = %s\n" _162_336 _162_335)))
end else begin
()
end
in (let _162_337 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e), (cres), (_162_337))))))
end)))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_61_752); FStar_Syntax_Syntax.lbunivs = _61_750; FStar_Syntax_Syntax.lbtyp = _61_748; FStar_Syntax_Syntax.lbeff = _61_746; FStar_Syntax_Syntax.lbdef = _61_744})::[]), _61_758) -> begin
(

let _61_761 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _162_338 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _162_338))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _61_765), _61_768) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_61_783); FStar_Syntax_Syntax.lbunivs = _61_781; FStar_Syntax_Syntax.lbtyp = _61_779; FStar_Syntax_Syntax.lbeff = _61_777; FStar_Syntax_Syntax.lbdef = _61_775})::_61_773), _61_789) -> begin
(

let _61_792 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _162_339 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _162_339))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _61_796), _61_799) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let _61_813 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_61_813) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _162_353 = (let _162_352 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _162_352))
in FStar_Util.Inr (_162_353))
end
in (

let is_data_ctor = (fun uu___336 -> (match (uu___336) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _61_823 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _162_359 = (let _162_358 = (let _162_357 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _162_356 = (FStar_TypeChecker_Env.get_range env)
in ((_162_357), (_162_356))))
in FStar_Errors.Error (_162_358))
in (Prims.raise _162_359))
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
(let _162_361 = (let _162_360 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" _162_360))
in (failwith _162_361))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (match ((let _162_362 = (FStar_Syntax_Subst.compress t1)
in _162_362.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_61_834) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _61_837 -> begin
(

let imp = (("uvar in term"), (env), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let _61_839 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _61_839.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _61_839.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _61_839.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _61_854 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(

let _61_847 = (FStar_Syntax_Util.type_u ())
in (match (_61_847) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
end))
end
| Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end)
in (match (_61_854) with
| (t, _61_852, g0) -> begin
(

let _61_859 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (_61_859) with
| (e, _61_857, g1) -> begin
(let _162_365 = (let _162_363 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right _162_363 FStar_Syntax_Util.lcomp_of_comp))
in (let _162_364 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e), (_162_365), (_162_364))))
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

let _61_863 = x
in {FStar_Syntax_Syntax.ppname = _61_863.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _61_863.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let _61_869 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_61_869) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _162_367 = (let _162_366 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _162_366))
in FStar_Util.Inr (_162_367))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _61_876; FStar_Syntax_Syntax.pos = _61_874; FStar_Syntax_Syntax.vars = _61_872}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let _61_886 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_61_886) with
| (us', t) -> begin
(

let _61_893 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _162_370 = (let _162_369 = (let _162_368 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (_162_368)))
in FStar_Errors.Error (_162_369))
in (Prims.raise _162_370))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _61_892 -> begin
(failwith "Impossible")
end)) us' us)
end
in (

let fv' = (

let _61_895 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _61_897 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _61_897.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _61_897.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _61_895.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _61_895.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _162_373 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _162_373 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let _61_905 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_61_905) with
| (us, t) -> begin
(

let _61_906 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Range"))) then begin
(let _162_383 = (let _162_374 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Syntax_Print.lid_to_string _162_374))
in (let _162_382 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _162_381 = (let _162_376 = (let _162_375 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.range_of_lid _162_375))
in (FStar_Range.string_of_range _162_376))
in (let _162_380 = (let _162_378 = (let _162_377 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.range_of_lid _162_377))
in (FStar_Range.string_of_use_range _162_378))
in (let _162_379 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print5 "Lookup up fvar %s at location %s (lid range = %s, %s); got type %s" _162_383 _162_382 _162_381 _162_380 _162_379))))))
end else begin
()
end
in (

let fv' = (

let _61_908 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _61_910 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _61_910.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _61_910.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _61_908.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _61_908.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _162_384 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _162_384 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
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

let _61_924 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_61_924) with
| (bs, c) -> begin
(

let env0 = env
in (

let _61_929 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_61_929) with
| (env, _61_928) -> begin
(

let _61_934 = (tc_binders env bs)
in (match (_61_934) with
| (bs, env, g, us) -> begin
(

let _61_938 = (tc_comp env c)
in (match (_61_938) with
| (c, uc, f) -> begin
(

let e = (

let _61_939 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _61_939.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _61_939.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _61_939.FStar_Syntax_Syntax.vars})
in (

let _61_942 = (check_smt_pat env e bs c)
in (

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _162_385 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _162_385))
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

let _61_958 = (let _162_387 = (let _162_386 = (FStar_Syntax_Syntax.mk_binder x)
in (_162_386)::[])
in (FStar_Syntax_Subst.open_term _162_387 phi))
in (match (_61_958) with
| (x, phi) -> begin
(

let env0 = env
in (

let _61_963 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_61_963) with
| (env, _61_962) -> begin
(

let _61_968 = (let _162_388 = (FStar_List.hd x)
in (tc_binder env _162_388))
in (match (_61_968) with
| (x, env, f1, u) -> begin
(

let _61_969 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _162_391 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _162_390 = (FStar_Syntax_Print.term_to_string phi)
in (let _162_389 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _162_391 _162_390 _162_389))))
end else begin
()
end
in (

let _61_974 = (FStar_Syntax_Util.type_u ())
in (match (_61_974) with
| (t_phi, _61_973) -> begin
(

let _61_979 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_61_979) with
| (phi, _61_977, f2) -> begin
(

let e = (

let _61_980 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _61_980.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _61_980.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _61_980.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _162_392 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _162_392))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _61_988) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (

let _61_994 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _162_393 = (FStar_Syntax_Print.term_to_string (

let _61_992 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))); FStar_Syntax_Syntax.tk = _61_992.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _61_992.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _61_992.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _162_393))
end else begin
()
end
in (

let _61_998 = (FStar_Syntax_Subst.open_term bs body)
in (match (_61_998) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _61_1000 -> begin
(let _162_396 = (let _162_395 = (FStar_Syntax_Print.term_to_string top)
in (let _162_394 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" _162_395 _162_394)))
in (failwith _162_396))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_61_1005) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_61_1008, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_61_1013, Some (_61_1015)) -> begin
(failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (_61_1020) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_61_1023) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_61_1026) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_61_1030) -> begin
FStar_TypeChecker_Common.t_range
end
| _61_1033 -> begin
(Prims.raise (FStar_Errors.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _61_1039) -> begin
(

let _61_1044 = (FStar_Syntax_Util.type_u ())
in (match (_61_1044) with
| (k, u) -> begin
(

let _61_1049 = (tc_check_tot_or_gtot_term env t k)
in (match (_61_1049) with
| (t, _61_1047, g) -> begin
(let _162_401 = (FStar_Syntax_Syntax.mk_Total' t (Some (u)))
in ((_162_401), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t, _61_1052) -> begin
(

let _61_1057 = (FStar_Syntax_Util.type_u ())
in (match (_61_1057) with
| (k, u) -> begin
(

let _61_1062 = (tc_check_tot_or_gtot_term env t k)
in (match (_61_1062) with
| (t, _61_1060, g) -> begin
(let _162_402 = (FStar_Syntax_Syntax.mk_GTotal' t (Some (u)))
in ((_162_402), (u), (g)))
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

let tc = (let _162_404 = (let _162_403 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_162_403)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _162_404 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let _61_1074 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_61_1074) with
| (tc, _61_1072, f) -> begin
(

let _61_1077 = (FStar_Syntax_Util.head_and_args tc)
in (match (_61_1077) with
| (head, args) -> begin
(

let comp_univs = (match ((let _162_405 = (FStar_Syntax_Subst.compress head)
in _162_405.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (_61_1079, us) -> begin
us
end
| _61_1084 -> begin
[]
end)
in (

let _61_1089 = (FStar_Syntax_Util.head_and_args tc)
in (match (_61_1089) with
| (_61_1087, args) -> begin
(

let _61_1092 = (let _162_407 = (FStar_List.hd args)
in (let _162_406 = (FStar_List.tl args)
in ((_162_407), (_162_406))))
in (match (_61_1092) with
| (res, args) -> begin
(

let _61_1108 = (let _162_409 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___337 -> (match (uu___337) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _61_1099 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_61_1099) with
| (env, _61_1098) -> begin
(

let _61_1104 = (tc_tot_or_gtot_term env e)
in (match (_61_1104) with
| (e, _61_1102, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e)), (g))
end))
end))
end
| f -> begin
((f), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right _162_409 FStar_List.unzip))
in (match (_61_1108) with
| (flags, guards) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (Prims.fst res))
in (

let c = (FStar_Syntax_Syntax.mk_Comp (

let _61_1110 = c
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = _61_1110.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _61_1110.FStar_Syntax_Syntax.flags}))
in (

let u_c = (match ((FStar_TypeChecker_Util.effect_repr env c u)) with
| None -> begin
u
end
| Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end)
in (let _162_410 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((c), (u_c), (_162_410))))))
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
| FStar_Syntax_Syntax.U_bvar (_61_1123) -> begin
(failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _162_415 = (aux u)
in FStar_Syntax_Syntax.U_succ (_162_415))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _162_416 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_162_416))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
u
end)))
in if env.FStar_TypeChecker_Env.lax_universes then begin
FStar_Syntax_Syntax.U_zero
end else begin
(match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _162_417 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _162_417 Prims.snd))
end
| _61_1138 -> begin
(aux u)
end)
end))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _162_426 = (let _162_425 = (let _162_424 = (FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function env msg t top)
in ((_162_424), (top.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (_162_425))
in (Prims.raise _162_426)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun _61_1156 bs bs_expected -> (match (_61_1156) with
| (env, out, g, subst) -> begin
(match (((bs), (bs_expected))) with
| ([], []) -> begin
((env), ((FStar_List.rev out)), (None), (g), (subst))
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
(

let _61_1187 = (match (((imp), (imp'))) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _162_443 = (let _162_442 = (let _162_441 = (let _162_439 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _162_439))
in (let _162_440 = (FStar_Syntax_Syntax.range_of_bv hd)
in ((_162_441), (_162_440))))
in FStar_Errors.Error (_162_442))
in (Prims.raise _162_443))
end
| _61_1186 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _61_1204 = (match ((let _162_444 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _162_444.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| _61_1192 -> begin
(

let _61_1193 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _162_445 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _162_445))
end else begin
()
end
in (

let _61_1199 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_61_1199) with
| (t, _61_1197, g1) -> begin
(

let g2 = (let _162_447 = (FStar_TypeChecker_Env.get_range env)
in (let _162_446 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _162_447 "Type annotation on parameter incompatible with the expected type" _162_446)))
in (

let g = (let _162_448 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _162_448))
in ((t), (g))))
end)))
end)
in (match (_61_1204) with
| (t, g) -> begin
(

let hd = (

let _61_1205 = hd
in {FStar_Syntax_Syntax.ppname = _61_1205.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _61_1205.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env = (push_binding env b)
in (

let subst = (let _162_449 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _162_449))
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

let _61_1226 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _61_1225 -> begin
(failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (

let _61_1233 = (tc_binders env bs)
in (match (_61_1233) with
| (bs, envbody, g, _61_1232) -> begin
(

let _61_1251 = (match ((let _162_456 = (FStar_Syntax_Subst.compress body)
in _162_456.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _61_1238) -> begin
(

let _61_1245 = (tc_comp envbody c)
in (match (_61_1245) with
| (c, _61_1243, g') -> begin
(let _162_457 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((Some (c)), (body), (_162_457)))
end))
end
| _61_1247 -> begin
((None), (body), (g))
end)
in (match (_61_1251) with
| (copt, body, g) -> begin
((None), (bs), ([]), (copt), (envbody), (body), (g))
end))
end)))
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm t -> (match ((let _162_462 = (FStar_Syntax_Subst.compress t)
in _162_462.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let _61_1278 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _61_1277 -> begin
(failwith "Impossible")
end)
in (

let _61_1285 = (tc_binders env bs)
in (match (_61_1285) with
| (bs, envbody, g, _61_1284) -> begin
(

let _61_1289 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_61_1289) with
| (envbody, _61_1288) -> begin
((Some (((t), (true)))), (bs), ([]), (None), (envbody), (body), (g))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _61_1292) -> begin
(

let _61_1303 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_61_1303) with
| (_61_1296, bs, bs', copt, env, body, g) -> begin
((Some (((t), (false)))), (bs), (bs'), (copt), (env), (body), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _61_1310 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_61_1310) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun _61_1321 c_expected -> (match (_61_1321) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _162_473 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in ((env), (bs), (guard), (_162_473)))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (let _162_474 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _162_474))
in (let _162_475 = (FStar_Syntax_Subst.subst_comp subst c)
in ((env), (bs), (guard), (_162_475))))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(

let c = (FStar_Syntax_Subst.subst_comp subst c_expected)
in if (FStar_Syntax_Util.is_named_tot c) then begin
(

let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _61_1342 = (check_binders env more_bs bs_expected)
in (match (_61_1342) with
| (env, bs', more, guard', subst) -> begin
(let _162_477 = (let _162_476 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env), ((FStar_List.append bs bs')), (more), (_162_476), (subst)))
in (handle_more _162_477 c_expected))
end))
end
| _61_1344 -> begin
(let _162_479 = (let _162_478 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _162_478))
in (fail _162_479 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _162_480 = (check_binders env bs bs_expected)
in (handle_more _162_480 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let _61_1350 = envbody
in {FStar_TypeChecker_Env.solver = _61_1350.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_1350.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_1350.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_1350.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_1350.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_1350.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_1350.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_1350.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _61_1350.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _61_1350.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _61_1350.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _61_1350.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _61_1350.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _61_1350.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _61_1350.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _61_1350.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _61_1350.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _61_1350.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _61_1350.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _61_1350.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_1350.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _61_1350.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _61_1350.FStar_TypeChecker_Env.qname_and_index})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _61_1355 _61_1358 -> (match (((_61_1355), (_61_1358))) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _61_1364 = (let _162_490 = (let _162_489 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _162_489 Prims.fst))
in (tc_term _162_490 t))
in (match (_61_1364) with
| (t, _61_1361, _61_1363) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l (([]), (t)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _162_491 = (FStar_Syntax_Syntax.mk_binder (

let _61_1368 = x
in {FStar_Syntax_Syntax.ppname = _61_1368.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _61_1368.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_162_491)::letrec_binders)
end
| _61_1371 -> begin
letrec_binders
end)
in ((env), (lb))))
end))
end)) ((envbody), ([])))))))
in (

let _61_1377 = (check_actuals_against_formals env bs bs_expected)
in (match (_61_1377) with
| (envbody, bs, g, c) -> begin
(

let _61_1380 = if (FStar_TypeChecker_Env.should_verify env) then begin
(mk_letrec_env envbody bs c)
end else begin
((envbody), ([]))
end
in (match (_61_1380) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in ((Some (((t), (false)))), (bs), (letrecs), (Some (c)), (envbody), (body), (g)))
end))
end))))
end))
end
| _61_1383 -> begin
if (not (norm)) then begin
(let _162_492 = (unfold_whnf env t)
in (as_function_typ true _162_492))
end else begin
(

let _61_1393 = (expected_function_typ env None body)
in (match (_61_1393) with
| (_61_1385, bs, _61_1388, c_opt, envbody, body, g) -> begin
((Some (((t), (false)))), (bs), ([]), (c_opt), (envbody), (body), (g))
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let _61_1397 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_61_1397) with
| (env, topt) -> begin
(

let _61_1401 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _162_493 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _162_493 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (

let _61_1410 = (expected_function_typ env topt body)
in (match (_61_1410) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let _61_1416 = (tc_term (

let _61_1411 = envbody
in {FStar_TypeChecker_Env.solver = _61_1411.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_1411.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_1411.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_1411.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_1411.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_1411.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_1411.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_1411.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _61_1411.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _61_1411.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _61_1411.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _61_1411.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _61_1411.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _61_1411.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _61_1411.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _61_1411.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _61_1411.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _61_1411.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _61_1411.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_1411.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _61_1411.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _61_1411.FStar_TypeChecker_Env.qname_and_index}) body)
in (match (_61_1416) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _61_1418 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _162_496 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _162_495 = (let _162_494 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _162_494))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _162_496 _162_495)))
end else begin
()
end
in (

let _61_1425 = (let _162_498 = (let _162_497 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body), (_162_497)))
in (check_expected_effect (

let _61_1420 = envbody
in {FStar_TypeChecker_Env.solver = _61_1420.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_1420.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_1420.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_1420.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_1420.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_1420.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_1420.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_1420.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _61_1420.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _61_1420.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _61_1420.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _61_1420.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _61_1420.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _61_1420.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _61_1420.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _61_1420.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _61_1420.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _61_1420.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _61_1420.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _61_1420.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_1420.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _61_1420.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _61_1420.FStar_TypeChecker_Env.qname_and_index}) c_opt _162_498))
in (match (_61_1425) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(let _162_499 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _162_499))
end else begin
(

let guard = (let _162_500 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) _162_500))
in guard)
end
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _162_504 = (let _162_503 = (let _162_502 = (FStar_All.pipe_right (FStar_Util.dflt cbody c_opt) FStar_Syntax_Util.lcomp_of_comp)
in (FStar_All.pipe_right _162_502 (fun _162_501 -> FStar_Util.Inl (_162_501))))
in Some (_162_503))
in (FStar_Syntax_Util.abs bs body _162_504))
in (

let _61_1448 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_61_1437) -> begin
((e), (t), (guard))
end
| _61_1440 -> begin
(

let _61_1443 = if use_teq then begin
(let _162_505 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in ((e), (_162_505)))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_61_1443) with
| (e, guard') -> begin
(let _162_506 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((e), (t), (_162_506)))
end))
end))
end
| None -> begin
((e), (tfun_computed), (guard))
end)
in (match (_61_1448) with
| (e, tfun, guard) -> begin
(

let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (

let _61_1452 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_61_1452) with
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

let _61_1462 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _162_515 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _162_514 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _162_515 _162_514)))
end else begin
()
end
in (

let monadic_application = (fun _61_1469 subst arg_comps_rev arg_rets guard fvs bs -> (match (_61_1469) with
| (head, chead, ghead, cres) -> begin
(

let rt = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _61_1477 = cres
in {FStar_Syntax_Syntax.eff_name = _61_1477.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = rt; FStar_Syntax_Syntax.cflags = _61_1477.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _61_1477.FStar_Syntax_Syntax.comp})
in (

let _61_1508 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun uu___338 -> (match (uu___338) with
| (_61_1485, _61_1487, FStar_Util.Inl (_61_1489)) -> begin
false
end
| (_61_1493, _61_1495, FStar_Util.Inr (c)) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _162_531 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _162_531 cres))
end else begin
(

let _61_1500 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _162_534 = (FStar_Syntax_Print.term_to_string head)
in (let _162_533 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _162_532 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _162_534 _162_533 _162_532))))
end else begin
()
end
in cres)
end
in ((cres), (g))))))
end
| _61_1504 -> begin
(

let g = (let _162_535 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right _162_535 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _162_540 = (let _162_539 = (let _162_538 = (let _162_537 = (let _162_536 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _162_536))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _162_537))
in (FStar_Syntax_Syntax.mk_Total _162_538))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _162_539))
in ((_162_540), (g))))
end)
in (match (_61_1508) with
| (cres, guard) -> begin
(

let _61_1509 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _162_541 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _162_541))
end else begin
()
end
in (

let _61_1534 = (FStar_List.fold_left (fun _61_1514 _61_1520 -> (match (((_61_1514), (_61_1520))) with
| ((args, out_c, monadic), ((e, q), x, c)) -> begin
(match (c) with
| FStar_Util.Inl (eff_name, arg_typ) -> begin
(let _162_546 = (let _162_545 = (let _162_544 = (FStar_TypeChecker_Util.maybe_lift env e eff_name out_c.FStar_Syntax_Syntax.eff_name arg_typ)
in ((_162_544), (q)))
in (_162_545)::args)
in ((_162_546), (out_c), (monadic)))
end
| FStar_Util.Inr (c) -> begin
(

let monadic = (monadic || (not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c))))
in (

let out_c = (FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env None c ((x), (out_c)))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e c.FStar_Syntax_Syntax.eff_name out_c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (((((e), (q)))::args), (out_c), (monadic))))))
end)
end)) (([]), (cres), (false)) arg_comps_rev)
in (match (_61_1534) with
| (args, comp, monadic) -> begin
(

let comp = (FStar_TypeChecker_Util.bind head.FStar_Syntax_Syntax.pos env None chead ((None), (comp)))
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app = if (monadic || (not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp comp)))) then begin
(FStar_TypeChecker_Util.maybe_monadic env app comp.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.res_typ)
end else begin
app
end
in (

let _61_1540 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (_61_1540) with
| (comp, g) -> begin
((app), (comp), (g))
end)))))
end)))
end))))
end))
in (

let rec tc_args = (fun head_info _61_1548 bs args -> (match (_61_1548) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args))) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (_61_1554))))::rest, ((_61_1562, None))::_61_1560) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let t = (check_no_escape (Some (head)) env fvs t)
in (

let _61_1573 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_61_1573) with
| (varg, _61_1571, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst
in (

let arg = (let _162_556 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (_162_556)))
in (let _162_558 = (let _162_557 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst), ((((arg), (None), (FStar_Util.Inl (((FStar_Syntax_Const.effect_Tot_lid), (t))))))::outargs), ((arg)::arg_rets), (_162_557), (fvs)))
in (tc_args head_info _162_558 rest args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
(

let _61_1605 = (match (((aqual), (aq))) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _61_1604 -> begin
(Prims.raise (FStar_Errors.Error ((("Inconsistent implicit qualifier"), (e.FStar_Syntax_Syntax.pos)))))
end)
in (

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let _61_1608 = x
in {FStar_Syntax_Syntax.ppname = _61_1608.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _61_1608.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (

let _61_1611 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _162_559 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _162_559))
end else begin
()
end
in (

let targ = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let _61_1615 = env
in {FStar_TypeChecker_Env.solver = _61_1615.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_1615.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_1615.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_1615.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_1615.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_1615.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_1615.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_1615.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _61_1615.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _61_1615.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _61_1615.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _61_1615.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _61_1615.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _61_1615.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _61_1615.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _61_1615.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _61_1615.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _61_1615.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _61_1615.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _61_1615.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_1615.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _61_1615.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _61_1615.FStar_TypeChecker_Env.qname_and_index})
in (

let _61_1618 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _162_562 = (FStar_Syntax_Print.tag_of_term e)
in (let _162_561 = (FStar_Syntax_Print.term_to_string e)
in (let _162_560 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _162_562 _162_561 _162_560))))
end else begin
()
end
in (

let _61_1623 = (tc_term env e)
in (match (_61_1623) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = ((e), (aq))
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(

let subst = (let _162_563 = (FStar_List.hd bs)
in (maybe_extend_subst subst _162_563 e))
in (tc_args head_info ((subst), ((((arg), (None), (FStar_Util.Inl (((c.FStar_Syntax_Syntax.eff_name), (c.FStar_Syntax_Syntax.res_typ))))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(

let subst = (let _162_564 = (FStar_List.hd bs)
in (maybe_extend_subst subst _162_564 e))
in (tc_args head_info ((subst), ((((arg), (Some (x)), (FStar_Util.Inr (c))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (let _162_565 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _162_565)) then begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _162_566 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _162_566))
in (tc_args head_info ((subst), ((((arg), (Some (newx)), (FStar_Util.Inr (c))))::outargs), ((arg')::arg_rets), (g), (fvs)) rest rest')))
end else begin
(let _162_570 = (let _162_569 = (let _162_568 = (let _162_567 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _162_567))
in (_162_568)::arg_rets)
in ((subst), ((((arg), (Some (x)), (FStar_Util.Inr (c))))::outargs), (_162_569), (g), ((x)::fvs)))
in (tc_args head_info _162_570 rest rest'))
end
end
end))
end))))))))))
end
| (_61_1631, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::_61_1636) -> begin
(

let _61_1643 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (_61_1643) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _162_575 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _162_575 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let _61_1654 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (_61_1654) with
| (bs, cres') -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp cres')))
in (

let _61_1656 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _162_576 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _162_576))
end else begin
()
end
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args)))
end))
end
| _61_1659 when (not (norm)) -> begin
(let _162_577 = (unfold_whnf env tres)
in (aux true _162_577))
end
| _61_1661 -> begin
(let _162_583 = (let _162_582 = (let _162_581 = (let _162_579 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (let _162_578 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _162_579 _162_578)))
in (let _162_580 = (FStar_Syntax_Syntax.argpos arg)
in ((_162_581), (_162_580))))
in FStar_Errors.Error (_162_582))
in (Prims.raise _162_583))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (match ((let _162_588 = (FStar_Syntax_Util.unrefine tf)
in _162_588.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl -> begin
(

let _61_1694 = (tc_term env e)
in (match (_61_1694) with
| (e, c, g_e) -> begin
(

let _61_1698 = (tc_args env tl)
in (match (_61_1698) with
| (args, comps, g_rest) -> begin
(let _162_593 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e), (imp)))::args), ((((e.FStar_Syntax_Syntax.pos), (c)))::comps), (_162_593)))
end))
end))
end))
in (

let _61_1702 = (tc_args env args)
in (match (_61_1702) with
| (args, comps, g_args) -> begin
(

let bs = (let _162_595 = (FStar_All.pipe_right comps (FStar_List.map (fun _61_1706 -> (match (_61_1706) with
| (_61_1704, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks _162_595))
in (

let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _61_1712 -> begin
FStar_Syntax_Util.ml_comp
end)
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _162_610 = (FStar_Syntax_Subst.compress t)
in _162_610.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_61_1718) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _61_1723 -> begin
ml_or_tot
end)
end)
in (

let cres = (let _162_615 = (let _162_614 = (let _162_613 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _162_613 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _162_614))
in (ml_or_tot _162_615 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (

let _61_1727 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _162_618 = (FStar_Syntax_Print.term_to_string head)
in (let _162_617 = (FStar_Syntax_Print.term_to_string tf)
in (let _162_616 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _162_618 _162_617 _162_616))))
end else begin
()
end
in (

let _61_1729 = (let _162_619 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _162_619))
in (

let comp = (let _162_622 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _61_1733 out -> (match (_61_1733) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c ((None), (out)))
end)) ((((head.FStar_Syntax_Syntax.pos), (chead)))::comps) _162_622))
in (let _162_624 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _162_623 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((_162_624), (comp), (_162_623))))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _61_1742 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_61_1742) with
| (bs, c) -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp c)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args))
end))
end
| _61_1745 -> begin
if (not (norm)) then begin
(let _162_625 = (unfold_whnf env tf)
in (check_function_app true _162_625))
end else begin
(let _162_628 = (let _162_627 = (let _162_626 = (FStar_TypeChecker_Err.expected_function_typ env tf)
in ((_162_626), (head.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (_162_627))
in (Prims.raise _162_628))
end
end))
in (let _162_630 = (let _162_629 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _162_629))
in (check_function_app false _162_630))))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let _61_1781 = (FStar_List.fold_left2 (fun _61_1762 _61_1765 _61_1768 -> (match (((_61_1762), (_61_1765), (_61_1768))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(

let _61_1769 = if (aq <> aq') then begin
(Prims.raise (FStar_Errors.Error ((("Inconsistent implicit qualifiers"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _61_1774 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_61_1774) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (let _162_640 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _162_640 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _162_644 = (let _162_642 = (let _162_641 = (FStar_Syntax_Syntax.as_arg e)
in (_162_641)::[])
in (FStar_List.append seen _162_642))
in (let _162_643 = (FStar_TypeChecker_Rel.conj_guard guard g)
in ((_162_644), (_162_643), (ghost)))))))
end)))
end)) (([]), (g_head), (false)) args bs)
in (match (_61_1781) with
| (args, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = if ghost then begin
(let _162_645 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _162_645 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (

let _61_1786 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_61_1786) with
| (c, g) -> begin
((e), (c), (g))
end))))
end)))
end
| _61_1788 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let _61_1795 = (FStar_Syntax_Subst.open_branch branch)
in (match (_61_1795) with
| (pattern, when_clause, branch_exp) -> begin
(

let _61_1800 = branch
in (match (_61_1800) with
| (cpat, _61_1798, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _61_1808 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_61_1808) with
| (pat_bvs, exps, p) -> begin
(

let _61_1809 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _162_657 = (FStar_Syntax_Print.pat_to_string p0)
in (let _162_656 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _162_657 _162_656)))
end else begin
()
end
in (

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let _61_1815 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_61_1815) with
| (env1, _61_1814) -> begin
(

let env1 = (

let _61_1816 = env1
in {FStar_TypeChecker_Env.solver = _61_1816.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_1816.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_1816.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_1816.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_1816.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_1816.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_1816.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_1816.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _61_1816.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _61_1816.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _61_1816.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _61_1816.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _61_1816.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _61_1816.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _61_1816.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _61_1816.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _61_1816.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _61_1816.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _61_1816.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _61_1816.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_1816.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _61_1816.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _61_1816.FStar_TypeChecker_Env.qname_and_index})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _61_1855 = (let _162_680 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _61_1821 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _162_660 = (FStar_Syntax_Print.term_to_string e)
in (let _162_659 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _162_660 _162_659)))
end else begin
()
end
in (

let _61_1826 = (tc_term env1 e)
in (match (_61_1826) with
| (e, lc, g) -> begin
(

let _61_1827 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _162_662 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _162_661 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _162_662 _162_661)))
end else begin
()
end
in (

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let _61_1833 = (let _162_663 = (FStar_TypeChecker_Rel.discharge_guard env (

let _61_1831 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _61_1831.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _61_1831.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _61_1831.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _162_663 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _162_668 = (let _162_667 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _162_667 (FStar_List.map (fun _61_1841 -> (match (_61_1841) with
| (u, _61_1840) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _162_668 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _61_1849 = if (let _162_669 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _162_669)) then begin
(

let unresolved = (let _162_670 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _162_670 FStar_Util.set_elements))
in (let _162_678 = (let _162_677 = (let _162_676 = (let _162_675 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _162_674 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _162_673 = (let _162_672 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _61_1848 -> (match (_61_1848) with
| (u, _61_1847) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _162_672 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _162_675 _162_674 _162_673))))
in ((_162_676), (p.FStar_Syntax_Syntax.p)))
in FStar_Errors.Error (_162_677))
in (Prims.raise _162_678)))
end else begin
()
end
in (

let _61_1851 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _162_679 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _162_679))
end else begin
()
end
in ((e), (e'))))))))))))
end))))))
in (FStar_All.pipe_right _162_680 FStar_List.unzip))
in (match (_61_1855) with
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

let _61_1862 = (let _162_681 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _162_681 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_61_1862) with
| (scrutinee_env, _61_1861) -> begin
(

let _61_1868 = (tc_pat true pat_t pattern)
in (match (_61_1868) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let _61_1878 = (match (when_clause) with
| None -> begin
((None), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (e) -> begin
if (FStar_TypeChecker_Env.should_verify env) then begin
(Prims.raise (FStar_Errors.Error ((("When clauses are not yet supported in --verify mode; they will be some day"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
(

let _61_1875 = (let _162_682 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _162_682 e))
in (match (_61_1875) with
| (e, c, g) -> begin
((Some (e)), (g))
end))
end
end)
in (match (_61_1878) with
| (when_clause, g_when) -> begin
(

let _61_1882 = (tc_term pat_env branch_exp)
in (match (_61_1882) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _162_684 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _162_683 -> Some (_162_683)) _162_684))
end)
in (

let _61_1940 = (

let eqs = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
None
end else begin
(FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _61_1900 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _162_688 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _162_687 -> Some (_162_687)) _162_688))
end))
end))) None))
end
in (

let _61_1908 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_61_1908) with
| (c, g_branch) -> begin
(

let _61_1935 = (match (((eqs), (when_condition))) with
| _61_1910 when (not ((FStar_TypeChecker_Env.should_verify env))) -> begin
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
in (let _162_691 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _162_690 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((_162_691), (_162_690))))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (let _162_692 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_162_692))
in (let _162_695 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _162_694 = (let _162_693 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _162_693 g_when))
in ((_162_695), (_162_694))))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _162_696 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in ((_162_696), (g_when)))))
end)
in (match (_61_1935) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _162_698 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _162_697 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in ((_162_698), (_162_697), (g_branch)))))
end))
end)))
in (match (_61_1940) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
FStar_Syntax_Util.t_true
end else begin
(

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> if ((let _162_708 = (let _162_707 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _162_707))
in (FStar_List.length _162_708)) > (Prims.parse_int "1")) then begin
(

let discriminator = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env discriminator)) with
| None -> begin
[]
end
| _61_1950 -> begin
(

let disc = (FStar_Syntax_Syntax.fvar discriminator FStar_Syntax_Syntax.Delta_equational None)
in (

let disc = (let _162_710 = (let _162_709 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_162_709)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _162_710 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _162_711 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_162_711)::[])))
end))
end else begin
[]
end)
in (

let fail = (fun _61_1954 -> (match (()) with
| () -> begin
(let _162_717 = (let _162_716 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _162_715 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _162_714 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _162_716 _162_715 _162_714))))
in (failwith _162_717))
end))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _61_1961) -> begin
(head_constructor t)
end
| _61_1965 -> begin
(fail ())
end))
in (

let pat_exp = (let _162_720 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _162_720 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_61_1990) -> begin
(let _162_725 = (let _162_724 = (let _162_723 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _162_722 = (let _162_721 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_162_721)::[])
in (_162_723)::_162_722))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _162_724 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_162_725)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _162_726 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _162_726))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(

let sub_term_guards = (let _162_732 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _61_2008 -> (match (_61_2008) with
| (ei, _61_2007) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _61_2012 -> begin
(

let sub_term = (let _162_731 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p) FStar_Syntax_Syntax.Delta_equational None)
in (let _162_730 = (let _162_729 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_162_729)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _162_731 _162_730 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _162_732 FStar_List.flatten))
in (let _162_733 = (discriminate scrutinee_tm f)
in (FStar_List.append _162_733 sub_term_guards)))
end)
end
| _61_2016 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(

let t = (let _162_738 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _162_738))
in (

let _61_2024 = (FStar_Syntax_Util.type_u ())
in (match (_61_2024) with
| (k, _61_2023) -> begin
(

let _61_2030 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_61_2030) with
| (t, _61_2027, _61_2029) -> begin
t
end))
end)))
end)
in (

let branch_guard = (let _162_739 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _162_739 FStar_Syntax_Util.mk_disj_l))
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

let _61_2038 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _162_740 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _162_740))
end else begin
()
end
in (let _162_741 = (FStar_Syntax_Subst.close_branch ((pattern), (when_clause), (branch_exp)))
in ((_162_741), (branch_guard), (c), (guard))))))
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

let _61_2055 = (check_let_bound_def true env lb)
in (match (_61_2055) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let _61_2069 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
((g1), (e1), (univ_vars), (c1))
end else begin
(

let g1 = (let _162_744 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _162_744 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _61_2057 = ()
in (

let _61_2064 = (let _162_748 = (let _162_747 = (let _162_746 = (let _162_745 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (_162_745)))
in (_162_746)::[])
in (FStar_TypeChecker_Util.generalize env _162_747))
in (FStar_List.hd _162_748))
in (match (_61_2064) with
| (_61_2060, univs, e1, c1) -> begin
((g1), (e1), (univs), ((FStar_Syntax_Util.lcomp_of_comp c1)))
end))))
end
in (match (_61_2069) with
| (g1, e1, univ_vars, c1) -> begin
(

let _61_2080 = if (FStar_TypeChecker_Env.should_verify env) then begin
(

let _61_2072 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_61_2072) with
| (ok, c1) -> begin
if ok then begin
((e2), (c1))
end else begin
(

let _61_2073 = if (FStar_Options.warn_top_level_effects ()) then begin
(let _162_749 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.warn _162_749 FStar_TypeChecker_Err.top_level_effect))
end else begin
()
end
in (let _162_750 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) None e2.FStar_Syntax_Syntax.pos)
in ((_162_750), (c1))))
end
end))
end else begin
(

let _61_2075 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (

let c = (let _162_751 = (c1.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_right _162_751 (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env)))
in ((e2), (c))))
end
in (match (_61_2080) with
| (e2, c1) -> begin
(

let cres = (let _162_752 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _162_752))
in (

let _61_2082 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _162_753 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((_162_753), (cres), (FStar_TypeChecker_Rel.trivial_guard))))))
end))
end))
end))
end
| _61_2086 -> begin
(failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let _61_2097 = env
in {FStar_TypeChecker_Env.solver = _61_2097.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_2097.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_2097.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_2097.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_2097.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_2097.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_2097.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_2097.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _61_2097.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _61_2097.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _61_2097.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _61_2097.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _61_2097.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _61_2097.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _61_2097.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _61_2097.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _61_2097.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _61_2097.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _61_2097.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _61_2097.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_2097.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _61_2097.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _61_2097.FStar_TypeChecker_Env.qname_and_index})
in (

let _61_2106 = (let _162_757 = (let _162_756 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _162_756 Prims.fst))
in (check_let_bound_def false _162_757 lb))
in (match (_61_2106) with
| (e1, _61_2102, c1, g1, annotated) -> begin
(

let x = (

let _61_2107 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _61_2107.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _61_2107.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let _61_2112 = (let _162_759 = (let _162_758 = (FStar_Syntax_Syntax.mk_binder x)
in (_162_758)::[])
in (FStar_Syntax_Subst.open_term _162_759 e2))
in (match (_61_2112) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _61_2118 = (let _162_760 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _162_760 e2))
in (match (_61_2118) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (x)), (c2)))
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let e2 = (FStar_TypeChecker_Util.maybe_lift env e2 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.res_typ)
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let e = (let _162_763 = (let _162_762 = (let _162_761 = (FStar_Syntax_Subst.close xb e2)
in ((((false), ((lb)::[]))), (_162_761)))
in FStar_Syntax_Syntax.Tm_let (_162_762))
in (FStar_Syntax_Syntax.mk _162_763 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (let _162_766 = (let _162_765 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _162_765 e1))
in (FStar_All.pipe_left (fun _162_764 -> FStar_TypeChecker_Common.NonTrivial (_162_764)) _162_766))
in (

let g2 = (let _162_768 = (let _162_767 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _162_767 g2))
in (FStar_TypeChecker_Rel.close_guard xb _162_768))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if (let _162_769 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome _162_769)) then begin
(

let tt = (let _162_770 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_All.pipe_right _162_770 FStar_Option.get))
in (

let _61_2129 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Exports"))) then begin
(let _162_772 = (FStar_Syntax_Print.term_to_string tt)
in (let _162_771 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Got expected type from env %s\ncres.res_typ=%s\n" _162_772 _162_771)))
end else begin
()
end
in ((e), (cres), (guard))))
end else begin
(

let t = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (

let _61_2132 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Exports"))) then begin
(let _162_774 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (let _162_773 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checked %s has no escaping types; normalized to %s\n" _162_774 _162_773)))
end else begin
()
end
in ((e), ((

let _61_2134 = cres
in {FStar_Syntax_Syntax.eff_name = _61_2134.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _61_2134.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _61_2134.FStar_Syntax_Syntax.comp})), (guard))))
end)))))))))
end))))
end)))
end)))
end
| _61_2137 -> begin
(failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _61_2149 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_61_2149) with
| (lbs, e2) -> begin
(

let _61_2152 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_61_2152) with
| (env0, topt) -> begin
(

let _61_2155 = (build_let_rec_env true env0 lbs)
in (match (_61_2155) with
| (lbs, rec_env) -> begin
(

let _61_2158 = (check_let_recs rec_env lbs)
in (match (_61_2158) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (let _162_777 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _162_777 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _162_780 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _162_780 (fun _162_779 -> Some (_162_779))))
in (

let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(

let ecs = (let _162_784 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _162_783 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (_162_783))))))
in (FStar_TypeChecker_Util.generalize env _162_784))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _61_2169 -> (match (_61_2169) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _162_786 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _162_786))
in (

let _61_2172 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _61_2176 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_61_2176) with
| (lbs, e2) -> begin
(let _162_788 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _162_787 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in ((_162_788), (cres), (_162_787))))
end)))))))
end))
end))
end))
end))
end
| _61_2178 -> begin
(failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _61_2190 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_61_2190) with
| (lbs, e2) -> begin
(

let _61_2193 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_61_2193) with
| (env0, topt) -> begin
(

let _61_2196 = (build_let_rec_env false env0 lbs)
in (match (_61_2196) with
| (lbs, rec_env) -> begin
(

let _61_2199 = (check_let_recs rec_env lbs)
in (match (_61_2199) with
| (lbs, g_lbs) -> begin
(

let _61_2211 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let _61_2202 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _61_2202.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _61_2202.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let _61_2205 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _61_2205.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _61_2205.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _61_2205.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _61_2205.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (lb.FStar_Syntax_Syntax.lbtyp)))
in ((env), (lb)))))) env))
in (match (_61_2211) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let _61_2217 = (tc_term env e2)
in (match (_61_2217) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _61_2221 = cres
in {FStar_Syntax_Syntax.eff_name = _61_2221.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _61_2221.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _61_2221.FStar_Syntax_Syntax.comp})
in (

let _61_2226 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_61_2226) with
| (lbs, e2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_61_2229) -> begin
((e), (cres), (guard))
end
| None -> begin
(

let tres = (check_no_escape None env bvs tres)
in (

let cres = (

let _61_2233 = cres
in {FStar_Syntax_Syntax.eff_name = _61_2233.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _61_2233.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _61_2233.FStar_Syntax_Syntax.comp})
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
| _61_2237 -> begin
(failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun t -> (

let _61_2247 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (_61_2247) with
| (_61_2245, c) -> begin
(

let quals = (FStar_TypeChecker_Env.lookup_effect_quals env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
end)))
in (

let _61_2278 = (FStar_List.fold_left (fun _61_2251 lb -> (match (_61_2251) with
| (lbs, env) -> begin
(

let _61_2256 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_61_2256) with
| (univ_vars, t, check_t) -> begin
(

let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (

let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (

let t = if (not (check_t)) then begin
t
end else begin
(

let _61_2265 = (let _162_802 = (let _162_801 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _162_801))
in (tc_check_tot_or_gtot_term (

let _61_2259 = env0
in {FStar_TypeChecker_Env.solver = _61_2259.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_2259.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_2259.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_2259.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_2259.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_2259.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_2259.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_2259.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _61_2259.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _61_2259.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _61_2259.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _61_2259.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _61_2259.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _61_2259.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _61_2259.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _61_2259.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _61_2259.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _61_2259.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _61_2259.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _61_2259.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_2259.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _61_2259.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _61_2259.FStar_TypeChecker_Env.qname_and_index}) t _162_802))
in (match (_61_2265) with
| (t, _61_2263, g) -> begin
(

let g = (FStar_TypeChecker_Rel.resolve_implicits g)
in (

let _61_2267 = (let _162_803 = (FStar_TypeChecker_Rel.discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _162_803))
in (norm env0 t)))
end))
end
in (

let env = if ((termination_check_enabled t) && (FStar_TypeChecker_Env.should_verify env)) then begin
(

let _61_2270 = env
in {FStar_TypeChecker_Env.solver = _61_2270.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_2270.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_2270.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_2270.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_2270.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_2270.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_2270.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_2270.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _61_2270.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _61_2270.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _61_2270.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _61_2270.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t)))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _61_2270.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _61_2270.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _61_2270.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _61_2270.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _61_2270.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _61_2270.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _61_2270.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _61_2270.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_2270.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _61_2270.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _61_2270.FStar_TypeChecker_Env.qname_and_index})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (t)))
end
in (

let lb = (

let _61_2273 = lb
in {FStar_Syntax_Syntax.lbname = _61_2273.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _61_2273.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb)::lbs), (env)))))))
end))
end)) (([]), (env)) lbs)
in (match (_61_2278) with
| (lbs, env) -> begin
(((FStar_List.rev lbs)), (env))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _61_2291 = (let _162_808 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _61_2285 = (let _162_807 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _162_807 lb.FStar_Syntax_Syntax.lbdef))
in (match (_61_2285) with
| (e, c, g) -> begin
(

let _61_2286 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Errors.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in ((lb), (g))))
end)))))
in (FStar_All.pipe_right _162_808 FStar_List.unzip))
in (match (_61_2291) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _61_2299 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_61_2299) with
| (env1, _61_2298) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _61_2306 = (check_lbtyp top_level env lb)
in (match (_61_2306) with
| (topt, wf_annot, univ_vars, univ_opening, env1) -> begin
(

let _61_2307 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Errors.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _61_2309 = ()
in (

let e1 = (FStar_Syntax_Subst.subst univ_opening e1)
in (

let _61_2317 = (tc_maybe_toplevel_term (

let _61_2312 = env1
in {FStar_TypeChecker_Env.solver = _61_2312.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_2312.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_2312.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_2312.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_2312.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_2312.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_2312.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_2312.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _61_2312.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _61_2312.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _61_2312.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _61_2312.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _61_2312.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _61_2312.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _61_2312.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _61_2312.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _61_2312.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _61_2312.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _61_2312.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _61_2312.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_2312.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _61_2312.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _61_2312.FStar_TypeChecker_Env.qname_and_index}) e1)
in (match (_61_2317) with
| (e1, c1, g1) -> begin
(

let _61_2321 = (let _162_815 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _61_2318 -> (match (()) with
| () -> begin
FStar_TypeChecker_Err.ill_kinded_type
end)))) _162_815 e1 c1 wf_annot))
in (match (_61_2321) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _61_2323 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _162_818 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _162_817 = (FStar_Syntax_Print.term_to_string c1.FStar_Syntax_Syntax.res_typ)
in (let _162_816 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print3 "checked top-level def %s, result type is %s, guard is %s\n" _162_818 _162_817 _162_816))))
end else begin
()
end
in (let _162_819 = (FStar_Option.isSome topt)
in ((e1), (univ_vars), (c1), (g1), (_162_819)))))
end))
end)))))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.subst_elt Prims.list * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _61_2330 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in ((None), (FStar_TypeChecker_Rel.trivial_guard), ([]), ([]), (env)))
end
| _61_2333 -> begin
(

let _61_2336 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (_61_2336) with
| (univ_opening, univ_vars) -> begin
(

let t = (FStar_Syntax_Subst.subst univ_opening t)
in (

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _162_823 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars), (univ_opening), (_162_823)))
end else begin
(

let _61_2342 = (FStar_Syntax_Util.type_u ())
in (match (_61_2342) with
| (k, _61_2341) -> begin
(

let _61_2347 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_61_2347) with
| (t, _61_2345, g) -> begin
(

let _61_2348 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _162_826 = (let _162_824 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _162_824))
in (let _162_825 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _162_826 _162_825)))
end else begin
()
end
in (

let t = (norm env1 t)
in (let _162_827 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (g), (univ_vars), (univ_opening), (_162_827)))))
end))
end))
end))
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _61_2354 -> (match (_61_2354) with
| (x, imp) -> begin
(

let _61_2357 = (FStar_Syntax_Util.type_u ())
in (match (_61_2357) with
| (tu, u) -> begin
(

let _61_2358 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _162_832 = (FStar_Syntax_Print.bv_to_string x)
in (let _162_831 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _162_830 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binders %s:%s at type %s\n" _162_832 _162_831 _162_830))))
end else begin
()
end
in (

let _61_2364 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_61_2364) with
| (t, _61_2362, g) -> begin
(

let x = (((

let _61_2365 = x
in {FStar_Syntax_Syntax.ppname = _61_2365.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _61_2365.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in (

let _61_2368 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _162_834 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _162_833 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _162_834 _162_833)))
end else begin
()
end
in (let _162_835 = (push_binding env x)
in ((x), (_162_835), (g), (u)))))
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

let _61_2383 = (tc_binder env b)
in (match (_61_2383) with
| (b, env', g, u) -> begin
(

let _61_2388 = (aux env' bs)
in (match (_61_2388) with
| (bs, env', g', us) -> begin
(let _162_843 = (let _162_842 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _162_842))
in (((b)::bs), (env'), (_162_843), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun _61_2396 _61_2399 -> (match (((_61_2396), (_61_2399))) with
| ((t, imp), (args, g)) -> begin
(

let _61_2404 = (tc_term env t)
in (match (_61_2404) with
| (t, _61_2402, g') -> begin
(let _162_852 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t), (imp)))::args), (_162_852)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p _61_2408 -> (match (_61_2408) with
| (pats, g) -> begin
(

let _61_2411 = (tc_args env p)
in (match (_61_2411) with
| (args, g') -> begin
(let _162_855 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats), (_162_855)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _61_2417 = (tc_maybe_toplevel_term env e)
in (match (_61_2417) with
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

let _61_2423 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _162_858 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in ((_162_858), (false)))
end else begin
(let _162_859 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in ((_162_859), (true)))
end
in (match (_61_2423) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _162_860 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (_162_860)))
end
| _61_2427 -> begin
if allow_ghost then begin
(let _162_863 = (let _162_862 = (let _162_861 = (FStar_TypeChecker_Err.expected_ghost_expression e c)
in ((_162_861), (e.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (_162_862))
in (Prims.raise _162_863))
end else begin
(let _162_866 = (let _162_865 = (let _162_864 = (FStar_TypeChecker_Err.expected_pure_expression e c)
in ((_162_864), (e.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (_162_865))
in (Prims.raise _162_866))
end
end)
end)))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let _61_2437 = (tc_tot_or_gtot_term env t)
in (match (_61_2437) with
| (t, c, g) -> begin
(

let _61_2438 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in ((t), (c)))
end)))


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _61_2442 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _162_876 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _162_876))
end else begin
()
end
in (

let env = (

let _61_2444 = env
in {FStar_TypeChecker_Env.solver = _61_2444.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_2444.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_2444.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_2444.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_2444.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_2444.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_2444.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_2444.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _61_2444.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _61_2444.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _61_2444.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _61_2444.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _61_2444.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _61_2444.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _61_2444.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _61_2444.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _61_2444.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _61_2444.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _61_2444.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _61_2444.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_2444.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _61_2444.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _61_2444.FStar_TypeChecker_Env.qname_and_index})
in (

let _61_2458 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Errors.Error (msg, _61_2450) -> begin
(let _162_881 = (let _162_880 = (let _162_879 = (FStar_TypeChecker_Env.get_range env)
in (((Prims.strcat "Implicit argument: " msg)), (_162_879)))
in FStar_Errors.Error (_162_880))
in (Prims.raise _162_881))
end
in (match (_61_2458) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end else begin
(let _162_886 = (let _162_885 = (let _162_884 = (let _162_882 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _162_882))
in (let _162_883 = (FStar_TypeChecker_Env.get_range env)
in ((_162_884), (_162_883))))
in FStar_Errors.Error (_162_885))
in (Prims.raise _162_886))
end
end)))))


let universe_or_type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.universe) FStar_Util.either = (fun env e -> (

let _61_2461 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _162_891 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "<start> universe_of %s\n" _162_891))
end else begin
()
end
in (

let _61_2466 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_61_2466) with
| (env, _61_2465) -> begin
(

let env = (

let _61_2467 = env
in {FStar_TypeChecker_Env.solver = _61_2467.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_2467.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_2467.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_2467.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_2467.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_2467.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_2467.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_2467.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _61_2467.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _61_2467.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _61_2467.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _61_2467.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _61_2467.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _61_2467.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _61_2467.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _61_2467.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _61_2467.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _61_2467.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _61_2467.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_2467.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _61_2467.FStar_TypeChecker_Env.qname_and_index})
in (

let fail = (fun e t -> FStar_Util.Inl (t))
in (

let ok = (fun u -> (

let _61_2475 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _162_900 = (FStar_Syntax_Print.tag_of_term e)
in (let _162_899 = (FStar_Syntax_Print.term_to_string e)
in (let _162_898 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.print3 "<end> universe_of (%s) %s is %s\n" _162_900 _162_899 _162_898))))
end else begin
()
end
in FStar_Util.Inr (u)))
in (

let universe_of_type = (fun e t -> (match ((let _162_905 = (FStar_Syntax_Util.unrefine t)
in _162_905.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(ok u)
end
| _61_2483 -> begin
(fail e t)
end))
in (

let _61_2486 = (FStar_Syntax_Util.head_and_args e)
in (match (_61_2486) with
| (head, args) -> begin
(match ((let _162_906 = (FStar_Syntax_Subst.compress head)
in _162_906.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_61_2488, t) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _162_907 = (FStar_Syntax_Subst.compress t)
in _162_907.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_61_2494, t) -> begin
(universe_of_type e (FStar_Syntax_Util.comp_result t))
end
| _61_2499 -> begin
(universe_of_type e t)
end))
end
| _61_2501 -> begin
(

let t = (match ((FStar_ST.read e.FStar_Syntax_Syntax.tk)) with
| (None) | (Some (FStar_Syntax_Syntax.Tm_unknown)) -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::[]) env e)
in (

let _61_2517 = (tc_term env e)
in (match (_61_2517) with
| (_61_2507, {FStar_Syntax_Syntax.eff_name = _61_2514; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _61_2511; FStar_Syntax_Syntax.comp = _61_2509}, g) -> begin
(

let _61_2518 = (let _162_909 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (FStar_All.pipe_right _162_909 Prims.ignore))
in t)
end)))
end
| Some (t) -> begin
(FStar_Syntax_Syntax.mk t None e.FStar_Syntax_Syntax.pos)
end)
in (let _162_910 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (FStar_All.pipe_left (universe_of_type e) _162_910)))
end)
end))))))
end))))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> (match ((universe_or_type_of env e)) with
| FStar_Util.Inl (t) -> begin
(let _162_920 = (let _162_919 = (let _162_918 = (let _162_916 = (FStar_Syntax_Print.term_to_string e)
in (let _162_915 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" _162_916 _162_915)))
in (let _162_917 = (FStar_TypeChecker_Env.get_range env)
in ((_162_918), (_162_917))))
in FStar_Errors.Error (_162_919))
in (Prims.raise _162_920))
end
| FStar_Util.Inr (u) -> begin
u
end))




