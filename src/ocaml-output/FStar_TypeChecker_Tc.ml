
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

let _57_18 = env
in {FStar_TypeChecker_Env.solver = _57_18.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_18.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_18.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_18.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_18.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_18.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_18.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_18.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_18.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _57_18.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_18.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_18.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_18.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_18.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_18.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_18.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_18.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_18.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_18.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_18.FStar_TypeChecker_Env.use_bv_sorts}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _57_21 = env
in {FStar_TypeChecker_Env.solver = _57_21.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_21.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_21.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_21.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_21.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_21.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_21.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_21.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_21.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _57_21.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_21.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_21.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_21.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_21.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_21.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_21.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_21.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_21.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_21.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_21.FStar_TypeChecker_Env.use_bv_sorts}))


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
| _57_31 -> begin
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
| _57_48 -> begin
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

let fail = (fun _57_55 -> (match (()) with
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
| _57_64 -> begin
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
| _57_74 -> begin
[]
end))


let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.subst_t = (fun s b v -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
s
end else begin
(FStar_Syntax_Syntax.NT (((Prims.fst b), v)))::s
end)


let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (

let _57_80 = lc
in {FStar_Syntax_Syntax.eff_name = _57_80.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _57_80.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _57_82 -> (match (()) with
| () -> begin
(let _147_76 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _147_76 t))
end))}))


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _147_85 = if (not ((FStar_Syntax_Util.is_pure_or_ghost_function t))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _147_85))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _57_114 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, guard)
end
| Some (t') -> begin
(

let _57_96 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_87 = (FStar_Syntax_Print.term_to_string t)
in (let _147_86 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _147_87 _147_86)))
end else begin
()
end
in (

let _57_100 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_57_100) with
| (e, lc) -> begin
(

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _57_104 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_57_104) with
| (e, g) -> begin
(

let _57_105 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_89 = (FStar_Syntax_Print.term_to_string t)
in (let _147_88 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _147_89 _147_88)))
end else begin
()
end
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let _57_110 = (let _147_95 = (FStar_All.pipe_left (fun _147_94 -> Some (_147_94)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _147_95 env e lc g))
in (match (_57_110) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))))
end)))
end)))
end)
in (match (_57_114) with
| (e, lc, g) -> begin
(

let _57_115 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_96 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _147_96))
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

let _57_125 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_57_125) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _57_130 -> (match (_57_130) with
| (e, c) -> begin
(

let expected_c_opt = (match (copt) with
| Some (_57_132) -> begin
copt
end
| None -> begin
if ((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Syntax_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) then begin
(let _147_109 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (_147_109))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
if (FStar_Syntax_Util.is_pure_comp c) then begin
(let _147_110 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (_147_110))
end else begin
if (FStar_Syntax_Util.is_pure_or_ghost_comp c) then begin
(let _147_111 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (_147_111))
end else begin
None
end
end
end
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _147_112 = (norm_c env c)
in (e, _147_112, FStar_TypeChecker_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(

let _57_139 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_115 = (FStar_Syntax_Print.term_to_string e)
in (let _147_114 = (FStar_Syntax_Print.comp_to_string c)
in (let _147_113 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _147_115 _147_114 _147_113))))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _57_142 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_118 = (FStar_Syntax_Print.term_to_string e)
in (let _147_117 = (FStar_Syntax_Print.comp_to_string c)
in (let _147_116 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _147_118 _147_117 _147_116))))
end else begin
()
end
in (

let _57_148 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_57_148) with
| (e, _57_146, g) -> begin
(

let g = (let _147_119 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _147_119 "could not prove post-condition" g))
in (

let _57_150 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_121 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _147_120 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _147_121 _147_120)))
end else begin
()
end
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e (FStar_Syntax_Util.comp_effect_name c) (FStar_Syntax_Util.comp_effect_name expected_c))
in (e, expected_c, g))))
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
(let _147_127 = (let _147_126 = (let _147_125 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _147_124 = (FStar_TypeChecker_Env.get_range env)
in (_147_125, _147_124)))
in FStar_Syntax_Syntax.Error (_147_126))
in (Prims.raise _147_127))
end)
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _147_130 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _147_130))
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
(let _147_137 = (let _147_136 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _147_136))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _147_137))
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

let t = (let _147_151 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _147_151))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _57_224 -> begin
(let _147_152 = (FStar_Syntax_Syntax.bv_to_name b)
in (_147_152)::[])
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
(match ((let _147_158 = (FStar_Syntax_Subst.compress t)
in _147_158.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _57_263 -> (match (_57_263) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _147_162 = (let _147_161 = (let _147_160 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_147_160))
in (FStar_Syntax_Syntax.new_bv _147_161 x.FStar_Syntax_Syntax.sort))
in (_147_162, imp))
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

let precedes = (let _147_166 = (let _147_165 = (FStar_Syntax_Syntax.as_arg dec)
in (let _147_164 = (let _147_163 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_147_163)::[])
in (_147_165)::_147_164))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _147_166 None r))
in (

let _57_274 = (FStar_Util.prefix formals)
in (match (_57_274) with
| (bs, (last, imp)) -> begin
(

let last = (

let _57_275 = last
in (let _147_167 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _57_275.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_275.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_167}))
in (

let refined_formals = (FStar_List.append bs (((last, imp))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (

let _57_280 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_170 = (FStar_Syntax_Print.lbname_to_string l)
in (let _147_169 = (FStar_Syntax_Print.term_to_string t)
in (let _147_168 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _147_170 _147_169 _147_168))))
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
(let _147_238 = (let _147_236 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _147_236))
in (let _147_237 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _147_238 _147_237)))
end else begin
()
end
in (

let top = e
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_57_295) -> begin
(let _147_242 = (FStar_Syntax_Subst.compress e)
in (tc_term env _147_242))
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
in (let _147_244 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_pattern (pats)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _147_243 = (FStar_TypeChecker_Rel.conj_guard g g')
in (_147_244, c, _147_243))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _147_245 = (FStar_Syntax_Subst.compress e)
in _147_245.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_57_368, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _57_375; FStar_Syntax_Syntax.lbtyp = _57_373; FStar_Syntax_Syntax.lbeff = _57_371; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _57_386 = (let _147_246 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _147_246 e1))
in (match (_57_386) with
| (e1, c1, g1) -> begin
(

let _57_390 = (tc_term env e2)
in (match (_57_390) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (None, c2))
in (

let e = (let _147_251 = (let _147_250 = (let _147_249 = (let _147_248 = (let _147_247 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Common.t_unit, e1))
in (_147_247)::[])
in (false, _147_248))
in (_147_249, e2))
in FStar_Syntax_Syntax.Tm_let (_147_250))
in (FStar_Syntax_Syntax.mk _147_251 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _147_252 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _147_252)))))
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

let _57_429 = (let _147_254 = (let _147_253 = (c'.FStar_Syntax_Syntax.comp ())
in (e, _147_253))
in (check_expected_effect env (Some (expected_c)) _147_254))
in (match (_57_429) with
| (e, expected_c, g'') -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (let _147_257 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t_res), Some ((FStar_Syntax_Util.comp_effect_name expected_c))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _147_256 = (let _147_255 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _147_255))
in (_147_257, (FStar_Syntax_Util.lcomp_of_comp expected_c), _147_256))))
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

let _57_449 = (let _147_258 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _147_258 e))
in (match (_57_449) with
| (e, c, g) -> begin
(

let _57_453 = (let _147_262 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_450 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _147_262 e c f))
in (match (_57_453) with
| (c, f) -> begin
(

let _57_457 = (let _147_263 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t), Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _147_263 c))
in (match (_57_457) with
| (e, c, f2) -> begin
(let _147_265 = (let _147_264 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _147_264))
in (e, c, _147_265))
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

let env = (let _147_267 = (let _147_266 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _147_266 Prims.fst))
in (FStar_All.pipe_right _147_267 instantiate_both))
in (

let _57_464 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_269 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _147_268 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _147_269 _147_268)))
end else begin
()
end
in (

let _57_469 = (tc_term (no_inst env) head)
in (match (_57_469) with
| (head, chead, g_head) -> begin
(

let _57_473 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _147_270 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _147_270))
end else begin
(let _147_271 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _147_271))
end
in (match (_57_473) with
| (e, c, g) -> begin
(

let _57_474 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _147_272 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _147_272))
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

let gimp = (match ((let _147_273 = (FStar_Syntax_Subst.compress head)
in _147_273.FStar_Syntax_Syntax.n)) with
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

let gres = (let _147_274 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _147_274))
in (

let _57_493 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _147_276 = (FStar_Syntax_Print.term_to_string e)
in (let _147_275 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" _147_276 _147_275)))
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
in (let _147_277 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_147_277, res_t)))
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
(let _147_280 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _147_280))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_531) with
| (cases, g) -> begin
(let _147_281 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_147_281, g))
end))
in (match (_57_534) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (Some (guard_x), c_branches))
in (

let e = (let _147_285 = (let _147_284 = (let _147_283 = (FStar_List.map (fun _57_543 -> (match (_57_543) with
| (f, _57_538, _57_540, _57_542) -> begin
f
end)) t_eqns)
in (e1, _147_283))
in FStar_Syntax_Syntax.Tm_match (_147_284))
in (FStar_Syntax_Syntax.mk _147_285 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ), Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (

let _57_546 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _147_288 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _147_287 = (let _147_286 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _147_286))
in (FStar_Util.print2 "(%s) comp type = %s\n" _147_288 _147_287)))
end else begin
()
end
in (let _147_289 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _147_289))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_558); FStar_Syntax_Syntax.lbunivs = _57_556; FStar_Syntax_Syntax.lbtyp = _57_554; FStar_Syntax_Syntax.lbeff = _57_552; FStar_Syntax_Syntax.lbdef = _57_550})::[]), _57_564) -> begin
(

let _57_567 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_290 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _147_290))
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
(let _147_291 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _147_291))
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
(let _147_305 = (let _147_304 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _147_304))
in FStar_Util.Inr (_147_305))
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
(let _147_311 = (let _147_310 = (let _147_309 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _147_308 = (FStar_TypeChecker_Env.get_range env)
in (_147_309, _147_308)))
in FStar_Syntax_Syntax.Error (_147_310))
in (Prims.raise _147_311))
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

let g = (match ((let _147_312 = (FStar_Syntax_Subst.compress t1)
in _147_312.FStar_Syntax_Syntax.n)) with
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
(let _147_314 = (let _147_313 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _147_313))
in FStar_Util.Inr (_147_314))
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
(let _147_317 = (let _147_316 = (let _147_315 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _147_315))
in FStar_Syntax_Syntax.Error (_147_316))
in (Prims.raise _147_317))
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

let e = (let _147_320 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _147_320 us))
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

let e = (let _147_321 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _147_321 us))
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

let g = (let _147_322 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _147_322))
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

let _57_750 = (let _147_324 = (let _147_323 = (FStar_Syntax_Syntax.mk_binder x)
in (_147_323)::[])
in (FStar_Syntax_Subst.open_term _147_324 phi))
in (match (_57_750) with
| (x, phi) -> begin
(

let env0 = env
in (

let _57_755 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_755) with
| (env, _57_754) -> begin
(

let _57_760 = (let _147_325 = (FStar_List.hd x)
in (tc_binder env _147_325))
in (match (_57_760) with
| (x, env, f1, u) -> begin
(

let _57_761 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_328 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _147_327 = (FStar_Syntax_Print.term_to_string phi)
in (let _147_326 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _147_328 _147_327 _147_326))))
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

let g = (let _147_329 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _147_329))
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
(let _147_330 = (FStar_Syntax_Print.term_to_string (

let _57_784 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _57_784.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_784.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_784.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _147_330))
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
(let _147_332 = (let _147_331 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _147_331))
in (FStar_All.failwith _147_332))
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
| FStar_Const.Const_int (_57_805, Some (_57_807)) -> begin
(FStar_All.failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (_57_812) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_57_815) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_57_818) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_57_822) -> begin
FStar_TypeChecker_Common.t_range
end
| _57_825 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(

let _57_832 = (FStar_Syntax_Util.type_u ())
in (match (_57_832) with
| (k, u) -> begin
(

let _57_837 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_837) with
| (t, _57_835, g) -> begin
(let _147_337 = (FStar_Syntax_Syntax.mk_Total t)
in (_147_337, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(

let _57_842 = (FStar_Syntax_Util.type_u ())
in (match (_57_842) with
| (k, u) -> begin
(

let _57_847 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_847) with
| (t, _57_845, g) -> begin
(let _147_338 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_147_338, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (

let tc = (let _147_340 = (let _147_339 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_147_339)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _147_340 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let _57_856 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_57_856) with
| (tc, _57_854, f) -> begin
(

let _57_860 = (FStar_Syntax_Util.head_and_args tc)
in (match (_57_860) with
| (_57_858, args) -> begin
(

let _57_863 = (let _147_342 = (FStar_List.hd args)
in (let _147_341 = (FStar_List.tl args)
in (_147_342, _147_341)))
in (match (_57_863) with
| (res, args) -> begin
(

let _57_879 = (let _147_344 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _57_5 -> (match (_57_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _57_870 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_870) with
| (env, _57_869) -> begin
(

let _57_875 = (tc_tot_or_gtot_term env e)
in (match (_57_875) with
| (e, _57_873, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _147_344 FStar_List.unzip))
in (match (_57_879) with
| (flags, guards) -> begin
(

let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| tk -> begin
(FStar_All.failwith "Impossible")
end)
in (let _147_346 = (FStar_Syntax_Syntax.mk_Comp (

let _57_885 = c
in {FStar_Syntax_Syntax.effect_name = _57_885.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _57_885.FStar_Syntax_Syntax.flags}))
in (let _147_345 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_147_346, u, _147_345))))
end))
end))
end))
end))))
end))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_57_893) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _147_351 = (aux u)
in FStar_Syntax_Syntax.U_succ (_147_351))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _147_352 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_147_352))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _147_356 = (let _147_355 = (let _147_354 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _147_353 = (FStar_TypeChecker_Env.get_range env)
in (_147_354, _147_353)))
in FStar_Syntax_Syntax.Error (_147_355))
in (Prims.raise _147_356))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _147_357 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _147_357 Prims.snd))
end
| _57_908 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _147_366 = (let _147_365 = (let _147_364 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_147_364, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_147_365))
in (Prims.raise _147_366)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun _57_926 bs bs_expected -> (match (_57_926) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
(

let _57_957 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _147_383 = (let _147_382 = (let _147_381 = (let _147_379 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _147_379))
in (let _147_380 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_147_381, _147_380)))
in FStar_Syntax_Syntax.Error (_147_382))
in (Prims.raise _147_383))
end
| _57_956 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _57_974 = (match ((let _147_384 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _147_384.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _57_962 -> begin
(

let _57_963 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_385 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _147_385))
end else begin
()
end
in (

let _57_969 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_57_969) with
| (t, _57_967, g1) -> begin
(

let g2 = (let _147_387 = (FStar_TypeChecker_Env.get_range env)
in (let _147_386 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _147_387 "Type annotation on parameter incompatible with the expected type" _147_386)))
in (

let g = (let _147_388 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _147_388))
in (t, g)))
end)))
end)
in (match (_57_974) with
| (t, g) -> begin
(

let hd = (

let _57_975 = hd
in {FStar_Syntax_Syntax.ppname = _57_975.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_975.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = (hd, imp)
in (

let b_expected = (hd_expected, imp')
in (

let env = (push_binding env b)
in (

let subst = (let _147_389 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _147_389))
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

let _57_996 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_995 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (

let _57_1003 = (tc_binders env bs)
in (match (_57_1003) with
| (bs, envbody, g, _57_1002) -> begin
(

let _57_1021 = (match ((let _147_396 = (FStar_Syntax_Subst.compress body)
in _147_396.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _57_1008) -> begin
(

let _57_1015 = (tc_comp envbody c)
in (match (_57_1015) with
| (c, _57_1013, g') -> begin
(let _147_397 = (FStar_TypeChecker_Rel.conj_guard g g')
in (Some (c), body, _147_397))
end))
end
| _57_1017 -> begin
(None, body, g)
end)
in (match (_57_1021) with
| (copt, body, g) -> begin
(None, bs, [], copt, envbody, body, g)
end))
end)))
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm t -> (match ((let _147_402 = (FStar_Syntax_Subst.compress t)
in _147_402.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let _57_1048 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1047 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _57_1055 = (tc_binders env bs)
in (match (_57_1055) with
| (bs, envbody, g, _57_1054) -> begin
(

let _57_1059 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_57_1059) with
| (envbody, _57_1058) -> begin
(Some ((t, true)), bs, [], None, envbody, body, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _57_1062) -> begin
(

let _57_1073 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_57_1073) with
| (_57_1066, bs, bs', copt, env, body, g) -> begin
(Some ((t, false)), bs, bs', copt, env, body, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _57_1080 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_57_1080) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun _57_1091 c_expected -> (match (_57_1091) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _147_413 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _147_413))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (let _147_414 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _147_414))
in (let _147_415 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _147_415)))
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

let _57_1112 = (check_binders env more_bs bs_expected)
in (match (_57_1112) with
| (env, bs', more, guard', subst) -> begin
(let _147_417 = (let _147_416 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _147_416, subst))
in (handle_more _147_417 c_expected))
end))
end
| _57_1114 -> begin
(let _147_419 = (let _147_418 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _147_418))
in (fail _147_419 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _147_420 = (check_binders env bs bs_expected)
in (handle_more _147_420 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let _57_1120 = envbody
in {FStar_TypeChecker_Env.solver = _57_1120.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1120.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1120.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1120.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1120.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1120.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1120.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1120.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1120.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1120.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1120.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1120.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_1120.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1120.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1120.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1120.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1120.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1120.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1120.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1120.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _57_1125 _57_1128 -> (match ((_57_1125, _57_1128)) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _57_1134 = (let _147_430 = (let _147_429 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _147_429 Prims.fst))
in (tc_term _147_430 t))
in (match (_57_1134) with
| (t, _57_1131, _57_1133) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _147_431 = (FStar_Syntax_Syntax.mk_binder (

let _57_1138 = x
in {FStar_Syntax_Syntax.ppname = _57_1138.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1138.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_147_431)::letrec_binders)
end
| _57_1141 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (

let _57_1147 = (check_actuals_against_formals env bs bs_expected)
in (match (_57_1147) with
| (envbody, bs, g, c) -> begin
(

let _57_1150 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_57_1150) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, body, g))
end))
end))))
end))
end
| _57_1153 -> begin
if (not (norm)) then begin
(let _147_432 = (unfold_whnf env t)
in (as_function_typ true _147_432))
end else begin
(

let _57_1163 = (expected_function_typ env None body)
in (match (_57_1163) with
| (_57_1155, bs, _57_1158, c_opt, envbody, body, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, body, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let _57_1167 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1167) with
| (env, topt) -> begin
(

let _57_1171 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_433 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _147_433 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (

let _57_1180 = (expected_function_typ env topt body)
in (match (_57_1180) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let _57_1186 = (tc_term (

let _57_1181 = envbody
in {FStar_TypeChecker_Env.solver = _57_1181.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1181.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1181.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1181.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1181.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1181.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1181.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1181.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1181.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1181.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1181.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1181.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1181.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1181.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1181.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1181.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1181.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1181.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1181.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_57_1186) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _57_1188 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _147_436 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _147_435 = (let _147_434 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _147_434))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _147_436 _147_435)))
end else begin
()
end
in (

let _57_1195 = (let _147_438 = (let _147_437 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _147_437))
in (check_expected_effect (

let _57_1190 = envbody
in {FStar_TypeChecker_Env.solver = _57_1190.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1190.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1190.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1190.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1190.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1190.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1190.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1190.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1190.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1190.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1190.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1190.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1190.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1190.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1190.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1190.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1190.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1190.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1190.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1190.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _147_438))
in (match (_57_1195) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _147_439 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _147_439))
end else begin
(

let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _147_442 = (let _147_441 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _147_440 -> FStar_Util.Inl (_147_440)))
in Some (_147_441))
in (FStar_Syntax_Util.abs bs body _147_442))
in (

let _57_1218 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_1207) -> begin
(e, t, guard)
end
| _57_1210 -> begin
(

let _57_1213 = if use_teq then begin
(let _147_443 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _147_443))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_57_1213) with
| (e, guard') -> begin
(let _147_444 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _147_444))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_57_1218) with
| (e, tfun, guard) -> begin
(

let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (

let _57_1222 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_57_1222) with
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

let _57_1232 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_453 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _147_452 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _147_453 _147_452)))
end else begin
()
end
in (

let monadic_application = (fun _57_1239 subst arg_comps_rev arg_rets guard fvs bs -> (match (_57_1239) with
| (head, chead, ghead, cres) -> begin
(

let _57_1246 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let _57_1274 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun _57_6 -> (match (_57_6) with
| (_57_1253, _57_1255, None) -> begin
false
end
| (_57_1259, _57_1261, Some (c)) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _147_469 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _147_469 cres))
end else begin
(

let _57_1266 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_472 = (FStar_Syntax_Print.term_to_string head)
in (let _147_471 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _147_470 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _147_472 _147_471 _147_470))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _57_1270 -> begin
(

let g = (let _147_473 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right _147_473 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _147_478 = (let _147_477 = (let _147_476 = (let _147_475 = (let _147_474 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _147_474))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _147_475))
in (FStar_Syntax_Syntax.mk_Total _147_476))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _147_477))
in (_147_478, g)))
end)
in (match (_57_1274) with
| (cres, guard) -> begin
(

let _57_1275 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_479 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _147_479))
end else begin
()
end
in (

let _57_1293 = (FStar_List.fold_left (fun _57_1279 _57_1285 -> (match ((_57_1279, _57_1285)) with
| ((args, out_c), ((e, q), x, c)) -> begin
(match (c) with
| None -> begin
(((e, q))::args, out_c)
end
| Some (c) -> begin
(

let out_c = (FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env (Some (e)) c (x, out_c))
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e c.FStar_Syntax_Syntax.eff_name out_c.FStar_Syntax_Syntax.eff_name)
in (((e, q))::args, out_c)))
end)
end)) ([], cres) arg_comps_rev)
in (match (_57_1293) with
| (args, comp) -> begin
(

let comp = (FStar_TypeChecker_Util.bind head.FStar_Syntax_Syntax.pos env None chead (None, comp))
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app = (FStar_TypeChecker_Util.maybe_monadic env app comp.FStar_Syntax_Syntax.eff_name)
in (

let _57_1299 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (_57_1299) with
| (comp, g) -> begin
(app, comp, g)
end)))))
end)))
end)))
end))
in (

let rec tc_args = (fun head_info _57_1307 bs args -> (match (_57_1307) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match ((bs, args)) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (_57_1313))))::rest, ((_57_1321, None))::_57_1319) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _57_1327 = (check_no_escape (Some (head)) env fvs t)
in (

let _57_1333 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_57_1333) with
| (varg, _57_1331, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (

let arg = (let _147_491 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _147_491))
in (let _147_493 = (let _147_492 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, ((arg, None, None))::outargs, (arg)::arg_rets, _147_492, fvs))
in (tc_args head_info _147_493 rest args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
(

let _57_1365 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _57_1364 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let _57_1368 = x
in {FStar_Syntax_Syntax.ppname = _57_1368.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1368.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (

let _57_1371 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _147_494 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _147_494))
end else begin
()
end
in (

let _57_1373 = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let _57_1376 = env
in {FStar_TypeChecker_Env.solver = _57_1376.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1376.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1376.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1376.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1376.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1376.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1376.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1376.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1376.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1376.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1376.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1376.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1376.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1376.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1376.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _57_1376.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1376.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1376.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1376.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1376.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_1379 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_497 = (FStar_Syntax_Print.tag_of_term e)
in (let _147_496 = (FStar_Syntax_Print.term_to_string e)
in (let _147_495 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _147_497 _147_496 _147_495))))
end else begin
()
end
in (

let _57_1384 = (tc_term env e)
in (match (_57_1384) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(

let subst = (let _147_498 = (FStar_List.hd bs)
in (maybe_extend_subst subst _147_498 e))
in (tc_args head_info (subst, ((arg, None, None))::outargs, (arg)::arg_rets, g, fvs) rest rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(

let subst = (let _147_499 = (FStar_List.hd bs)
in (maybe_extend_subst subst _147_499 e))
in (tc_args head_info (subst, ((arg, Some (x), Some (c)))::outargs, (arg)::arg_rets, g, fvs) rest rest'))
end else begin
if (let _147_500 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _147_500)) then begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _147_501 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _147_501))
in (tc_args head_info (subst, ((arg, Some (newx), Some (c)))::outargs, (arg')::arg_rets, g, fvs) rest rest')))
end else begin
(let _147_505 = (let _147_504 = (let _147_503 = (let _147_502 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _147_502))
in (_147_503)::arg_rets)
in (subst, ((arg, Some (x), Some (c)))::outargs, _147_504, g, (x)::fvs))
in (tc_args head_info _147_505 rest rest'))
end
end
end))
end))))))))))
end
| (_57_1392, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::_57_1397) -> begin
(

let _57_1404 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (_57_1404) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _147_510 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _147_510 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let _57_1415 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (_57_1415) with
| (bs, cres') -> begin
(

let head_info = (head, chead, ghead, (FStar_Syntax_Util.lcomp_of_comp cres'))
in (

let _57_1417 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_511 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _147_511))
end else begin
()
end
in (tc_args head_info ([], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs args)))
end))
end
| _57_1420 when (not (norm)) -> begin
(let _147_512 = (unfold_whnf env tres)
in (aux true _147_512))
end
| _57_1422 -> begin
(let _147_518 = (let _147_517 = (let _147_516 = (let _147_514 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (let _147_513 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _147_514 _147_513)))
in (let _147_515 = (FStar_Syntax_Syntax.argpos arg)
in (_147_516, _147_515)))
in FStar_Syntax_Syntax.Error (_147_517))
in (Prims.raise _147_518))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (match ((let _147_523 = (FStar_Syntax_Util.unrefine tf)
in _147_523.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| ((e, imp))::tl -> begin
(

let _57_1455 = (tc_term env e)
in (match (_57_1455) with
| (e, c, g_e) -> begin
(

let _57_1459 = (tc_args env tl)
in (match (_57_1459) with
| (args, comps, g_rest) -> begin
(let _147_528 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, ((e.FStar_Syntax_Syntax.pos, c))::comps, _147_528))
end))
end))
end))
in (

let _57_1463 = (tc_args env args)
in (match (_57_1463) with
| (args, comps, g_args) -> begin
(

let bs = (let _147_530 = (FStar_All.pipe_right comps (FStar_List.map (fun _57_1467 -> (match (_57_1467) with
| (_57_1465, c) -> begin
(c.FStar_Syntax_Syntax.res_typ, None)
end))))
in (FStar_Syntax_Util.null_binders_of_tks _147_530))
in (

let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _57_1473 -> begin
FStar_Syntax_Util.ml_comp
end)
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _147_545 = (FStar_Syntax_Subst.compress t)
in _147_545.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_1479) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _57_1484 -> begin
ml_or_tot
end)
end)
in (

let cres = (let _147_550 = (let _147_549 = (let _147_548 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _147_548 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _147_549))
in (ml_or_tot _147_550 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (

let _57_1488 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _147_553 = (FStar_Syntax_Print.term_to_string head)
in (let _147_552 = (FStar_Syntax_Print.term_to_string tf)
in (let _147_551 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _147_553 _147_552 _147_551))))
end else begin
()
end
in (

let _57_1490 = (let _147_554 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _147_554))
in (

let comp = (let _147_557 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _57_1494 out -> (match (_57_1494) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c (None, out))
end)) (((head.FStar_Syntax_Syntax.pos, chead))::comps) _147_557))
in (let _147_559 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _147_558 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_147_559, comp, _147_558)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _57_1503 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_1503) with
| (bs, c) -> begin
(

let head_info = (head, chead, ghead, (FStar_Syntax_Util.lcomp_of_comp c))
in (tc_args head_info ([], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs args))
end))
end
| _57_1506 -> begin
if (not (norm)) then begin
(let _147_560 = (unfold_whnf env tf)
in (check_function_app true _147_560))
end else begin
(let _147_563 = (let _147_562 = (let _147_561 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_147_561, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_147_562))
in (Prims.raise _147_563))
end
end))
in (let _147_565 = (let _147_564 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _147_564))
in (check_function_app false _147_565))))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let _57_1542 = (FStar_List.fold_left2 (fun _57_1523 _57_1526 _57_1529 -> (match ((_57_1523, _57_1526, _57_1529)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(

let _57_1530 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let _57_1535 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_57_1535) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (let _147_575 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _147_575 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _147_579 = (let _147_577 = (let _147_576 = (FStar_Syntax_Syntax.as_arg e)
in (_147_576)::[])
in (FStar_List.append seen _147_577))
in (let _147_578 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_147_579, _147_578, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_57_1542) with
| (args, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = if ghost then begin
(let _147_580 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _147_580 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (

let _57_1547 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_57_1547) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _57_1549 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let _57_1556 = (FStar_Syntax_Subst.open_branch branch)
in (match (_57_1556) with
| (pattern, when_clause, branch_exp) -> begin
(

let _57_1561 = branch
in (match (_57_1561) with
| (cpat, _57_1559, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _57_1569 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_57_1569) with
| (pat_bvs, exps, p) -> begin
(

let _57_1570 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_592 = (FStar_Syntax_Print.pat_to_string p0)
in (let _147_591 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _147_592 _147_591)))
end else begin
()
end
in (

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let _57_1576 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_57_1576) with
| (env1, _57_1575) -> begin
(

let env1 = (

let _57_1577 = env1
in {FStar_TypeChecker_Env.solver = _57_1577.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1577.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1577.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1577.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1577.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1577.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1577.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1577.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _57_1577.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1577.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1577.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1577.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1577.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1577.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1577.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1577.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1577.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1577.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1577.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1577.FStar_TypeChecker_Env.use_bv_sorts})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _57_1616 = (let _147_615 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _57_1582 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_595 = (FStar_Syntax_Print.term_to_string e)
in (let _147_594 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _147_595 _147_594)))
end else begin
()
end
in (

let _57_1587 = (tc_term env1 e)
in (match (_57_1587) with
| (e, lc, g) -> begin
(

let _57_1588 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_597 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _147_596 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _147_597 _147_596)))
end else begin
()
end
in (

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let _57_1594 = (let _147_598 = (FStar_TypeChecker_Rel.discharge_guard env (

let _57_1592 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_1592.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_1592.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_1592.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _147_598 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _147_603 = (let _147_602 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _147_602 (FStar_List.map (fun _57_1602 -> (match (_57_1602) with
| (u, _57_1601) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _147_603 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _57_1610 = if (let _147_604 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _147_604)) then begin
(

let unresolved = (let _147_605 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _147_605 FStar_Util.set_elements))
in (let _147_613 = (let _147_612 = (let _147_611 = (let _147_610 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _147_609 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _147_608 = (let _147_607 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _57_1609 -> (match (_57_1609) with
| (u, _57_1608) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _147_607 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _147_610 _147_609 _147_608))))
in (_147_611, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_147_612))
in (Prims.raise _147_613)))
end else begin
()
end
in (

let _57_1612 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_614 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _147_614))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _147_615 FStar_List.unzip))
in (match (_57_1616) with
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

let _57_1623 = (let _147_616 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _147_616 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_57_1623) with
| (scrutinee_env, _57_1622) -> begin
(

let _57_1629 = (tc_pat true pat_t pattern)
in (match (_57_1629) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let _57_1639 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(

let _57_1636 = (let _147_617 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _147_617 e))
in (match (_57_1636) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_57_1639) with
| (when_clause, g_when) -> begin
(

let _57_1643 = (tc_term pat_env branch_exp)
in (match (_57_1643) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _147_619 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _147_618 -> Some (_147_618)) _147_619))
end)
in (

let _57_1699 = (

let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _57_1661 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _147_623 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _147_622 -> Some (_147_622)) _147_623))
end))
end))) None))
in (

let _57_1669 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_57_1669) with
| (c, g_branch) -> begin
(

let _57_1694 = (match ((eqs, when_condition)) with
| (None, None) -> begin
(c, g_when)
end
| (Some (f), None) -> begin
(

let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _147_626 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _147_625 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_147_626, _147_625)))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (let _147_627 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_147_627))
in (let _147_630 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _147_629 = (let _147_628 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _147_628 g_when))
in (_147_630, _147_629)))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _147_631 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_147_631, g_when))))
end)
in (match (_57_1694) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _147_633 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _147_632 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_147_633, _147_632, g_branch))))
end))
end)))
in (match (_57_1699) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = (

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> if ((let _147_643 = (let _147_642 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _147_642))
in (FStar_List.length _147_643)) > 1) then begin
(

let disc = (let _147_644 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _147_644 FStar_Syntax_Syntax.Delta_equational None))
in (

let disc = (let _147_646 = (let _147_645 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_147_645)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _147_646 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _147_647 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_147_647)::[])))
end else begin
[]
end)
in (

let fail = (fun _57_1709 -> (match (()) with
| () -> begin
(let _147_653 = (let _147_652 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _147_651 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _147_650 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _147_652 _147_651 _147_650))))
in (FStar_All.failwith _147_653))
end))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _57_1716) -> begin
(head_constructor t)
end
| _57_1720 -> begin
(fail ())
end))
in (

let pat_exp = (let _147_656 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _147_656 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_57_1745) -> begin
(let _147_661 = (let _147_660 = (let _147_659 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _147_658 = (let _147_657 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_147_657)::[])
in (_147_659)::_147_658))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _147_660 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_147_661)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _147_662 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _147_662))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(

let sub_term_guards = (let _147_669 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _57_1763 -> (match (_57_1763) with
| (ei, _57_1762) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _57_1767 -> begin
(

let sub_term = (let _147_668 = (let _147_665 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _147_665 FStar_Syntax_Syntax.Delta_equational None))
in (let _147_667 = (let _147_666 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_147_666)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _147_668 _147_667 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _147_669 FStar_List.flatten))
in (let _147_670 = (discriminate scrutinee_tm f)
in (FStar_List.append _147_670 sub_term_guards)))
end)
end
| _57_1771 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(

let t = (let _147_675 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _147_675))
in (

let _57_1779 = (FStar_Syntax_Util.type_u ())
in (match (_57_1779) with
| (k, _57_1778) -> begin
(

let _57_1785 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_57_1785) with
| (t, _57_1782, _57_1784) -> begin
t
end))
end)))
end)
in (

let branch_guard = (let _147_676 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _147_676 FStar_Syntax_Util.mk_disj_l))
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

let _57_1793 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_677 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _147_677))
end else begin
()
end
in (let _147_678 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_147_678, branch_guard, c, guard)))))
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

let _57_1810 = (check_let_bound_def true env lb)
in (match (_57_1810) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let _57_1822 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(

let g1 = (let _147_681 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _147_681 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _57_1817 = (let _147_685 = (let _147_684 = (let _147_683 = (let _147_682 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _147_682))
in (_147_683)::[])
in (FStar_TypeChecker_Util.generalize env _147_684))
in (FStar_List.hd _147_685))
in (match (_57_1817) with
| (_57_1813, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_57_1822) with
| (g1, e1, univ_vars, c1) -> begin
(

let _57_1832 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(

let _57_1825 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_57_1825) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(

let _57_1826 = if (FStar_Options.warn_top_level_effects ()) then begin
(let _147_686 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _147_686 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _147_687 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_147_687, c1)))
end
end))
end else begin
(

let _57_1828 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _147_688 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _147_688)))
end
in (match (_57_1832) with
| (e2, c1) -> begin
(

let cres = (let _147_689 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _147_689))
in (

let _57_1834 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _147_690 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_147_690, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _57_1838 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let _57_1849 = env
in {FStar_TypeChecker_Env.solver = _57_1849.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1849.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1849.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1849.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1849.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1849.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1849.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1849.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1849.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1849.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1849.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1849.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1849.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1849.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1849.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1849.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1849.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1849.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1849.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1849.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_1858 = (let _147_694 = (let _147_693 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _147_693 Prims.fst))
in (check_let_bound_def false _147_694 lb))
in (match (_57_1858) with
| (e1, _57_1854, c1, g1, annotated) -> begin
(

let x = (

let _57_1859 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1859.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1859.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let _57_1865 = (let _147_696 = (let _147_695 = (FStar_Syntax_Syntax.mk_binder x)
in (_147_695)::[])
in (FStar_Syntax_Subst.open_term _147_696 e2))
in (match (_57_1865) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _57_1871 = (let _147_697 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _147_697 e2))
in (match (_57_1871) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (Some (x), c2))
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e2 = (FStar_TypeChecker_Util.maybe_lift env e2 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e = (let _147_700 = (let _147_699 = (let _147_698 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _147_698))
in FStar_Syntax_Syntax.Tm_let (_147_699))
in (FStar_Syntax_Syntax.mk _147_700 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name)
in (

let x_eq_e1 = (let _147_703 = (let _147_702 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _147_702 e1))
in (FStar_All.pipe_left (fun _147_701 -> FStar_TypeChecker_Common.NonTrivial (_147_701)) _147_703))
in (

let g2 = (let _147_705 = (let _147_704 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _147_704 g2))
in (FStar_TypeChecker_Rel.close_guard xb _147_705))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if (let _147_706 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome _147_706)) then begin
(e, cres, guard)
end else begin
(

let _57_1880 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end))))))))
end))))
end))))
end)))
end
| _57_1883 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _57_1895 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1895) with
| (lbs, e2) -> begin
(

let _57_1898 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1898) with
| (env0, topt) -> begin
(

let _57_1901 = (build_let_rec_env true env0 lbs)
in (match (_57_1901) with
| (lbs, rec_env) -> begin
(

let _57_1904 = (check_let_recs rec_env lbs)
in (match (_57_1904) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (let _147_709 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _147_709 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _147_712 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _147_712 (fun _147_711 -> Some (_147_711))))
in (

let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(

let ecs = (let _147_716 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _147_715 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _147_715)))))
in (FStar_TypeChecker_Util.generalize env _147_716))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _57_1915 -> (match (_57_1915) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _147_718 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _147_718))
in (

let _57_1918 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _57_1922 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1922) with
| (lbs, e2) -> begin
(let _147_720 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _147_719 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_147_720, cres, _147_719)))
end)))))))
end))
end))
end))
end))
end
| _57_1924 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _57_1936 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1936) with
| (lbs, e2) -> begin
(

let _57_1939 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1939) with
| (env0, topt) -> begin
(

let _57_1942 = (build_let_rec_env false env0 lbs)
in (match (_57_1942) with
| (lbs, rec_env) -> begin
(

let _57_1945 = (check_let_recs rec_env lbs)
in (match (_57_1945) with
| (lbs, g_lbs) -> begin
(

let _57_1957 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let _57_1948 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1948.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1948.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let _57_1951 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _57_1951.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1951.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1951.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _57_1951.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], lb.FStar_Syntax_Syntax.lbtyp))
in (env, lb))))) env))
in (match (_57_1957) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let _57_1963 = (tc_term env e2)
in (match (_57_1963) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _57_1967 = cres
in {FStar_Syntax_Syntax.eff_name = _57_1967.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _57_1967.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_1967.FStar_Syntax_Syntax.comp})
in (

let _57_1972 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1972) with
| (lbs, e2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_57_1975) -> begin
(e, cres, guard)
end
| None -> begin
(

let _57_1978 = (check_no_escape None env bvs tres)
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
| _57_1981 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let _57_2014 = (FStar_List.fold_left (fun _57_1988 lb -> (match (_57_1988) with
| (lbs, env) -> begin
(

let _57_1993 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_57_1993) with
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

let _57_2002 = (let _147_732 = (let _147_731 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _147_731))
in (tc_check_tot_or_gtot_term (

let _57_1996 = env0
in {FStar_TypeChecker_Env.solver = _57_1996.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1996.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1996.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1996.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1996.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1996.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1996.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1996.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1996.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1996.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1996.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1996.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1996.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1996.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _57_1996.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1996.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1996.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1996.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1996.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1996.FStar_TypeChecker_Env.use_bv_sorts}) t _147_732))
in (match (_57_2002) with
| (t, _57_2000, g) -> begin
(

let _57_2003 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (

let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(

let _57_2006 = env
in {FStar_TypeChecker_Env.solver = _57_2006.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2006.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2006.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2006.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2006.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2006.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2006.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2006.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2006.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2006.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2006.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2006.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2006.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_2006.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2006.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2006.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2006.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2006.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2006.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2006.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (

let lb = (

let _57_2009 = lb
in {FStar_Syntax_Syntax.lbname = _57_2009.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _57_2009.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_57_2014) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _57_2027 = (let _147_737 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _57_2021 = (let _147_736 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _147_736 lb.FStar_Syntax_Syntax.lbdef))
in (match (_57_2021) with
| (e, c, g) -> begin
(

let _57_2022 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _147_737 FStar_List.unzip))
in (match (_57_2027) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _57_2035 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_2035) with
| (env1, _57_2034) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _57_2041 = (check_lbtyp top_level env lb)
in (match (_57_2041) with
| (topt, wf_annot, univ_vars, env1) -> begin
(

let _57_2042 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let _57_2049 = (tc_maybe_toplevel_term (

let _57_2044 = env1
in {FStar_TypeChecker_Env.solver = _57_2044.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2044.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2044.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2044.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2044.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2044.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2044.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2044.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2044.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2044.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2044.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2044.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2044.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _57_2044.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2044.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2044.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2044.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2044.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2044.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2044.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_57_2049) with
| (e1, c1, g1) -> begin
(

let _57_2053 = (let _147_744 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_2050 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _147_744 e1 c1 wf_annot))
in (match (_57_2053) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _57_2055 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _147_745 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _147_745))
end else begin
()
end
in (let _147_746 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _147_746))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _57_2062 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _57_2065 -> begin
(

let _57_2068 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_57_2068) with
| (univ_vars, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _147_750 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _147_750))
end else begin
(

let _57_2073 = (FStar_Syntax_Util.type_u ())
in (match (_57_2073) with
| (k, _57_2072) -> begin
(

let _57_2078 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_57_2078) with
| (t, _57_2076, g) -> begin
(

let _57_2079 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _147_753 = (let _147_751 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _147_751))
in (let _147_752 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _147_753 _147_752)))
end else begin
()
end
in (

let t = (norm env1 t)
in (let _147_754 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _147_754))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _57_2085 -> (match (_57_2085) with
| (x, imp) -> begin
(

let _57_2088 = (FStar_Syntax_Util.type_u ())
in (match (_57_2088) with
| (tu, u) -> begin
(

let _57_2093 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_57_2093) with
| (t, _57_2091, g) -> begin
(

let x = ((

let _57_2094 = x
in {FStar_Syntax_Syntax.ppname = _57_2094.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2094.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (

let _57_2097 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_758 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _147_757 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _147_758 _147_757)))
end else begin
()
end
in (let _147_759 = (push_binding env x)
in (x, _147_759, g, u))))
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

let _57_2112 = (tc_binder env b)
in (match (_57_2112) with
| (b, env', g, u) -> begin
(

let _57_2117 = (aux env' bs)
in (match (_57_2117) with
| (bs, env', g', us) -> begin
(let _147_767 = (let _147_766 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _147_766))
in ((b)::bs, env', _147_767, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun _57_2125 _57_2128 -> (match ((_57_2125, _57_2128)) with
| ((t, imp), (args, g)) -> begin
(

let _57_2133 = (tc_term env t)
in (match (_57_2133) with
| (t, _57_2131, g') -> begin
(let _147_776 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _147_776))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _57_2137 -> (match (_57_2137) with
| (pats, g) -> begin
(

let _57_2140 = (tc_args env p)
in (match (_57_2140) with
| (args, g') -> begin
(let _147_779 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _147_779))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _57_2146 = (tc_maybe_toplevel_term env e)
in (match (_57_2146) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let _57_2149 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _147_782 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _147_782))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _57_2154 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _147_783 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_147_783, false))
end else begin
(let _147_784 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_147_784, true))
end
in (match (_57_2154) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _147_785 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _147_785))
end
| _57_2158 -> begin
if allow_ghost then begin
(let _147_788 = (let _147_787 = (let _147_786 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_147_786, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_147_787))
in (Prims.raise _147_788))
end else begin
(let _147_791 = (let _147_790 = (let _147_789 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_147_789, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_147_790))
in (Prims.raise _147_791))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))


let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let _57_2168 = (tc_tot_or_gtot_term env t)
in (match (_57_2168) with
| (t, c, g) -> begin
(

let _57_2169 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let _57_2177 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_2177) with
| (t, c, g) -> begin
(

let _57_2178 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _147_811 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _147_811)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _147_815 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _147_815))))


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let _57_2193 = (tc_binders env tps)
in (match (_57_2193) with
| (tps, env, g, us) -> begin
(

let _57_2194 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (

let fail = (fun _57_2200 -> (match (()) with
| () -> begin
(let _147_830 = (let _147_829 = (let _147_828 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_147_828, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_147_829))
in (Prims.raise _147_830))
end))
in (

let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _57_2213))::((wp, _57_2209))::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2217 -> begin
(fail ())
end))
end
| _57_2219 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let _57_2226 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_57_2226) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _57_2228 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let _57_2232 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_57_2232) with
| (uvs, t') -> begin
(match ((let _147_837 = (FStar_Syntax_Subst.compress t')
in _147_837.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _57_2238 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))


let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (

let fail = (fun t -> (let _147_848 = (let _147_847 = (let _147_846 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_147_846, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_147_847))
in (Prims.raise _147_848)))
in (match ((let _147_849 = (FStar_Syntax_Subst.compress signature)
in _147_849.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _57_2255))::((wp, _57_2251))::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2259 -> begin
(fail signature)
end))
end
| _57_2261 -> begin
(fail signature)
end)))


let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (

let _57_2266 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_57_2266) with
| (a, wp) -> begin
(

let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _57_2269 -> begin
(

let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (

let op = (fun ts -> (

let _57_2273 = ()
in (

let t0 = (Prims.snd ts)
in (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (

let _57_2277 = ed
in (let _147_865 = (op ed.FStar_Syntax_Syntax.ret)
in (let _147_864 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _147_863 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _147_862 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _147_861 = (op ed.FStar_Syntax_Syntax.stronger)
in (let _147_860 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _147_859 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _147_858 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _147_857 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _147_856 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _57_2277.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2277.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2277.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2277.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2277.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _147_865; FStar_Syntax_Syntax.bind_wp = _147_864; FStar_Syntax_Syntax.if_then_else = _147_863; FStar_Syntax_Syntax.ite_wp = _147_862; FStar_Syntax_Syntax.stronger = _147_861; FStar_Syntax_Syntax.close_wp = _147_860; FStar_Syntax_Syntax.assert_p = _147_859; FStar_Syntax_Syntax.assume_p = _147_858; FStar_Syntax_Syntax.null_wp = _147_857; FStar_Syntax_Syntax.trivial = _147_856})))))))))))))
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

let n = (match ((let _147_887 = (FStar_Syntax_Subst.compress tm)
in _147_887.FStar_Syntax_Syntax.n)) with
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
| _57_2312 -> begin
tm.FStar_Syntax_Syntax.n
end)
in (

let _57_2314 = tm
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2314.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2314.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2314.FStar_Syntax_Syntax.vars})))
and visit_binder = (fun _57_2318 -> (match (_57_2318) with
| (bv, a) -> begin
(let _147_891 = (

let _57_2319 = bv
in (let _147_889 = (visit_term bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_2319.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2319.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_889}))
in (let _147_890 = (FStar_Syntax_Syntax.as_implicit false)
in (_147_891, _147_890)))
end))
and visit_maybe_lcomp = (fun lcomp -> (match (lcomp) with
| Some (FStar_Util.Inl (lcomp)) -> begin
(let _147_896 = (let _147_895 = (let _147_894 = (let _147_893 = (lcomp.FStar_Syntax_Syntax.comp ())
in (visit_comp _147_893))
in (FStar_Syntax_Util.lcomp_of_comp _147_894))
in FStar_Util.Inl (_147_895))
in Some (_147_896))
end
| comp -> begin
comp
end))
and visit_comp = (fun comp -> (

let n = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tm) -> begin
(let _147_898 = (visit_term tm)
in FStar_Syntax_Syntax.Total (_147_898))
end
| FStar_Syntax_Syntax.GTotal (tm) -> begin
(let _147_899 = (visit_term tm)
in FStar_Syntax_Syntax.GTotal (_147_899))
end
| comp -> begin
comp
end)
in (

let _57_2333 = comp
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2333.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2333.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2333.FStar_Syntax_Syntax.vars})))
and visit_args = (fun args -> (FStar_List.map (fun _57_2338 -> (match (_57_2338) with
| (tm, q) -> begin
(let _147_902 = (visit_term tm)
in (_147_902, q))
end)) args))
in (visit_term tm))))
in (

let check = (fun str t -> if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _57_2342 = (let _147_907 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Generated term for %s: %s\n" str _147_907))
in (

let t = (normalize t)
in (

let t = (FStar_Syntax_Subst.compress t)
in (

let _57_2357 = (tc_term env t)
in (match (_57_2357) with
| (e, {FStar_Syntax_Syntax.eff_name = _57_2353; FStar_Syntax_Syntax.res_typ = res_typ; FStar_Syntax_Syntax.cflags = _57_2350; FStar_Syntax_Syntax.comp = _57_2348}, _57_2356) -> begin
(

let _57_2358 = (let _147_910 = (let _147_909 = (normalize res_typ)
in (FStar_Syntax_Print.term_to_string _147_909))
in (FStar_Util.print2 "Inferred type for %s: %s\n" str _147_910))
in (let _147_912 = (let _147_911 = (normalize e)
in (FStar_Syntax_Print.term_to_string _147_911))
in (FStar_Util.print2 "Elaborated term for %s: %s\n" str _147_912)))
end)))))
end else begin
()
end)
in (

let rec collect_binders = (fun t -> (match ((let _147_915 = (FStar_Syntax_Subst.compress t)
in _147_915.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
t
end
| _57_2369 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _147_916 = (collect_binders rest)
in (FStar_List.append bs _147_916)))
end
| FStar_Syntax_Syntax.Tm_type (_57_2372) -> begin
[]
end
| _57_2375 -> begin
(FStar_All.failwith "wp_a doesn\'t end in Type0")
end))
in (

let _57_2390 = (

let i = (FStar_ST.alloc 0)
in (

let wp_binders = (let _147_923 = (normalize wp_a)
in (collect_binders _147_923))
in ((fun t -> (let _147_929 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow wp_binders _147_929))), (fun t -> (let _147_932 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow wp_binders _147_932))), (fun _57_2380 -> (match (()) with
| () -> begin
(FStar_List.map (fun _57_2384 -> (match (_57_2384) with
| (bv, _57_2383) -> begin
(

let _57_2385 = (let _147_936 = ((FStar_ST.read i) + 1)
in (FStar_ST.op_Colon_Equals i _147_936))
in (let _147_939 = (let _147_938 = (let _147_937 = (FStar_ST.read i)
in (FStar_Util.string_of_int _147_937))
in (Prims.strcat "g" _147_938))
in (FStar_Syntax_Syntax.gen_bv _147_939 None bv.FStar_Syntax_Syntax.sort)))
end)) wp_binders)
end)))))
in (match (_57_2390) with
| (mk_ctx, mk_gctx, mk_gamma) -> begin
(

let binders_of_list = (FStar_List.map (fun _57_2393 -> (match (_57_2393) with
| (t, b) -> begin
(let _147_945 = (FStar_Syntax_Syntax.as_implicit b)
in (t, _147_945))
end)))
in (

let implicit_binders_of_list = (FStar_List.map (fun t -> (let _147_948 = (FStar_Syntax_Syntax.as_implicit true)
in (t, _147_948))))
in (

let args_of_bv = (FStar_List.map (fun bv -> (let _147_951 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_Syntax_Syntax.as_arg _147_951))))
in (

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let x = (let _147_952 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _147_952))
in (

let ret = (let _147_957 = (let _147_956 = (let _147_955 = (let _147_954 = (let _147_953 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx _147_953))
in (FStar_Syntax_Syntax.mk_Total _147_954))
in (FStar_Syntax_Util.lcomp_of_comp _147_955))
in FStar_Util.Inl (_147_956))
in Some (_147_957))
in (

let gamma = (mk_gamma ())
in (

let body = (let _147_959 = (implicit_binders_of_list gamma)
in (let _147_958 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs _147_959 _147_958 ret)))
in (let _147_960 = (binders_of_list (((t, true))::((x, false))::[]))
in (FStar_Syntax_Util.abs _147_960 body ret)))))))
in (

let _57_2405 = (let _147_964 = (let _147_963 = (let _147_962 = (let _147_961 = (FStar_Syntax_Syntax.mk_binder a)
in (_147_961)::[])
in (FStar_List.append binders _147_962))
in (FStar_Syntax_Util.abs _147_963 c_pure None))
in (check "pure" _147_964))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let l = (let _147_972 = (let _147_971 = (let _147_970 = (let _147_967 = (let _147_966 = (let _147_965 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _147_965))
in (FStar_Syntax_Syntax.mk_binder _147_966))
in (_147_967)::[])
in (let _147_969 = (let _147_968 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _147_968))
in (FStar_Syntax_Util.arrow _147_970 _147_969)))
in (mk_gctx _147_971))
in (FStar_Syntax_Syntax.gen_bv "l" None _147_972))
in (

let r = (let _147_974 = (let _147_973 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _147_973))
in (FStar_Syntax_Syntax.gen_bv "r" None _147_974))
in (

let ret = (let _147_979 = (let _147_978 = (let _147_977 = (let _147_976 = (let _147_975 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _147_975))
in (FStar_Syntax_Syntax.mk_Total _147_976))
in (FStar_Syntax_Util.lcomp_of_comp _147_977))
in FStar_Util.Inl (_147_978))
in Some (_147_979))
in (

let outer_body = (

let gamma = (mk_gamma ())
in (

let gamma_as_args = (args_of_bv gamma)
in (

let inner_body = (let _147_985 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _147_984 = (let _147_983 = (let _147_982 = (let _147_981 = (let _147_980 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _147_980 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg _147_981))
in (_147_982)::[])
in (FStar_List.append gamma_as_args _147_983))
in (FStar_Syntax_Util.mk_app _147_985 _147_984)))
in (let _147_986 = (implicit_binders_of_list gamma)
in (FStar_Syntax_Util.abs _147_986 inner_body ret)))))
in (let _147_987 = (binders_of_list (((t1, true))::((t2, true))::((l, false))::((r, false))::[]))
in (FStar_Syntax_Util.abs _147_987 outer_body ret))))))))
in (

let _57_2417 = (let _147_991 = (let _147_990 = (let _147_989 = (let _147_988 = (FStar_Syntax_Syntax.mk_binder a)
in (_147_988)::[])
in (FStar_List.append binders _147_989))
in (FStar_Syntax_Util.abs _147_990 c_app None))
in (check "app" _147_991))
in (

let unknown = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _147_996 = (let _147_993 = (let _147_992 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _147_992))
in (_147_993)::[])
in (let _147_995 = (let _147_994 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _147_994))
in (FStar_Syntax_Util.arrow _147_996 _147_995)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _147_998 = (let _147_997 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _147_997))
in (FStar_Syntax_Syntax.gen_bv "a1" None _147_998))
in (

let ret = (let _147_1003 = (let _147_1002 = (let _147_1001 = (let _147_1000 = (let _147_999 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _147_999))
in (FStar_Syntax_Syntax.mk_Total _147_1000))
in (FStar_Syntax_Util.lcomp_of_comp _147_1001))
in FStar_Util.Inl (_147_1002))
in Some (_147_1003))
in (let _147_1016 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::((a1, false))::[]))
in (let _147_1015 = (let _147_1014 = (let _147_1013 = (let _147_1012 = (let _147_1011 = (let _147_1010 = (let _147_1007 = (let _147_1006 = (let _147_1005 = (let _147_1004 = (FStar_Syntax_Syntax.bv_to_name f)
in (_147_1004)::[])
in (unknown)::_147_1005)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1006))
in (FStar_Syntax_Util.mk_app c_pure _147_1007))
in (let _147_1009 = (let _147_1008 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_147_1008)::[])
in (_147_1010)::_147_1009))
in (unknown)::_147_1011)
in (unknown)::_147_1012)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1013))
in (FStar_Syntax_Util.mk_app c_app _147_1014))
in (FStar_Syntax_Util.abs _147_1016 _147_1015 ret)))))))))
in (

let _57_2427 = (let _147_1020 = (let _147_1019 = (let _147_1018 = (let _147_1017 = (FStar_Syntax_Syntax.mk_binder a)
in (_147_1017)::[])
in (FStar_List.append binders _147_1018))
in (FStar_Syntax_Util.abs _147_1019 c_lift1 None))
in (check "lift1" _147_1020))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _147_1028 = (let _147_1025 = (let _147_1021 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _147_1021))
in (let _147_1024 = (let _147_1023 = (let _147_1022 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder _147_1022))
in (_147_1023)::[])
in (_147_1025)::_147_1024))
in (let _147_1027 = (let _147_1026 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal _147_1026))
in (FStar_Syntax_Util.arrow _147_1028 _147_1027)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _147_1030 = (let _147_1029 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _147_1029))
in (FStar_Syntax_Syntax.gen_bv "a1" None _147_1030))
in (

let a2 = (let _147_1032 = (let _147_1031 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _147_1031))
in (FStar_Syntax_Syntax.gen_bv "a2" None _147_1032))
in (

let ret = (let _147_1037 = (let _147_1036 = (let _147_1035 = (let _147_1034 = (let _147_1033 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx _147_1033))
in (FStar_Syntax_Syntax.mk_Total _147_1034))
in (FStar_Syntax_Util.lcomp_of_comp _147_1035))
in FStar_Util.Inl (_147_1036))
in Some (_147_1037))
in (let _147_1057 = (binders_of_list (((t1, true))::((t2, true))::((t3, true))::((f, false))::((a1, false))::((a2, false))::[]))
in (let _147_1056 = (let _147_1055 = (let _147_1054 = (let _147_1053 = (let _147_1052 = (let _147_1051 = (let _147_1048 = (let _147_1047 = (let _147_1046 = (let _147_1045 = (let _147_1044 = (let _147_1041 = (let _147_1040 = (let _147_1039 = (let _147_1038 = (FStar_Syntax_Syntax.bv_to_name f)
in (_147_1038)::[])
in (unknown)::_147_1039)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1040))
in (FStar_Syntax_Util.mk_app c_pure _147_1041))
in (let _147_1043 = (let _147_1042 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_147_1042)::[])
in (_147_1044)::_147_1043))
in (unknown)::_147_1045)
in (unknown)::_147_1046)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1047))
in (FStar_Syntax_Util.mk_app c_app _147_1048))
in (let _147_1050 = (let _147_1049 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_147_1049)::[])
in (_147_1051)::_147_1050))
in (unknown)::_147_1052)
in (unknown)::_147_1053)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1054))
in (FStar_Syntax_Util.mk_app c_app _147_1055))
in (FStar_Syntax_Util.abs _147_1057 _147_1056 ret)))))))))))
in (

let _57_2438 = (let _147_1061 = (let _147_1060 = (let _147_1059 = (let _147_1058 = (FStar_Syntax_Syntax.mk_binder a)
in (_147_1058)::[])
in (FStar_List.append binders _147_1059))
in (FStar_Syntax_Util.abs _147_1060 c_lift2 None))
in (check "lift2" _147_1061))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _147_1067 = (let _147_1063 = (let _147_1062 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _147_1062))
in (_147_1063)::[])
in (let _147_1066 = (let _147_1065 = (let _147_1064 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _147_1064))
in (FStar_Syntax_Syntax.mk_Total _147_1065))
in (FStar_Syntax_Util.arrow _147_1067 _147_1066)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let ret = (let _147_1077 = (let _147_1076 = (let _147_1075 = (let _147_1074 = (let _147_1073 = (let _147_1072 = (let _147_1069 = (let _147_1068 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _147_1068))
in (_147_1069)::[])
in (let _147_1071 = (let _147_1070 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _147_1070))
in (FStar_Syntax_Util.arrow _147_1072 _147_1071)))
in (mk_ctx _147_1073))
in (FStar_Syntax_Syntax.mk_Total _147_1074))
in (FStar_Syntax_Util.lcomp_of_comp _147_1075))
in FStar_Util.Inl (_147_1076))
in Some (_147_1077))
in (

let e1 = (let _147_1078 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _147_1078))
in (

let gamma = (mk_gamma ())
in (

let body = (let _147_1088 = (let _147_1081 = (FStar_Syntax_Syntax.binders_of_list gamma)
in (let _147_1080 = (let _147_1079 = (FStar_Syntax_Syntax.mk_binder e1)
in (_147_1079)::[])
in (FStar_List.append _147_1081 _147_1080)))
in (let _147_1087 = (let _147_1086 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _147_1085 = (let _147_1084 = (let _147_1082 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _147_1082))
in (let _147_1083 = (args_of_bv gamma)
in (_147_1084)::_147_1083))
in (FStar_Syntax_Util.mk_app _147_1086 _147_1085)))
in (FStar_Syntax_Util.abs _147_1088 _147_1087 ret)))
in (let _147_1089 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::[]))
in (FStar_Syntax_Util.abs _147_1089 body ret))))))))))
in (

let _57_2449 = (let _147_1093 = (let _147_1092 = (let _147_1091 = (let _147_1090 = (FStar_Syntax_Syntax.mk_binder a)
in (_147_1090)::[])
in (FStar_List.append binders _147_1091))
in (FStar_Syntax_Util.abs _147_1092 c_push None))
in (check "push" _147_1093))
in (

let ret_tot_wp_a = (let _147_1096 = (let _147_1095 = (let _147_1094 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _147_1094))
in FStar_Util.Inl (_147_1095))
in Some (_147_1096))
in (

let wp_if_then_else = (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _147_1107 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (let _147_1106 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_unfoldable (2)) None)
in (let _147_1105 = (let _147_1104 = (let _147_1103 = (let _147_1102 = (let _147_1101 = (let _147_1100 = (let _147_1099 = (let _147_1098 = (let _147_1097 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _147_1097))
in (_147_1098)::[])
in (FStar_Syntax_Util.mk_app l_ite _147_1099))
in (_147_1100)::[])
in (unknown)::_147_1101)
in (unknown)::_147_1102)
in (unknown)::_147_1103)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1104))
in (FStar_Syntax_Util.mk_app c_lift2 _147_1105)))
in (FStar_Syntax_Util.abs _147_1107 _147_1106 ret_tot_wp_a))))
in (

let wp_if_then_else = (normalize_and_make_binders_explicit wp_if_then_else)
in (

let _57_2456 = (let _147_1108 = (FStar_Syntax_Util.abs binders wp_if_then_else None)
in (check "wp_if_then_else" _147_1108))
in (

let wp_assert = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_and = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (

let body = (let _147_1122 = (let _147_1121 = (let _147_1120 = (let _147_1119 = (let _147_1118 = (let _147_1115 = (let _147_1114 = (let _147_1113 = (let _147_1112 = (let _147_1111 = (let _147_1110 = (let _147_1109 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _147_1109))
in (_147_1110)::[])
in (FStar_Syntax_Util.mk_app l_and _147_1111))
in (_147_1112)::[])
in (unknown)::_147_1113)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1114))
in (FStar_Syntax_Util.mk_app c_pure _147_1115))
in (let _147_1117 = (let _147_1116 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_147_1116)::[])
in (_147_1118)::_147_1117))
in (unknown)::_147_1119)
in (unknown)::_147_1120)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1121))
in (FStar_Syntax_Util.mk_app c_app _147_1122))
in (let _147_1123 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _147_1123 body ret_tot_wp_a))))))
in (

let wp_assert = (normalize_and_make_binders_explicit wp_assert)
in (

let _57_2464 = (let _147_1124 = (FStar_Syntax_Util.abs binders wp_assert None)
in (check "wp_assert" _147_1124))
in (

let wp_assume = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_imp = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (

let body = (let _147_1138 = (let _147_1137 = (let _147_1136 = (let _147_1135 = (let _147_1134 = (let _147_1131 = (let _147_1130 = (let _147_1129 = (let _147_1128 = (let _147_1127 = (let _147_1126 = (let _147_1125 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _147_1125))
in (_147_1126)::[])
in (FStar_Syntax_Util.mk_app l_imp _147_1127))
in (_147_1128)::[])
in (unknown)::_147_1129)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1130))
in (FStar_Syntax_Util.mk_app c_pure _147_1131))
in (let _147_1133 = (let _147_1132 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_147_1132)::[])
in (_147_1134)::_147_1133))
in (unknown)::_147_1135)
in (unknown)::_147_1136)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1137))
in (FStar_Syntax_Util.mk_app c_app _147_1138))
in (let _147_1139 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _147_1139 body ret_tot_wp_a))))))
in (

let wp_assume = (normalize_and_make_binders_explicit wp_assume)
in (

let _57_2472 = (let _147_1140 = (FStar_Syntax_Util.abs binders wp_assume None)
in (check "wp_assume" _147_1140))
in (

let tforall = (let _147_1143 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _147_1142 = (let _147_1141 = (FStar_Syntax_Syntax.as_arg unknown)
in (_147_1141)::[])
in (FStar_Syntax_Util.mk_app _147_1143 _147_1142)))
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _147_1147 = (let _147_1145 = (let _147_1144 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _147_1144))
in (_147_1145)::[])
in (let _147_1146 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _147_1147 _147_1146)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (let _147_1160 = (let _147_1159 = (let _147_1158 = (let _147_1157 = (let _147_1156 = (let _147_1148 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((unknown)::(tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _147_1148))
in (let _147_1155 = (let _147_1154 = (let _147_1153 = (let _147_1152 = (let _147_1151 = (let _147_1150 = (let _147_1149 = (FStar_Syntax_Syntax.bv_to_name f)
in (_147_1149)::[])
in (unknown)::_147_1150)
in (unknown)::_147_1151)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1152))
in (FStar_Syntax_Util.mk_app c_push _147_1153))
in (_147_1154)::[])
in (_147_1156)::_147_1155))
in (unknown)::_147_1157)
in (unknown)::_147_1158)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1159))
in (FStar_Syntax_Util.mk_app c_app _147_1160))
in (let _147_1161 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_Syntax_Util.abs _147_1161 body ret_tot_wp_a))))))
in (

let wp_close = (normalize_and_make_binders_explicit wp_close)
in (

let _57_2481 = (let _147_1162 = (FStar_Syntax_Util.abs binders wp_close None)
in (check "wp_close" _147_1162))
in (

let ret_tot_type0 = (let _147_1165 = (let _147_1164 = (let _147_1163 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _147_1163))
in FStar_Util.Inl (_147_1164))
in Some (_147_1165))
in (

let mk_forall = (fun x body -> (

let tforall = (let _147_1172 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _147_1171 = (let _147_1170 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (_147_1170)::[])
in (FStar_Syntax_Util.mk_app _147_1172 _147_1171)))
in (let _147_1179 = (let _147_1178 = (let _147_1177 = (let _147_1176 = (let _147_1175 = (let _147_1174 = (let _147_1173 = (FStar_Syntax_Syntax.mk_binder x)
in (_147_1173)::[])
in (FStar_Syntax_Util.abs _147_1174 body ret_tot_type0))
in (FStar_Syntax_Syntax.as_arg _147_1175))
in (_147_1176)::[])
in (tforall, _147_1177))
in FStar_Syntax_Syntax.Tm_app (_147_1178))
in (FStar_Syntax_Syntax.mk _147_1179 None FStar_Range.dummyRange))))
in (

let rec mk_leq = (fun t x y -> (match ((let _147_1187 = (let _147_1186 = (FStar_Syntax_Subst.compress t)
in (normalize _147_1186))
in _147_1187.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_2493) -> begin
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

let body = (let _147_1199 = (let _147_1189 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _147_1188 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_leq a _147_1189 _147_1188)))
in (let _147_1198 = (let _147_1197 = (let _147_1192 = (let _147_1191 = (let _147_1190 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _147_1190))
in (_147_1191)::[])
in (FStar_Syntax_Util.mk_app x _147_1192))
in (let _147_1196 = (let _147_1195 = (let _147_1194 = (let _147_1193 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _147_1193))
in (_147_1194)::[])
in (FStar_Syntax_Util.mk_app y _147_1195))
in (mk_leq b _147_1197 _147_1196)))
in (FStar_Syntax_Util.mk_imp _147_1199 _147_1198)))
in (let _147_1200 = (mk_forall a2 body)
in (mk_forall a1 _147_1200))))))
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let _57_2529 = t
in (let _147_1204 = (let _147_1203 = (let _147_1202 = (let _147_1201 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _147_1201))
in ((binder)::[], _147_1202))
in FStar_Syntax_Syntax.Tm_arrow (_147_1203))
in {FStar_Syntax_Syntax.n = _147_1204; FStar_Syntax_Syntax.tk = _57_2529.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2529.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2529.FStar_Syntax_Syntax.vars}))
in (mk_leq t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_57_2533) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _57_2536 -> begin
(FStar_Syntax_Util.mk_eq t t x y)
end))
in (

let stronger = (

let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (

let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (

let body = (let _147_1206 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _147_1205 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_leq wp_a _147_1206 _147_1205)))
in (let _147_1207 = (FStar_Syntax_Syntax.binders_of_list ((wp1)::(wp2)::[]))
in (FStar_Syntax_Util.abs _147_1207 body ret_tot_type0)))))
in (

let _57_2541 = (let _147_1211 = (let _147_1210 = (let _147_1209 = (let _147_1208 = (FStar_Syntax_Syntax.mk_binder a)
in (_147_1208)::[])
in (FStar_List.append binders _147_1209))
in (FStar_Syntax_Util.abs _147_1210 stronger None))
in (check "stronger" _147_1211))
in (

let null_wp = (Prims.snd ed.FStar_Syntax_Syntax.null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (let _147_1219 = (let _147_1218 = (let _147_1217 = (let _147_1214 = (let _147_1213 = (let _147_1212 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _147_1212))
in (_147_1213)::[])
in (FStar_Syntax_Util.mk_app null_wp _147_1214))
in (let _147_1216 = (let _147_1215 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_147_1215)::[])
in (_147_1217)::_147_1216))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _147_1218))
in (FStar_Syntax_Util.mk_app stronger _147_1219))
in (let _147_1220 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_Syntax_Util.abs _147_1220 body ret_tot_type0))))
in (

let wp_trivial = (normalize_and_make_binders_explicit wp_trivial)
in (

let _57_2548 = (let _147_1221 = (FStar_Syntax_Util.abs binders wp_trivial None)
in (check "wp_trivial" _147_1221))
in (

let _57_2550 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2550.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2550.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2550.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2550.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2550.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _57_2550.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2550.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = ([], wp_if_then_else); FStar_Syntax_Syntax.ite_wp = _57_2550.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _57_2550.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = ([], wp_close); FStar_Syntax_Syntax.assert_p = ([], wp_assert); FStar_Syntax_Syntax.assume_p = ([], wp_assume); FStar_Syntax_Syntax.null_wp = _57_2550.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = ([], wp_trivial)}))))))))))))))))))))))))))))))))))))))
end))))))))


let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  effect_cost  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed is_for_free -> (

let _57_2555 = ()
in (

let _57_2559 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_57_2559) with
| (binders_un, signature_un) -> begin
(

let _57_2564 = (tc_tparams env0 binders_un)
in (match (_57_2564) with
| (binders, env, _57_2563) -> begin
(

let _57_2568 = (tc_trivial_guard env signature_un)
in (match (_57_2568) with
| (signature, _57_2567) -> begin
(

let ed = (

let _57_2569 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2569.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2569.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2569.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _57_2569.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2569.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _57_2569.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _57_2569.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _57_2569.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _57_2569.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _57_2569.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _57_2569.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _57_2569.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _57_2569.FStar_Syntax_Syntax.trivial})
in (

let _57_2575 = (open_effect_decl env ed)
in (match (_57_2575) with
| (ed, a, wp_a) -> begin
(

let get_effect_signature = (fun _57_2577 -> (match (()) with
| () -> begin
(

let _57_2581 = (tc_trivial_guard env signature_un)
in (match (_57_2581) with
| (signature, _57_2580) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (

let env = (let _147_1230 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _147_1230))
in (

let _57_2583 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _147_1233 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _147_1232 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _147_1231 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checking effect signature: %s %s : %s\n" _147_1233 _147_1232 _147_1231))))
end else begin
()
end
in (

let check_and_gen' = (fun env _57_2590 k -> (match (_57_2590) with
| (_57_2588, t) -> begin
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

let expected_k = (let _147_1245 = (let _147_1243 = (FStar_Syntax_Syntax.mk_binder a)
in (let _147_1242 = (let _147_1241 = (let _147_1240 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _147_1240))
in (_147_1241)::[])
in (_147_1243)::_147_1242))
in (let _147_1244 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _147_1245 _147_1244)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (

let bind_wp = (

let _57_2599 = (get_effect_signature ())
in (match (_57_2599) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _147_1249 = (let _147_1247 = (let _147_1246 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _147_1246))
in (_147_1247)::[])
in (let _147_1248 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _147_1249 _147_1248)))
in (

let expected_k = (let _147_1260 = (let _147_1258 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _147_1257 = (let _147_1256 = (FStar_Syntax_Syntax.mk_binder a)
in (let _147_1255 = (let _147_1254 = (FStar_Syntax_Syntax.mk_binder b)
in (let _147_1253 = (let _147_1252 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _147_1251 = (let _147_1250 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (_147_1250)::[])
in (_147_1252)::_147_1251))
in (_147_1254)::_147_1253))
in (_147_1256)::_147_1255))
in (_147_1258)::_147_1257))
in (let _147_1259 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _147_1260 _147_1259)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (let _147_1262 = (let _147_1261 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _147_1261 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _147_1262))
in (

let expected_k = (let _147_1271 = (let _147_1269 = (FStar_Syntax_Syntax.mk_binder a)
in (let _147_1268 = (let _147_1267 = (FStar_Syntax_Syntax.mk_binder p)
in (let _147_1266 = (let _147_1265 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _147_1264 = (let _147_1263 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_147_1263)::[])
in (_147_1265)::_147_1264))
in (_147_1267)::_147_1266))
in (_147_1269)::_147_1268))
in (let _147_1270 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _147_1271 _147_1270)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (let _147_1276 = (let _147_1274 = (FStar_Syntax_Syntax.mk_binder a)
in (let _147_1273 = (let _147_1272 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_147_1272)::[])
in (_147_1274)::_147_1273))
in (let _147_1275 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _147_1276 _147_1275)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let _57_2611 = (FStar_Syntax_Util.type_u ())
in (match (_57_2611) with
| (t, _57_2610) -> begin
(

let expected_k = (let _147_1283 = (let _147_1281 = (FStar_Syntax_Syntax.mk_binder a)
in (let _147_1280 = (let _147_1279 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _147_1278 = (let _147_1277 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_147_1277)::[])
in (_147_1279)::_147_1278))
in (_147_1281)::_147_1280))
in (let _147_1282 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _147_1283 _147_1282)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (let _147_1285 = (let _147_1284 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _147_1284 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _147_1285))
in (

let b_wp_a = (let _147_1289 = (let _147_1287 = (let _147_1286 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _147_1286))
in (_147_1287)::[])
in (let _147_1288 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _147_1289 _147_1288)))
in (

let expected_k = (let _147_1296 = (let _147_1294 = (FStar_Syntax_Syntax.mk_binder a)
in (let _147_1293 = (let _147_1292 = (FStar_Syntax_Syntax.mk_binder b)
in (let _147_1291 = (let _147_1290 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_147_1290)::[])
in (_147_1292)::_147_1291))
in (_147_1294)::_147_1293))
in (let _147_1295 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _147_1296 _147_1295)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (let _147_1305 = (let _147_1303 = (FStar_Syntax_Syntax.mk_binder a)
in (let _147_1302 = (let _147_1301 = (let _147_1298 = (let _147_1297 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _147_1297 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _147_1298))
in (let _147_1300 = (let _147_1299 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_147_1299)::[])
in (_147_1301)::_147_1300))
in (_147_1303)::_147_1302))
in (let _147_1304 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _147_1305 _147_1304)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _147_1314 = (let _147_1312 = (FStar_Syntax_Syntax.mk_binder a)
in (let _147_1311 = (let _147_1310 = (let _147_1307 = (let _147_1306 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _147_1306 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _147_1307))
in (let _147_1309 = (let _147_1308 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_147_1308)::[])
in (_147_1310)::_147_1309))
in (_147_1312)::_147_1311))
in (let _147_1313 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _147_1314 _147_1313)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _147_1317 = (let _147_1315 = (FStar_Syntax_Syntax.mk_binder a)
in (_147_1315)::[])
in (let _147_1316 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _147_1317 _147_1316)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let _57_2627 = (FStar_Syntax_Util.type_u ())
in (match (_57_2627) with
| (t, _57_2626) -> begin
(

let expected_k = (let _147_1322 = (let _147_1320 = (FStar_Syntax_Syntax.mk_binder a)
in (let _147_1319 = (let _147_1318 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_147_1318)::[])
in (_147_1320)::_147_1319))
in (let _147_1321 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _147_1322 _147_1321)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let t = (let _147_1323 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _147_1323))
in (

let _57_2633 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_57_2633) with
| (univs, t) -> begin
(

let _57_2649 = (match ((let _147_1325 = (let _147_1324 = (FStar_Syntax_Subst.compress t)
in _147_1324.FStar_Syntax_Syntax.n)
in (binders, _147_1325))) with
| ([], _57_2636) -> begin
([], t)
end
| (_57_2639, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _57_2646 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_2649) with
| (binders, signature) -> begin
(

let close = (fun n ts -> (

let ts = (let _147_1330 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _147_1330))
in (

let _57_2654 = ()
in ts)))
in (

let ed = (

let _57_2656 = ed
in (let _147_1340 = (close 0 ret)
in (let _147_1339 = (close 1 bind_wp)
in (let _147_1338 = (close 0 if_then_else)
in (let _147_1337 = (close 0 ite_wp)
in (let _147_1336 = (close 0 stronger)
in (let _147_1335 = (close 1 close_wp)
in (let _147_1334 = (close 0 assert_p)
in (let _147_1333 = (close 0 assume_p)
in (let _147_1332 = (close 0 null_wp)
in (let _147_1331 = (close 0 trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _57_2656.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2656.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _147_1340; FStar_Syntax_Syntax.bind_wp = _147_1339; FStar_Syntax_Syntax.if_then_else = _147_1338; FStar_Syntax_Syntax.ite_wp = _147_1337; FStar_Syntax_Syntax.stronger = _147_1336; FStar_Syntax_Syntax.close_wp = _147_1335; FStar_Syntax_Syntax.assert_p = _147_1334; FStar_Syntax_Syntax.assume_p = _147_1333; FStar_Syntax_Syntax.null_wp = _147_1332; FStar_Syntax_Syntax.trivial = _147_1331})))))))))))
in (

let _57_2659 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_1341 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _147_1341))
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

let _57_2665 = ()
in (

let _57_2673 = ()
in (match (ses) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _57_2702, _57_2704, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _57_2693, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _57_2682, r2))::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
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

let lex_top_t = (let _147_1349 = (let _147_1348 = (let _147_1347 = (let _147_1346 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _147_1346 FStar_Syntax_Syntax.Delta_constant None))
in (_147_1347, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_147_1348))
in (FStar_Syntax_Syntax.mk _147_1349 None r1))
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

let a = (let _147_1350 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _147_1350))
in (

let hd = (let _147_1351 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _147_1351))
in (

let tl = (let _147_1356 = (let _147_1355 = (let _147_1354 = (let _147_1353 = (let _147_1352 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _147_1352 FStar_Syntax_Syntax.Delta_constant None))
in (_147_1353, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_147_1354))
in (FStar_Syntax_Syntax.mk _147_1355 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _147_1356))
in (

let res = (let _147_1360 = (let _147_1359 = (let _147_1358 = (let _147_1357 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _147_1357 FStar_Syntax_Syntax.Delta_constant None))
in (_147_1358, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_147_1359))
in (FStar_Syntax_Syntax.mk _147_1360 None r2))
in (let _147_1361 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _147_1361))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _147_1363 = (let _147_1362 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _147_1362))
in FStar_Syntax_Syntax.Sig_bundle (_147_1363)))))))))))))))
end
| _57_2728 -> begin
(let _147_1365 = (let _147_1364 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _147_1364))
in (FStar_All.failwith _147_1365))
end))))


let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _147_1379 = (let _147_1378 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _147_1378))
in (FStar_TypeChecker_Errors.diag r _147_1379)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let _57_2750 = ()
in (

let _57_2752 = (warn_positivity tc r)
in (

let _57_2756 = (FStar_Syntax_Subst.open_term tps k)
in (match (_57_2756) with
| (tps, k) -> begin
(

let _57_2760 = (tc_tparams env tps)
in (match (_57_2760) with
| (tps, env_tps, us) -> begin
(

let _57_2763 = (FStar_Syntax_Util.arrow_formals k)
in (match (_57_2763) with
| (indices, t) -> begin
(

let _57_2767 = (tc_tparams env_tps indices)
in (match (_57_2767) with
| (indices, env', us') -> begin
(

let _57_2771 = (tc_trivial_guard env' t)
in (match (_57_2771) with
| (t, _57_2770) -> begin
(

let k = (let _147_1384 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _147_1384))
in (

let _57_2775 = (FStar_Syntax_Util.type_u ())
in (match (_57_2775) with
| (t_type, u) -> begin
(

let _57_2776 = (let _147_1385 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _147_1385))
in (

let t_tc = (let _147_1386 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _147_1386))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _147_1387 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) ([], t_tc))
in (_147_1387, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u)))))))
end)))
end))
end))
end))
end))
end))))
end
| _57_2783 -> begin
(FStar_All.failwith "impossible")
end))
in (

let positive_if_pure = (fun _57_2785 l -> ())
in (

let tc_data = (fun env tcs _57_7 -> (match (_57_7) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let _57_2802 = ()
in (

let _57_2837 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _57_2806 -> (match (_57_2806) with
| (se, u_tc) -> begin
if (let _147_1400 = (let _147_1399 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _147_1399))
in (FStar_Ident.lid_equals tc_lid _147_1400)) then begin
(

let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2808, _57_2810, tps, _57_2813, _57_2815, _57_2817, _57_2819, _57_2821) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _57_2827 -> (match (_57_2827) with
| (x, _57_2826) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _57_2829 -> begin
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
in (match (_57_2837) with
| (tps, u_tc) -> begin
(

let _57_2857 = (match ((let _147_1402 = (FStar_Syntax_Subst.compress t)
in _147_1402.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _57_2845 = (FStar_Util.first_N ntps bs)
in (match (_57_2845) with
| (_57_2843, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _57_2851 -> (match (_57_2851) with
| (x, _57_2850) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _147_1405 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _147_1405))))
end))
end
| _57_2854 -> begin
([], t)
end)
in (match (_57_2857) with
| (arguments, result) -> begin
(

let _57_2858 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_1408 = (FStar_Syntax_Print.lid_to_string c)
in (let _147_1407 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _147_1406 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _147_1408 _147_1407 _147_1406))))
end else begin
()
end
in (

let _57_2863 = (tc_tparams env arguments)
in (match (_57_2863) with
| (arguments, env', us) -> begin
(

let _57_2867 = (tc_trivial_guard env' result)
in (match (_57_2867) with
| (result, _57_2866) -> begin
(

let _57_2871 = (FStar_Syntax_Util.head_and_args result)
in (match (_57_2871) with
| (head, _57_2870) -> begin
(

let _57_2876 = (match ((let _147_1409 = (FStar_Syntax_Subst.compress head)
in _147_1409.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _57_2875 -> begin
(let _147_1414 = (let _147_1413 = (let _147_1412 = (let _147_1411 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _147_1410 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _147_1411 _147_1410)))
in (_147_1412, r))
in FStar_Syntax_Syntax.Error (_147_1413))
in (Prims.raise _147_1414))
end)
in (

let g = (FStar_List.fold_left2 (fun g _57_2882 u_x -> (match (_57_2882) with
| (x, _57_2881) -> begin
(

let _57_2884 = ()
in (let _147_1418 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _147_1418)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _147_1422 = (let _147_1420 = (FStar_All.pipe_right tps (FStar_List.map (fun _57_2890 -> (match (_57_2890) with
| (x, _57_2889) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _147_1420 arguments))
in (let _147_1421 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _147_1422 _147_1421)))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _57_2893 -> begin
(FStar_All.failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let _57_2899 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_8 -> (match (_57_8) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2903, _57_2905, tps, k, _57_2909, _57_2911, _57_2913, _57_2915) -> begin
(let _147_1433 = (let _147_1432 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _147_1432))
in (FStar_Syntax_Syntax.null_binder _147_1433))
end
| _57_2919 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _57_9 -> (match (_57_9) with
| FStar_Syntax_Syntax.Sig_datacon (_57_2923, _57_2925, t, _57_2928, _57_2930, _57_2932, _57_2934, _57_2936) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _57_2940 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let t = (let _147_1435 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _147_1435))
in (

let _57_2943 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_1436 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _147_1436))
end else begin
()
end
in (

let _57_2947 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_57_2947) with
| (uvs, t) -> begin
(

let _57_2949 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_1440 = (let _147_1438 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _147_1438 (FStar_String.concat ", ")))
in (let _147_1439 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _147_1440 _147_1439)))
end else begin
()
end
in (

let _57_2953 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_57_2953) with
| (uvs, t) -> begin
(

let _57_2957 = (FStar_Syntax_Util.arrow_formals t)
in (match (_57_2957) with
| (args, _57_2956) -> begin
(

let _57_2960 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_57_2960) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _57_2964 se -> (match (_57_2964) with
| (x, _57_2963) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_2968, tps, _57_2971, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let _57_2994 = (match ((let _147_1443 = (FStar_Syntax_Subst.compress ty)
in _147_1443.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _57_2985 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_57_2985) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _57_2988 -> begin
(let _147_1444 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _147_1444 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _57_2991 -> begin
([], ty)
end)
in (match (_57_2994) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _57_2996 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| _57_3000 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _147_1445 -> FStar_Syntax_Syntax.U_name (_147_1445))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_10 -> (match (_57_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3005, _57_3007, _57_3009, _57_3011, _57_3013, _57_3015, _57_3017) -> begin
(tc, uvs_universes)
end
| _57_3021 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _57_3026 d -> (match (_57_3026) with
| (t, _57_3025) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _57_3030, _57_3032, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _147_1449 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _147_1449 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _57_3042 -> begin
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

let _57_3052 = (FStar_All.pipe_right ses (FStar_List.partition (fun _57_11 -> (match (_57_11) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_3046) -> begin
true
end
| _57_3049 -> begin
false
end))))
in (match (_57_3052) with
| (tys, datas) -> begin
(

let env0 = env
in (

let _57_3069 = (FStar_List.fold_right (fun tc _57_3058 -> (match (_57_3058) with
| (env, all_tcs, g) -> begin
(

let _57_3062 = (tc_tycon env tc)
in (match (_57_3062) with
| (env, tc, tc_u) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (

let _57_3064 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_1453 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _147_1453))
end else begin
()
end
in (let _147_1454 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _147_1454))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_3069) with
| (env, tcs, g) -> begin
(

let _57_3079 = (FStar_List.fold_right (fun se _57_3073 -> (match (_57_3073) with
| (datas, g) -> begin
(

let _57_3076 = (tc_data env tcs se)
in (match (_57_3076) with
| (data, g') -> begin
(let _147_1457 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _147_1457))
end))
end)) datas ([], g))
in (match (_57_3079) with
| (datas, g) -> begin
(

let _57_3082 = (let _147_1458 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _147_1458 datas))
in (match (_57_3082) with
| (tcs, datas) -> begin
(let _147_1460 = (let _147_1459 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _147_1459))
in FStar_Syntax_Syntax.Sig_bundle (_147_1460))
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
in (let _147_1465 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _147_1465))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let se = (tc_inductive env ses quals lids)
in (let _147_1466 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _147_1466))))
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

let _57_3120 = (set_options FStar_Options.Set o)
in (se, env))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(

let _57_3124 = (let _147_1471 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _147_1471 Prims.ignore))
in (

let _57_3129 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _57_3131 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
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

let _57_3153 = (let _147_1472 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _147_1472))
in (match (_57_3153) with
| (a, wp_a_src) -> begin
(

let _57_3156 = (let _147_1473 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _147_1473))
in (match (_57_3156) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _147_1477 = (let _147_1476 = (let _147_1475 = (let _147_1474 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _147_1474))
in FStar_Syntax_Syntax.NT (_147_1475))
in (_147_1476)::[])
in (FStar_Syntax_Subst.subst _147_1477 wp_b_tgt))
in (

let expected_k = (let _147_1482 = (let _147_1480 = (FStar_Syntax_Syntax.mk_binder a)
in (let _147_1479 = (let _147_1478 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_147_1478)::[])
in (_147_1480)::_147_1479))
in (let _147_1481 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _147_1482 _147_1481)))
in (

let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (

let sub = (

let _57_3160 = sub
in {FStar_Syntax_Syntax.source = _57_3160.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _57_3160.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
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

let _57_3173 = ()
in (

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _57_3179 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_57_3179) with
| (tps, c) -> begin
(

let _57_3183 = (tc_tparams env tps)
in (match (_57_3183) with
| (tps, env, us) -> begin
(

let _57_3187 = (tc_comp env c)
in (match (_57_3187) with
| (c, u, g) -> begin
(

let _57_3188 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let _57_3194 = (let _147_1483 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _147_1483))
in (match (_57_3194) with
| (uvs, t) -> begin
(

let _57_3213 = (match ((let _147_1485 = (let _147_1484 = (FStar_Syntax_Subst.compress t)
in _147_1484.FStar_Syntax_Syntax.n)
in (tps, _147_1485))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_57_3197, c)) -> begin
([], c)
end
| (_57_3203, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _57_3210 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_3213) with
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

let _57_3224 = ()
in (

let _57_3228 = (let _147_1487 = (let _147_1486 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _147_1486))
in (check_and_gen env t _147_1487))
in (match (_57_3228) with
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

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _57_3241 = (FStar_Syntax_Util.type_u ())
in (match (_57_3241) with
| (k, _57_3240) -> begin
(

let phi = (let _147_1488 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _147_1488 (norm env)))
in (

let _57_3243 = (FStar_TypeChecker_Util.check_uvars r phi)
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

let _57_3256 = (tc_term env e)
in (match (_57_3256) with
| (e, c, g1) -> begin
(

let _57_3261 = (let _147_1492 = (let _147_1489 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_147_1489))
in (let _147_1491 = (let _147_1490 = (c.FStar_Syntax_Syntax.comp ())
in (e, _147_1490))
in (check_expected_effect env _147_1492 _147_1491)))
in (match (_57_3261) with
| (e, _57_3259, g) -> begin
(

let _57_3262 = (let _147_1493 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _147_1493))
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
(let _147_1505 = (let _147_1504 = (let _147_1503 = (let _147_1502 = (FStar_Syntax_Print.lid_to_string l)
in (let _147_1501 = (FStar_Syntax_Print.quals_to_string q)
in (let _147_1500 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _147_1502 _147_1501 _147_1500))))
in (_147_1503, r))
in FStar_Syntax_Syntax.Error (_147_1504))
in (Prims.raise _147_1505))
end
end))
in (

let _57_3306 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _57_3283 lb -> (match (_57_3283) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _57_3302 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (

let _57_3297 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _57_3296 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _147_1508 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _147_1508, quals_opt))))
end)
in (match (_57_3302) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_57_3306) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _57_12 -> (match (_57_12) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _57_3315 -> begin
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

let e = (let _147_1512 = (let _147_1511 = (let _147_1510 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _147_1510))
in FStar_Syntax_Syntax.Tm_let (_147_1511))
in (FStar_Syntax_Syntax.mk _147_1512 None r))
in (

let _57_3349 = (match ((tc_maybe_toplevel_term (

let _57_3319 = env
in {FStar_TypeChecker_Env.solver = _57_3319.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3319.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3319.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3319.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3319.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3319.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3319.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3319.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3319.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3319.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3319.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _57_3319.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _57_3319.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3319.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3319.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3319.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3319.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3319.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3319.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _57_3326; FStar_Syntax_Syntax.pos = _57_3324; FStar_Syntax_Syntax.vars = _57_3322}, _57_3333, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_57_3337, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _57_3343 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _57_3346 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_57_3349) with
| (se, lbs) -> begin
(

let _57_3355 = if (log env) then begin
(let _147_1520 = (let _147_1519 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _147_1516 = (let _147_1515 = (let _147_1514 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _147_1514.FStar_Syntax_Syntax.fv_name)
in _147_1515.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _147_1516))) with
| None -> begin
true
end
| _57_3353 -> begin
false
end)
in if should_log then begin
(let _147_1518 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _147_1517 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _147_1518 _147_1517)))
end else begin
""
end))))
in (FStar_All.pipe_right _147_1519 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _147_1520))
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

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _57_13 -> (match (_57_13) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _57_3365 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _57_3375 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_57_3377) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _57_3388, _57_3390) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _57_3396 -> (match (_57_3396) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _57_3402, _57_3404, quals, r) -> begin
(

let dec = (let _147_1536 = (let _147_1535 = (let _147_1534 = (let _147_1533 = (let _147_1532 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _147_1532))
in FStar_Syntax_Syntax.Tm_arrow (_147_1533))
in (FStar_Syntax_Syntax.mk _147_1534 None r))
in (l, us, _147_1535, (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_147_1536))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _57_3414, _57_3416, _57_3418, _57_3420, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _57_3426 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_57_3428, _57_3430, quals, _57_3433) -> begin
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
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _57_14 -> (match (_57_14) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _57_3452 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_57_3454) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _57_3473, _57_3475, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
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
(let _147_1543 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _147_1542 = (let _147_1541 = (let _147_1540 = (let _147_1539 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _147_1539.FStar_Syntax_Syntax.fv_name)
in _147_1540.FStar_Syntax_Syntax.v)
in (_147_1541, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_147_1542)))))
in (_147_1543, hidden))
end else begin
((se)::[], hidden)
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let _57_3514 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _57_3495 se -> (match (_57_3495) with
| (ses, exports, env, hidden) -> begin
(

let _57_3497 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_1550 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _147_1550))
end else begin
()
end
in (

let _57_3501 = (tc_decl env se)
in (match (_57_3501) with
| (se, env) -> begin
(

let _57_3502 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _147_1551 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _147_1551))
end else begin
()
end
in (

let _57_3504 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (

let _57_3508 = (for_export hidden se)
in (match (_57_3508) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_57_3514) with
| (ses, exports, env, _57_3513) -> begin
(let _147_1552 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _147_1552, env))
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

let _57_3519 = env
in (let _147_1557 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _57_3519.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3519.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3519.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3519.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3519.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3519.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3519.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3519.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3519.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3519.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3519.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3519.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3519.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_3519.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_3519.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3519.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _147_1557; FStar_TypeChecker_Env.type_of = _57_3519.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3519.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3519.FStar_TypeChecker_Env.use_bv_sorts}))
in (

let _57_3522 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let _57_3528 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_57_3528) with
| (ses, exports, env) -> begin
((

let _57_3529 = modul
in {FStar_Syntax_Syntax.name = _57_3529.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _57_3529.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3529.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let _57_3537 = (tc_decls env decls)
in (match (_57_3537) with
| (ses, exports, env) -> begin
(

let modul = (

let _57_3538 = modul
in {FStar_Syntax_Syntax.name = _57_3538.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _57_3538.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3538.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul = (

let _57_3544 = modul
in {FStar_Syntax_Syntax.name = _57_3544.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _57_3544.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in (

let _57_3554 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(

let _57_3548 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let _57_3550 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (

let _57_3552 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _147_1570 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _147_1570 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let _57_3561 = (tc_partial_modul env modul)
in (match (_57_3561) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _57_3564 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _147_1579 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _147_1579))
end else begin
()
end
in (

let env = (

let _57_3566 = env
in {FStar_TypeChecker_Env.solver = _57_3566.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3566.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3566.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3566.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3566.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3566.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3566.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3566.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3566.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3566.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3566.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3566.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3566.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_3566.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3566.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3566.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3566.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3566.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3566.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3566.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_3582 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _57_3574) -> begin
(let _147_1584 = (let _147_1583 = (let _147_1582 = (FStar_TypeChecker_Env.get_range env)
in ((Prims.strcat "Implicit argument: " msg), _147_1582))
in FStar_Syntax_Syntax.Error (_147_1583))
in (Prims.raise _147_1584))
end
in (match (_57_3582) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(t, c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(let _147_1589 = (let _147_1588 = (let _147_1587 = (let _147_1585 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _147_1585))
in (let _147_1586 = (FStar_TypeChecker_Env.get_range env)
in (_147_1587, _147_1586)))
in FStar_Syntax_Syntax.Error (_147_1588))
in (Prims.raise _147_1589))
end
end)))))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

let _57_3585 = if (FStar_Options.debug_any ()) then begin
(let _147_1594 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _147_1594))
end else begin
()
end
in (

let _57_3589 = (tc_modul env m)
in (match (_57_3589) with
| (m, env) -> begin
(

let _57_3590 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _147_1595 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _147_1595))
end else begin
()
end
in (m, env))
end))))




