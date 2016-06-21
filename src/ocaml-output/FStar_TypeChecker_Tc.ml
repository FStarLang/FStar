
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
in (let _148_19 = (let _148_18 = (FStar_Syntax_Syntax.as_arg v)
in (let _148_17 = (let _148_16 = (FStar_Syntax_Syntax.as_arg tl)
in (_148_16)::[])
in (_148_18)::_148_17))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _148_19 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))


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


let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _148_32 = (steps env)
in (FStar_TypeChecker_Normalize.normalize _148_32 env t)))


let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _148_37 = (steps env)
in (FStar_TypeChecker_Normalize.normalize_comp _148_37 env c)))


let check_no_escape : FStar_Syntax_Syntax.term Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun head_opt env fvs kt -> (

let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
()
end
| _57_48 -> begin
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

let fail = (fun _57_55 -> (match (()) with
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
(let _148_76 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _148_76 t))
end))}))


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _148_85 = if (not ((FStar_Syntax_Util.is_pure_or_ghost_function t))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _148_85))
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
(let _148_87 = (FStar_Syntax_Print.term_to_string t)
in (let _148_86 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _148_87 _148_86)))
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
(let _148_89 = (FStar_Syntax_Print.term_to_string t)
in (let _148_88 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _148_89 _148_88)))
end else begin
()
end
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let _57_110 = (let _148_95 = (FStar_All.pipe_left (fun _148_94 -> Some (_148_94)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _148_95 env e lc g))
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
(let _148_96 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _148_96))
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
(let _148_109 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (_148_109))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
if (FStar_Syntax_Util.is_pure_comp c) then begin
(let _148_110 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (_148_110))
end else begin
if (FStar_Syntax_Util.is_pure_or_ghost_comp c) then begin
(let _148_111 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (_148_111))
end else begin
None
end
end
end
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _148_112 = (norm_c env c)
in (e, _148_112, FStar_TypeChecker_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(

let _57_139 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_115 = (FStar_Syntax_Print.term_to_string e)
in (let _148_114 = (FStar_Syntax_Print.comp_to_string c)
in (let _148_113 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _148_115 _148_114 _148_113))))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _57_142 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_118 = (FStar_Syntax_Print.term_to_string e)
in (let _148_117 = (FStar_Syntax_Print.comp_to_string c)
in (let _148_116 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _148_118 _148_117 _148_116))))
end else begin
()
end
in (

let _57_148 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_57_148) with
| (e, _57_146, g) -> begin
(

let g = (let _148_119 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _148_119 "could not prove post-condition" g))
in (

let _57_150 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_121 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _148_120 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _148_121 _148_120)))
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
(let _148_127 = (let _148_126 = (let _148_125 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _148_124 = (FStar_TypeChecker_Env.get_range env)
in (_148_125, _148_124)))
in FStar_Syntax_Syntax.Error (_148_126))
in (Prims.raise _148_127))
end)
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _148_130 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _148_130))
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
(let _148_137 = (let _148_136 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _148_136))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _148_137))
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

let t = (let _148_151 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _148_151))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _57_224 -> begin
(let _148_152 = (FStar_Syntax_Syntax.bv_to_name b)
in (_148_152)::[])
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
(match ((let _148_158 = (FStar_Syntax_Subst.compress t)
in _148_158.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _57_263 -> (match (_57_263) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _148_162 = (let _148_161 = (let _148_160 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_148_160))
in (FStar_Syntax_Syntax.new_bv _148_161 x.FStar_Syntax_Syntax.sort))
in (_148_162, imp))
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

let precedes = (let _148_166 = (let _148_165 = (FStar_Syntax_Syntax.as_arg dec)
in (let _148_164 = (let _148_163 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_148_163)::[])
in (_148_165)::_148_164))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _148_166 None r))
in (

let _57_274 = (FStar_Util.prefix formals)
in (match (_57_274) with
| (bs, (last, imp)) -> begin
(

let last = (

let _57_275 = last
in (let _148_167 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _57_275.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_275.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_167}))
in (

let refined_formals = (FStar_List.append bs (((last, imp))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (

let _57_280 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_170 = (FStar_Syntax_Print.lbname_to_string l)
in (let _148_169 = (FStar_Syntax_Print.term_to_string t)
in (let _148_168 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _148_170 _148_169 _148_168))))
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
(let _148_238 = (let _148_236 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _148_236))
in (let _148_237 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _148_238 _148_237)))
end else begin
()
end
in (

let top = e
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_57_295) -> begin
(let _148_242 = (FStar_Syntax_Subst.compress e)
in (tc_term env _148_242))
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
in (let _148_244 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_pattern (pats)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _148_243 = (FStar_TypeChecker_Rel.conj_guard g g')
in (_148_244, c, _148_243))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _148_245 = (FStar_Syntax_Subst.compress e)
in _148_245.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_57_368, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _57_375; FStar_Syntax_Syntax.lbtyp = _57_373; FStar_Syntax_Syntax.lbeff = _57_371; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _57_386 = (let _148_246 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _148_246 e1))
in (match (_57_386) with
| (e1, c1, g1) -> begin
(

let _57_390 = (tc_term env e2)
in (match (_57_390) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (None, c2))
in (

let e = (let _148_251 = (let _148_250 = (let _148_249 = (let _148_248 = (let _148_247 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Common.t_unit, e1))
in (_148_247)::[])
in (false, _148_248))
in (_148_249, e2))
in FStar_Syntax_Syntax.Tm_let (_148_250))
in (FStar_Syntax_Syntax.mk _148_251 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _148_252 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _148_252)))))
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

let _57_429 = (let _148_254 = (let _148_253 = (c'.FStar_Syntax_Syntax.comp ())
in (e, _148_253))
in (check_expected_effect env (Some (expected_c)) _148_254))
in (match (_57_429) with
| (e, expected_c, g'') -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (let _148_257 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t_res), Some ((FStar_Syntax_Util.comp_effect_name expected_c))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _148_256 = (let _148_255 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _148_255))
in (_148_257, (FStar_Syntax_Util.lcomp_of_comp expected_c), _148_256))))
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

let _57_449 = (let _148_258 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _148_258 e))
in (match (_57_449) with
| (e, c, g) -> begin
(

let _57_453 = (let _148_262 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_450 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _148_262 e c f))
in (match (_57_453) with
| (c, f) -> begin
(

let _57_457 = (let _148_263 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t), Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _148_263 c))
in (match (_57_457) with
| (e, c, f2) -> begin
(let _148_265 = (let _148_264 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _148_264))
in (e, c, _148_265))
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

let env = (let _148_267 = (let _148_266 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _148_266 Prims.fst))
in (FStar_All.pipe_right _148_267 instantiate_both))
in (

let _57_464 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_269 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _148_268 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _148_269 _148_268)))
end else begin
()
end
in (

let _57_469 = (tc_term (no_inst env) head)
in (match (_57_469) with
| (head, chead, g_head) -> begin
(

let _57_473 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _148_270 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _148_270))
end else begin
(let _148_271 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _148_271))
end
in (match (_57_473) with
| (e, c, g) -> begin
(

let _57_474 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_272 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _148_272))
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

let gimp = (match ((let _148_273 = (FStar_Syntax_Subst.compress head)
in _148_273.FStar_Syntax_Syntax.n)) with
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

let gres = (let _148_274 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _148_274))
in (

let _57_493 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_276 = (FStar_Syntax_Print.term_to_string e)
in (let _148_275 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" _148_276 _148_275)))
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
in (let _148_277 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_148_277, res_t)))
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
(let _148_280 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _148_280))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_531) with
| (cases, g) -> begin
(let _148_281 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_148_281, g))
end))
in (match (_57_534) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (Some (guard_x), c_branches))
in (

let e = (let _148_285 = (let _148_284 = (let _148_283 = (FStar_List.map (fun _57_543 -> (match (_57_543) with
| (f, _57_538, _57_540, _57_542) -> begin
f
end)) t_eqns)
in (e1, _148_283))
in FStar_Syntax_Syntax.Tm_match (_148_284))
in (FStar_Syntax_Syntax.mk _148_285 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ), Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (

let _57_546 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_288 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _148_287 = (let _148_286 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _148_286))
in (FStar_Util.print2 "(%s) comp type = %s\n" _148_288 _148_287)))
end else begin
()
end
in (let _148_289 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _148_289))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_558); FStar_Syntax_Syntax.lbunivs = _57_556; FStar_Syntax_Syntax.lbtyp = _57_554; FStar_Syntax_Syntax.lbeff = _57_552; FStar_Syntax_Syntax.lbdef = _57_550})::[]), _57_564) -> begin
(

let _57_567 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_290 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _148_290))
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
(let _148_291 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _148_291))
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
(let _148_305 = (let _148_304 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_304))
in FStar_Util.Inr (_148_305))
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
(let _148_311 = (let _148_310 = (let _148_309 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _148_308 = (FStar_TypeChecker_Env.get_range env)
in (_148_309, _148_308)))
in FStar_Syntax_Syntax.Error (_148_310))
in (Prims.raise _148_311))
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

let g = (match ((let _148_312 = (FStar_Syntax_Subst.compress t1)
in _148_312.FStar_Syntax_Syntax.n)) with
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

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _57_657 = (FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
in (match (_57_657) with
| (t, _57_655, g0) -> begin
(

let _57_662 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (_57_662) with
| (e, _57_660, g1) -> begin
(let _148_313 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) _148_313))
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

let _57_666 = x
in {FStar_Syntax_Syntax.ppname = _57_666.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_666.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let _57_672 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_672) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _148_315 = (let _148_314 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_314))
in FStar_Util.Inr (_148_315))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _57_679; FStar_Syntax_Syntax.pos = _57_677; FStar_Syntax_Syntax.vars = _57_675}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let _57_689 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_689) with
| (us', t) -> begin
(

let _57_696 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _148_318 = (let _148_317 = (let _148_316 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _148_316))
in FStar_Syntax_Syntax.Error (_148_317))
in (Prims.raise _148_318))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _57_695 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (

let fv' = (

let _57_698 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _57_700 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_700.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_700.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_698.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_698.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _148_321 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _148_321 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let _57_708 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_708) with
| (us, t) -> begin
(

let fv' = (

let _57_709 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _57_711 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_711.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_711.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_709.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_709.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _148_322 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _148_322 us))
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

let _57_725 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_725) with
| (bs, c) -> begin
(

let env0 = env
in (

let _57_730 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_730) with
| (env, _57_729) -> begin
(

let _57_735 = (tc_binders env bs)
in (match (_57_735) with
| (bs, env, g, us) -> begin
(

let _57_739 = (tc_comp env c)
in (match (_57_739) with
| (c, uc, f) -> begin
(

let e = (

let _57_740 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _57_740.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_740.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_740.FStar_Syntax_Syntax.vars})
in (

let _57_743 = (check_smt_pat env e bs c)
in (

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _148_323 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _148_323))
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

let _57_759 = (let _148_325 = (let _148_324 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_324)::[])
in (FStar_Syntax_Subst.open_term _148_325 phi))
in (match (_57_759) with
| (x, phi) -> begin
(

let env0 = env
in (

let _57_764 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_764) with
| (env, _57_763) -> begin
(

let _57_769 = (let _148_326 = (FStar_List.hd x)
in (tc_binder env _148_326))
in (match (_57_769) with
| (x, env, f1, u) -> begin
(

let _57_770 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_329 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _148_328 = (FStar_Syntax_Print.term_to_string phi)
in (let _148_327 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _148_329 _148_328 _148_327))))
end else begin
()
end
in (

let _57_775 = (FStar_Syntax_Util.type_u ())
in (match (_57_775) with
| (t_phi, _57_774) -> begin
(

let _57_780 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_57_780) with
| (phi, _57_778, f2) -> begin
(

let e = (

let _57_781 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _57_781.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_781.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_781.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _148_330 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _148_330))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _57_789) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (

let _57_795 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_331 = (FStar_Syntax_Print.term_to_string (

let _57_793 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _57_793.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_793.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_793.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _148_331))
end else begin
()
end
in (

let _57_799 = (FStar_Syntax_Subst.open_term bs body)
in (match (_57_799) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _57_801 -> begin
(let _148_333 = (let _148_332 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _148_332))
in (FStar_All.failwith _148_333))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_57_806) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_57_809, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_57_814, Some (_57_816)) -> begin
(FStar_All.failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (_57_821) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_57_824) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_57_827) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_57_831) -> begin
FStar_TypeChecker_Common.t_range
end
| _57_834 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(

let _57_841 = (FStar_Syntax_Util.type_u ())
in (match (_57_841) with
| (k, u) -> begin
(

let _57_846 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_846) with
| (t, _57_844, g) -> begin
(let _148_338 = (FStar_Syntax_Syntax.mk_Total t)
in (_148_338, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(

let _57_851 = (FStar_Syntax_Util.type_u ())
in (match (_57_851) with
| (k, u) -> begin
(

let _57_856 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_856) with
| (t, _57_854, g) -> begin
(let _148_339 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_148_339, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (

let tc = (let _148_341 = (let _148_340 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_148_340)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _148_341 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let _57_865 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_57_865) with
| (tc, _57_863, f) -> begin
(

let _57_869 = (FStar_Syntax_Util.head_and_args tc)
in (match (_57_869) with
| (_57_867, args) -> begin
(

let _57_872 = (let _148_343 = (FStar_List.hd args)
in (let _148_342 = (FStar_List.tl args)
in (_148_343, _148_342)))
in (match (_57_872) with
| (res, args) -> begin
(

let _57_888 = (let _148_345 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _57_5 -> (match (_57_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _57_879 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_879) with
| (env, _57_878) -> begin
(

let _57_884 = (tc_tot_or_gtot_term env e)
in (match (_57_884) with
| (e, _57_882, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _148_345 FStar_List.unzip))
in (match (_57_888) with
| (flags, guards) -> begin
(

let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| tk -> begin
(FStar_All.failwith "Impossible")
end)
in (let _148_347 = (FStar_Syntax_Syntax.mk_Comp (

let _57_894 = c
in {FStar_Syntax_Syntax.effect_name = _57_894.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _57_894.FStar_Syntax_Syntax.flags}))
in (let _148_346 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_148_347, u, _148_346))))
end))
end))
end))
end))))
end))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_57_902) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _148_352 = (aux u)
in FStar_Syntax_Syntax.U_succ (_148_352))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _148_353 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_148_353))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _148_357 = (let _148_356 = (let _148_355 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _148_354 = (FStar_TypeChecker_Env.get_range env)
in (_148_355, _148_354)))
in FStar_Syntax_Syntax.Error (_148_356))
in (Prims.raise _148_357))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _148_358 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_358 Prims.snd))
end
| _57_917 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _148_367 = (let _148_366 = (let _148_365 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_148_365, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_148_366))
in (Prims.raise _148_367)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun _57_935 bs bs_expected -> (match (_57_935) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
(

let _57_966 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _148_384 = (let _148_383 = (let _148_382 = (let _148_380 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _148_380))
in (let _148_381 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_148_382, _148_381)))
in FStar_Syntax_Syntax.Error (_148_383))
in (Prims.raise _148_384))
end
| _57_965 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _57_983 = (match ((let _148_385 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _148_385.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _57_971 -> begin
(

let _57_972 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_386 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _148_386))
end else begin
()
end
in (

let _57_978 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_57_978) with
| (t, _57_976, g1) -> begin
(

let g2 = (let _148_388 = (FStar_TypeChecker_Env.get_range env)
in (let _148_387 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _148_388 "Type annotation on parameter incompatible with the expected type" _148_387)))
in (

let g = (let _148_389 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _148_389))
in (t, g)))
end)))
end)
in (match (_57_983) with
| (t, g) -> begin
(

let hd = (

let _57_984 = hd
in {FStar_Syntax_Syntax.ppname = _57_984.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_984.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = (hd, imp)
in (

let b_expected = (hd_expected, imp')
in (

let env = (push_binding env b)
in (

let subst = (let _148_390 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _148_390))
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

let _57_1005 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1004 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (

let _57_1012 = (tc_binders env bs)
in (match (_57_1012) with
| (bs, envbody, g, _57_1011) -> begin
(

let _57_1030 = (match ((let _148_397 = (FStar_Syntax_Subst.compress body)
in _148_397.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _57_1017) -> begin
(

let _57_1024 = (tc_comp envbody c)
in (match (_57_1024) with
| (c, _57_1022, g') -> begin
(let _148_398 = (FStar_TypeChecker_Rel.conj_guard g g')
in (Some (c), body, _148_398))
end))
end
| _57_1026 -> begin
(None, body, g)
end)
in (match (_57_1030) with
| (copt, body, g) -> begin
(None, bs, [], copt, envbody, body, g)
end))
end)))
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm t -> (match ((let _148_403 = (FStar_Syntax_Subst.compress t)
in _148_403.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let _57_1057 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1056 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _57_1064 = (tc_binders env bs)
in (match (_57_1064) with
| (bs, envbody, g, _57_1063) -> begin
(

let _57_1068 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_57_1068) with
| (envbody, _57_1067) -> begin
(Some ((t, true)), bs, [], None, envbody, body, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _57_1071) -> begin
(

let _57_1082 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_57_1082) with
| (_57_1075, bs, bs', copt, env, body, g) -> begin
(Some ((t, false)), bs, bs', copt, env, body, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _57_1089 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_57_1089) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun _57_1100 c_expected -> (match (_57_1100) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _148_414 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _148_414))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (let _148_415 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _148_415))
in (let _148_416 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _148_416)))
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

let _57_1121 = (check_binders env more_bs bs_expected)
in (match (_57_1121) with
| (env, bs', more, guard', subst) -> begin
(let _148_418 = (let _148_417 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _148_417, subst))
in (handle_more _148_418 c_expected))
end))
end
| _57_1123 -> begin
(let _148_420 = (let _148_419 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _148_419))
in (fail _148_420 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _148_421 = (check_binders env bs bs_expected)
in (handle_more _148_421 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let _57_1129 = envbody
in {FStar_TypeChecker_Env.solver = _57_1129.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1129.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1129.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1129.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1129.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1129.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1129.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1129.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1129.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1129.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1129.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1129.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_1129.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1129.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1129.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1129.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1129.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1129.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1129.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1129.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _57_1134 _57_1137 -> (match ((_57_1134, _57_1137)) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _57_1143 = (let _148_431 = (let _148_430 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _148_430 Prims.fst))
in (tc_term _148_431 t))
in (match (_57_1143) with
| (t, _57_1140, _57_1142) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _148_432 = (FStar_Syntax_Syntax.mk_binder (

let _57_1147 = x
in {FStar_Syntax_Syntax.ppname = _57_1147.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1147.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_148_432)::letrec_binders)
end
| _57_1150 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (

let _57_1156 = (check_actuals_against_formals env bs bs_expected)
in (match (_57_1156) with
| (envbody, bs, g, c) -> begin
(

let _57_1159 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_57_1159) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, body, g))
end))
end))))
end))
end
| _57_1162 -> begin
if (not (norm)) then begin
(let _148_433 = (unfold_whnf env t)
in (as_function_typ true _148_433))
end else begin
(

let _57_1172 = (expected_function_typ env None body)
in (match (_57_1172) with
| (_57_1164, bs, _57_1167, c_opt, envbody, body, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, body, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let _57_1176 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1176) with
| (env, topt) -> begin
(

let _57_1180 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_434 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _148_434 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (

let _57_1189 = (expected_function_typ env topt body)
in (match (_57_1189) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let _57_1195 = (tc_term (

let _57_1190 = envbody
in {FStar_TypeChecker_Env.solver = _57_1190.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1190.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1190.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1190.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1190.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1190.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1190.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1190.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1190.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1190.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1190.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1190.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1190.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1190.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1190.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1190.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1190.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1190.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1190.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_57_1195) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _57_1197 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _148_437 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _148_436 = (let _148_435 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _148_435))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _148_437 _148_436)))
end else begin
()
end
in (

let _57_1204 = (let _148_439 = (let _148_438 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _148_438))
in (check_expected_effect (

let _57_1199 = envbody
in {FStar_TypeChecker_Env.solver = _57_1199.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1199.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1199.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1199.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1199.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1199.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1199.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1199.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1199.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1199.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1199.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1199.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1199.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1199.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1199.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1199.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1199.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1199.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1199.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1199.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _148_439))
in (match (_57_1204) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _148_440 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _148_440))
end else begin
(

let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _148_443 = (let _148_442 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _148_441 -> FStar_Util.Inl (_148_441)))
in Some (_148_442))
in (FStar_Syntax_Util.abs bs body _148_443))
in (

let _57_1227 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_1216) -> begin
(e, t, guard)
end
| _57_1219 -> begin
(

let _57_1222 = if use_teq then begin
(let _148_444 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _148_444))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_57_1222) with
| (e, guard') -> begin
(let _148_445 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _148_445))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_57_1227) with
| (e, tfun, guard) -> begin
(

let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (

let _57_1231 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_57_1231) with
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

let _57_1241 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_454 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _148_453 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _148_454 _148_453)))
end else begin
()
end
in (

let monadic_application = (fun _57_1248 subst arg_comps_rev arg_rets guard fvs bs -> (match (_57_1248) with
| (head, chead, ghead, cres) -> begin
(

let _57_1255 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let _57_1283 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun _57_6 -> (match (_57_6) with
| (_57_1262, _57_1264, None) -> begin
false
end
| (_57_1268, _57_1270, Some (c)) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _148_470 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _148_470 cres))
end else begin
(

let _57_1275 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_473 = (FStar_Syntax_Print.term_to_string head)
in (let _148_472 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _148_471 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _148_473 _148_472 _148_471))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _57_1279 -> begin
(

let g = (let _148_474 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right _148_474 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _148_479 = (let _148_478 = (let _148_477 = (let _148_476 = (let _148_475 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _148_475))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _148_476))
in (FStar_Syntax_Syntax.mk_Total _148_477))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_478))
in (_148_479, g)))
end)
in (match (_57_1283) with
| (cres, guard) -> begin
(

let _57_1284 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_480 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _148_480))
end else begin
()
end
in (

let _57_1302 = (FStar_List.fold_left (fun _57_1288 _57_1294 -> (match ((_57_1288, _57_1294)) with
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
in (match (_57_1302) with
| (args, comp) -> begin
(

let comp = (FStar_TypeChecker_Util.bind head.FStar_Syntax_Syntax.pos env None chead (None, comp))
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app = (FStar_TypeChecker_Util.maybe_monadic env app comp.FStar_Syntax_Syntax.eff_name)
in (

let _57_1308 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (_57_1308) with
| (comp, g) -> begin
(app, comp, g)
end)))))
end)))
end)))
end))
in (

let rec tc_args = (fun head_info _57_1316 bs args -> (match (_57_1316) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match ((bs, args)) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (_57_1322))))::rest, ((_57_1330, None))::_57_1328) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _57_1336 = (check_no_escape (Some (head)) env fvs t)
in (

let _57_1342 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_57_1342) with
| (varg, _57_1340, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (

let arg = (let _148_492 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _148_492))
in (let _148_494 = (let _148_493 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, ((arg, None, None))::outargs, (arg)::arg_rets, _148_493, fvs))
in (tc_args head_info _148_494 rest args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
(

let _57_1374 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _57_1373 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let _57_1377 = x
in {FStar_Syntax_Syntax.ppname = _57_1377.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1377.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (

let _57_1380 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_495 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _148_495))
end else begin
()
end
in (

let _57_1382 = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let _57_1385 = env
in {FStar_TypeChecker_Env.solver = _57_1385.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1385.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1385.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1385.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1385.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1385.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1385.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1385.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1385.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1385.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1385.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1385.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1385.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1385.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1385.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _57_1385.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1385.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1385.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1385.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1385.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_1388 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_498 = (FStar_Syntax_Print.tag_of_term e)
in (let _148_497 = (FStar_Syntax_Print.term_to_string e)
in (let _148_496 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _148_498 _148_497 _148_496))))
end else begin
()
end
in (

let _57_1393 = (tc_term env e)
in (match (_57_1393) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(

let subst = (let _148_499 = (FStar_List.hd bs)
in (maybe_extend_subst subst _148_499 e))
in (tc_args head_info (subst, ((arg, None, None))::outargs, (arg)::arg_rets, g, fvs) rest rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(

let subst = (let _148_500 = (FStar_List.hd bs)
in (maybe_extend_subst subst _148_500 e))
in (tc_args head_info (subst, ((arg, Some (x), Some (c)))::outargs, (arg)::arg_rets, g, fvs) rest rest'))
end else begin
if (let _148_501 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _148_501)) then begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _148_502 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _148_502))
in (tc_args head_info (subst, ((arg, Some (newx), Some (c)))::outargs, (arg')::arg_rets, g, fvs) rest rest')))
end else begin
(let _148_506 = (let _148_505 = (let _148_504 = (let _148_503 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _148_503))
in (_148_504)::arg_rets)
in (subst, ((arg, Some (x), Some (c)))::outargs, _148_505, g, (x)::fvs))
in (tc_args head_info _148_506 rest rest'))
end
end
end))
end))))))))))
end
| (_57_1401, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::_57_1406) -> begin
(

let _57_1413 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (_57_1413) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _148_511 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _148_511 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let _57_1424 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (_57_1424) with
| (bs, cres') -> begin
(

let head_info = (head, chead, ghead, (FStar_Syntax_Util.lcomp_of_comp cres'))
in (

let _57_1426 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_512 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _148_512))
end else begin
()
end
in (tc_args head_info ([], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs args)))
end))
end
| _57_1429 when (not (norm)) -> begin
(let _148_513 = (unfold_whnf env tres)
in (aux true _148_513))
end
| _57_1431 -> begin
(let _148_519 = (let _148_518 = (let _148_517 = (let _148_515 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (let _148_514 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _148_515 _148_514)))
in (let _148_516 = (FStar_Syntax_Syntax.argpos arg)
in (_148_517, _148_516)))
in FStar_Syntax_Syntax.Error (_148_518))
in (Prims.raise _148_519))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (match ((let _148_524 = (FStar_Syntax_Util.unrefine tf)
in _148_524.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| ((e, imp))::tl -> begin
(

let _57_1464 = (tc_term env e)
in (match (_57_1464) with
| (e, c, g_e) -> begin
(

let _57_1468 = (tc_args env tl)
in (match (_57_1468) with
| (args, comps, g_rest) -> begin
(let _148_529 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, ((e.FStar_Syntax_Syntax.pos, c))::comps, _148_529))
end))
end))
end))
in (

let _57_1472 = (tc_args env args)
in (match (_57_1472) with
| (args, comps, g_args) -> begin
(

let bs = (let _148_531 = (FStar_All.pipe_right comps (FStar_List.map (fun _57_1476 -> (match (_57_1476) with
| (_57_1474, c) -> begin
(c.FStar_Syntax_Syntax.res_typ, None)
end))))
in (FStar_Syntax_Util.null_binders_of_tks _148_531))
in (

let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _57_1482 -> begin
FStar_Syntax_Util.ml_comp
end)
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _148_546 = (FStar_Syntax_Subst.compress t)
in _148_546.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_1488) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _57_1493 -> begin
ml_or_tot
end)
end)
in (

let cres = (let _148_551 = (let _148_550 = (let _148_549 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_549 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _148_550))
in (ml_or_tot _148_551 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (

let _57_1497 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _148_554 = (FStar_Syntax_Print.term_to_string head)
in (let _148_553 = (FStar_Syntax_Print.term_to_string tf)
in (let _148_552 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _148_554 _148_553 _148_552))))
end else begin
()
end
in (

let _57_1499 = (let _148_555 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _148_555))
in (

let comp = (let _148_558 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _57_1503 out -> (match (_57_1503) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c (None, out))
end)) (((head.FStar_Syntax_Syntax.pos, chead))::comps) _148_558))
in (let _148_560 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _148_559 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_148_560, comp, _148_559)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _57_1512 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_1512) with
| (bs, c) -> begin
(

let head_info = (head, chead, ghead, (FStar_Syntax_Util.lcomp_of_comp c))
in (tc_args head_info ([], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs args))
end))
end
| _57_1515 -> begin
if (not (norm)) then begin
(let _148_561 = (unfold_whnf env tf)
in (check_function_app true _148_561))
end else begin
(let _148_564 = (let _148_563 = (let _148_562 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_148_562, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_148_563))
in (Prims.raise _148_564))
end
end))
in (let _148_566 = (let _148_565 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _148_565))
in (check_function_app false _148_566))))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let _57_1551 = (FStar_List.fold_left2 (fun _57_1532 _57_1535 _57_1538 -> (match ((_57_1532, _57_1535, _57_1538)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(

let _57_1539 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let _57_1544 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_57_1544) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (let _148_576 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _148_576 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _148_580 = (let _148_578 = (let _148_577 = (FStar_Syntax_Syntax.as_arg e)
in (_148_577)::[])
in (FStar_List.append seen _148_578))
in (let _148_579 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_148_580, _148_579, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_57_1551) with
| (args, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = if ghost then begin
(let _148_581 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _148_581 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (

let _57_1556 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_57_1556) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _57_1558 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let _57_1565 = (FStar_Syntax_Subst.open_branch branch)
in (match (_57_1565) with
| (pattern, when_clause, branch_exp) -> begin
(

let _57_1570 = branch
in (match (_57_1570) with
| (cpat, _57_1568, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _57_1578 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_57_1578) with
| (pat_bvs, exps, p) -> begin
(

let _57_1579 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_593 = (FStar_Syntax_Print.pat_to_string p0)
in (let _148_592 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _148_593 _148_592)))
end else begin
()
end
in (

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let _57_1585 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_57_1585) with
| (env1, _57_1584) -> begin
(

let env1 = (

let _57_1586 = env1
in {FStar_TypeChecker_Env.solver = _57_1586.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1586.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1586.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1586.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1586.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1586.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1586.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1586.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _57_1586.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1586.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1586.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1586.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1586.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1586.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1586.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1586.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1586.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1586.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1586.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1586.FStar_TypeChecker_Env.use_bv_sorts})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _57_1625 = (let _148_616 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _57_1591 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_596 = (FStar_Syntax_Print.term_to_string e)
in (let _148_595 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _148_596 _148_595)))
end else begin
()
end
in (

let _57_1596 = (tc_term env1 e)
in (match (_57_1596) with
| (e, lc, g) -> begin
(

let _57_1597 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_598 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _148_597 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _148_598 _148_597)))
end else begin
()
end
in (

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let _57_1603 = (let _148_599 = (FStar_TypeChecker_Rel.discharge_guard env (

let _57_1601 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_1601.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_1601.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_1601.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _148_599 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _148_604 = (let _148_603 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _148_603 (FStar_List.map (fun _57_1611 -> (match (_57_1611) with
| (u, _57_1610) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _148_604 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _57_1619 = if (let _148_605 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _148_605)) then begin
(

let unresolved = (let _148_606 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _148_606 FStar_Util.set_elements))
in (let _148_614 = (let _148_613 = (let _148_612 = (let _148_611 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _148_610 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _148_609 = (let _148_608 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _57_1618 -> (match (_57_1618) with
| (u, _57_1617) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _148_608 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _148_611 _148_610 _148_609))))
in (_148_612, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_148_613))
in (Prims.raise _148_614)))
end else begin
()
end
in (

let _57_1621 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_615 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _148_615))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _148_616 FStar_List.unzip))
in (match (_57_1625) with
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

let _57_1632 = (let _148_617 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _148_617 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_57_1632) with
| (scrutinee_env, _57_1631) -> begin
(

let _57_1638 = (tc_pat true pat_t pattern)
in (match (_57_1638) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let _57_1648 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(

let _57_1645 = (let _148_618 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _148_618 e))
in (match (_57_1645) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_57_1648) with
| (when_clause, g_when) -> begin
(

let _57_1652 = (tc_term pat_env branch_exp)
in (match (_57_1652) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _148_620 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _148_619 -> Some (_148_619)) _148_620))
end)
in (

let _57_1708 = (

let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _57_1670 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _148_624 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _148_623 -> Some (_148_623)) _148_624))
end))
end))) None))
in (

let _57_1678 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_57_1678) with
| (c, g_branch) -> begin
(

let _57_1703 = (match ((eqs, when_condition)) with
| (None, None) -> begin
(c, g_when)
end
| (Some (f), None) -> begin
(

let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _148_627 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _148_626 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_148_627, _148_626)))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (let _148_628 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_148_628))
in (let _148_631 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _148_630 = (let _148_629 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _148_629 g_when))
in (_148_631, _148_630)))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _148_632 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_148_632, g_when))))
end)
in (match (_57_1703) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _148_634 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _148_633 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_148_634, _148_633, g_branch))))
end))
end)))
in (match (_57_1708) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = (

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> if ((let _148_644 = (let _148_643 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _148_643))
in (FStar_List.length _148_644)) > 1) then begin
(

let disc = (let _148_645 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _148_645 FStar_Syntax_Syntax.Delta_equational None))
in (

let disc = (let _148_647 = (let _148_646 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_148_646)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _148_647 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _148_648 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_148_648)::[])))
end else begin
[]
end)
in (

let fail = (fun _57_1718 -> (match (()) with
| () -> begin
(let _148_654 = (let _148_653 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _148_652 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _148_651 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _148_653 _148_652 _148_651))))
in (FStar_All.failwith _148_654))
end))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _57_1725) -> begin
(head_constructor t)
end
| _57_1729 -> begin
(fail ())
end))
in (

let pat_exp = (let _148_657 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _148_657 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_57_1754) -> begin
(let _148_662 = (let _148_661 = (let _148_660 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _148_659 = (let _148_658 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_148_658)::[])
in (_148_660)::_148_659))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _148_661 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_148_662)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _148_663 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _148_663))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(

let sub_term_guards = (let _148_670 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _57_1772 -> (match (_57_1772) with
| (ei, _57_1771) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _57_1776 -> begin
(

let sub_term = (let _148_669 = (let _148_666 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _148_666 FStar_Syntax_Syntax.Delta_equational None))
in (let _148_668 = (let _148_667 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_148_667)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _148_669 _148_668 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _148_670 FStar_List.flatten))
in (let _148_671 = (discriminate scrutinee_tm f)
in (FStar_List.append _148_671 sub_term_guards)))
end)
end
| _57_1780 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(

let t = (let _148_676 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _148_676))
in (

let _57_1788 = (FStar_Syntax_Util.type_u ())
in (match (_57_1788) with
| (k, _57_1787) -> begin
(

let _57_1794 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_57_1794) with
| (t, _57_1791, _57_1793) -> begin
t
end))
end)))
end)
in (

let branch_guard = (let _148_677 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _148_677 FStar_Syntax_Util.mk_disj_l))
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

let _57_1802 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_678 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _148_678))
end else begin
()
end
in (let _148_679 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_148_679, branch_guard, c, guard)))))
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

let _57_1819 = (check_let_bound_def true env lb)
in (match (_57_1819) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let _57_1831 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(

let g1 = (let _148_682 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _148_682 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _57_1826 = (let _148_686 = (let _148_685 = (let _148_684 = (let _148_683 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _148_683))
in (_148_684)::[])
in (FStar_TypeChecker_Util.generalize env _148_685))
in (FStar_List.hd _148_686))
in (match (_57_1826) with
| (_57_1822, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_57_1831) with
| (g1, e1, univ_vars, c1) -> begin
(

let _57_1841 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(

let _57_1834 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_57_1834) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(

let _57_1835 = if (FStar_Options.warn_top_level_effects ()) then begin
(let _148_687 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _148_687 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _148_688 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_148_688, c1)))
end
end))
end else begin
(

let _57_1837 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _148_689 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _148_689)))
end
in (match (_57_1841) with
| (e2, c1) -> begin
(

let cres = (let _148_690 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_690))
in (

let _57_1843 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _148_691 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_148_691, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _57_1847 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let _57_1858 = env
in {FStar_TypeChecker_Env.solver = _57_1858.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1858.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1858.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1858.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1858.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1858.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1858.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1858.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1858.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1858.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1858.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1858.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1858.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1858.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1858.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1858.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1858.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1858.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1858.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1858.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_1867 = (let _148_695 = (let _148_694 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _148_694 Prims.fst))
in (check_let_bound_def false _148_695 lb))
in (match (_57_1867) with
| (e1, _57_1863, c1, g1, annotated) -> begin
(

let x = (

let _57_1868 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1868.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1868.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let _57_1874 = (let _148_697 = (let _148_696 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_696)::[])
in (FStar_Syntax_Subst.open_term _148_697 e2))
in (match (_57_1874) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _57_1880 = (let _148_698 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _148_698 e2))
in (match (_57_1880) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (Some (x), c2))
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e2 = (FStar_TypeChecker_Util.maybe_lift env e2 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e = (let _148_701 = (let _148_700 = (let _148_699 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _148_699))
in FStar_Syntax_Syntax.Tm_let (_148_700))
in (FStar_Syntax_Syntax.mk _148_701 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name)
in (

let x_eq_e1 = (let _148_704 = (let _148_703 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _148_703 e1))
in (FStar_All.pipe_left (fun _148_702 -> FStar_TypeChecker_Common.NonTrivial (_148_702)) _148_704))
in (

let g2 = (let _148_706 = (let _148_705 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _148_705 g2))
in (FStar_TypeChecker_Rel.close_guard xb _148_706))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if (let _148_707 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome _148_707)) then begin
(e, cres, guard)
end else begin
(

let _57_1889 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end))))))))
end))))
end))))
end)))
end
| _57_1892 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _57_1904 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1904) with
| (lbs, e2) -> begin
(

let _57_1907 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1907) with
| (env0, topt) -> begin
(

let _57_1910 = (build_let_rec_env true env0 lbs)
in (match (_57_1910) with
| (lbs, rec_env) -> begin
(

let _57_1913 = (check_let_recs rec_env lbs)
in (match (_57_1913) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (let _148_710 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _148_710 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _148_713 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _148_713 (fun _148_712 -> Some (_148_712))))
in (

let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(

let ecs = (let _148_717 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _148_716 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _148_716)))))
in (FStar_TypeChecker_Util.generalize env _148_717))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _57_1924 -> (match (_57_1924) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _148_719 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_719))
in (

let _57_1927 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _57_1931 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1931) with
| (lbs, e2) -> begin
(let _148_721 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _148_720 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_148_721, cres, _148_720)))
end)))))))
end))
end))
end))
end))
end
| _57_1933 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _57_1945 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1945) with
| (lbs, e2) -> begin
(

let _57_1948 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1948) with
| (env0, topt) -> begin
(

let _57_1951 = (build_let_rec_env false env0 lbs)
in (match (_57_1951) with
| (lbs, rec_env) -> begin
(

let _57_1954 = (check_let_recs rec_env lbs)
in (match (_57_1954) with
| (lbs, g_lbs) -> begin
(

let _57_1966 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let _57_1957 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1957.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1957.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let _57_1960 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _57_1960.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1960.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1960.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _57_1960.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], lb.FStar_Syntax_Syntax.lbtyp))
in (env, lb))))) env))
in (match (_57_1966) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let _57_1972 = (tc_term env e2)
in (match (_57_1972) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _57_1976 = cres
in {FStar_Syntax_Syntax.eff_name = _57_1976.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _57_1976.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_1976.FStar_Syntax_Syntax.comp})
in (

let _57_1981 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1981) with
| (lbs, e2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_57_1984) -> begin
(e, cres, guard)
end
| None -> begin
(

let _57_1987 = (check_no_escape None env bvs tres)
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
| _57_1990 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let _57_2023 = (FStar_List.fold_left (fun _57_1997 lb -> (match (_57_1997) with
| (lbs, env) -> begin
(

let _57_2002 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_57_2002) with
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

let _57_2011 = (let _148_733 = (let _148_732 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _148_732))
in (tc_check_tot_or_gtot_term (

let _57_2005 = env0
in {FStar_TypeChecker_Env.solver = _57_2005.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2005.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2005.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2005.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2005.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2005.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2005.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2005.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2005.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2005.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2005.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2005.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2005.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2005.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _57_2005.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2005.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2005.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2005.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2005.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2005.FStar_TypeChecker_Env.use_bv_sorts}) t _148_733))
in (match (_57_2011) with
| (t, _57_2009, g) -> begin
(

let _57_2012 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (

let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(

let _57_2015 = env
in {FStar_TypeChecker_Env.solver = _57_2015.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2015.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2015.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2015.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2015.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2015.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2015.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2015.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2015.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2015.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2015.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2015.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2015.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_2015.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2015.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2015.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2015.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2015.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2015.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2015.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (

let lb = (

let _57_2018 = lb
in {FStar_Syntax_Syntax.lbname = _57_2018.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _57_2018.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_57_2023) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _57_2036 = (let _148_738 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _57_2030 = (let _148_737 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _148_737 lb.FStar_Syntax_Syntax.lbdef))
in (match (_57_2030) with
| (e, c, g) -> begin
(

let _57_2031 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _148_738 FStar_List.unzip))
in (match (_57_2036) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _57_2044 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_2044) with
| (env1, _57_2043) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _57_2050 = (check_lbtyp top_level env lb)
in (match (_57_2050) with
| (topt, wf_annot, univ_vars, env1) -> begin
(

let _57_2051 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let _57_2058 = (tc_maybe_toplevel_term (

let _57_2053 = env1
in {FStar_TypeChecker_Env.solver = _57_2053.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2053.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2053.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2053.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2053.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2053.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2053.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2053.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2053.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2053.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2053.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2053.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2053.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _57_2053.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2053.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2053.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2053.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2053.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2053.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2053.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_57_2058) with
| (e1, c1, g1) -> begin
(

let _57_2062 = (let _148_745 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_2059 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _148_745 e1 c1 wf_annot))
in (match (_57_2062) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _57_2064 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_746 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _148_746))
end else begin
()
end
in (let _148_747 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _148_747))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _57_2071 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _57_2074 -> begin
(

let _57_2077 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_57_2077) with
| (univ_vars, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _148_751 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _148_751))
end else begin
(

let _57_2082 = (FStar_Syntax_Util.type_u ())
in (match (_57_2082) with
| (k, _57_2081) -> begin
(

let _57_2087 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_57_2087) with
| (t, _57_2085, g) -> begin
(

let _57_2088 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _148_754 = (let _148_752 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _148_752))
in (let _148_753 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _148_754 _148_753)))
end else begin
()
end
in (

let t = (norm env1 t)
in (let _148_755 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _148_755))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _57_2094 -> (match (_57_2094) with
| (x, imp) -> begin
(

let _57_2097 = (FStar_Syntax_Util.type_u ())
in (match (_57_2097) with
| (tu, u) -> begin
(

let _57_2102 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_57_2102) with
| (t, _57_2100, g) -> begin
(

let x = ((

let _57_2103 = x
in {FStar_Syntax_Syntax.ppname = _57_2103.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2103.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (

let _57_2106 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_759 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _148_758 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _148_759 _148_758)))
end else begin
()
end
in (let _148_760 = (push_binding env x)
in (x, _148_760, g, u))))
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

let _57_2121 = (tc_binder env b)
in (match (_57_2121) with
| (b, env', g, u) -> begin
(

let _57_2126 = (aux env' bs)
in (match (_57_2126) with
| (bs, env', g', us) -> begin
(let _148_768 = (let _148_767 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _148_767))
in ((b)::bs, env', _148_768, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun _57_2134 _57_2137 -> (match ((_57_2134, _57_2137)) with
| ((t, imp), (args, g)) -> begin
(

let _57_2142 = (tc_term env t)
in (match (_57_2142) with
| (t, _57_2140, g') -> begin
(let _148_777 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _148_777))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _57_2146 -> (match (_57_2146) with
| (pats, g) -> begin
(

let _57_2149 = (tc_args env p)
in (match (_57_2149) with
| (args, g') -> begin
(let _148_780 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _148_780))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _57_2155 = (tc_maybe_toplevel_term env e)
in (match (_57_2155) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let _57_2158 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_783 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _148_783))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _57_2163 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _148_784 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_148_784, false))
end else begin
(let _148_785 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_148_785, true))
end
in (match (_57_2163) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _148_786 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _148_786))
end
| _57_2167 -> begin
if allow_ghost then begin
(let _148_789 = (let _148_788 = (let _148_787 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_148_787, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_148_788))
in (Prims.raise _148_789))
end else begin
(let _148_792 = (let _148_791 = (let _148_790 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_148_790, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_148_791))
in (Prims.raise _148_792))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))


let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let _57_2177 = (tc_tot_or_gtot_term env t)
in (match (_57_2177) with
| (t, c, g) -> begin
(

let _57_2178 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let _57_2186 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_2186) with
| (t, c, g) -> begin
(

let _57_2187 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _148_812 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _148_812)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _148_816 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _148_816))))


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let _57_2202 = (tc_binders env tps)
in (match (_57_2202) with
| (tps, env, g, us) -> begin
(

let _57_2203 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (

let fail = (fun _57_2209 -> (match (()) with
| () -> begin
(let _148_831 = (let _148_830 = (let _148_829 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_148_829, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_148_830))
in (Prims.raise _148_831))
end))
in (

let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _57_2222))::((wp, _57_2218))::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2226 -> begin
(fail ())
end))
end
| _57_2228 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let _57_2235 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_57_2235) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _57_2237 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let _57_2241 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_57_2241) with
| (uvs, t') -> begin
(match ((let _148_838 = (FStar_Syntax_Subst.compress t')
in _148_838.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _57_2247 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))


let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (

let fail = (fun t -> (let _148_849 = (let _148_848 = (let _148_847 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_148_847, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_148_848))
in (Prims.raise _148_849)))
in (match ((let _148_850 = (FStar_Syntax_Subst.compress signature)
in _148_850.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _57_2264))::((wp, _57_2260))::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2268 -> begin
(fail signature)
end))
end
| _57_2270 -> begin
(fail signature)
end)))


let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (

let _57_2275 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_57_2275) with
| (a, wp) -> begin
(

let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _57_2278 -> begin
(

let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (

let op = (fun ts -> (

let _57_2282 = ()
in (

let t0 = (Prims.snd ts)
in (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (

let _57_2286 = ed
in (let _148_866 = (op ed.FStar_Syntax_Syntax.ret)
in (let _148_865 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _148_864 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _148_863 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _148_862 = (op ed.FStar_Syntax_Syntax.stronger)
in (let _148_861 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _148_860 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _148_859 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _148_858 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _148_857 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _57_2286.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2286.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2286.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2286.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2286.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _148_866; FStar_Syntax_Syntax.bind_wp = _148_865; FStar_Syntax_Syntax.if_then_else = _148_864; FStar_Syntax_Syntax.ite_wp = _148_863; FStar_Syntax_Syntax.stronger = _148_862; FStar_Syntax_Syntax.close_wp = _148_861; FStar_Syntax_Syntax.assert_p = _148_860; FStar_Syntax_Syntax.assume_p = _148_859; FStar_Syntax_Syntax.null_wp = _148_858; FStar_Syntax_Syntax.trivial = _148_857})))))))))))))
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

let n = (match ((let _148_888 = (FStar_Syntax_Subst.compress tm)
in _148_888.FStar_Syntax_Syntax.n)) with
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
| _57_2321 -> begin
tm.FStar_Syntax_Syntax.n
end)
in (

let _57_2323 = tm
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2323.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2323.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2323.FStar_Syntax_Syntax.vars})))
and visit_binder = (fun _57_2327 -> (match (_57_2327) with
| (bv, a) -> begin
(let _148_892 = (

let _57_2328 = bv
in (let _148_890 = (visit_term bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_2328.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2328.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_890}))
in (let _148_891 = (FStar_Syntax_Syntax.as_implicit false)
in (_148_892, _148_891)))
end))
and visit_maybe_lcomp = (fun lcomp -> (match (lcomp) with
| Some (FStar_Util.Inl (lcomp)) -> begin
(let _148_897 = (let _148_896 = (let _148_895 = (let _148_894 = (lcomp.FStar_Syntax_Syntax.comp ())
in (visit_comp _148_894))
in (FStar_Syntax_Util.lcomp_of_comp _148_895))
in FStar_Util.Inl (_148_896))
in Some (_148_897))
end
| comp -> begin
comp
end))
and visit_comp = (fun comp -> (

let n = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tm) -> begin
(let _148_899 = (visit_term tm)
in FStar_Syntax_Syntax.Total (_148_899))
end
| FStar_Syntax_Syntax.GTotal (tm) -> begin
(let _148_900 = (visit_term tm)
in FStar_Syntax_Syntax.GTotal (_148_900))
end
| comp -> begin
comp
end)
in (

let _57_2342 = comp
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2342.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2342.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2342.FStar_Syntax_Syntax.vars})))
and visit_args = (fun args -> (FStar_List.map (fun _57_2347 -> (match (_57_2347) with
| (tm, q) -> begin
(let _148_903 = (visit_term tm)
in (_148_903, q))
end)) args))
in (visit_term tm))))
in (

let check = (fun str t -> if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _57_2351 = (let _148_908 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Generated term for %s: %s\n" str _148_908))
in (

let t = (normalize t)
in (

let t = (FStar_Syntax_Subst.compress t)
in (

let _57_2366 = (tc_term env t)
in (match (_57_2366) with
| (e, {FStar_Syntax_Syntax.eff_name = _57_2362; FStar_Syntax_Syntax.res_typ = res_typ; FStar_Syntax_Syntax.cflags = _57_2359; FStar_Syntax_Syntax.comp = _57_2357}, _57_2365) -> begin
(

let _57_2367 = (let _148_911 = (let _148_910 = (normalize res_typ)
in (FStar_Syntax_Print.term_to_string _148_910))
in (FStar_Util.print2 "Inferred type for %s: %s\n" str _148_911))
in (let _148_913 = (let _148_912 = (normalize e)
in (FStar_Syntax_Print.term_to_string _148_912))
in (FStar_Util.print2 "Elaborated term for %s: %s\n" str _148_913)))
end)))))
end else begin
()
end)
in (

let rec collect_binders = (fun t -> (match ((let _148_916 = (FStar_Syntax_Subst.compress t)
in _148_916.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
t
end
| _57_2378 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _148_917 = (collect_binders rest)
in (FStar_List.append bs _148_917)))
end
| FStar_Syntax_Syntax.Tm_type (_57_2381) -> begin
[]
end
| _57_2384 -> begin
(FStar_All.failwith "wp_a doesn\'t end in Type0")
end))
in (

let _57_2399 = (

let i = (FStar_ST.alloc 0)
in (

let wp_binders = (let _148_924 = (normalize wp_a)
in (collect_binders _148_924))
in ((fun t -> (let _148_930 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow wp_binders _148_930))), (fun t -> (let _148_933 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow wp_binders _148_933))), (fun _57_2389 -> (match (()) with
| () -> begin
(FStar_List.map (fun _57_2393 -> (match (_57_2393) with
| (bv, _57_2392) -> begin
(

let _57_2394 = (let _148_937 = ((FStar_ST.read i) + 1)
in (FStar_ST.op_Colon_Equals i _148_937))
in (let _148_940 = (let _148_939 = (let _148_938 = (FStar_ST.read i)
in (FStar_Util.string_of_int _148_938))
in (Prims.strcat "g" _148_939))
in (FStar_Syntax_Syntax.gen_bv _148_940 None bv.FStar_Syntax_Syntax.sort)))
end)) wp_binders)
end)))))
in (match (_57_2399) with
| (mk_ctx, mk_gctx, mk_gamma) -> begin
(

let binders_of_list = (FStar_List.map (fun _57_2402 -> (match (_57_2402) with
| (t, b) -> begin
(let _148_946 = (FStar_Syntax_Syntax.as_implicit b)
in (t, _148_946))
end)))
in (

let implicit_binders_of_list = (FStar_List.map (fun t -> (let _148_949 = (FStar_Syntax_Syntax.as_implicit true)
in (t, _148_949))))
in (

let args_of_bv = (FStar_List.map (fun bv -> (let _148_952 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_Syntax_Syntax.as_arg _148_952))))
in (

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let x = (let _148_953 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _148_953))
in (

let ret = (let _148_958 = (let _148_957 = (let _148_956 = (let _148_955 = (let _148_954 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx _148_954))
in (FStar_Syntax_Syntax.mk_Total _148_955))
in (FStar_Syntax_Util.lcomp_of_comp _148_956))
in FStar_Util.Inl (_148_957))
in Some (_148_958))
in (

let gamma = (mk_gamma ())
in (

let body = (let _148_960 = (implicit_binders_of_list gamma)
in (let _148_959 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs _148_960 _148_959 ret)))
in (let _148_961 = (binders_of_list (((t, true))::((x, false))::[]))
in (FStar_Syntax_Util.abs _148_961 body ret)))))))
in (

let _57_2414 = (let _148_965 = (let _148_964 = (let _148_963 = (let _148_962 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_962)::[])
in (FStar_List.append binders _148_963))
in (FStar_Syntax_Util.abs _148_964 c_pure None))
in (check "pure" _148_965))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let l = (let _148_973 = (let _148_972 = (let _148_971 = (let _148_968 = (let _148_967 = (let _148_966 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _148_966))
in (FStar_Syntax_Syntax.mk_binder _148_967))
in (_148_968)::[])
in (let _148_970 = (let _148_969 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _148_969))
in (FStar_Syntax_Util.arrow _148_971 _148_970)))
in (mk_gctx _148_972))
in (FStar_Syntax_Syntax.gen_bv "l" None _148_973))
in (

let r = (let _148_975 = (let _148_974 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _148_974))
in (FStar_Syntax_Syntax.gen_bv "r" None _148_975))
in (

let ret = (let _148_980 = (let _148_979 = (let _148_978 = (let _148_977 = (let _148_976 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _148_976))
in (FStar_Syntax_Syntax.mk_Total _148_977))
in (FStar_Syntax_Util.lcomp_of_comp _148_978))
in FStar_Util.Inl (_148_979))
in Some (_148_980))
in (

let outer_body = (

let gamma = (mk_gamma ())
in (

let gamma_as_args = (args_of_bv gamma)
in (

let inner_body = (let _148_986 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _148_985 = (let _148_984 = (let _148_983 = (let _148_982 = (let _148_981 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _148_981 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg _148_982))
in (_148_983)::[])
in (FStar_List.append gamma_as_args _148_984))
in (FStar_Syntax_Util.mk_app _148_986 _148_985)))
in (let _148_987 = (implicit_binders_of_list gamma)
in (FStar_Syntax_Util.abs _148_987 inner_body ret)))))
in (let _148_988 = (binders_of_list (((t1, true))::((t2, true))::((l, false))::((r, false))::[]))
in (FStar_Syntax_Util.abs _148_988 outer_body ret))))))))
in (

let _57_2426 = (let _148_992 = (let _148_991 = (let _148_990 = (let _148_989 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_989)::[])
in (FStar_List.append binders _148_990))
in (FStar_Syntax_Util.abs _148_991 c_app None))
in (check "app" _148_992))
in (

let unknown = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _148_997 = (let _148_994 = (let _148_993 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _148_993))
in (_148_994)::[])
in (let _148_996 = (let _148_995 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _148_995))
in (FStar_Syntax_Util.arrow _148_997 _148_996)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _148_999 = (let _148_998 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _148_998))
in (FStar_Syntax_Syntax.gen_bv "a1" None _148_999))
in (

let ret = (let _148_1004 = (let _148_1003 = (let _148_1002 = (let _148_1001 = (let _148_1000 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _148_1000))
in (FStar_Syntax_Syntax.mk_Total _148_1001))
in (FStar_Syntax_Util.lcomp_of_comp _148_1002))
in FStar_Util.Inl (_148_1003))
in Some (_148_1004))
in (let _148_1017 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::((a1, false))::[]))
in (let _148_1016 = (let _148_1015 = (let _148_1014 = (let _148_1013 = (let _148_1012 = (let _148_1011 = (let _148_1008 = (let _148_1007 = (let _148_1006 = (let _148_1005 = (FStar_Syntax_Syntax.bv_to_name f)
in (_148_1005)::[])
in (unknown)::_148_1006)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1007))
in (FStar_Syntax_Util.mk_app c_pure _148_1008))
in (let _148_1010 = (let _148_1009 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_148_1009)::[])
in (_148_1011)::_148_1010))
in (unknown)::_148_1012)
in (unknown)::_148_1013)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1014))
in (FStar_Syntax_Util.mk_app c_app _148_1015))
in (FStar_Syntax_Util.abs _148_1017 _148_1016 ret)))))))))
in (

let _57_2436 = (let _148_1021 = (let _148_1020 = (let _148_1019 = (let _148_1018 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_1018)::[])
in (FStar_List.append binders _148_1019))
in (FStar_Syntax_Util.abs _148_1020 c_lift1 None))
in (check "lift1" _148_1021))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _148_1029 = (let _148_1026 = (let _148_1022 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _148_1022))
in (let _148_1025 = (let _148_1024 = (let _148_1023 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder _148_1023))
in (_148_1024)::[])
in (_148_1026)::_148_1025))
in (let _148_1028 = (let _148_1027 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal _148_1027))
in (FStar_Syntax_Util.arrow _148_1029 _148_1028)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _148_1031 = (let _148_1030 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _148_1030))
in (FStar_Syntax_Syntax.gen_bv "a1" None _148_1031))
in (

let a2 = (let _148_1033 = (let _148_1032 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _148_1032))
in (FStar_Syntax_Syntax.gen_bv "a2" None _148_1033))
in (

let ret = (let _148_1038 = (let _148_1037 = (let _148_1036 = (let _148_1035 = (let _148_1034 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx _148_1034))
in (FStar_Syntax_Syntax.mk_Total _148_1035))
in (FStar_Syntax_Util.lcomp_of_comp _148_1036))
in FStar_Util.Inl (_148_1037))
in Some (_148_1038))
in (let _148_1058 = (binders_of_list (((t1, true))::((t2, true))::((t3, true))::((f, false))::((a1, false))::((a2, false))::[]))
in (let _148_1057 = (let _148_1056 = (let _148_1055 = (let _148_1054 = (let _148_1053 = (let _148_1052 = (let _148_1049 = (let _148_1048 = (let _148_1047 = (let _148_1046 = (let _148_1045 = (let _148_1042 = (let _148_1041 = (let _148_1040 = (let _148_1039 = (FStar_Syntax_Syntax.bv_to_name f)
in (_148_1039)::[])
in (unknown)::_148_1040)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1041))
in (FStar_Syntax_Util.mk_app c_pure _148_1042))
in (let _148_1044 = (let _148_1043 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_148_1043)::[])
in (_148_1045)::_148_1044))
in (unknown)::_148_1046)
in (unknown)::_148_1047)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1048))
in (FStar_Syntax_Util.mk_app c_app _148_1049))
in (let _148_1051 = (let _148_1050 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_148_1050)::[])
in (_148_1052)::_148_1051))
in (unknown)::_148_1053)
in (unknown)::_148_1054)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1055))
in (FStar_Syntax_Util.mk_app c_app _148_1056))
in (FStar_Syntax_Util.abs _148_1058 _148_1057 ret)))))))))))
in (

let _57_2447 = (let _148_1062 = (let _148_1061 = (let _148_1060 = (let _148_1059 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_1059)::[])
in (FStar_List.append binders _148_1060))
in (FStar_Syntax_Util.abs _148_1061 c_lift2 None))
in (check "lift2" _148_1062))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _148_1068 = (let _148_1064 = (let _148_1063 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _148_1063))
in (_148_1064)::[])
in (let _148_1067 = (let _148_1066 = (let _148_1065 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _148_1065))
in (FStar_Syntax_Syntax.mk_Total _148_1066))
in (FStar_Syntax_Util.arrow _148_1068 _148_1067)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let ret = (let _148_1078 = (let _148_1077 = (let _148_1076 = (let _148_1075 = (let _148_1074 = (let _148_1073 = (let _148_1070 = (let _148_1069 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _148_1069))
in (_148_1070)::[])
in (let _148_1072 = (let _148_1071 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _148_1071))
in (FStar_Syntax_Util.arrow _148_1073 _148_1072)))
in (mk_ctx _148_1074))
in (FStar_Syntax_Syntax.mk_Total _148_1075))
in (FStar_Syntax_Util.lcomp_of_comp _148_1076))
in FStar_Util.Inl (_148_1077))
in Some (_148_1078))
in (

let e1 = (let _148_1079 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _148_1079))
in (

let gamma = (mk_gamma ())
in (

let body = (let _148_1089 = (let _148_1082 = (FStar_Syntax_Syntax.binders_of_list gamma)
in (let _148_1081 = (let _148_1080 = (FStar_Syntax_Syntax.mk_binder e1)
in (_148_1080)::[])
in (FStar_List.append _148_1082 _148_1081)))
in (let _148_1088 = (let _148_1087 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _148_1086 = (let _148_1085 = (let _148_1083 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _148_1083))
in (let _148_1084 = (args_of_bv gamma)
in (_148_1085)::_148_1084))
in (FStar_Syntax_Util.mk_app _148_1087 _148_1086)))
in (FStar_Syntax_Util.abs _148_1089 _148_1088 ret)))
in (let _148_1090 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::[]))
in (FStar_Syntax_Util.abs _148_1090 body ret))))))))))
in (

let _57_2458 = (let _148_1094 = (let _148_1093 = (let _148_1092 = (let _148_1091 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_1091)::[])
in (FStar_List.append binders _148_1092))
in (FStar_Syntax_Util.abs _148_1093 c_push None))
in (check "push" _148_1094))
in (

let ret_tot_wp_a = (let _148_1097 = (let _148_1096 = (let _148_1095 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _148_1095))
in FStar_Util.Inl (_148_1096))
in Some (_148_1097))
in (

let wp_if_then_else = (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _148_1108 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (let _148_1107 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_unfoldable (2)) None)
in (let _148_1106 = (let _148_1105 = (let _148_1104 = (let _148_1103 = (let _148_1102 = (let _148_1101 = (let _148_1100 = (let _148_1099 = (let _148_1098 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _148_1098))
in (_148_1099)::[])
in (FStar_Syntax_Util.mk_app l_ite _148_1100))
in (_148_1101)::[])
in (unknown)::_148_1102)
in (unknown)::_148_1103)
in (unknown)::_148_1104)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1105))
in (FStar_Syntax_Util.mk_app c_lift2 _148_1106)))
in (FStar_Syntax_Util.abs _148_1108 _148_1107 ret_tot_wp_a))))
in (

let wp_if_then_else = (normalize_and_make_binders_explicit wp_if_then_else)
in (

let _57_2465 = (let _148_1109 = (FStar_Syntax_Util.abs binders wp_if_then_else None)
in (check "wp_if_then_else" _148_1109))
in (

let wp_assert = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_and = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (

let body = (let _148_1123 = (let _148_1122 = (let _148_1121 = (let _148_1120 = (let _148_1119 = (let _148_1116 = (let _148_1115 = (let _148_1114 = (let _148_1113 = (let _148_1112 = (let _148_1111 = (let _148_1110 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _148_1110))
in (_148_1111)::[])
in (FStar_Syntax_Util.mk_app l_and _148_1112))
in (_148_1113)::[])
in (unknown)::_148_1114)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1115))
in (FStar_Syntax_Util.mk_app c_pure _148_1116))
in (let _148_1118 = (let _148_1117 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_148_1117)::[])
in (_148_1119)::_148_1118))
in (unknown)::_148_1120)
in (unknown)::_148_1121)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1122))
in (FStar_Syntax_Util.mk_app c_app _148_1123))
in (let _148_1124 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _148_1124 body ret_tot_wp_a))))))
in (

let wp_assert = (normalize_and_make_binders_explicit wp_assert)
in (

let _57_2473 = (let _148_1125 = (FStar_Syntax_Util.abs binders wp_assert None)
in (check "wp_assert" _148_1125))
in (

let wp_assume = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_imp = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (

let body = (let _148_1139 = (let _148_1138 = (let _148_1137 = (let _148_1136 = (let _148_1135 = (let _148_1132 = (let _148_1131 = (let _148_1130 = (let _148_1129 = (let _148_1128 = (let _148_1127 = (let _148_1126 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _148_1126))
in (_148_1127)::[])
in (FStar_Syntax_Util.mk_app l_imp _148_1128))
in (_148_1129)::[])
in (unknown)::_148_1130)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1131))
in (FStar_Syntax_Util.mk_app c_pure _148_1132))
in (let _148_1134 = (let _148_1133 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_148_1133)::[])
in (_148_1135)::_148_1134))
in (unknown)::_148_1136)
in (unknown)::_148_1137)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1138))
in (FStar_Syntax_Util.mk_app c_app _148_1139))
in (let _148_1140 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _148_1140 body ret_tot_wp_a))))))
in (

let wp_assume = (normalize_and_make_binders_explicit wp_assume)
in (

let _57_2481 = (let _148_1141 = (FStar_Syntax_Util.abs binders wp_assume None)
in (check "wp_assume" _148_1141))
in (

let tforall = (let _148_1144 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _148_1143 = (let _148_1142 = (FStar_Syntax_Syntax.as_arg unknown)
in (_148_1142)::[])
in (FStar_Syntax_Util.mk_app _148_1144 _148_1143)))
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _148_1148 = (let _148_1146 = (let _148_1145 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _148_1145))
in (_148_1146)::[])
in (let _148_1147 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1148 _148_1147)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (let _148_1161 = (let _148_1160 = (let _148_1159 = (let _148_1158 = (let _148_1157 = (let _148_1149 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((unknown)::(tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _148_1149))
in (let _148_1156 = (let _148_1155 = (let _148_1154 = (let _148_1153 = (let _148_1152 = (let _148_1151 = (let _148_1150 = (FStar_Syntax_Syntax.bv_to_name f)
in (_148_1150)::[])
in (unknown)::_148_1151)
in (unknown)::_148_1152)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1153))
in (FStar_Syntax_Util.mk_app c_push _148_1154))
in (_148_1155)::[])
in (_148_1157)::_148_1156))
in (unknown)::_148_1158)
in (unknown)::_148_1159)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1160))
in (FStar_Syntax_Util.mk_app c_app _148_1161))
in (let _148_1162 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_Syntax_Util.abs _148_1162 body ret_tot_wp_a))))))
in (

let wp_close = (normalize_and_make_binders_explicit wp_close)
in (

let _57_2490 = (let _148_1163 = (FStar_Syntax_Util.abs binders wp_close None)
in (check "wp_close" _148_1163))
in (

let ret_tot_type0 = (let _148_1166 = (let _148_1165 = (let _148_1164 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_1164))
in FStar_Util.Inl (_148_1165))
in Some (_148_1166))
in (

let mk_forall = (fun x body -> (

let tforall = (let _148_1173 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _148_1172 = (let _148_1171 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (_148_1171)::[])
in (FStar_Syntax_Util.mk_app _148_1173 _148_1172)))
in (let _148_1180 = (let _148_1179 = (let _148_1178 = (let _148_1177 = (let _148_1176 = (let _148_1175 = (let _148_1174 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_1174)::[])
in (FStar_Syntax_Util.abs _148_1175 body ret_tot_type0))
in (FStar_Syntax_Syntax.as_arg _148_1176))
in (_148_1177)::[])
in (tforall, _148_1178))
in FStar_Syntax_Syntax.Tm_app (_148_1179))
in (FStar_Syntax_Syntax.mk _148_1180 None FStar_Range.dummyRange))))
in (

let rec mk_leq = (fun t x y -> (match ((let _148_1188 = (let _148_1187 = (FStar_Syntax_Subst.compress t)
in (normalize _148_1187))
in _148_1188.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_2502) -> begin
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

let body = (let _148_1200 = (let _148_1190 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _148_1189 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_leq a _148_1190 _148_1189)))
in (let _148_1199 = (let _148_1198 = (let _148_1193 = (let _148_1192 = (let _148_1191 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _148_1191))
in (_148_1192)::[])
in (FStar_Syntax_Util.mk_app x _148_1193))
in (let _148_1197 = (let _148_1196 = (let _148_1195 = (let _148_1194 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _148_1194))
in (_148_1195)::[])
in (FStar_Syntax_Util.mk_app y _148_1196))
in (mk_leq b _148_1198 _148_1197)))
in (FStar_Syntax_Util.mk_imp _148_1200 _148_1199)))
in (let _148_1201 = (mk_forall a2 body)
in (mk_forall a1 _148_1201))))))
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let _57_2538 = t
in (let _148_1205 = (let _148_1204 = (let _148_1203 = (let _148_1202 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _148_1202))
in ((binder)::[], _148_1203))
in FStar_Syntax_Syntax.Tm_arrow (_148_1204))
in {FStar_Syntax_Syntax.n = _148_1205; FStar_Syntax_Syntax.tk = _57_2538.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2538.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2538.FStar_Syntax_Syntax.vars}))
in (mk_leq t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_57_2542) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _57_2545 -> begin
(FStar_Syntax_Util.mk_eq t t x y)
end))
in (

let stronger = (

let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (

let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (

let body = (let _148_1207 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _148_1206 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_leq wp_a _148_1207 _148_1206)))
in (let _148_1208 = (FStar_Syntax_Syntax.binders_of_list ((wp1)::(wp2)::[]))
in (FStar_Syntax_Util.abs _148_1208 body ret_tot_type0)))))
in (

let _57_2550 = (let _148_1212 = (let _148_1211 = (let _148_1210 = (let _148_1209 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_1209)::[])
in (FStar_List.append binders _148_1210))
in (FStar_Syntax_Util.abs _148_1211 stronger None))
in (check "stronger" _148_1212))
in (

let null_wp = (Prims.snd ed.FStar_Syntax_Syntax.null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (let _148_1220 = (let _148_1219 = (let _148_1218 = (let _148_1215 = (let _148_1214 = (let _148_1213 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _148_1213))
in (_148_1214)::[])
in (FStar_Syntax_Util.mk_app null_wp _148_1215))
in (let _148_1217 = (let _148_1216 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_148_1216)::[])
in (_148_1218)::_148_1217))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1219))
in (FStar_Syntax_Util.mk_app stronger _148_1220))
in (let _148_1221 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_Syntax_Util.abs _148_1221 body ret_tot_type0))))
in (

let wp_trivial = (normalize_and_make_binders_explicit wp_trivial)
in (

let _57_2557 = (let _148_1222 = (FStar_Syntax_Util.abs binders wp_trivial None)
in (check "wp_trivial" _148_1222))
in (

let _57_2559 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2559.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2559.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2559.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2559.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2559.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _57_2559.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2559.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = ([], wp_if_then_else); FStar_Syntax_Syntax.ite_wp = _57_2559.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _57_2559.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = ([], wp_close); FStar_Syntax_Syntax.assert_p = ([], wp_assert); FStar_Syntax_Syntax.assume_p = ([], wp_assume); FStar_Syntax_Syntax.null_wp = _57_2559.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = ([], wp_trivial)}))))))))))))))))))))))))))))))))))))))
end))))))))


let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  effect_cost  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed is_for_free -> (

let _57_2564 = ()
in (

let _57_2568 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_57_2568) with
| (binders_un, signature_un) -> begin
(

let _57_2573 = (tc_tparams env0 binders_un)
in (match (_57_2573) with
| (binders, env, _57_2572) -> begin
(

let _57_2577 = (tc_trivial_guard env signature_un)
in (match (_57_2577) with
| (signature, _57_2576) -> begin
(

let ed = (

let _57_2578 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2578.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2578.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2578.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _57_2578.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2578.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _57_2578.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _57_2578.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _57_2578.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _57_2578.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _57_2578.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _57_2578.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _57_2578.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _57_2578.FStar_Syntax_Syntax.trivial})
in (

let _57_2584 = (open_effect_decl env ed)
in (match (_57_2584) with
| (ed, a, wp_a) -> begin
(

let get_effect_signature = (fun _57_2586 -> (match (()) with
| () -> begin
(

let _57_2590 = (tc_trivial_guard env signature_un)
in (match (_57_2590) with
| (signature, _57_2589) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (

let env = (let _148_1231 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _148_1231))
in (

let _57_2592 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _148_1234 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _148_1233 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _148_1232 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checking effect signature: %s %s : %s\n" _148_1234 _148_1233 _148_1232))))
end else begin
()
end
in (

let check_and_gen' = (fun env _57_2599 k -> (match (_57_2599) with
| (_57_2597, t) -> begin
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

let expected_k = (let _148_1246 = (let _148_1244 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1243 = (let _148_1242 = (let _148_1241 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _148_1241))
in (_148_1242)::[])
in (_148_1244)::_148_1243))
in (let _148_1245 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _148_1246 _148_1245)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (

let bind_wp = (

let _57_2608 = (get_effect_signature ())
in (match (_57_2608) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _148_1250 = (let _148_1248 = (let _148_1247 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _148_1247))
in (_148_1248)::[])
in (let _148_1249 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _148_1250 _148_1249)))
in (

let expected_k = (let _148_1261 = (let _148_1259 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _148_1258 = (let _148_1257 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1256 = (let _148_1255 = (FStar_Syntax_Syntax.mk_binder b)
in (let _148_1254 = (let _148_1253 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _148_1252 = (let _148_1251 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (_148_1251)::[])
in (_148_1253)::_148_1252))
in (_148_1255)::_148_1254))
in (_148_1257)::_148_1256))
in (_148_1259)::_148_1258))
in (let _148_1260 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _148_1261 _148_1260)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (let _148_1263 = (let _148_1262 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_1262 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _148_1263))
in (

let expected_k = (let _148_1272 = (let _148_1270 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1269 = (let _148_1268 = (FStar_Syntax_Syntax.mk_binder p)
in (let _148_1267 = (let _148_1266 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _148_1265 = (let _148_1264 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1264)::[])
in (_148_1266)::_148_1265))
in (_148_1268)::_148_1267))
in (_148_1270)::_148_1269))
in (let _148_1271 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1272 _148_1271)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (let _148_1277 = (let _148_1275 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1274 = (let _148_1273 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1273)::[])
in (_148_1275)::_148_1274))
in (let _148_1276 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1277 _148_1276)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let _57_2620 = (FStar_Syntax_Util.type_u ())
in (match (_57_2620) with
| (t, _57_2619) -> begin
(

let expected_k = (let _148_1284 = (let _148_1282 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1281 = (let _148_1280 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _148_1279 = (let _148_1278 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1278)::[])
in (_148_1280)::_148_1279))
in (_148_1282)::_148_1281))
in (let _148_1283 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _148_1284 _148_1283)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (let _148_1286 = (let _148_1285 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_1285 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _148_1286))
in (

let b_wp_a = (let _148_1290 = (let _148_1288 = (let _148_1287 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _148_1287))
in (_148_1288)::[])
in (let _148_1289 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1290 _148_1289)))
in (

let expected_k = (let _148_1297 = (let _148_1295 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1294 = (let _148_1293 = (FStar_Syntax_Syntax.mk_binder b)
in (let _148_1292 = (let _148_1291 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_148_1291)::[])
in (_148_1293)::_148_1292))
in (_148_1295)::_148_1294))
in (let _148_1296 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1297 _148_1296)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (let _148_1306 = (let _148_1304 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1303 = (let _148_1302 = (let _148_1299 = (let _148_1298 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_1298 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _148_1299))
in (let _148_1301 = (let _148_1300 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1300)::[])
in (_148_1302)::_148_1301))
in (_148_1304)::_148_1303))
in (let _148_1305 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1306 _148_1305)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _148_1315 = (let _148_1313 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1312 = (let _148_1311 = (let _148_1308 = (let _148_1307 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_1307 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _148_1308))
in (let _148_1310 = (let _148_1309 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1309)::[])
in (_148_1311)::_148_1310))
in (_148_1313)::_148_1312))
in (let _148_1314 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1315 _148_1314)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _148_1318 = (let _148_1316 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_1316)::[])
in (let _148_1317 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1318 _148_1317)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let _57_2636 = (FStar_Syntax_Util.type_u ())
in (match (_57_2636) with
| (t, _57_2635) -> begin
(

let expected_k = (let _148_1323 = (let _148_1321 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1320 = (let _148_1319 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1319)::[])
in (_148_1321)::_148_1320))
in (let _148_1322 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _148_1323 _148_1322)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let t = (let _148_1324 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _148_1324))
in (

let _57_2642 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_57_2642) with
| (univs, t) -> begin
(

let _57_2658 = (match ((let _148_1326 = (let _148_1325 = (FStar_Syntax_Subst.compress t)
in _148_1325.FStar_Syntax_Syntax.n)
in (binders, _148_1326))) with
| ([], _57_2645) -> begin
([], t)
end
| (_57_2648, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _57_2655 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_2658) with
| (binders, signature) -> begin
(

let close = (fun n ts -> (

let ts = (let _148_1331 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _148_1331))
in (

let _57_2663 = ()
in ts)))
in (

let ed = (

let _57_2665 = ed
in (let _148_1341 = (close 0 ret)
in (let _148_1340 = (close 1 bind_wp)
in (let _148_1339 = (close 0 if_then_else)
in (let _148_1338 = (close 0 ite_wp)
in (let _148_1337 = (close 0 stronger)
in (let _148_1336 = (close 1 close_wp)
in (let _148_1335 = (close 0 assert_p)
in (let _148_1334 = (close 0 assume_p)
in (let _148_1333 = (close 0 null_wp)
in (let _148_1332 = (close 0 trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _57_2665.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2665.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _148_1341; FStar_Syntax_Syntax.bind_wp = _148_1340; FStar_Syntax_Syntax.if_then_else = _148_1339; FStar_Syntax_Syntax.ite_wp = _148_1338; FStar_Syntax_Syntax.stronger = _148_1337; FStar_Syntax_Syntax.close_wp = _148_1336; FStar_Syntax_Syntax.assert_p = _148_1335; FStar_Syntax_Syntax.assume_p = _148_1334; FStar_Syntax_Syntax.null_wp = _148_1333; FStar_Syntax_Syntax.trivial = _148_1332})))))))))))
in (

let _57_2668 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1342 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _148_1342))
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

let _57_2674 = ()
in (

let _57_2682 = ()
in (match (ses) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _57_2711, _57_2713, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _57_2702, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _57_2691, r2))::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
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

let lex_top_t = (let _148_1350 = (let _148_1349 = (let _148_1348 = (let _148_1347 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _148_1347 FStar_Syntax_Syntax.Delta_constant None))
in (_148_1348, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_148_1349))
in (FStar_Syntax_Syntax.mk _148_1350 None r1))
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

let a = (let _148_1351 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _148_1351))
in (

let hd = (let _148_1352 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _148_1352))
in (

let tl = (let _148_1357 = (let _148_1356 = (let _148_1355 = (let _148_1354 = (let _148_1353 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _148_1353 FStar_Syntax_Syntax.Delta_constant None))
in (_148_1354, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_148_1355))
in (FStar_Syntax_Syntax.mk _148_1356 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _148_1357))
in (

let res = (let _148_1361 = (let _148_1360 = (let _148_1359 = (let _148_1358 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _148_1358 FStar_Syntax_Syntax.Delta_constant None))
in (_148_1359, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_148_1360))
in (FStar_Syntax_Syntax.mk _148_1361 None r2))
in (let _148_1362 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _148_1362))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _148_1364 = (let _148_1363 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _148_1363))
in FStar_Syntax_Syntax.Sig_bundle (_148_1364)))))))))))))))
end
| _57_2737 -> begin
(let _148_1366 = (let _148_1365 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _148_1365))
in (FStar_All.failwith _148_1366))
end))))


let tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _57_2717 = (FStar_Syntax_Util.type_u ())
in (match (_57_2717) with
| (k, _57_2716) -> begin
(

let phi = (let _147_1399 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _147_1399 (norm env)))
in (

let _57_2719 = (FStar_TypeChecker_Util.check_uvars r phi)
in FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))))
end))))


let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (

<<<<<<< HEAD
let warn_positivity = (fun l r -> (let _147_1413 = (let _147_1412 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _147_1412))
in (FStar_TypeChecker_Errors.diag r _147_1413)))
=======
let warn_positivity = (fun l r -> (let _148_1380 = (let _148_1379 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _148_1379))
in (FStar_TypeChecker_Errors.diag r _148_1380)))
>>>>>>> master
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

<<<<<<< HEAD
let _57_2742 = ()
in (

let _57_2744 = (warn_positivity tc r)
in (

let _57_2748 = (FStar_Syntax_Subst.open_term tps k)
in (match (_57_2748) with
| (tps, k) -> begin
(

let _57_2752 = (tc_tparams env tps)
in (match (_57_2752) with
| (tps, env_tps, us) -> begin
(

let _57_2755 = (FStar_Syntax_Util.arrow_formals k)
in (match (_57_2755) with
| (indices, t) -> begin
(

let _57_2759 = (tc_tparams env_tps indices)
in (match (_57_2759) with
| (indices, env', us') -> begin
(

let _57_2763 = (tc_trivial_guard env' t)
in (match (_57_2763) with
| (t, _57_2762) -> begin
(

let k = (let _147_1418 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _147_1418))
in (

let _57_2767 = (FStar_Syntax_Util.type_u ())
in (match (_57_2767) with
| (t_type, u) -> begin
(

let _57_2768 = (let _147_1419 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _147_1419))
in (

let t_tc = (let _147_1420 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _147_1420))
=======
let _57_2759 = ()
in (

let _57_2761 = (warn_positivity tc r)
in (

let _57_2765 = (FStar_Syntax_Subst.open_term tps k)
in (match (_57_2765) with
| (tps, k) -> begin
(

let _57_2770 = (tc_binders env tps)
in (match (_57_2770) with
| (tps, env_tps, guard_params, us) -> begin
(

let _57_2773 = (FStar_Syntax_Util.arrow_formals k)
in (match (_57_2773) with
| (indices, t) -> begin
(

let _57_2778 = (tc_binders env_tps indices)
in (match (_57_2778) with
| (indices, env', guard_indices, us') -> begin
(

let _57_2786 = (

let _57_2783 = (tc_tot_or_gtot_term env' t)
in (match (_57_2783) with
| (t, _57_2781, g) -> begin
(let _148_1387 = (let _148_1386 = (let _148_1385 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params _148_1385))
in (FStar_TypeChecker_Rel.discharge_guard env' _148_1386))
in (t, _148_1387))
end))
in (match (_57_2786) with
| (t, guard) -> begin
(

let k = (let _148_1388 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _148_1388))
in (

let _57_2790 = (FStar_Syntax_Util.type_u ())
in (match (_57_2790) with
| (t_type, u) -> begin
(

let _57_2791 = (let _148_1389 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _148_1389))
in (

let t_tc = (let _148_1390 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _148_1390))
>>>>>>> master
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
<<<<<<< HEAD
in (let _147_1421 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) ([], t_tc))
in (_147_1421, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u)))))))
=======
in (let _148_1391 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) ([], t_tc))
in (_148_1391, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u, guard)))))))
>>>>>>> master
end)))
end))
end))
end))
end))
end))))
end
<<<<<<< HEAD
| _57_2775 -> begin
=======
| _57_2798 -> begin
>>>>>>> master
(FStar_All.failwith "impossible")
end))
in (

<<<<<<< HEAD
let positive_if_pure = (fun _57_2777 l -> ())
=======
let positive_if_pure = (fun _57_2800 l -> ())
>>>>>>> master
in (

let tc_data = (fun env tcs _57_7 -> (match (_57_7) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

<<<<<<< HEAD
let _57_2794 = ()
in (

let _57_2829 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _57_2798 -> (match (_57_2798) with
| (se, u_tc) -> begin
if (let _147_1434 = (let _147_1433 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _147_1433))
in (FStar_Ident.lid_equals tc_lid _147_1434)) then begin
(

let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2800, _57_2802, tps, _57_2805, _57_2807, _57_2809, _57_2811, _57_2813) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _57_2819 -> (match (_57_2819) with
| (x, _57_2818) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _57_2821 -> begin
=======
let _57_2817 = ()
in (

let _57_2852 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _57_2821 -> (match (_57_2821) with
| (se, u_tc) -> begin
if (let _148_1404 = (let _148_1403 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _148_1403))
in (FStar_Ident.lid_equals tc_lid _148_1404)) then begin
(

let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2823, _57_2825, tps, _57_2828, _57_2830, _57_2832, _57_2834, _57_2836) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _57_2842 -> (match (_57_2842) with
| (x, _57_2841) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _57_2844 -> begin
>>>>>>> master
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
<<<<<<< HEAD
in (match (_57_2829) with
| (tps, u_tc) -> begin
(

let _57_2849 = (match ((let _147_1436 = (FStar_Syntax_Subst.compress t)
in _147_1436.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _57_2837 = (FStar_Util.first_N ntps bs)
in (match (_57_2837) with
| (_57_2835, bs') -> begin
=======
in (match (_57_2852) with
| (tps, u_tc) -> begin
(

let _57_2872 = (match ((let _148_1406 = (FStar_Syntax_Subst.compress t)
in _148_1406.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _57_2860 = (FStar_Util.first_N ntps bs)
in (match (_57_2860) with
| (_57_2858, bs') -> begin
>>>>>>> master
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (

<<<<<<< HEAD
let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _57_2843 -> (match (_57_2843) with
| (x, _57_2842) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _147_1439 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _147_1439))))
end))
end
| _57_2846 -> begin
([], t)
end)
in (match (_57_2849) with
| (arguments, result) -> begin
(

let _57_2850 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_1442 = (FStar_Syntax_Print.lid_to_string c)
in (let _147_1441 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _147_1440 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _147_1442 _147_1441 _147_1440))))
=======
let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _57_2866 -> (match (_57_2866) with
| (x, _57_2865) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _148_1409 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _148_1409))))
end))
end
| _57_2869 -> begin
([], t)
end)
in (match (_57_2872) with
| (arguments, result) -> begin
(

let _57_2873 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1412 = (FStar_Syntax_Print.lid_to_string c)
in (let _148_1411 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _148_1410 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _148_1412 _148_1411 _148_1410))))
>>>>>>> master
end else begin
()
end
in (

<<<<<<< HEAD
let _57_2855 = (tc_tparams env arguments)
in (match (_57_2855) with
| (arguments, env', us) -> begin
(

let _57_2859 = (tc_trivial_guard env' result)
in (match (_57_2859) with
| (result, _57_2858) -> begin
(

let _57_2863 = (FStar_Syntax_Util.head_and_args result)
in (match (_57_2863) with
| (head, _57_2862) -> begin
(

let _57_2868 = (match ((let _147_1443 = (FStar_Syntax_Subst.compress head)
in _147_1443.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _57_2867 -> begin
(let _147_1447 = (let _147_1446 = (let _147_1445 = (let _147_1444 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _147_1444))
in (_147_1445, r))
in FStar_Syntax_Syntax.Error (_147_1446))
in (Prims.raise _147_1447))
end)
in (

let g = (FStar_List.fold_left2 (fun g _57_2874 u_x -> (match (_57_2874) with
| (x, _57_2873) -> begin
(

let _57_2876 = ()
in (let _147_1451 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _147_1451)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _147_1455 = (let _147_1453 = (FStar_All.pipe_right tps (FStar_List.map (fun _57_2882 -> (match (_57_2882) with
| (x, _57_2881) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _147_1453 arguments))
in (let _147_1454 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _147_1455 _147_1454)))
=======
let _57_2878 = (tc_tparams env arguments)
in (match (_57_2878) with
| (arguments, env', us) -> begin
(

let _57_2882 = (tc_trivial_guard env' result)
in (match (_57_2882) with
| (result, _57_2881) -> begin
(

let _57_2886 = (FStar_Syntax_Util.head_and_args result)
in (match (_57_2886) with
| (head, _57_2885) -> begin
(

let _57_2891 = (match ((let _148_1413 = (FStar_Syntax_Subst.compress head)
in _148_1413.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _57_2890 -> begin
(let _148_1418 = (let _148_1417 = (let _148_1416 = (let _148_1415 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _148_1414 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _148_1415 _148_1414)))
in (_148_1416, r))
in FStar_Syntax_Syntax.Error (_148_1417))
in (Prims.raise _148_1418))
end)
in (

let g = (FStar_List.fold_left2 (fun g _57_2897 u_x -> (match (_57_2897) with
| (x, _57_2896) -> begin
(

let _57_2899 = ()
in (let _148_1422 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _148_1422)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _148_1426 = (let _148_1424 = (FStar_All.pipe_right tps (FStar_List.map (fun _57_2905 -> (match (_57_2905) with
| (x, _57_2904) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _148_1424 arguments))
in (let _148_1425 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _148_1426 _148_1425)))
>>>>>>> master
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
<<<<<<< HEAD
| _57_2885 -> begin
=======
| _57_2908 -> begin
>>>>>>> master
(FStar_All.failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

<<<<<<< HEAD
let _57_2891 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_7 -> (match (_57_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2895, _57_2897, tps, k, _57_2901, _57_2903, _57_2905, _57_2907) -> begin
(let _147_1466 = (let _147_1465 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _147_1465))
in (FStar_Syntax_Syntax.null_binder _147_1466))
end
| _57_2911 -> begin
=======
let _57_2914 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_8 -> (match (_57_8) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2918, _57_2920, tps, k, _57_2924, _57_2926, _57_2928, _57_2930) -> begin
(let _148_1437 = (let _148_1436 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _148_1436))
in (FStar_Syntax_Syntax.null_binder _148_1437))
end
| _57_2934 -> begin
>>>>>>> master
(FStar_All.failwith "Impossible")
end))))
in (

<<<<<<< HEAD
let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _57_8 -> (match (_57_8) with
| FStar_Syntax_Syntax.Sig_datacon (_57_2915, _57_2917, t, _57_2920, _57_2922, _57_2924, _57_2926, _57_2928) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _57_2932 -> begin
=======
let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _57_9 -> (match (_57_9) with
| FStar_Syntax_Syntax.Sig_datacon (_57_2938, _57_2940, t, _57_2943, _57_2945, _57_2947, _57_2949, _57_2951) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _57_2955 -> begin
>>>>>>> master
(FStar_All.failwith "Impossible")
end))))
in (

<<<<<<< HEAD
let t = (let _147_1468 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _147_1468))
in (

let _57_2935 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_1469 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _147_1469))
=======
let t = (let _148_1439 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _148_1439))
in (

let _57_2958 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1440 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _148_1440))
>>>>>>> master
end else begin
()
end
in (

<<<<<<< HEAD
let _57_2939 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_57_2939) with
| (uvs, t) -> begin
(

let _57_2941 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_1473 = (let _147_1471 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _147_1471 (FStar_String.concat ", ")))
in (let _147_1472 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _147_1473 _147_1472)))
=======
let _57_2962 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_57_2962) with
| (uvs, t) -> begin
(

let _57_2964 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1444 = (let _148_1442 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _148_1442 (FStar_String.concat ", ")))
in (let _148_1443 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _148_1444 _148_1443)))
>>>>>>> master
end else begin
()
end
in (

<<<<<<< HEAD
let _57_2945 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_57_2945) with
| (uvs, t) -> begin
(

let _57_2949 = (FStar_Syntax_Util.arrow_formals t)
in (match (_57_2949) with
| (args, _57_2948) -> begin
(

let _57_2952 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_57_2952) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _57_2956 se -> (match (_57_2956) with
| (x, _57_2955) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_2960, tps, _57_2963, mutuals, datas, quals, r) -> begin
=======
let _57_2968 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_57_2968) with
| (uvs, t) -> begin
(

let _57_2972 = (FStar_Syntax_Util.arrow_formals t)
in (match (_57_2972) with
| (args, _57_2971) -> begin
(

let _57_2975 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_57_2975) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _57_2979 se -> (match (_57_2979) with
| (x, _57_2978) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_2983, tps, _57_2986, mutuals, datas, quals, r) -> begin
>>>>>>> master
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

<<<<<<< HEAD
let _57_2986 = (match ((let _147_1476 = (FStar_Syntax_Subst.compress ty)
in _147_1476.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _57_2977 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_57_2977) with
=======
let _57_3009 = (match ((let _148_1447 = (FStar_Syntax_Subst.compress ty)
in _148_1447.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _57_3000 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_57_3000) with
>>>>>>> master
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
<<<<<<< HEAD
| _57_2980 -> begin
(let _147_1477 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _147_1477 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
=======
| _57_3003 -> begin
(let _148_1448 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _148_1448 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
>>>>>>> master
end)
in (tps, t))
end))
end
<<<<<<< HEAD
| _57_2983 -> begin
([], ty)
end)
in (match (_57_2986) with
=======
| _57_3006 -> begin
([], ty)
end)
in (match (_57_3009) with
>>>>>>> master
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
<<<<<<< HEAD
| _57_2988 -> begin
=======
| _57_3011 -> begin
>>>>>>> master
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
<<<<<<< HEAD
| _57_2992 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _147_1478 -> FStar_Syntax_Syntax.U_name (_147_1478))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_9 -> (match (_57_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_2997, _57_2999, _57_3001, _57_3003, _57_3005, _57_3007, _57_3009) -> begin
(tc, uvs_universes)
end
| _57_3013 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _57_3018 d -> (match (_57_3018) with
| (t, _57_3017) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _57_3022, _57_3024, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _147_1482 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _147_1482 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _57_3034 -> begin
=======
| _57_3015 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _148_1449 -> FStar_Syntax_Syntax.U_name (_148_1449))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_10 -> (match (_57_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3020, _57_3022, _57_3024, _57_3026, _57_3028, _57_3030, _57_3032) -> begin
(tc, uvs_universes)
end
| _57_3036 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _57_3041 d -> (match (_57_3041) with
| (t, _57_3040) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _57_3045, _57_3047, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _148_1453 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _148_1453 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _57_3057 -> begin
>>>>>>> master
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

<<<<<<< HEAD
let _57_3044 = (FStar_All.pipe_right ses (FStar_List.partition (fun _57_10 -> (match (_57_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_3038) -> begin
true
end
| _57_3041 -> begin
false
end))))
in (match (_57_3044) with
=======
let _57_3067 = (FStar_All.pipe_right ses (FStar_List.partition (fun _57_11 -> (match (_57_11) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_3061) -> begin
true
end
| _57_3064 -> begin
false
end))))
in (match (_57_3067) with
>>>>>>> master
| (tys, datas) -> begin
(

let env0 = env
in (

<<<<<<< HEAD
let _57_3061 = (FStar_List.fold_right (fun tc _57_3050 -> (match (_57_3050) with
| (env, all_tcs, g) -> begin
(

let _57_3054 = (tc_tycon env tc)
in (match (_57_3054) with
| (env, tc, tc_u) -> begin
=======
let _57_3085 = (FStar_List.fold_right (fun tc _57_3073 -> (match (_57_3073) with
| (env, all_tcs, g) -> begin
(

let _57_3078 = (tc_tycon env tc)
in (match (_57_3078) with
| (env, tc, tc_u, guard) -> begin
>>>>>>> master
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (

<<<<<<< HEAD
let _57_3056 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_1486 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _147_1486))
end else begin
()
end
in (let _147_1487 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _147_1487))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_3061) with
| (env, tcs, g) -> begin
(

let _57_3071 = (FStar_List.fold_right (fun se _57_3065 -> (match (_57_3065) with
| (datas, g) -> begin
(

let _57_3068 = (tc_data env tcs se)
in (match (_57_3068) with
| (data, g') -> begin
(let _147_1490 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _147_1490))
end))
end)) datas ([], g))
in (match (_57_3071) with
| (datas, g) -> begin
(

let _57_3074 = (let _147_1491 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _147_1491 datas))
in (match (_57_3074) with
| (tcs, datas) -> begin
(

let sig_bndle = (let _147_1493 = (let _147_1492 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _147_1492))
in FStar_Syntax_Syntax.Sig_bundle (_147_1493))
in (

let split_arrow = (fun t -> (match ((let _147_1496 = (FStar_Syntax_Subst.compress t)
in _147_1496.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(bs, c)
end
| _57_3083 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (_57_3087, _57_3089, t, _57_3092, _57_3094, _57_3096, _57_3098, _57_3100) -> begin
t
end
| _57_3104 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let dr = FStar_Range.dummyRange
in (

let haseq_ty = (fun usubst us acc ty -> (

let _57_3131 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _57_3113, bs, t, _57_3117, d_lids, _57_3120, _57_3122) -> begin
(lid, bs, t, d_lids)
end
| _57_3126 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_57_3131) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _147_1507 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _147_1507 t))
in (

let _57_3136 = (FStar_Syntax_Subst.open_term bs t)
in (match (_57_3136) with
| (bs, t) -> begin
(

let ibs = (match ((let _147_1508 = (FStar_Syntax_Subst.compress t)
in _147_1508.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _57_3139) -> begin
ibs
end
| _57_3143 -> begin
[]
end)
in (

let ibs = (FStar_List.map (fun b -> if (FStar_Syntax_Syntax.is_null_bv (Prims.fst b)) then begin
(let _147_1510 = (FStar_Syntax_Syntax.gen_bv "_indexb_" None (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_147_1510, (Prims.snd b)))
end else begin
b
end) ibs)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _147_1513 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _147_1512 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _147_1513 _147_1512)))
in (

let ind = (let _147_1516 = (FStar_List.map (fun _57_3152 -> (match (_57_3152) with
| (bv, aq) -> begin
(let _147_1515 = (FStar_Syntax_Syntax.bv_to_name bv)
in (_147_1515, aq))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _147_1516 None dr))
in (

let ind = (let _147_1519 = (FStar_List.map (fun _57_3156 -> (match (_57_3156) with
| (bv, aq) -> begin
(let _147_1518 = (FStar_Syntax_Syntax.bv_to_name bv)
in (_147_1518, aq))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _147_1519 None dr))
in (

let haseq_ind = (let _147_1521 = (let _147_1520 = (FStar_Syntax_Syntax.as_arg ind)
in (_147_1520)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _147_1521 None dr))
in (

let bs' = (FStar_List.filter (fun b -> (

let _57_3167 = acc
in (match (_57_3167) with
| (_57_3161, en, _57_3164, _57_3166) -> begin
(

let opt = (let _147_1524 = (let _147_1523 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _147_1523))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort _147_1524 false))
in (match (opt) with
| None -> begin
false
end
| Some (_57_3171) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (let _147_1530 = (let _147_1529 = (let _147_1528 = (let _147_1527 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg _147_1527))
in (_147_1528)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _147_1529 None dr))
in (FStar_Syntax_Util.mk_conj t _147_1530))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let _57_3178 = fml
in (let _147_1536 = (let _147_1535 = (let _147_1534 = (let _147_1533 = (let _147_1532 = (let _147_1531 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_147_1531)::[])
in (_147_1532)::[])
in FStar_Syntax_Syntax.Meta_pattern (_147_1533))
in (fml, _147_1534))
in FStar_Syntax_Syntax.Tm_meta (_147_1535))
in {FStar_Syntax_Syntax.n = _147_1536; FStar_Syntax_Syntax.tk = _57_3178.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_3178.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_3178.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _147_1542 = (let _147_1541 = (let _147_1540 = (let _147_1539 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs ((((Prims.fst b), None))::[]) _147_1539 None))
in (FStar_Syntax_Syntax.as_arg _147_1540))
in (_147_1541)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _147_1542 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _147_1548 = (let _147_1547 = (let _147_1546 = (let _147_1545 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs ((((Prims.fst b), None))::[]) _147_1545 None))
in (FStar_Syntax_Syntax.as_arg _147_1546))
in (_147_1547)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _147_1548 None dr))) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let _57_3192 = acc
in (match (_57_3192) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_57_3197, _57_3199, _57_3201, t_lid, _57_3204, _57_3206, _57_3208, _57_3210) -> begin
(t_lid = lid)
end
| _57_3214 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let haseq_data = (fun acc data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (match ((let _147_1554 = (FStar_Syntax_Subst.compress dt)
in _147_1554.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _57_3223) -> begin
(

let dbs = (let _147_1555 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _147_1555))
in (

let dbs = (let _147_1556 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _147_1556 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (let _147_1561 = (let _147_1560 = (let _147_1559 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_147_1559)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _147_1560 None dr))
in (FStar_Syntax_Util.mk_conj t _147_1561))) FStar_Syntax_Util.t_true dbs)
in (

let _57_3234 = acc
in (match (_57_3234) with
| (env, cond') -> begin
(let _147_1563 = (FStar_TypeChecker_Env.push_binders env dbs)
in (let _147_1562 = (FStar_Syntax_Util.mk_conj cond' cond)
in (_147_1563, _147_1562)))
end))))))
end
| _57_3236 -> begin
acc
end))))
in (

let _57_3239 = (FStar_List.fold_left haseq_data (env, FStar_Syntax_Util.t_true) t_datas)
in (match (_57_3239) with
| (env, cond) -> begin
(

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (let _147_1565 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _147_1564 = (FStar_Syntax_Util.mk_conj cond' cond)
in ((FStar_List.append l_axioms (((axiom_lid, fml))::[])), env, _147_1565, _147_1564))))
end))))))
end))))))))))))))))
end))))
end)))
in (

let is_noeq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Noeq)) quals)
in (

let _57_3265 = if ((FStar_List.length tcs) > 0) then begin
(

let debug_lid = (match ((FStar_List.hd tcs)) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _57_3245, _57_3247, _57_3249, _57_3251, _57_3253, _57_3255, _57_3257) -> begin
lid
end
| _57_3261 -> begin
(FStar_All.failwith "Impossible!")
end)
in (

let _57_3263 = if is_noeq then begin
(FStar_Util.print1 "Skipping this type since noeq:%s\n" debug_lid.FStar_Ident.str)
end else begin
()
end
in ()))
end else begin
()
end
in if ((((not ((FStar_Options.nohaseq ()))) && (not ((FStar_Ident.lid_equals env.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid)))) && (not (is_noeq))) && ((FStar_List.length tcs) > 0)) then begin
(

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_3269, us, _57_3272, _57_3274, _57_3276, _57_3278, _57_3280, _57_3282) -> begin
us
end
| _57_3286 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let _57_3290 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_57_3290) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _57_3292 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _57_3294 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let _57_3301 = (FStar_List.fold_left (haseq_ty usubst us) ([], env, FStar_Syntax_Util.t_true, FStar_Syntax_Util.t_true) tcs)
in (match (_57_3301) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let _57_3303 = (let _147_1567 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print1 "Checking tc_trivial_guard for:\n\n%s\n\n" _147_1567))
in (

let _57_3308 = (tc_trivial_guard env phi)
in (match (_57_3308) with
| (phi, _57_3307) -> begin
(

let _57_3309 = (let _147_1568 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print1 "Checking haseq soundness for:%s\n" _147_1568))
in (

let _57_3311 = (let _147_1569 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _147_1569))
in (

let _57_3313 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env0 us)
in (

let ses = (FStar_List.fold_left (fun l _57_3319 -> (match (_57_3319) with
| (lid, fml) -> begin
(

let _57_3320 = (let _147_1572 = (FStar_Syntax_Print.term_to_string fml)
in (FStar_Util.print1 "Checking tc_assume for axiom:%s\n" _147_1572))
in (

let se = (tc_assume env lid fml [] dr)
in (FStar_List.append l ((se)::[]))))
end)) [] axioms)
in (let _147_1574 = (let _147_1573 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append (FStar_List.append tcs datas) ses), quals, lids, _147_1573))
in FStar_Syntax_Syntax.Sig_bundle (_147_1574)))))))
end))))
end))))))
end)))
end else begin
sig_bndle
end)))))))
=======
let _57_3080 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1457 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _148_1457))
end else begin
()
end
in (let _148_1459 = (let _148_1458 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g _148_1458))
in (env, ((tc, tc_u))::all_tcs, _148_1459))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_3085) with
| (env, tcs, g) -> begin
(

let _57_3095 = (FStar_List.fold_right (fun se _57_3089 -> (match (_57_3089) with
| (datas, g) -> begin
(

let _57_3092 = (tc_data env tcs se)
in (match (_57_3092) with
| (data, g') -> begin
(let _148_1462 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _148_1462))
end))
end)) datas ([], g))
in (match (_57_3095) with
| (datas, g) -> begin
(

let _57_3098 = (let _148_1463 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _148_1463 datas))
in (match (_57_3098) with
| (tcs, datas) -> begin
(let _148_1465 = (let _148_1464 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _148_1464))
in FStar_Syntax_Syntax.Sig_bundle (_148_1465))
>>>>>>> master
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
<<<<<<< HEAD
in (let _147_1579 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _147_1579))))
=======
in (let _148_1470 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _148_1470))))
>>>>>>> master
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let se = (tc_inductive env ses quals lids)
<<<<<<< HEAD
in (let _147_1580 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _147_1580))))
=======
in (let _148_1471 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _148_1471))))
>>>>>>> master
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

<<<<<<< HEAD
let _57_3361 = (set_options FStar_Options.Set o)
=======
let _57_3136 = (set_options FStar_Options.Set o)
>>>>>>> master
in (se, env))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(

<<<<<<< HEAD
let _57_3365 = (let _147_1585 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _147_1585 Prims.ignore))
in (

let _57_3370 = (match (sopt) with
=======
let _57_3140 = (let _148_1476 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _148_1476 Prims.ignore))
in (

let _57_3145 = (match (sopt) with
>>>>>>> master
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

<<<<<<< HEAD
let _57_3372 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
=======
let _57_3147 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
>>>>>>> master
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

<<<<<<< HEAD
let _57_3394 = (let _147_1586 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _147_1586))
in (match (_57_3394) with
| (a, wp_a_src) -> begin
(

let _57_3397 = (let _147_1587 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _147_1587))
in (match (_57_3397) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _147_1591 = (let _147_1590 = (let _147_1589 = (let _147_1588 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _147_1588))
in FStar_Syntax_Syntax.NT (_147_1589))
in (_147_1590)::[])
in (FStar_Syntax_Subst.subst _147_1591 wp_b_tgt))
in (

let expected_k = (let _147_1596 = (let _147_1594 = (FStar_Syntax_Syntax.mk_binder a)
in (let _147_1593 = (let _147_1592 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_147_1592)::[])
in (_147_1594)::_147_1593))
in (let _147_1595 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _147_1596 _147_1595)))
=======
let _57_3169 = (let _148_1477 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _148_1477))
in (match (_57_3169) with
| (a, wp_a_src) -> begin
(

let _57_3172 = (let _148_1478 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _148_1478))
in (match (_57_3172) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _148_1482 = (let _148_1481 = (let _148_1480 = (let _148_1479 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _148_1479))
in FStar_Syntax_Syntax.NT (_148_1480))
in (_148_1481)::[])
in (FStar_Syntax_Subst.subst _148_1482 wp_b_tgt))
in (

let expected_k = (let _148_1487 = (let _148_1485 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1484 = (let _148_1483 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_148_1483)::[])
in (_148_1485)::_148_1484))
in (let _148_1486 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _148_1487 _148_1486)))
>>>>>>> master
in (

let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (

let sub = (

<<<<<<< HEAD
let _57_3401 = sub
in {FStar_Syntax_Syntax.source = _57_3401.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _57_3401.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
=======
let _57_3176 = sub
in {FStar_Syntax_Syntax.source = _57_3176.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _57_3176.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
>>>>>>> master
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

<<<<<<< HEAD
let _57_3414 = ()
=======
let _57_3189 = ()
>>>>>>> master
in (

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

<<<<<<< HEAD
let _57_3420 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_57_3420) with
| (tps, c) -> begin
(

let _57_3424 = (tc_tparams env tps)
in (match (_57_3424) with
| (tps, env, us) -> begin
(

let _57_3428 = (tc_comp env c)
in (match (_57_3428) with
| (c, u, g) -> begin
(

let _57_3429 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
=======
let _57_3195 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_57_3195) with
| (tps, c) -> begin
(

let _57_3199 = (tc_tparams env tps)
in (match (_57_3199) with
| (tps, env, us) -> begin
(

let _57_3203 = (tc_comp env c)
in (match (_57_3203) with
| (c, u, g) -> begin
(

let _57_3204 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
>>>>>>> master
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

<<<<<<< HEAD
let _57_3435 = (let _147_1597 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _147_1597))
in (match (_57_3435) with
| (uvs, t) -> begin
(

let _57_3454 = (match ((let _147_1599 = (let _147_1598 = (FStar_Syntax_Subst.compress t)
in _147_1598.FStar_Syntax_Syntax.n)
in (tps, _147_1599))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_57_3438, c)) -> begin
([], c)
end
| (_57_3444, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _57_3451 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_3454) with
=======
let _57_3210 = (let _148_1488 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _148_1488))
in (match (_57_3210) with
| (uvs, t) -> begin
(

let _57_3229 = (match ((let _148_1490 = (let _148_1489 = (FStar_Syntax_Subst.compress t)
in _148_1489.FStar_Syntax_Syntax.n)
in (tps, _148_1490))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_57_3213, c)) -> begin
([], c)
end
| (_57_3219, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _57_3226 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_3229) with
>>>>>>> master
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

<<<<<<< HEAD
let _57_3465 = ()
in (

let _57_3469 = (let _147_1601 = (let _147_1600 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _147_1600))
in (check_and_gen env t _147_1601))
in (match (_57_3469) with
=======
let _57_3240 = ()
in (

let _57_3244 = (let _148_1492 = (let _148_1491 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _148_1491))
in (check_and_gen env t _148_1492))
in (match (_57_3244) with
>>>>>>> master
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

<<<<<<< HEAD
let se = (tc_assume env lid phi quals r)
=======
let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _57_3257 = (FStar_Syntax_Util.type_u ())
in (match (_57_3257) with
| (k, _57_3256) -> begin
(

let phi = (let _148_1493 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _148_1493 (norm env)))
in (

let _57_3259 = (FStar_TypeChecker_Util.check_uvars r phi)
in (

let se = FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))
>>>>>>> master
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

<<<<<<< HEAD
let _57_3489 = (tc_term env e)
in (match (_57_3489) with
| (e, c, g1) -> begin
(

let _57_3494 = (let _147_1605 = (let _147_1602 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_147_1602))
in (let _147_1604 = (let _147_1603 = (c.FStar_Syntax_Syntax.comp ())
in (e, _147_1603))
in (check_expected_effect env _147_1605 _147_1604)))
in (match (_57_3494) with
| (e, _57_3492, g) -> begin
(

let _57_3495 = (let _147_1606 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _147_1606))
=======
let _57_3272 = (tc_term env e)
in (match (_57_3272) with
| (e, c, g1) -> begin
(

let _57_3277 = (let _148_1497 = (let _148_1494 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_148_1494))
in (let _148_1496 = (let _148_1495 = (c.FStar_Syntax_Syntax.comp ())
in (e, _148_1495))
in (check_expected_effect env _148_1497 _148_1496)))
in (match (_57_3277) with
| (e, _57_3275, g) -> begin
(

let _57_3278 = (let _148_1498 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _148_1498))
>>>>>>> master
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
<<<<<<< HEAD
(let _147_1618 = (let _147_1617 = (let _147_1616 = (let _147_1615 = (FStar_Syntax_Print.lid_to_string l)
in (let _147_1614 = (FStar_Syntax_Print.quals_to_string q)
in (let _147_1613 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _147_1615 _147_1614 _147_1613))))
in (_147_1616, r))
in FStar_Syntax_Syntax.Error (_147_1617))
in (Prims.raise _147_1618))
=======
(let _148_1510 = (let _148_1509 = (let _148_1508 = (let _148_1507 = (FStar_Syntax_Print.lid_to_string l)
in (let _148_1506 = (FStar_Syntax_Print.quals_to_string q)
in (let _148_1505 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _148_1507 _148_1506 _148_1505))))
in (_148_1508, r))
in FStar_Syntax_Syntax.Error (_148_1509))
in (Prims.raise _148_1510))
>>>>>>> master
end
end))
in (

<<<<<<< HEAD
let _57_3539 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _57_3516 lb -> (match (_57_3516) with
=======
let _57_3322 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _57_3299 lb -> (match (_57_3299) with
>>>>>>> master
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

<<<<<<< HEAD
let _57_3535 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
=======
let _57_3318 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
>>>>>>> master
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (

<<<<<<< HEAD
let _57_3530 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _57_3529 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _147_1621 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _147_1621, quals_opt))))
end)
in (match (_57_3535) with
=======
let _57_3313 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _57_3312 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _148_1513 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _148_1513, quals_opt))))
end)
in (match (_57_3318) with
>>>>>>> master
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
<<<<<<< HEAD
in (match (_57_3539) with
=======
in (match (_57_3322) with
>>>>>>> master
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
<<<<<<< HEAD
| _57_3548 -> begin
=======
| _57_3331 -> begin
>>>>>>> master
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

<<<<<<< HEAD
let e = (let _147_1625 = (let _147_1624 = (let _147_1623 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _147_1623))
in FStar_Syntax_Syntax.Tm_let (_147_1624))
in (FStar_Syntax_Syntax.mk _147_1625 None r))
in (

let _57_3582 = (match ((tc_maybe_toplevel_term (

let _57_3552 = env
in {FStar_TypeChecker_Env.solver = _57_3552.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3552.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3552.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3552.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3552.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3552.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3552.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3552.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3552.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3552.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3552.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _57_3552.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _57_3552.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3552.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3552.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3552.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3552.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3552.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3552.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _57_3559; FStar_Syntax_Syntax.pos = _57_3557; FStar_Syntax_Syntax.vars = _57_3555}, _57_3566, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_57_3570, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _57_3576 -> begin
=======
let e = (let _148_1517 = (let _148_1516 = (let _148_1515 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _148_1515))
in FStar_Syntax_Syntax.Tm_let (_148_1516))
in (FStar_Syntax_Syntax.mk _148_1517 None r))
in (

let _57_3365 = (match ((tc_maybe_toplevel_term (

let _57_3335 = env
in {FStar_TypeChecker_Env.solver = _57_3335.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3335.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3335.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3335.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3335.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3335.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3335.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3335.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3335.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3335.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3335.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _57_3335.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _57_3335.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3335.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3335.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3335.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3335.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3335.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3335.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _57_3342; FStar_Syntax_Syntax.pos = _57_3340; FStar_Syntax_Syntax.vars = _57_3338}, _57_3349, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_57_3353, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _57_3359 -> begin
>>>>>>> master
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
<<<<<<< HEAD
| _57_3579 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_57_3582) with
| (se, lbs) -> begin
(

let _57_3588 = if (log env) then begin
(let _147_1633 = (let _147_1632 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _147_1629 = (let _147_1628 = (let _147_1627 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _147_1627.FStar_Syntax_Syntax.fv_name)
in _147_1628.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _147_1629))) with
| None -> begin
true
end
| _57_3586 -> begin
false
end)
in if should_log then begin
(let _147_1631 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _147_1630 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _147_1631 _147_1630)))
end else begin
""
end))))
in (FStar_All.pipe_right _147_1632 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _147_1633))
=======
| _57_3362 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_57_3365) with
| (se, lbs) -> begin
(

let _57_3371 = if (log env) then begin
(let _148_1525 = (let _148_1524 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _148_1521 = (let _148_1520 = (let _148_1519 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _148_1519.FStar_Syntax_Syntax.fv_name)
in _148_1520.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _148_1521))) with
| None -> begin
true
end
| _57_3369 -> begin
false
end)
in if should_log then begin
(let _148_1523 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _148_1522 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _148_1523 _148_1522)))
end else begin
""
end))))
in (FStar_All.pipe_right _148_1524 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _148_1525))
>>>>>>> master
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
<<<<<<< HEAD
| _57_3598 -> begin
=======
| _57_3381 -> begin
>>>>>>> master
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
<<<<<<< HEAD
| _57_3608 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_57_3610) -> begin
=======
| _57_3391 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_57_3393) -> begin
>>>>>>> master
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
<<<<<<< HEAD
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _57_3621, _57_3623) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _57_3629 -> (match (_57_3629) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _57_3635, _57_3637, quals, r) -> begin
(

let dec = (let _147_1649 = (let _147_1648 = (let _147_1647 = (let _147_1646 = (let _147_1645 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _147_1645))
in FStar_Syntax_Syntax.Tm_arrow (_147_1646))
in (FStar_Syntax_Syntax.mk _147_1647 None r))
in (l, us, _147_1648, (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_147_1649))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _57_3647, _57_3649, _57_3651, _57_3653, r) -> begin
=======
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _57_3404, _57_3406) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _57_3412 -> (match (_57_3412) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _57_3418, _57_3420, quals, r) -> begin
(

let dec = (let _148_1541 = (let _148_1540 = (let _148_1539 = (let _148_1538 = (let _148_1537 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _148_1537))
in FStar_Syntax_Syntax.Tm_arrow (_148_1538))
in (FStar_Syntax_Syntax.mk _148_1539 None r))
in (l, us, _148_1540, (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_148_1541))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _57_3430, _57_3432, _57_3434, _57_3436, r) -> begin
>>>>>>> master
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
<<<<<<< HEAD
| _57_3659 -> begin
=======
| _57_3442 -> begin
>>>>>>> master
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
<<<<<<< HEAD
| FStar_Syntax_Syntax.Sig_assume (_57_3661, _57_3663, quals, _57_3666) -> begin
=======
| FStar_Syntax_Syntax.Sig_assume (_57_3444, _57_3446, quals, _57_3449) -> begin
>>>>>>> master
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
<<<<<<< HEAD
| _57_3685 -> begin
=======
| _57_3468 -> begin
>>>>>>> master
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
<<<<<<< HEAD
| FStar_Syntax_Syntax.Sig_main (_57_3687) -> begin
=======
| FStar_Syntax_Syntax.Sig_main (_57_3470) -> begin
>>>>>>> master
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
<<<<<<< HEAD
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _57_3706, _57_3708, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
=======
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _57_3489, _57_3491, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
>>>>>>> master
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
<<<<<<< HEAD
(let _147_1656 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _147_1655 = (let _147_1654 = (let _147_1653 = (let _147_1652 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _147_1652.FStar_Syntax_Syntax.fv_name)
in _147_1653.FStar_Syntax_Syntax.v)
in (_147_1654, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_147_1655)))))
in (_147_1656, hidden))
=======
(let _148_1548 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _148_1547 = (let _148_1546 = (let _148_1545 = (let _148_1544 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _148_1544.FStar_Syntax_Syntax.fv_name)
in _148_1545.FStar_Syntax_Syntax.v)
in (_148_1546, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_148_1547)))))
in (_148_1548, hidden))
>>>>>>> master
end else begin
((se)::[], hidden)
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

<<<<<<< HEAD
let _57_3747 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _57_3728 se -> (match (_57_3728) with
| (ses, exports, env, hidden) -> begin
(

let _57_3730 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _147_1663 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _147_1663))
=======
let _57_3530 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _57_3511 se -> (match (_57_3511) with
| (ses, exports, env, hidden) -> begin
(

let _57_3513 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1555 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _148_1555))
>>>>>>> master
end else begin
()
end
in (

<<<<<<< HEAD
let _57_3734 = (tc_decl env se)
in (match (_57_3734) with
| (se, env) -> begin
(

let _57_3735 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _147_1664 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _147_1664))
=======
let _57_3517 = (tc_decl env se)
in (match (_57_3517) with
| (se, env) -> begin
(

let _57_3518 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _148_1556 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _148_1556))
>>>>>>> master
end else begin
()
end
in (

<<<<<<< HEAD
let _57_3737 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (

let _57_3741 = (for_export hidden se)
in (match (_57_3741) with
=======
let _57_3520 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (

let _57_3524 = (for_export hidden se)
in (match (_57_3524) with
>>>>>>> master
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
<<<<<<< HEAD
in (match (_57_3747) with
| (ses, exports, env, _57_3746) -> begin
(let _147_1665 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _147_1665, env))
=======
in (match (_57_3530) with
| (ses, exports, env, _57_3529) -> begin
(let _148_1557 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _148_1557, env))
>>>>>>> master
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

<<<<<<< HEAD
let _57_3752 = env
in (let _147_1670 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _57_3752.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3752.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3752.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3752.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3752.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3752.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3752.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3752.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3752.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3752.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3752.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3752.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3752.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_3752.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_3752.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3752.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _147_1670; FStar_TypeChecker_Env.type_of = _57_3752.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3752.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3752.FStar_TypeChecker_Env.use_bv_sorts}))
in (

let _57_3755 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
=======
let _57_3535 = env
in (let _148_1562 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _57_3535.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3535.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3535.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3535.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3535.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3535.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3535.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3535.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3535.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3535.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3535.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3535.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3535.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_3535.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_3535.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3535.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _148_1562; FStar_TypeChecker_Env.type_of = _57_3535.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3535.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3535.FStar_TypeChecker_Env.use_bv_sorts}))
in (

let _57_3538 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
>>>>>>> master
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

<<<<<<< HEAD
let _57_3761 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_57_3761) with
| (ses, exports, env) -> begin
((

let _57_3762 = modul
in {FStar_Syntax_Syntax.name = _57_3762.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _57_3762.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3762.FStar_Syntax_Syntax.is_interface}), exports, env)
=======
let _57_3544 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_57_3544) with
| (ses, exports, env) -> begin
((

let _57_3545 = modul
in {FStar_Syntax_Syntax.name = _57_3545.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _57_3545.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3545.FStar_Syntax_Syntax.is_interface}), exports, env)
>>>>>>> master
end))))))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

<<<<<<< HEAD
let _57_3770 = (tc_decls env decls)
in (match (_57_3770) with
=======
let _57_3553 = (tc_decls env decls)
in (match (_57_3553) with
>>>>>>> master
| (ses, exports, env) -> begin
(

let modul = (

<<<<<<< HEAD
let _57_3771 = modul
in {FStar_Syntax_Syntax.name = _57_3771.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _57_3771.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3771.FStar_Syntax_Syntax.is_interface})
=======
let _57_3554 = modul
in {FStar_Syntax_Syntax.name = _57_3554.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _57_3554.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3554.FStar_Syntax_Syntax.is_interface})
>>>>>>> master
in (modul, exports, env))
end)))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul = (

<<<<<<< HEAD
let _57_3777 = modul
in {FStar_Syntax_Syntax.name = _57_3777.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _57_3777.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
=======
let _57_3560 = modul
in {FStar_Syntax_Syntax.name = _57_3560.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _57_3560.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
>>>>>>> master
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in (

<<<<<<< HEAD
let _57_3787 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(

let _57_3781 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let _57_3783 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (

let _57_3785 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _147_1683 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _147_1683 Prims.ignore)))))
=======
let _57_3570 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(

let _57_3564 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let _57_3566 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (

let _57_3568 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _148_1575 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _148_1575 Prims.ignore)))))
>>>>>>> master
end else begin
()
end
in (modul, env)))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

<<<<<<< HEAD
let _57_3794 = (tc_partial_modul env modul)
in (match (_57_3794) with
=======
let _57_3577 = (tc_partial_modul env modul)
in (match (_57_3577) with
>>>>>>> master
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

<<<<<<< HEAD
let _57_3797 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _147_1692 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _147_1692))
=======
let _57_3580 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _148_1584 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _148_1584))
>>>>>>> master
end else begin
()
end
in (

let env = (

<<<<<<< HEAD
let _57_3799 = env
in {FStar_TypeChecker_Env.solver = _57_3799.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3799.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3799.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3799.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3799.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3799.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3799.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3799.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3799.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3799.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3799.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3799.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3799.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_3799.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3799.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3799.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3799.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3799.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3799.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3799.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_3815 = try
=======
let _57_3582 = env
in {FStar_TypeChecker_Env.solver = _57_3582.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3582.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3582.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3582.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3582.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3582.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3582.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3582.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3582.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3582.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3582.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3582.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3582.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_3582.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3582.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3582.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3582.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3582.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3582.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3582.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_3598 = try
>>>>>>> master
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
<<<<<<< HEAD
| FStar_Syntax_Syntax.Error (msg, _57_3807) -> begin
(let _147_1697 = (let _147_1696 = (let _147_1695 = (FStar_TypeChecker_Env.get_range env)
in ((Prims.strcat "Implicit argument: " msg), _147_1695))
in FStar_Syntax_Syntax.Error (_147_1696))
in (Prims.raise _147_1697))
end
in (match (_57_3815) with
=======
| FStar_Syntax_Syntax.Error (msg, _57_3590) -> begin
(let _148_1589 = (let _148_1588 = (let _148_1587 = (FStar_TypeChecker_Env.get_range env)
in ((Prims.strcat "Implicit argument: " msg), _148_1587))
in FStar_Syntax_Syntax.Error (_148_1588))
in (Prims.raise _148_1589))
end
in (match (_57_3598) with
>>>>>>> master
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(t, c.FStar_Syntax_Syntax.res_typ, g)
end else begin
<<<<<<< HEAD
(let _147_1702 = (let _147_1701 = (let _147_1700 = (let _147_1698 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _147_1698))
in (let _147_1699 = (FStar_TypeChecker_Env.get_range env)
in (_147_1700, _147_1699)))
in FStar_Syntax_Syntax.Error (_147_1701))
in (Prims.raise _147_1702))
=======
(let _148_1594 = (let _148_1593 = (let _148_1592 = (let _148_1590 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _148_1590))
in (let _148_1591 = (FStar_TypeChecker_Env.get_range env)
in (_148_1592, _148_1591)))
in FStar_Syntax_Syntax.Error (_148_1593))
in (Prims.raise _148_1594))
>>>>>>> master
end
end)))))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

<<<<<<< HEAD
let _57_3818 = if (FStar_Options.debug_any ()) then begin
(let _147_1707 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
=======
let _57_3601 = if (FStar_Options.debug_any ()) then begin
(let _148_1599 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
>>>>>>> master
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
<<<<<<< HEAD
end) _147_1707))
=======
end) _148_1599))
>>>>>>> master
end else begin
()
end
in (

<<<<<<< HEAD
let _57_3822 = (tc_modul env m)
in (match (_57_3822) with
| (m, env) -> begin
(

let _57_3823 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _147_1708 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _147_1708))
=======
let _57_3605 = (tc_modul env m)
in (match (_57_3605) with
| (m, env) -> begin
(

let _57_3606 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _148_1600 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _148_1600))
>>>>>>> master
end else begin
()
end
in (m, env))
end))))




