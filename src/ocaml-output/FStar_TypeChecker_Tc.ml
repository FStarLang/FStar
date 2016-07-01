
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
in {FStar_TypeChecker_Env.solver = _57_19.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_19.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_19.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_19.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_19.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_19.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_19.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_19.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_19.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _57_19.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_19.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_19.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_19.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_19.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_19.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_19.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_19.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_19.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_19.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_19.FStar_TypeChecker_Env.use_bv_sorts}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _57_22 = env
in {FStar_TypeChecker_Env.solver = _57_22.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_22.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_22.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_22.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_22.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_22.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_22.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_22.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_22.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _57_22.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_22.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_22.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_22.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_22.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_22.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_22.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_22.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_22.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_22.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_22.FStar_TypeChecker_Env.use_bv_sorts}))


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

let _57_115 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, guard)
end
| Some (t') -> begin
(

let _57_97 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_87 = (FStar_Syntax_Print.term_to_string t)
in (let _148_86 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _148_87 _148_86)))
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
(let _148_89 = (FStar_Syntax_Print.term_to_string t)
in (let _148_88 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _148_89 _148_88)))
end else begin
()
end
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let _57_111 = (let _148_95 = (FStar_All.pipe_left (fun _148_94 -> Some (_148_94)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _148_95 env e lc g))
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

let _57_140 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
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

let _57_143 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_118 = (FStar_Syntax_Print.term_to_string e)
in (let _148_117 = (FStar_Syntax_Print.comp_to_string c)
in (let _148_116 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _148_118 _148_117 _148_116))))
end else begin
()
end
in (

let _57_149 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_57_149) with
| (e, _57_147, g) -> begin
(

let g = (let _148_119 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _148_119 "could not prove post-condition" g))
in (

let _57_151 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
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


let no_logical_guard = (fun env _57_158 -> (match (_57_158) with
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
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _57_182; FStar_Syntax_Syntax.result_typ = _57_180; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, _57_174))::[]; FStar_Syntax_Syntax.flags = _57_171}) -> begin
(

let pat_vars = (FStar_Syntax_Free.names pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _57_189 -> (match (_57_189) with
| (b, _57_188) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _57_193) -> begin
(let _148_137 = (let _148_136 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _148_136))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _148_137))
end))
end
| _57_197 -> begin
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

let _57_204 = env
in {FStar_TypeChecker_Env.solver = _57_204.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_204.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_204.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_204.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_204.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_204.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_204.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_204.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_204.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_204.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_204.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_204.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_204.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_204.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_204.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_204.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_204.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_204.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_204.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_204.FStar_TypeChecker_Env.use_bv_sorts})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _57_216 -> (match (_57_216) with
| (b, _57_215) -> begin
(

let t = (let _148_151 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _148_151))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _57_225 -> begin
(let _148_152 = (FStar_Syntax_Syntax.bv_to_name b)
in (_148_152)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let _57_231 = (FStar_Syntax_Util.head_and_args dec)
in (match (_57_231) with
| (head, _57_230) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _57_235 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _57_3 -> (match (_57_3) with
| FStar_Syntax_Syntax.DECREASES (_57_239) -> begin
true
end
| _57_242 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _57_247 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| _57_252 -> begin
(mk_lex_list xs)
end))
end)))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun _57_257 -> (match (_57_257) with
| (l, t) -> begin
(match ((let _148_158 = (FStar_Syntax_Subst.compress t)
in _148_158.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _57_264 -> (match (_57_264) with
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

let _57_268 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_57_268) with
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

let _57_275 = (FStar_Util.prefix formals)
in (match (_57_275) with
| (bs, (last, imp)) -> begin
(

let last = (

let _57_276 = last
in (let _148_167 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _57_276.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_276.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_167}))
in (

let refined_formals = (FStar_List.append bs (((last, imp))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (

let _57_281 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
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
| _57_284 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end))


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let _57_287 = env
in {FStar_TypeChecker_Env.solver = _57_287.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_287.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_287.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_287.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_287.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_287.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_287.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_287.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_287.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_287.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_287.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_287.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_287.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_287.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_287.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_287.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_287.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_287.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_287.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_287.FStar_TypeChecker_Env.use_bv_sorts}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (

let _57_292 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
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
| FStar_Syntax_Syntax.Tm_delayed (_57_296) -> begin
(let _148_242 = (FStar_Syntax_Subst.compress e)
in (tc_term env _148_242))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let _57_337 = (tc_tot_or_gtot_term env e)
in (match (_57_337) with
| (e, c, g) -> begin
(

let g = (

let _57_338 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_338.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_338.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_338.FStar_TypeChecker_Env.implicits})
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let _57_348 = (FStar_Syntax_Util.type_u ())
in (match (_57_348) with
| (t, u) -> begin
(

let _57_352 = (tc_check_tot_or_gtot_term env e t)
in (match (_57_352) with
| (e, c, g) -> begin
(

let _57_359 = (

let _57_356 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_356) with
| (env, _57_355) -> begin
(tc_pats env pats)
end))
in (match (_57_359) with
| (pats, g') -> begin
(

let g' = (

let _57_360 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_360.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_360.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_360.FStar_TypeChecker_Env.implicits})
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
| FStar_Syntax_Syntax.Tm_let ((_57_369, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _57_376; FStar_Syntax_Syntax.lbtyp = _57_374; FStar_Syntax_Syntax.lbeff = _57_372; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _57_387 = (let _148_246 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _148_246 e1))
in (match (_57_387) with
| (e1, c1, g1) -> begin
(

let _57_391 = (tc_term env e2)
in (match (_57_391) with
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
| _57_396 -> begin
(

let _57_400 = (tc_term env e)
in (match (_57_400) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let _57_409 = (tc_term env e)
in (match (_57_409) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, m))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _57_415) -> begin
(

let _57_422 = (tc_comp env expected_c)
in (match (_57_422) with
| (expected_c, _57_420, g) -> begin
(

let _57_426 = (tc_term env e)
in (match (_57_426) with
| (e, c', g') -> begin
(

let _57_430 = (let _148_254 = (let _148_253 = (c'.FStar_Syntax_Syntax.comp ())
in (e, _148_253))
in (check_expected_effect env (Some (expected_c)) _148_254))
in (match (_57_430) with
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
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _57_436) -> begin
(

let _57_441 = (FStar_Syntax_Util.type_u ())
in (match (_57_441) with
| (k, u) -> begin
(

let _57_446 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_446) with
| (t, _57_444, f) -> begin
(

let _57_450 = (let _148_258 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _148_258 e))
in (match (_57_450) with
| (e, c, g) -> begin
(

let _57_454 = (let _148_262 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_451 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _148_262 e c f))
in (match (_57_454) with
| (c, f) -> begin
(

let _57_458 = (let _148_263 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t), Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _148_263 c))
in (match (_57_458) with
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

let _57_465 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_269 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _148_268 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _148_269 _148_268)))
end else begin
()
end
in (

let _57_470 = (tc_term (no_inst env) head)
in (match (_57_470) with
| (head, chead, g_head) -> begin
(

let _57_474 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _148_270 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _148_270))
end else begin
(let _148_271 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _148_271))
end
in (match (_57_474) with
| (e, c, g) -> begin
(

let _57_475 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
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

let _57_481 = (comp_check_expected_typ env0 e c)
in (match (_57_481) with
| (e, c, g') -> begin
(

let gimp = (match ((let _148_273 = (FStar_Syntax_Subst.compress head)
in _148_273.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _57_484) -> begin
(

let imp = ("head of application is a uvar", env0, u, e, c.FStar_Syntax_Syntax.res_typ, head.FStar_Syntax_Syntax.pos)
in (

let _57_488 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_488.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_488.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_488.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _57_491 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (

let gres = (let _148_274 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _148_274))
in (

let _57_494 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
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

let _57_502 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_502) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let _57_507 = (tc_term env1 e1)
in (match (_57_507) with
| (e1, c1, g1) -> begin
(

let _57_518 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(

let _57_514 = (FStar_Syntax_Util.type_u ())
in (match (_57_514) with
| (k, _57_513) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _148_277 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_148_277, res_t)))
end))
end)
in (match (_57_518) with
| (env_branches, res_t) -> begin
(

let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let _57_535 = (

let _57_532 = (FStar_List.fold_right (fun _57_526 _57_529 -> (match ((_57_526, _57_529)) with
| ((_57_522, f, c, g), (caccum, gaccum)) -> begin
(let _148_280 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _148_280))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_532) with
| (cases, g) -> begin
(let _148_281 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_148_281, g))
end))
in (match (_57_535) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (Some (guard_x), c_branches))
in (

let e = (let _148_285 = (let _148_284 = (let _148_283 = (FStar_List.map (fun _57_544 -> (match (_57_544) with
| (f, _57_539, _57_541, _57_543) -> begin
f
end)) t_eqns)
in (e1, _148_283))
in FStar_Syntax_Syntax.Tm_match (_148_284))
in (FStar_Syntax_Syntax.mk _148_285 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ), Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (

let _57_547 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
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
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_559); FStar_Syntax_Syntax.lbunivs = _57_557; FStar_Syntax_Syntax.lbtyp = _57_555; FStar_Syntax_Syntax.lbeff = _57_553; FStar_Syntax_Syntax.lbdef = _57_551})::[]), _57_565) -> begin
(

let _57_568 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_290 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _148_290))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _57_572), _57_575) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_590); FStar_Syntax_Syntax.lbunivs = _57_588; FStar_Syntax_Syntax.lbtyp = _57_586; FStar_Syntax_Syntax.lbeff = _57_584; FStar_Syntax_Syntax.lbdef = _57_582})::_57_580), _57_596) -> begin
(

let _57_599 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_291 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _148_291))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _57_603), _57_606) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let _57_620 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_620) with
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
| _57_630 -> begin
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
| FStar_Syntax_Syntax.Tm_arrow (_57_641) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _57_644 -> begin
(

let imp = ("uvar in term", env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (

let _57_646 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_646.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_646.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_646.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _57_652 = (FStar_Syntax_Util.type_u ())
in (match (_57_652) with
| (k, u) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _57_658 = (FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
in (match (_57_658) with
| (t, _57_656, g0) -> begin
(

let _57_663 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (_57_663) with
| (e, _57_661, g1) -> begin
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

let _57_667 = x
in {FStar_Syntax_Syntax.ppname = _57_667.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_667.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let _57_673 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_673) with
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
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _57_680; FStar_Syntax_Syntax.pos = _57_678; FStar_Syntax_Syntax.vars = _57_676}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let _57_690 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_690) with
| (us', t) -> begin
(

let _57_697 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _148_318 = (let _148_317 = (let _148_316 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _148_316))
in FStar_Syntax_Syntax.Error (_148_317))
in (Prims.raise _148_318))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _57_696 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (

let fv' = (

let _57_699 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _57_701 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_701.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_701.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_699.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_699.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _148_321 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _148_321 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let _57_709 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_709) with
| (us, t) -> begin
(

let fv' = (

let _57_710 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _57_712 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_712.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_712.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_710.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_710.FStar_Syntax_Syntax.fv_qual})
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

let _57_726 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_726) with
| (bs, c) -> begin
(

let env0 = env
in (

let _57_731 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_731) with
| (env, _57_730) -> begin
(

let _57_736 = (tc_binders env bs)
in (match (_57_736) with
| (bs, env, g, us) -> begin
(

let _57_740 = (tc_comp env c)
in (match (_57_740) with
| (c, uc, f) -> begin
(

let e = (

let _57_741 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _57_741.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_741.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_741.FStar_Syntax_Syntax.vars})
in (

let _57_744 = (check_smt_pat env e bs c)
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

let _57_760 = (let _148_325 = (let _148_324 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_324)::[])
in (FStar_Syntax_Subst.open_term _148_325 phi))
in (match (_57_760) with
| (x, phi) -> begin
(

let env0 = env
in (

let _57_765 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_765) with
| (env, _57_764) -> begin
(

let _57_770 = (let _148_326 = (FStar_List.hd x)
in (tc_binder env _148_326))
in (match (_57_770) with
| (x, env, f1, u) -> begin
(

let _57_771 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_329 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _148_328 = (FStar_Syntax_Print.term_to_string phi)
in (let _148_327 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _148_329 _148_328 _148_327))))
end else begin
()
end
in (

let _57_776 = (FStar_Syntax_Util.type_u ())
in (match (_57_776) with
| (t_phi, _57_775) -> begin
(

let _57_781 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_57_781) with
| (phi, _57_779, f2) -> begin
(

let e = (

let _57_782 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _57_782.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_782.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_782.FStar_Syntax_Syntax.vars})
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
| FStar_Syntax_Syntax.Tm_abs (bs, body, _57_790) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (

let _57_796 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_331 = (FStar_Syntax_Print.term_to_string (

let _57_794 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _57_794.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_794.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_794.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _148_331))
end else begin
()
end
in (

let _57_800 = (FStar_Syntax_Subst.open_term bs body)
in (match (_57_800) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _57_802 -> begin
(let _148_333 = (let _148_332 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _148_332))
in (FStar_All.failwith _148_333))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_57_807) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_57_810, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_57_815, Some (_57_817)) -> begin
(FStar_All.failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (_57_822) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_57_825) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_57_828) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_57_832) -> begin
FStar_TypeChecker_Common.t_range
end
| _57_835 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(

let _57_842 = (FStar_Syntax_Util.type_u ())
in (match (_57_842) with
| (k, u) -> begin
(

let _57_847 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_847) with
| (t, _57_845, g) -> begin
(let _148_338 = (FStar_Syntax_Syntax.mk_Total t)
in (_148_338, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(

let _57_852 = (FStar_Syntax_Util.type_u ())
in (match (_57_852) with
| (k, u) -> begin
(

let _57_857 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_857) with
| (t, _57_855, g) -> begin
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

let _57_866 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_57_866) with
| (tc, _57_864, f) -> begin
(

let _57_870 = (FStar_Syntax_Util.head_and_args tc)
in (match (_57_870) with
| (_57_868, args) -> begin
(

let _57_873 = (let _148_343 = (FStar_List.hd args)
in (let _148_342 = (FStar_List.tl args)
in (_148_343, _148_342)))
in (match (_57_873) with
| (res, args) -> begin
(

let _57_889 = (let _148_345 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _57_5 -> (match (_57_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _57_880 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_880) with
| (env, _57_879) -> begin
(

let _57_885 = (tc_tot_or_gtot_term env e)
in (match (_57_885) with
| (e, _57_883, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _148_345 FStar_List.unzip))
in (match (_57_889) with
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

let _57_895 = c
in {FStar_Syntax_Syntax.effect_name = _57_895.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _57_895.FStar_Syntax_Syntax.flags}))
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
| FStar_Syntax_Syntax.U_bvar (_57_903) -> begin
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
| _57_918 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _148_367 = (let _148_366 = (let _148_365 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_148_365, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_148_366))
in (Prims.raise _148_367)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun _57_936 bs bs_expected -> (match (_57_936) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
(

let _57_967 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _148_384 = (let _148_383 = (let _148_382 = (let _148_380 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _148_380))
in (let _148_381 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_148_382, _148_381)))
in FStar_Syntax_Syntax.Error (_148_383))
in (Prims.raise _148_384))
end
| _57_966 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _57_984 = (match ((let _148_385 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _148_385.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _57_972 -> begin
(

let _57_973 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_386 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _148_386))
end else begin
()
end
in (

let _57_979 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_57_979) with
| (t, _57_977, g1) -> begin
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
in (match (_57_984) with
| (t, g) -> begin
(

let hd = (

let _57_985 = hd
in {FStar_Syntax_Syntax.ppname = _57_985.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_985.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
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

let _57_1006 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1005 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (

let _57_1013 = (tc_binders env bs)
in (match (_57_1013) with
| (bs, envbody, g, _57_1012) -> begin
(

let _57_1031 = (match ((let _148_397 = (FStar_Syntax_Subst.compress body)
in _148_397.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _57_1018) -> begin
(

let _57_1025 = (tc_comp envbody c)
in (match (_57_1025) with
| (c, _57_1023, g') -> begin
(let _148_398 = (FStar_TypeChecker_Rel.conj_guard g g')
in (Some (c), body, _148_398))
end))
end
| _57_1027 -> begin
(None, body, g)
end)
in (match (_57_1031) with
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

let _57_1058 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1057 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _57_1065 = (tc_binders env bs)
in (match (_57_1065) with
| (bs, envbody, g, _57_1064) -> begin
(

let _57_1069 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_57_1069) with
| (envbody, _57_1068) -> begin
(Some ((t, true)), bs, [], None, envbody, body, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _57_1072) -> begin
(

let _57_1083 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_57_1083) with
| (_57_1076, bs, bs', copt, env, body, g) -> begin
(Some ((t, false)), bs, bs', copt, env, body, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _57_1090 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_57_1090) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun _57_1101 c_expected -> (match (_57_1101) with
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

let _57_1122 = (check_binders env more_bs bs_expected)
in (match (_57_1122) with
| (env, bs', more, guard', subst) -> begin
(let _148_418 = (let _148_417 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _148_417, subst))
in (handle_more _148_418 c_expected))
end))
end
| _57_1124 -> begin
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

let _57_1130 = envbody
in {FStar_TypeChecker_Env.solver = _57_1130.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1130.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1130.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1130.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1130.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1130.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1130.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1130.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1130.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1130.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1130.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1130.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_1130.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1130.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1130.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1130.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1130.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1130.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1130.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1130.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _57_1135 _57_1138 -> (match ((_57_1135, _57_1138)) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _57_1144 = (let _148_431 = (let _148_430 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _148_430 Prims.fst))
in (tc_term _148_431 t))
in (match (_57_1144) with
| (t, _57_1141, _57_1143) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _148_432 = (FStar_Syntax_Syntax.mk_binder (

let _57_1148 = x
in {FStar_Syntax_Syntax.ppname = _57_1148.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1148.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_148_432)::letrec_binders)
end
| _57_1151 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (

let _57_1157 = (check_actuals_against_formals env bs bs_expected)
in (match (_57_1157) with
| (envbody, bs, g, c) -> begin
(

let _57_1160 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_57_1160) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, body, g))
end))
end))))
end))
end
| _57_1163 -> begin
if (not (norm)) then begin
(let _148_433 = (unfold_whnf env t)
in (as_function_typ true _148_433))
end else begin
(

let _57_1173 = (expected_function_typ env None body)
in (match (_57_1173) with
| (_57_1165, bs, _57_1168, c_opt, envbody, body, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, body, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let _57_1177 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1177) with
| (env, topt) -> begin
(

let _57_1181 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
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

let _57_1190 = (expected_function_typ env topt body)
in (match (_57_1190) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let _57_1196 = (tc_term (

let _57_1191 = envbody
in {FStar_TypeChecker_Env.solver = _57_1191.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1191.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1191.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1191.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1191.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1191.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1191.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1191.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1191.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1191.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1191.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1191.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1191.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1191.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1191.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1191.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1191.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1191.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1191.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_57_1196) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _57_1198 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _148_437 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _148_436 = (let _148_435 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _148_435))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _148_437 _148_436)))
end else begin
()
end
in (

let _57_1205 = (let _148_439 = (let _148_438 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _148_438))
in (check_expected_effect (

let _57_1200 = envbody
in {FStar_TypeChecker_Env.solver = _57_1200.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1200.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1200.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1200.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1200.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1200.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1200.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1200.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1200.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1200.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1200.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1200.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1200.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1200.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1200.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1200.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1200.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1200.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1200.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1200.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _148_439))
in (match (_57_1205) with
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

let _57_1228 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_1217) -> begin
(e, t, guard)
end
| _57_1220 -> begin
(

let _57_1223 = if use_teq then begin
(let _148_444 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _148_444))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_57_1223) with
| (e, guard') -> begin
(let _148_445 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _148_445))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_57_1228) with
| (e, tfun, guard) -> begin
(

let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (

let _57_1232 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_57_1232) with
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

let _57_1242 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_454 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _148_453 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _148_454 _148_453)))
end else begin
()
end
in (

let monadic_application = (fun _57_1249 subst arg_comps_rev arg_rets guard fvs bs -> (match (_57_1249) with
| (head, chead, ghead, cres) -> begin
(

let _57_1256 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let _57_1284 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun _57_6 -> (match (_57_6) with
| (_57_1263, _57_1265, None) -> begin
false
end
| (_57_1269, _57_1271, Some (c)) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _148_470 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _148_470 cres))
end else begin
(

let _57_1276 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
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
| _57_1280 -> begin
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
in (match (_57_1284) with
| (cres, guard) -> begin
(

let _57_1285 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_480 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _148_480))
end else begin
()
end
in (

let _57_1303 = (FStar_List.fold_left (fun _57_1289 _57_1295 -> (match ((_57_1289, _57_1295)) with
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
in (match (_57_1303) with
| (args, comp) -> begin
(

let comp = (FStar_TypeChecker_Util.bind head.FStar_Syntax_Syntax.pos env None chead (None, comp))
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app = (FStar_TypeChecker_Util.maybe_monadic env app comp.FStar_Syntax_Syntax.eff_name)
in (

let _57_1309 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (_57_1309) with
| (comp, g) -> begin
(app, comp, g)
end)))))
end)))
end)))
end))
in (

let rec tc_args = (fun head_info _57_1317 bs args -> (match (_57_1317) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match ((bs, args)) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (_57_1323))))::rest, ((_57_1331, None))::_57_1329) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _57_1337 = (check_no_escape (Some (head)) env fvs t)
in (

let _57_1343 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_57_1343) with
| (varg, _57_1341, implicits) -> begin
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

let _57_1375 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _57_1374 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let _57_1378 = x
in {FStar_Syntax_Syntax.ppname = _57_1378.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1378.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (

let _57_1381 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_495 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _148_495))
end else begin
()
end
in (

let _57_1383 = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let _57_1386 = env
in {FStar_TypeChecker_Env.solver = _57_1386.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1386.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1386.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1386.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1386.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1386.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1386.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1386.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1386.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1386.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1386.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1386.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1386.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1386.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1386.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _57_1386.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1386.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1386.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1386.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1386.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_1389 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_498 = (FStar_Syntax_Print.tag_of_term e)
in (let _148_497 = (FStar_Syntax_Print.term_to_string e)
in (let _148_496 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _148_498 _148_497 _148_496))))
end else begin
()
end
in (

let _57_1394 = (tc_term env e)
in (match (_57_1394) with
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
| (_57_1402, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::_57_1407) -> begin
(

let _57_1414 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (_57_1414) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _148_511 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _148_511 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let _57_1425 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (_57_1425) with
| (bs, cres') -> begin
(

let head_info = (head, chead, ghead, (FStar_Syntax_Util.lcomp_of_comp cres'))
in (

let _57_1427 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_512 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _148_512))
end else begin
()
end
in (tc_args head_info ([], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs args)))
end))
end
| _57_1430 when (not (norm)) -> begin
(let _148_513 = (unfold_whnf env tres)
in (aux true _148_513))
end
| _57_1432 -> begin
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

let _57_1465 = (tc_term env e)
in (match (_57_1465) with
| (e, c, g_e) -> begin
(

let _57_1469 = (tc_args env tl)
in (match (_57_1469) with
| (args, comps, g_rest) -> begin
(let _148_529 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, ((e.FStar_Syntax_Syntax.pos, c))::comps, _148_529))
end))
end))
end))
in (

let _57_1473 = (tc_args env args)
in (match (_57_1473) with
| (args, comps, g_args) -> begin
(

let bs = (let _148_531 = (FStar_All.pipe_right comps (FStar_List.map (fun _57_1477 -> (match (_57_1477) with
| (_57_1475, c) -> begin
(c.FStar_Syntax_Syntax.res_typ, None)
end))))
in (FStar_Syntax_Util.null_binders_of_tks _148_531))
in (

let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _57_1483 -> begin
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
| FStar_Syntax_Syntax.Tm_type (_57_1489) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _57_1494 -> begin
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

let _57_1498 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _148_554 = (FStar_Syntax_Print.term_to_string head)
in (let _148_553 = (FStar_Syntax_Print.term_to_string tf)
in (let _148_552 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _148_554 _148_553 _148_552))))
end else begin
()
end
in (

let _57_1500 = (let _148_555 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _148_555))
in (

let comp = (let _148_558 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _57_1504 out -> (match (_57_1504) with
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

let _57_1513 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_1513) with
| (bs, c) -> begin
(

let head_info = (head, chead, ghead, (FStar_Syntax_Util.lcomp_of_comp c))
in (tc_args head_info ([], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs args))
end))
end
| _57_1516 -> begin
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

let _57_1552 = (FStar_List.fold_left2 (fun _57_1533 _57_1536 _57_1539 -> (match ((_57_1533, _57_1536, _57_1539)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(

let _57_1540 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let _57_1545 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_57_1545) with
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
in (match (_57_1552) with
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

let _57_1557 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_57_1557) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _57_1559 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let _57_1566 = (FStar_Syntax_Subst.open_branch branch)
in (match (_57_1566) with
| (pattern, when_clause, branch_exp) -> begin
(

let _57_1571 = branch
in (match (_57_1571) with
| (cpat, _57_1569, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _57_1579 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_57_1579) with
| (pat_bvs, exps, p) -> begin
(

let _57_1580 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_593 = (FStar_Syntax_Print.pat_to_string p0)
in (let _148_592 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _148_593 _148_592)))
end else begin
()
end
in (

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let _57_1586 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_57_1586) with
| (env1, _57_1585) -> begin
(

let env1 = (

let _57_1587 = env1
in {FStar_TypeChecker_Env.solver = _57_1587.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1587.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1587.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1587.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1587.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1587.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1587.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1587.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _57_1587.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1587.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1587.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1587.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1587.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1587.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1587.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1587.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1587.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1587.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1587.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1587.FStar_TypeChecker_Env.use_bv_sorts})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _57_1626 = (let _148_616 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _57_1592 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_596 = (FStar_Syntax_Print.term_to_string e)
in (let _148_595 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _148_596 _148_595)))
end else begin
()
end
in (

let _57_1597 = (tc_term env1 e)
in (match (_57_1597) with
| (e, lc, g) -> begin
(

let _57_1598 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
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

let _57_1604 = (let _148_599 = (FStar_TypeChecker_Rel.discharge_guard env (

let _57_1602 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_1602.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_1602.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_1602.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _148_599 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _148_604 = (let _148_603 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _148_603 (FStar_List.map (fun _57_1612 -> (match (_57_1612) with
| (u, _57_1611) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _148_604 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _57_1620 = if (let _148_605 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _148_605)) then begin
(

let unresolved = (let _148_606 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _148_606 FStar_Util.set_elements))
in (let _148_614 = (let _148_613 = (let _148_612 = (let _148_611 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _148_610 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _148_609 = (let _148_608 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _57_1619 -> (match (_57_1619) with
| (u, _57_1618) -> begin
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

let _57_1622 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_615 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _148_615))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _148_616 FStar_List.unzip))
in (match (_57_1626) with
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

let _57_1633 = (let _148_617 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _148_617 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_57_1633) with
| (scrutinee_env, _57_1632) -> begin
(

let _57_1639 = (tc_pat true pat_t pattern)
in (match (_57_1639) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let _57_1649 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(

let _57_1646 = (let _148_618 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _148_618 e))
in (match (_57_1646) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_57_1649) with
| (when_clause, g_when) -> begin
(

let _57_1653 = (tc_term pat_env branch_exp)
in (match (_57_1653) with
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

let _57_1709 = (

let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _57_1671 -> begin
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

let _57_1679 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_57_1679) with
| (c, g_branch) -> begin
(

let _57_1704 = (match ((eqs, when_condition)) with
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
in (match (_57_1704) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _148_634 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _148_633 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_148_634, _148_633, g_branch))))
end))
end)))
in (match (_57_1709) with
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

let fail = (fun _57_1719 -> (match (()) with
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
| FStar_Syntax_Syntax.Tm_uinst (t, _57_1726) -> begin
(head_constructor t)
end
| _57_1730 -> begin
(fail ())
end))
in (

let pat_exp = (let _148_657 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _148_657 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_57_1755) -> begin
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

let sub_term_guards = (let _148_670 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _57_1773 -> (match (_57_1773) with
| (ei, _57_1772) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _57_1777 -> begin
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
| _57_1781 -> begin
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

let _57_1789 = (FStar_Syntax_Util.type_u ())
in (match (_57_1789) with
| (k, _57_1788) -> begin
(

let _57_1795 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_57_1795) with
| (t, _57_1792, _57_1794) -> begin
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

let _57_1803 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
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

let _57_1820 = (check_let_bound_def true env lb)
in (match (_57_1820) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let _57_1832 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(

let g1 = (let _148_682 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _148_682 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _57_1827 = (let _148_686 = (let _148_685 = (let _148_684 = (let _148_683 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _148_683))
in (_148_684)::[])
in (FStar_TypeChecker_Util.generalize env _148_685))
in (FStar_List.hd _148_686))
in (match (_57_1827) with
| (_57_1823, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_57_1832) with
| (g1, e1, univ_vars, c1) -> begin
(

let _57_1842 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(

let _57_1835 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_57_1835) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(

let _57_1836 = if (FStar_Options.warn_top_level_effects ()) then begin
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

let _57_1838 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _148_689 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _148_689)))
end
in (match (_57_1842) with
| (e2, c1) -> begin
(

let cres = (let _148_690 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_690))
in (

let _57_1844 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _148_691 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_148_691, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _57_1848 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let _57_1859 = env
in {FStar_TypeChecker_Env.solver = _57_1859.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1859.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1859.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1859.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1859.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1859.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1859.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1859.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1859.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1859.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1859.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1859.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1859.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1859.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1859.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1859.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1859.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1859.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1859.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1859.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_1868 = (let _148_695 = (let _148_694 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _148_694 Prims.fst))
in (check_let_bound_def false _148_695 lb))
in (match (_57_1868) with
| (e1, _57_1864, c1, g1, annotated) -> begin
(

let x = (

let _57_1869 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1869.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1869.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let _57_1875 = (let _148_697 = (let _148_696 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_696)::[])
in (FStar_Syntax_Subst.open_term _148_697 e2))
in (match (_57_1875) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _57_1881 = (let _148_698 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _148_698 e2))
in (match (_57_1881) with
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

let _57_1890 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end))))))))
end))))
end))))
end)))
end
| _57_1893 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _57_1905 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1905) with
| (lbs, e2) -> begin
(

let _57_1908 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1908) with
| (env0, topt) -> begin
(

let _57_1911 = (build_let_rec_env true env0 lbs)
in (match (_57_1911) with
| (lbs, rec_env) -> begin
(

let _57_1914 = (check_let_recs rec_env lbs)
in (match (_57_1914) with
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
in (FStar_All.pipe_right ecs (FStar_List.map (fun _57_1925 -> (match (_57_1925) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _148_719 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_719))
in (

let _57_1928 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _57_1932 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1932) with
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
| _57_1934 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _57_1946 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1946) with
| (lbs, e2) -> begin
(

let _57_1949 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1949) with
| (env0, topt) -> begin
(

let _57_1952 = (build_let_rec_env false env0 lbs)
in (match (_57_1952) with
| (lbs, rec_env) -> begin
(

let _57_1955 = (check_let_recs rec_env lbs)
in (match (_57_1955) with
| (lbs, g_lbs) -> begin
(

let _57_1967 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let _57_1958 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1958.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1958.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let _57_1961 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _57_1961.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1961.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1961.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _57_1961.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], lb.FStar_Syntax_Syntax.lbtyp))
in (env, lb))))) env))
in (match (_57_1967) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let _57_1973 = (tc_term env e2)
in (match (_57_1973) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _57_1977 = cres
in {FStar_Syntax_Syntax.eff_name = _57_1977.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _57_1977.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_1977.FStar_Syntax_Syntax.comp})
in (

let _57_1982 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1982) with
| (lbs, e2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_57_1985) -> begin
(e, cres, guard)
end
| None -> begin
(

let _57_1988 = (check_no_escape None env bvs tres)
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
| _57_1991 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let _57_2024 = (FStar_List.fold_left (fun _57_1998 lb -> (match (_57_1998) with
| (lbs, env) -> begin
(

let _57_2003 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_57_2003) with
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

let _57_2012 = (let _148_733 = (let _148_732 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _148_732))
in (tc_check_tot_or_gtot_term (

let _57_2006 = env0
in {FStar_TypeChecker_Env.solver = _57_2006.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2006.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2006.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2006.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2006.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2006.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2006.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2006.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2006.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2006.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2006.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2006.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2006.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2006.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _57_2006.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2006.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2006.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2006.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2006.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2006.FStar_TypeChecker_Env.use_bv_sorts}) t _148_733))
in (match (_57_2012) with
| (t, _57_2010, g) -> begin
(

let _57_2013 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (

let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(

let _57_2016 = env
in {FStar_TypeChecker_Env.solver = _57_2016.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2016.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2016.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2016.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2016.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2016.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2016.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2016.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2016.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2016.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2016.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2016.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2016.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_2016.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2016.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2016.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2016.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2016.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2016.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2016.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (

let lb = (

let _57_2019 = lb
in {FStar_Syntax_Syntax.lbname = _57_2019.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _57_2019.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_57_2024) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _57_2037 = (let _148_738 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _57_2031 = (let _148_737 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _148_737 lb.FStar_Syntax_Syntax.lbdef))
in (match (_57_2031) with
| (e, c, g) -> begin
(

let _57_2032 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _148_738 FStar_List.unzip))
in (match (_57_2037) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _57_2045 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_2045) with
| (env1, _57_2044) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _57_2051 = (check_lbtyp top_level env lb)
in (match (_57_2051) with
| (topt, wf_annot, univ_vars, env1) -> begin
(

let _57_2052 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let _57_2059 = (tc_maybe_toplevel_term (

let _57_2054 = env1
in {FStar_TypeChecker_Env.solver = _57_2054.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2054.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2054.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2054.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2054.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2054.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2054.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2054.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2054.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2054.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2054.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2054.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2054.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _57_2054.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2054.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2054.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2054.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2054.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2054.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2054.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_57_2059) with
| (e1, c1, g1) -> begin
(

let _57_2063 = (let _148_745 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_2060 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _148_745 e1 c1 wf_annot))
in (match (_57_2063) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _57_2065 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
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

let _57_2072 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _57_2075 -> begin
(

let _57_2078 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_57_2078) with
| (univ_vars, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _148_751 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _148_751))
end else begin
(

let _57_2083 = (FStar_Syntax_Util.type_u ())
in (match (_57_2083) with
| (k, _57_2082) -> begin
(

let _57_2088 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_57_2088) with
| (t, _57_2086, g) -> begin
(

let _57_2089 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
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
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _57_2095 -> (match (_57_2095) with
| (x, imp) -> begin
(

let _57_2098 = (FStar_Syntax_Util.type_u ())
in (match (_57_2098) with
| (tu, u) -> begin
(

let _57_2103 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_57_2103) with
| (t, _57_2101, g) -> begin
(

let x = ((

let _57_2104 = x
in {FStar_Syntax_Syntax.ppname = _57_2104.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2104.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (

let _57_2107 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
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

let _57_2122 = (tc_binder env b)
in (match (_57_2122) with
| (b, env', g, u) -> begin
(

let _57_2127 = (aux env' bs)
in (match (_57_2127) with
| (bs, env', g', us) -> begin
(let _148_768 = (let _148_767 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _148_767))
in ((b)::bs, env', _148_768, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun _57_2135 _57_2138 -> (match ((_57_2135, _57_2138)) with
| ((t, imp), (args, g)) -> begin
(

let _57_2143 = (tc_term env t)
in (match (_57_2143) with
| (t, _57_2141, g') -> begin
(let _148_777 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _148_777))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _57_2147 -> (match (_57_2147) with
| (pats, g) -> begin
(

let _57_2150 = (tc_args env p)
in (match (_57_2150) with
| (args, g') -> begin
(let _148_780 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _148_780))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _57_2156 = (tc_maybe_toplevel_term env e)
in (match (_57_2156) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let _57_2159 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_783 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _148_783))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _57_2164 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _148_784 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_148_784, false))
end else begin
(let _148_785 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_148_785, true))
end
in (match (_57_2164) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _148_786 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _148_786))
end
| _57_2168 -> begin
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

let _57_2178 = (tc_tot_or_gtot_term env t)
in (match (_57_2178) with
| (t, c, g) -> begin
(

let _57_2179 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let _57_2187 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_2187) with
| (t, c, g) -> begin
(

let _57_2188 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _148_812 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _148_812)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _148_816 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _148_816))))


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let _57_2203 = (tc_binders env tps)
in (match (_57_2203) with
| (tps, env, g, us) -> begin
(

let _57_2204 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (

let fail = (fun _57_2210 -> (match (()) with
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
| ((a, _57_2223))::((wp, _57_2219))::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2227 -> begin
(fail ())
end))
end
| _57_2229 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let _57_2236 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_57_2236) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _57_2238 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let _57_2242 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_57_2242) with
| (uvs, t') -> begin
(match ((let _148_838 = (FStar_Syntax_Subst.compress t')
in _148_838.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _57_2248 -> begin
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
| ((a, _57_2265))::((wp, _57_2261))::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2269 -> begin
(fail signature)
end))
end
| _57_2271 -> begin
(fail signature)
end)))


let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (

let _57_2276 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_57_2276) with
| (a, wp) -> begin
(

let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _57_2279 -> begin
(

let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (

let op = (fun ts -> (

let _57_2283 = ()
in (

let t0 = (Prims.snd ts)
in (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (

let _57_2287 = ed
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
in {FStar_Syntax_Syntax.qualifiers = _57_2287.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2287.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2287.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2287.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2287.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _148_866; FStar_Syntax_Syntax.bind_wp = _148_865; FStar_Syntax_Syntax.if_then_else = _148_864; FStar_Syntax_Syntax.ite_wp = _148_863; FStar_Syntax_Syntax.stronger = _148_862; FStar_Syntax_Syntax.close_wp = _148_861; FStar_Syntax_Syntax.assert_p = _148_860; FStar_Syntax_Syntax.assume_p = _148_859; FStar_Syntax_Syntax.null_wp = _148_858; FStar_Syntax_Syntax.trivial = _148_857})))))))))))))
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
| _57_2322 -> begin
tm.FStar_Syntax_Syntax.n
end)
in (

let _57_2324 = tm
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2324.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2324.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2324.FStar_Syntax_Syntax.vars})))
and visit_binder = (fun _57_2328 -> (match (_57_2328) with
| (bv, a) -> begin
(let _148_892 = (

let _57_2329 = bv
in (let _148_890 = (visit_term bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_2329.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2329.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_890}))
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

let _57_2343 = comp
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2343.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2343.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2343.FStar_Syntax_Syntax.vars})))
and visit_args = (fun args -> (FStar_List.map (fun _57_2348 -> (match (_57_2348) with
| (tm, q) -> begin
(let _148_903 = (visit_term tm)
in (_148_903, q))
end)) args))
in (visit_term tm))))
in (

let check = (fun str t -> if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _57_2352 = (let _148_908 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Generated term for %s: %s\n" str _148_908))
in (

let t = (normalize t)
in (

let t = (FStar_Syntax_Subst.compress t)
in (

let _57_2367 = (tc_term env t)
in (match (_57_2367) with
| (e, {FStar_Syntax_Syntax.eff_name = _57_2363; FStar_Syntax_Syntax.res_typ = res_typ; FStar_Syntax_Syntax.cflags = _57_2360; FStar_Syntax_Syntax.comp = _57_2358}, _57_2366) -> begin
(

let _57_2368 = (let _148_911 = (let _148_910 = (normalize res_typ)
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
| _57_2379 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _148_917 = (collect_binders rest)
in (FStar_List.append bs _148_917)))
end
| FStar_Syntax_Syntax.Tm_type (_57_2382) -> begin
[]
end
| _57_2385 -> begin
(FStar_All.failwith "wp_a doesn\'t end in Type0")
end))
in (

let _57_2400 = (

let i = (FStar_ST.alloc 0)
in (

let wp_binders = (let _148_924 = (normalize wp_a)
in (collect_binders _148_924))
in ((fun t -> (let _148_930 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow wp_binders _148_930))), (fun t -> (let _148_933 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow wp_binders _148_933))), (fun _57_2390 -> (match (()) with
| () -> begin
(FStar_List.map (fun _57_2394 -> (match (_57_2394) with
| (bv, _57_2393) -> begin
(

let _57_2395 = (let _148_937 = ((FStar_ST.read i) + 1)
in (FStar_ST.op_Colon_Equals i _148_937))
in (let _148_940 = (let _148_939 = (let _148_938 = (FStar_ST.read i)
in (FStar_Util.string_of_int _148_938))
in (Prims.strcat "g" _148_939))
in (FStar_Syntax_Syntax.gen_bv _148_940 None bv.FStar_Syntax_Syntax.sort)))
end)) wp_binders)
end)))))
in (match (_57_2400) with
| (mk_ctx, mk_gctx, mk_gamma) -> begin
(

let binders_of_list = (FStar_List.map (fun _57_2403 -> (match (_57_2403) with
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

let _57_2415 = (let _148_965 = (let _148_964 = (let _148_963 = (let _148_962 = (FStar_Syntax_Syntax.mk_binder a)
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

let _57_2427 = (let _148_992 = (let _148_991 = (let _148_990 = (let _148_989 = (FStar_Syntax_Syntax.mk_binder a)
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

let _57_2437 = (let _148_1021 = (let _148_1020 = (let _148_1019 = (let _148_1018 = (FStar_Syntax_Syntax.mk_binder a)
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

let _57_2448 = (let _148_1062 = (let _148_1061 = (let _148_1060 = (let _148_1059 = (FStar_Syntax_Syntax.mk_binder a)
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

let _57_2459 = (let _148_1094 = (let _148_1093 = (let _148_1092 = (let _148_1091 = (FStar_Syntax_Syntax.mk_binder a)
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

let _57_2466 = (let _148_1109 = (FStar_Syntax_Util.abs binders wp_if_then_else None)
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

let _57_2474 = (let _148_1125 = (FStar_Syntax_Util.abs binders wp_assert None)
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

let _57_2482 = (let _148_1141 = (FStar_Syntax_Util.abs binders wp_assume None)
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

let _57_2491 = (let _148_1163 = (FStar_Syntax_Util.abs binders wp_close None)
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
| FStar_Syntax_Syntax.Tm_type (_57_2503) -> begin
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

let _57_2539 = t
in (let _148_1205 = (let _148_1204 = (let _148_1203 = (let _148_1202 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _148_1202))
in ((binder)::[], _148_1203))
in FStar_Syntax_Syntax.Tm_arrow (_148_1204))
in {FStar_Syntax_Syntax.n = _148_1205; FStar_Syntax_Syntax.tk = _57_2539.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2539.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2539.FStar_Syntax_Syntax.vars}))
in (mk_leq t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_57_2543) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _57_2546 -> begin
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

let _57_2551 = (let _148_1212 = (let _148_1211 = (let _148_1210 = (let _148_1209 = (FStar_Syntax_Syntax.mk_binder a)
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

let _57_2558 = (let _148_1222 = (FStar_Syntax_Util.abs binders wp_trivial None)
in (check "wp_trivial" _148_1222))
in (

let _57_2560 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2560.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2560.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2560.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2560.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2560.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _57_2560.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2560.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = ([], wp_if_then_else); FStar_Syntax_Syntax.ite_wp = _57_2560.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _57_2560.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = ([], wp_close); FStar_Syntax_Syntax.assert_p = ([], wp_assert); FStar_Syntax_Syntax.assume_p = ([], wp_assume); FStar_Syntax_Syntax.null_wp = _57_2560.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = ([], wp_trivial)}))))))))))))))))))))))))))))))))))))))
end))))))))


let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  effect_cost  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed is_for_free -> (

let _57_2565 = ()
in (

let _57_2569 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_57_2569) with
| (binders_un, signature_un) -> begin
(

let _57_2574 = (tc_tparams env0 binders_un)
in (match (_57_2574) with
| (binders, env, _57_2573) -> begin
(

let _57_2578 = (tc_trivial_guard env signature_un)
in (match (_57_2578) with
| (signature, _57_2577) -> begin
(

let ed = (

let _57_2579 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2579.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2579.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2579.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _57_2579.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2579.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _57_2579.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _57_2579.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _57_2579.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _57_2579.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _57_2579.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _57_2579.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _57_2579.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _57_2579.FStar_Syntax_Syntax.trivial})
in (

let _57_2585 = (open_effect_decl env ed)
in (match (_57_2585) with
| (ed, a, wp_a) -> begin
(

let get_effect_signature = (fun _57_2587 -> (match (()) with
| () -> begin
(

let _57_2591 = (tc_trivial_guard env signature_un)
in (match (_57_2591) with
| (signature, _57_2590) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (

let env = (let _148_1231 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _148_1231))
in (

let _57_2593 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _148_1234 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _148_1233 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _148_1232 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checking effect signature: %s %s : %s\n" _148_1234 _148_1233 _148_1232))))
end else begin
()
end
in (

let check_and_gen' = (fun env _57_2600 k -> (match (_57_2600) with
| (_57_2598, t) -> begin
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

let _57_2609 = (get_effect_signature ())
in (match (_57_2609) with
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

let _57_2621 = (FStar_Syntax_Util.type_u ())
in (match (_57_2621) with
| (t, _57_2620) -> begin
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

let _57_2637 = (FStar_Syntax_Util.type_u ())
in (match (_57_2637) with
| (t, _57_2636) -> begin
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

let _57_2643 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_57_2643) with
| (univs, t) -> begin
(

let _57_2659 = (match ((let _148_1326 = (let _148_1325 = (FStar_Syntax_Subst.compress t)
in _148_1325.FStar_Syntax_Syntax.n)
in (binders, _148_1326))) with
| ([], _57_2646) -> begin
([], t)
end
| (_57_2649, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _57_2656 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_2659) with
| (binders, signature) -> begin
(

let close = (fun n ts -> (

let ts = (let _148_1331 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _148_1331))
in (

let _57_2664 = ()
in ts)))
in (

let ed = (

let _57_2666 = ed
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
in {FStar_Syntax_Syntax.qualifiers = _57_2666.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2666.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _148_1341; FStar_Syntax_Syntax.bind_wp = _148_1340; FStar_Syntax_Syntax.if_then_else = _148_1339; FStar_Syntax_Syntax.ite_wp = _148_1338; FStar_Syntax_Syntax.stronger = _148_1337; FStar_Syntax_Syntax.close_wp = _148_1336; FStar_Syntax_Syntax.assert_p = _148_1335; FStar_Syntax_Syntax.assume_p = _148_1334; FStar_Syntax_Syntax.null_wp = _148_1333; FStar_Syntax_Syntax.trivial = _148_1332})))))))))))
in (

let _57_2669 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
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

let _57_2675 = ()
in (

let _57_2683 = ()
in (match (ses) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _57_2712, _57_2714, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _57_2703, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _57_2692, r2))::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
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
| _57_2738 -> begin
(let _148_1366 = (let _148_1365 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _148_1365))
in (FStar_All.failwith _148_1366))
end))))


let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _148_1380 = (let _148_1379 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _148_1379))
in (FStar_TypeChecker_Errors.diag r _148_1380)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let _57_2760 = ()
in (

let _57_2762 = (warn_positivity tc r)
in (

let _57_2766 = (FStar_Syntax_Subst.open_term tps k)
in (match (_57_2766) with
| (tps, k) -> begin
(

let _57_2771 = (tc_binders env tps)
in (match (_57_2771) with
| (tps, env_tps, guard_params, us) -> begin
(

let _57_2774 = (FStar_Syntax_Util.arrow_formals k)
in (match (_57_2774) with
| (indices, t) -> begin
(

let _57_2779 = (tc_binders env_tps indices)
in (match (_57_2779) with
| (indices, env', guard_indices, us') -> begin
(

let _57_2787 = (

let _57_2784 = (tc_tot_or_gtot_term env' t)
in (match (_57_2784) with
| (t, _57_2782, g) -> begin
(let _148_1387 = (let _148_1386 = (let _148_1385 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params _148_1385))
in (FStar_TypeChecker_Rel.discharge_guard env' _148_1386))
in (t, _148_1387))
end))
in (match (_57_2787) with
| (t, guard) -> begin
(

let k = (let _148_1388 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _148_1388))
in (

let _57_2791 = (FStar_Syntax_Util.type_u ())
in (match (_57_2791) with
| (t_type, u) -> begin
(

let _57_2792 = (let _148_1389 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _148_1389))
in (

let t_tc = (let _148_1390 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _148_1390))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _148_1391 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) ([], t_tc))
in (_148_1391, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u, guard)))))))
end)))
end))
end))
end))
end))
end))))
end
| _57_2799 -> begin
(FStar_All.failwith "impossible")
end))
in (

let positive_if_pure = (fun _57_2801 l -> ())
in (

let tc_data = (fun env tcs _57_7 -> (match (_57_7) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let _57_2818 = ()
in (

let _57_2853 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _57_2822 -> (match (_57_2822) with
| (se, u_tc) -> begin
if (let _148_1404 = (let _148_1403 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _148_1403))
in (FStar_Ident.lid_equals tc_lid _148_1404)) then begin
(

let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2824, _57_2826, tps, _57_2829, _57_2831, _57_2833, _57_2835, _57_2837) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _57_2843 -> (match (_57_2843) with
| (x, _57_2842) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _57_2845 -> begin
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
in (match (_57_2853) with
| (tps, u_tc) -> begin
(

let _57_2873 = (match ((let _148_1406 = (FStar_Syntax_Subst.compress t)
in _148_1406.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _57_2861 = (FStar_Util.first_N ntps bs)
in (match (_57_2861) with
| (_57_2859, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _57_2867 -> (match (_57_2867) with
| (x, _57_2866) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _148_1409 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _148_1409))))
end))
end
| _57_2870 -> begin
([], t)
end)
in (match (_57_2873) with
| (arguments, result) -> begin
(

let _57_2874 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1412 = (FStar_Syntax_Print.lid_to_string c)
in (let _148_1411 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _148_1410 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _148_1412 _148_1411 _148_1410))))
end else begin
()
end
in (

let _57_2879 = (tc_tparams env arguments)
in (match (_57_2879) with
| (arguments, env', us) -> begin
(

let _57_2883 = (tc_trivial_guard env' result)
in (match (_57_2883) with
| (result, _57_2882) -> begin
(

let _57_2887 = (FStar_Syntax_Util.head_and_args result)
in (match (_57_2887) with
| (head, _57_2886) -> begin
(

let _57_2892 = (match ((let _148_1413 = (FStar_Syntax_Subst.compress head)
in _148_1413.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _57_2891 -> begin
(let _148_1418 = (let _148_1417 = (let _148_1416 = (let _148_1415 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _148_1414 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _148_1415 _148_1414)))
in (_148_1416, r))
in FStar_Syntax_Syntax.Error (_148_1417))
in (Prims.raise _148_1418))
end)
in (

let g = (FStar_List.fold_left2 (fun g _57_2898 u_x -> (match (_57_2898) with
| (x, _57_2897) -> begin
(

let _57_2900 = ()
in (let _148_1422 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _148_1422)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _148_1426 = (let _148_1424 = (FStar_All.pipe_right tps (FStar_List.map (fun _57_2906 -> (match (_57_2906) with
| (x, _57_2905) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _148_1424 arguments))
in (let _148_1425 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _148_1426 _148_1425)))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _57_2909 -> begin
(FStar_All.failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let _57_2915 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_8 -> (match (_57_8) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2919, _57_2921, tps, k, _57_2925, _57_2927, _57_2929, _57_2931) -> begin
(let _148_1437 = (let _148_1436 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _148_1436))
in (FStar_Syntax_Syntax.null_binder _148_1437))
end
| _57_2935 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _57_9 -> (match (_57_9) with
| FStar_Syntax_Syntax.Sig_datacon (_57_2939, _57_2941, t, _57_2944, _57_2946, _57_2948, _57_2950, _57_2952) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _57_2956 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let t = (let _148_1439 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _148_1439))
in (

let _57_2959 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1440 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _148_1440))
end else begin
()
end
in (

let _57_2963 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_57_2963) with
| (uvs, t) -> begin
(

let _57_2965 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1444 = (let _148_1442 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _148_1442 (FStar_String.concat ", ")))
in (let _148_1443 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _148_1444 _148_1443)))
end else begin
()
end
in (

let _57_2969 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_57_2969) with
| (uvs, t) -> begin
(

let _57_2973 = (FStar_Syntax_Util.arrow_formals t)
in (match (_57_2973) with
| (args, _57_2972) -> begin
(

let _57_2976 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_57_2976) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _57_2980 se -> (match (_57_2980) with
| (x, _57_2979) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_2984, tps, _57_2987, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let _57_3010 = (match ((let _148_1447 = (FStar_Syntax_Subst.compress ty)
in _148_1447.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _57_3001 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_57_3001) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _57_3004 -> begin
(let _148_1448 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _148_1448 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _57_3007 -> begin
([], ty)
end)
in (match (_57_3010) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _57_3012 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| _57_3016 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _148_1449 -> FStar_Syntax_Syntax.U_name (_148_1449))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_10 -> (match (_57_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3021, _57_3023, _57_3025, _57_3027, _57_3029, _57_3031, _57_3033) -> begin
(tc, uvs_universes)
end
| _57_3037 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _57_3042 d -> (match (_57_3042) with
| (t, _57_3041) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _57_3046, _57_3048, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _148_1453 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _148_1453 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _57_3058 -> begin
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

let _57_3068 = (FStar_All.pipe_right ses (FStar_List.partition (fun _57_11 -> (match (_57_11) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_3062) -> begin
true
end
| _57_3065 -> begin
false
end))))
in (match (_57_3068) with
| (tys, datas) -> begin
(

let _57_3075 = if (FStar_All.pipe_right datas (FStar_Util.for_some (fun _57_12 -> (match (_57_12) with
| FStar_Syntax_Syntax.Sig_datacon (_57_3071) -> begin
false
end
| _57_3074 -> begin
true
end)))) then begin
(let _148_1458 = (let _148_1457 = (let _148_1456 = (FStar_TypeChecker_Env.get_range env)
in ("Mutually defined type contains a non-inductive element", _148_1456))
in FStar_Syntax_Syntax.Error (_148_1457))
in (Prims.raise _148_1458))
end else begin
()
end
in (

let env0 = env
in (

let _57_3094 = (FStar_List.fold_right (fun tc _57_3082 -> (match (_57_3082) with
| (env, all_tcs, g) -> begin
(

let _57_3087 = (tc_tycon env tc)
in (match (_57_3087) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (

let _57_3089 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1461 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _148_1461))
end else begin
()
end
in (let _148_1463 = (let _148_1462 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g _148_1462))
in (env, ((tc, tc_u))::all_tcs, _148_1463))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_3094) with
| (env, tcs, g) -> begin
(

let _57_3104 = (FStar_List.fold_right (fun se _57_3098 -> (match (_57_3098) with
| (datas, g) -> begin
(

let _57_3101 = (tc_data env tcs se)
in (match (_57_3101) with
| (data, g') -> begin
(let _148_1466 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _148_1466))
end))
end)) datas ([], g))
in (match (_57_3104) with
| (datas, g) -> begin
(

let _57_3107 = (let _148_1467 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _148_1467 datas))
in (match (_57_3107) with
| (tcs, datas) -> begin
(let _148_1469 = (let _148_1468 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _148_1468))
in FStar_Syntax_Syntax.Sig_bundle (_148_1469))
end))
end))
end))))
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
in (let _148_1474 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _148_1474))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let se = (tc_inductive env ses quals lids)
in (let _148_1475 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _148_1475))))
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

let _57_3145 = (set_options FStar_Options.Set o)
in (se, env))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(

let _57_3149 = (let _148_1480 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _148_1480 Prims.ignore))
in (

let _57_3154 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _57_3156 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
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

let _57_3178 = (let _148_1481 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _148_1481))
in (match (_57_3178) with
| (a, wp_a_src) -> begin
(

let _57_3181 = (let _148_1482 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _148_1482))
in (match (_57_3181) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _148_1486 = (let _148_1485 = (let _148_1484 = (let _148_1483 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _148_1483))
in FStar_Syntax_Syntax.NT (_148_1484))
in (_148_1485)::[])
in (FStar_Syntax_Subst.subst _148_1486 wp_b_tgt))
in (

let expected_k = (let _148_1491 = (let _148_1489 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1488 = (let _148_1487 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_148_1487)::[])
in (_148_1489)::_148_1488))
in (let _148_1490 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _148_1491 _148_1490)))
in (

let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (

let sub = (

let _57_3185 = sub
in {FStar_Syntax_Syntax.source = _57_3185.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _57_3185.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
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

let _57_3198 = ()
in (

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _57_3204 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_57_3204) with
| (tps, c) -> begin
(

let _57_3208 = (tc_tparams env tps)
in (match (_57_3208) with
| (tps, env, us) -> begin
(

let _57_3212 = (tc_comp env c)
in (match (_57_3212) with
| (c, u, g) -> begin
(

let _57_3213 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let _57_3219 = (let _148_1492 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _148_1492))
in (match (_57_3219) with
| (uvs, t) -> begin
(

let _57_3238 = (match ((let _148_1494 = (let _148_1493 = (FStar_Syntax_Subst.compress t)
in _148_1493.FStar_Syntax_Syntax.n)
in (tps, _148_1494))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_57_3222, c)) -> begin
([], c)
end
| (_57_3228, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _57_3235 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_3238) with
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

let _57_3249 = ()
in (

let _57_3253 = (let _148_1496 = (let _148_1495 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _148_1495))
in (check_and_gen env t _148_1496))
in (match (_57_3253) with
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

let _57_3266 = (FStar_Syntax_Util.type_u ())
in (match (_57_3266) with
| (k, _57_3265) -> begin
(

let phi = (let _148_1497 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _148_1497 (norm env)))
in (

let _57_3268 = (FStar_TypeChecker_Util.check_uvars r phi)
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

let _57_3281 = (tc_term env e)
in (match (_57_3281) with
| (e, c, g1) -> begin
(

let _57_3286 = (let _148_1501 = (let _148_1498 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_148_1498))
in (let _148_1500 = (let _148_1499 = (c.FStar_Syntax_Syntax.comp ())
in (e, _148_1499))
in (check_expected_effect env _148_1501 _148_1500)))
in (match (_57_3286) with
| (e, _57_3284, g) -> begin
(

let _57_3287 = (let _148_1502 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _148_1502))
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
(let _148_1514 = (let _148_1513 = (let _148_1512 = (let _148_1511 = (FStar_Syntax_Print.lid_to_string l)
in (let _148_1510 = (FStar_Syntax_Print.quals_to_string q)
in (let _148_1509 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _148_1511 _148_1510 _148_1509))))
in (_148_1512, r))
in FStar_Syntax_Syntax.Error (_148_1513))
in (Prims.raise _148_1514))
end
end))
in (

let _57_3331 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _57_3308 lb -> (match (_57_3308) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _57_3327 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (

let _57_3322 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _57_3321 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _148_1517 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _148_1517, quals_opt))))
end)
in (match (_57_3327) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_57_3331) with
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
| _57_3340 -> begin
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

let e = (let _148_1521 = (let _148_1520 = (let _148_1519 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _148_1519))
in FStar_Syntax_Syntax.Tm_let (_148_1520))
in (FStar_Syntax_Syntax.mk _148_1521 None r))
in (

let _57_3374 = (match ((tc_maybe_toplevel_term (

let _57_3344 = env
in {FStar_TypeChecker_Env.solver = _57_3344.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3344.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3344.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3344.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3344.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3344.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3344.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3344.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3344.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3344.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3344.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _57_3344.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _57_3344.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3344.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3344.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3344.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3344.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3344.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3344.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _57_3351; FStar_Syntax_Syntax.pos = _57_3349; FStar_Syntax_Syntax.vars = _57_3347}, _57_3358, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_57_3362, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _57_3368 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _57_3371 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_57_3374) with
| (se, lbs) -> begin
(

let _57_3380 = if (log env) then begin
(let _148_1529 = (let _148_1528 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _148_1525 = (let _148_1524 = (let _148_1523 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _148_1523.FStar_Syntax_Syntax.fv_name)
in _148_1524.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _148_1525))) with
| None -> begin
true
end
| _57_3378 -> begin
false
end)
in if should_log then begin
(let _148_1527 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _148_1526 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _148_1527 _148_1526)))
end else begin
""
end))))
in (FStar_All.pipe_right _148_1528 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _148_1529))
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

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _57_14 -> (match (_57_14) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _57_3390 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _57_3400 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_57_3402) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _57_3413, _57_3415) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _57_3421 -> (match (_57_3421) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _57_3427, _57_3429, quals, r) -> begin
(

let dec = (let _148_1545 = (let _148_1544 = (let _148_1543 = (let _148_1542 = (let _148_1541 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _148_1541))
in FStar_Syntax_Syntax.Tm_arrow (_148_1542))
in (FStar_Syntax_Syntax.mk _148_1543 None r))
in (l, us, _148_1544, (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_148_1545))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _57_3439, _57_3441, _57_3443, _57_3445, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _57_3451 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_57_3453, _57_3455, quals, _57_3458) -> begin
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
| _57_3477 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_57_3479) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _57_3498, _57_3500, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
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
(let _148_1552 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _148_1551 = (let _148_1550 = (let _148_1549 = (let _148_1548 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _148_1548.FStar_Syntax_Syntax.fv_name)
in _148_1549.FStar_Syntax_Syntax.v)
in (_148_1550, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_148_1551)))))
in (_148_1552, hidden))
end else begin
((se)::[], hidden)
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let _57_3539 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _57_3520 se -> (match (_57_3520) with
| (ses, exports, env, hidden) -> begin
(

let _57_3522 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1559 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _148_1559))
end else begin
()
end
in (

let _57_3526 = (tc_decl env se)
in (match (_57_3526) with
| (se, env) -> begin
(

let _57_3527 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _148_1560 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _148_1560))
end else begin
()
end
in (

let _57_3529 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (

let _57_3533 = (for_export hidden se)
in (match (_57_3533) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_57_3539) with
| (ses, exports, env, _57_3538) -> begin
(let _148_1561 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _148_1561, env))
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

let _57_3544 = env
in (let _148_1566 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _57_3544.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3544.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3544.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3544.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3544.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3544.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3544.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3544.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3544.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3544.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3544.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3544.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3544.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_3544.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_3544.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3544.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _148_1566; FStar_TypeChecker_Env.type_of = _57_3544.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3544.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3544.FStar_TypeChecker_Env.use_bv_sorts}))
in (

let _57_3547 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let _57_3553 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_57_3553) with
| (ses, exports, env) -> begin
((

let _57_3554 = modul
in {FStar_Syntax_Syntax.name = _57_3554.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _57_3554.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3554.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let _57_3562 = (tc_decls env decls)
in (match (_57_3562) with
| (ses, exports, env) -> begin
(

let modul = (

let _57_3563 = modul
in {FStar_Syntax_Syntax.name = _57_3563.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _57_3563.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3563.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul = (

let _57_3569 = modul
in {FStar_Syntax_Syntax.name = _57_3569.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _57_3569.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in (

let _57_3579 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(

let _57_3573 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let _57_3575 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (

let _57_3577 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _148_1579 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _148_1579 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let _57_3586 = (tc_partial_modul env modul)
in (match (_57_3586) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _57_3589 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _148_1588 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _148_1588))
end else begin
()
end
in (

let env = (

let _57_3591 = env
in {FStar_TypeChecker_Env.solver = _57_3591.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3591.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3591.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3591.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3591.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3591.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3591.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3591.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3591.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3591.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3591.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3591.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3591.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_3591.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3591.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3591.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3591.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3591.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3591.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3591.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_3607 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _57_3599) -> begin
(let _148_1593 = (let _148_1592 = (let _148_1591 = (FStar_TypeChecker_Env.get_range env)
in ((Prims.strcat "Implicit argument: " msg), _148_1591))
in FStar_Syntax_Syntax.Error (_148_1592))
in (Prims.raise _148_1593))
end
in (match (_57_3607) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(t, c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(let _148_1598 = (let _148_1597 = (let _148_1596 = (let _148_1594 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _148_1594))
in (let _148_1595 = (FStar_TypeChecker_Env.get_range env)
in (_148_1596, _148_1595)))
in FStar_Syntax_Syntax.Error (_148_1597))
in (Prims.raise _148_1598))
end
end)))))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

let _57_3610 = if (FStar_Options.debug_any ()) then begin
(let _148_1603 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _148_1603))
end else begin
()
end
in (

let _57_3614 = (tc_modul env m)
in (match (_57_3614) with
| (m, env) -> begin
(

let _57_3615 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _148_1604 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _148_1604))
end else begin
()
end
in (m, env))
end))))




