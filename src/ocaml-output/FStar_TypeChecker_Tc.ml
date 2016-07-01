
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
(let _148_240 = (let _148_238 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _148_238))
in (let _148_239 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _148_240 _148_239)))
end else begin
()
end
in (

let top = e
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_57_296) -> begin
(let _148_244 = (FStar_Syntax_Subst.compress e)
in (tc_term env _148_244))
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
in (let _148_246 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_pattern (pats)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _148_245 = (FStar_TypeChecker_Rel.conj_guard g g')
in (_148_246, c, _148_245))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _148_247 = (FStar_Syntax_Subst.compress e)
in _148_247.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_57_369, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _57_376; FStar_Syntax_Syntax.lbtyp = _57_374; FStar_Syntax_Syntax.lbeff = _57_372; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _57_387 = (let _148_248 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _148_248 e1))
in (match (_57_387) with
| (e1, c1, g1) -> begin
(

let _57_391 = (tc_term env e2)
in (match (_57_391) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (None, c2))
in (

let e = (let _148_253 = (let _148_252 = (let _148_251 = (let _148_250 = (let _148_249 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Common.t_unit, e1))
in (_148_249)::[])
in (false, _148_250))
in (_148_251, e2))
in FStar_Syntax_Syntax.Tm_let (_148_252))
in (FStar_Syntax_Syntax.mk _148_253 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _148_254 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _148_254)))))
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

let _57_430 = (let _148_256 = (let _148_255 = (c'.FStar_Syntax_Syntax.comp ())
in (e, _148_255))
in (check_expected_effect env (Some (expected_c)) _148_256))
in (match (_57_430) with
| (e, expected_c, g'') -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (let _148_259 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t_res), Some ((FStar_Syntax_Util.comp_effect_name expected_c))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _148_258 = (let _148_257 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _148_257))
in (_148_259, (FStar_Syntax_Util.lcomp_of_comp expected_c), _148_258))))
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

let _57_450 = (let _148_260 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _148_260 e))
in (match (_57_450) with
| (e, c, g) -> begin
(

let _57_454 = (let _148_264 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_451 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _148_264 e c f))
in (match (_57_454) with
| (c, f) -> begin
(

let _57_458 = (let _148_265 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t), Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _148_265 c))
in (match (_57_458) with
| (e, c, f2) -> begin
(let _148_267 = (let _148_266 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _148_266))
in (e, c, _148_267))
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

let _57_494 = (FStar_Syntax_Util.head_and_args top)
in (match (_57_494) with
| (unary_op, _57_493) -> begin
(

let head = (let _148_268 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (Prims.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((unary_op, (a)::[]))) None _148_268))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((head, rest))) None top.FStar_Syntax_Syntax.pos)
in (tc_term env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _57_502; FStar_Syntax_Syntax.pos = _57_500; FStar_Syntax_Syntax.vars = _57_498}, ((e, aqual))::[]) -> begin
(

let _57_512 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end else begin
()
end
in (

let _57_521 = (

let _57_517 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_517) with
| (env0, _57_516) -> begin
(tc_term env0 e)
end))
in (match (_57_521) with
| (e, c, g) -> begin
(

let _57_525 = (FStar_Syntax_Util.head_and_args top)
in (match (_57_525) with
| (reify_op, _57_524) -> begin
(

let u_c = (

let _57_531 = (tc_term env c.FStar_Syntax_Syntax.res_typ)
in (match (_57_531) with
| (_57_527, c, _57_530) -> begin
(match ((let _148_269 = (FStar_Syntax_Subst.compress c.FStar_Syntax_Syntax.res_typ)
in _148_269.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| _57_535 -> begin
(FStar_All.failwith "Unexpected result type of computation")
end)
end))
in (

let repr = (FStar_TypeChecker_Util.reify_comp env c u_c)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((reify_op, ((e, aqual))::[]))) (Some (repr.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let c = (let _148_270 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right _148_270 FStar_Syntax_Util.lcomp_of_comp))
in (

let _57_543 = (comp_check_expected_typ env e c)
in (match (_57_543) with
| (e, c, g') -> begin
(let _148_271 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, c, _148_271))
end))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.tk = _57_549; FStar_Syntax_Syntax.pos = _57_547; FStar_Syntax_Syntax.vars = _57_545}, ((e, aqual))::[]) -> begin
(

let _57_560 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end else begin
()
end
in (

let no_reflect = (fun _57_563 -> (match (()) with
| () -> begin
(let _148_276 = (let _148_275 = (let _148_274 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (_148_274, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_148_275))
in (Prims.raise _148_276))
end))
in (

let _57_567 = (FStar_Syntax_Util.head_and_args top)
in (match (_57_567) with
| (reflect_op, _57_566) -> begin
(match ((FStar_TypeChecker_Env.effect_decl_opt env l)) with
| None -> begin
(no_reflect ())
end
| Some (ed) -> begin
if (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable)))) then begin
(no_reflect ())
end else begin
(

let _57_573 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_573) with
| (env_no_ex, topt) -> begin
(

let _57_601 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env ed ([], ed.FStar_Syntax_Syntax.repr))
in (

let t = (let _148_282 = (let _148_281 = (let _148_280 = (let _148_279 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _148_278 = (let _148_277 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (_148_277)::[])
in (_148_279)::_148_278))
in (repr, _148_280))
in FStar_Syntax_Syntax.Tm_app (_148_281))
in (FStar_Syntax_Syntax.mk _148_282 None top.FStar_Syntax_Syntax.pos))
in (

let _57_581 = (let _148_284 = (let _148_283 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _148_283 Prims.fst))
in (tc_tot_or_gtot_term _148_284 t))
in (match (_57_581) with
| (t, _57_579, g) -> begin
(match ((let _148_285 = (FStar_Syntax_Subst.compress t)
in _148_285.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_57_583, ((res, _57_590))::((wp, _57_586))::[]) -> begin
(t, res, wp, g)
end
| _57_596 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))
in (match (_57_601) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let _57_615 = (

let _57_605 = (tc_tot_or_gtot_term env_no_ex e)
in (match (_57_605) with
| (e, c, g) -> begin
(

let _57_606 = if (let _148_286 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation _148_286)) then begin
(FStar_TypeChecker_Errors.add_errors env ((("Expected Tot, got a GTot computation", e.FStar_Syntax_Syntax.pos))::[]))
end else begin
()
end
in (match ((FStar_TypeChecker_Rel.try_teq env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)) with
| None -> begin
(

let _57_609 = (let _148_291 = (let _148_290 = (let _148_289 = (let _148_288 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _148_287 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" _148_288 _148_287)))
in (_148_289, e.FStar_Syntax_Syntax.pos))
in (_148_290)::[])
in (FStar_TypeChecker_Errors.add_errors env _148_291))
in (let _148_292 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (e, _148_292)))
end
| Some (g') -> begin
(let _148_294 = (let _148_293 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' _148_293))
in (e, _148_294))
end))
end))
in (match (_57_615) with
| (e, g) -> begin
(

let c = (let _148_298 = (let _148_297 = (let _148_296 = (let _148_295 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_295)::[])
in {FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = _148_296; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp _148_297))
in (FStar_All.pipe_right _148_298 FStar_Syntax_Util.lcomp_of_comp))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((reflect_op, ((e, aqual))::[]))) (Some (res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let _57_621 = (comp_check_expected_typ env e c)
in (match (_57_621) with
| (e, c, g') -> begin
(let _148_299 = (FStar_TypeChecker_Rel.conj_guard g' g)
in (e, c, _148_299))
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

let env = (let _148_301 = (let _148_300 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _148_300 Prims.fst))
in (FStar_All.pipe_right _148_301 instantiate_both))
in (

let _57_628 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_303 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _148_302 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _148_303 _148_302)))
end else begin
()
end
in (

let _57_633 = (tc_term (no_inst env) head)
in (match (_57_633) with
| (head, chead, g_head) -> begin
(

let _57_637 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _148_304 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _148_304))
end else begin
(let _148_305 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _148_305))
end
in (match (_57_637) with
| (e, c, g) -> begin
(

let _57_638 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_306 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _148_306))
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

let _57_644 = (comp_check_expected_typ env0 e c)
in (match (_57_644) with
| (e, c, g') -> begin
(

let gimp = (match ((let _148_307 = (FStar_Syntax_Subst.compress head)
in _148_307.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _57_647) -> begin
(

let imp = ("head of application is a uvar", env0, u, e, c.FStar_Syntax_Syntax.res_typ, head.FStar_Syntax_Syntax.pos)
in (

let _57_651 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_651.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_651.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_651.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _57_654 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (

let gres = (let _148_308 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _148_308))
in (

let _57_657 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_310 = (FStar_Syntax_Print.term_to_string e)
in (let _148_309 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" _148_310 _148_309)))
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

let _57_665 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_665) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let _57_670 = (tc_term env1 e1)
in (match (_57_670) with
| (e1, c1, g1) -> begin
(

let _57_681 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(

let _57_677 = (FStar_Syntax_Util.type_u ())
in (match (_57_677) with
| (k, _57_676) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _148_311 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_148_311, res_t)))
end))
end)
in (match (_57_681) with
| (env_branches, res_t) -> begin
(

let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let _57_698 = (

let _57_695 = (FStar_List.fold_right (fun _57_689 _57_692 -> (match ((_57_689, _57_692)) with
| ((_57_685, f, c, g), (caccum, gaccum)) -> begin
(let _148_314 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _148_314))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_695) with
| (cases, g) -> begin
(let _148_315 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_148_315, g))
end))
in (match (_57_698) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (Some (guard_x), c_branches))
in (

let e = (let _148_319 = (let _148_318 = (let _148_317 = (FStar_List.map (fun _57_707 -> (match (_57_707) with
| (f, _57_702, _57_704, _57_706) -> begin
f
end)) t_eqns)
in (e1, _148_317))
in FStar_Syntax_Syntax.Tm_match (_148_318))
in (FStar_Syntax_Syntax.mk _148_319 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ), Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (

let _57_710 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_322 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _148_321 = (let _148_320 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _148_320))
in (FStar_Util.print2 "(%s) comp type = %s\n" _148_322 _148_321)))
end else begin
()
end
in (let _148_323 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _148_323))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_722); FStar_Syntax_Syntax.lbunivs = _57_720; FStar_Syntax_Syntax.lbtyp = _57_718; FStar_Syntax_Syntax.lbeff = _57_716; FStar_Syntax_Syntax.lbdef = _57_714})::[]), _57_728) -> begin
(

let _57_731 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_324 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _148_324))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _57_735), _57_738) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_753); FStar_Syntax_Syntax.lbunivs = _57_751; FStar_Syntax_Syntax.lbtyp = _57_749; FStar_Syntax_Syntax.lbeff = _57_747; FStar_Syntax_Syntax.lbdef = _57_745})::_57_743), _57_759) -> begin
(

let _57_762 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_325 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _148_325))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _57_766), _57_769) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let _57_783 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_783) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _148_339 = (let _148_338 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_338))
in FStar_Util.Inr (_148_339))
end
in (

let is_data_ctor = (fun _57_4 -> (match (_57_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _57_793 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _148_345 = (let _148_344 = (let _148_343 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _148_342 = (FStar_TypeChecker_Env.get_range env)
in (_148_343, _148_342)))
in FStar_Syntax_Syntax.Error (_148_344))
in (Prims.raise _148_345))
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

let g = (match ((let _148_346 = (FStar_Syntax_Subst.compress t1)
in _148_346.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_804) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _57_807 -> begin
(

let imp = ("uvar in term", env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (

let _57_809 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_809.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_809.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_809.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _57_815 = (FStar_Syntax_Util.type_u ())
in (match (_57_815) with
| (k, u) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _57_821 = (FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
in (match (_57_821) with
| (t, _57_819, g0) -> begin
(

let _57_826 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (_57_826) with
| (e, _57_824, g1) -> begin
(let _148_347 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) _148_347))
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

let _57_830 = x
in {FStar_Syntax_Syntax.ppname = _57_830.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_830.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let _57_836 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_836) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _148_349 = (let _148_348 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_348))
in FStar_Util.Inr (_148_349))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _57_843; FStar_Syntax_Syntax.pos = _57_841; FStar_Syntax_Syntax.vars = _57_839}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let _57_853 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_853) with
| (us', t) -> begin
(

let _57_860 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _148_352 = (let _148_351 = (let _148_350 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _148_350))
in FStar_Syntax_Syntax.Error (_148_351))
in (Prims.raise _148_352))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _57_859 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (

let fv' = (

let _57_862 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _57_864 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_864.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_864.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_862.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_862.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _148_355 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _148_355 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let _57_872 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_872) with
| (us, t) -> begin
(

let fv' = (

let _57_873 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _57_875 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_875.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_875.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_873.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_873.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _148_356 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _148_356 us))
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

let _57_889 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_889) with
| (bs, c) -> begin
(

let env0 = env
in (

let _57_894 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_894) with
| (env, _57_893) -> begin
(

let _57_899 = (tc_binders env bs)
in (match (_57_899) with
| (bs, env, g, us) -> begin
(

let _57_903 = (tc_comp env c)
in (match (_57_903) with
| (c, uc, f) -> begin
(

let e = (

let _57_904 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _57_904.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_904.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_904.FStar_Syntax_Syntax.vars})
in (

let _57_907 = (check_smt_pat env e bs c)
in (

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _148_357 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _148_357))
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

let _57_923 = (let _148_359 = (let _148_358 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_358)::[])
in (FStar_Syntax_Subst.open_term _148_359 phi))
in (match (_57_923) with
| (x, phi) -> begin
(

let env0 = env
in (

let _57_928 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_928) with
| (env, _57_927) -> begin
(

let _57_933 = (let _148_360 = (FStar_List.hd x)
in (tc_binder env _148_360))
in (match (_57_933) with
| (x, env, f1, u) -> begin
(

let _57_934 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_363 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _148_362 = (FStar_Syntax_Print.term_to_string phi)
in (let _148_361 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _148_363 _148_362 _148_361))))
end else begin
()
end
in (

let _57_939 = (FStar_Syntax_Util.type_u ())
in (match (_57_939) with
| (t_phi, _57_938) -> begin
(

let _57_944 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_57_944) with
| (phi, _57_942, f2) -> begin
(

let e = (

let _57_945 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _57_945.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_945.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_945.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _148_364 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _148_364))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _57_953) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (

let _57_959 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_365 = (FStar_Syntax_Print.term_to_string (

let _57_957 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _57_957.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_957.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_957.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _148_365))
end else begin
()
end
in (

let _57_963 = (FStar_Syntax_Subst.open_term bs body)
in (match (_57_963) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _57_965 -> begin
(let _148_367 = (let _148_366 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _148_366))
in (FStar_All.failwith _148_367))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_57_970) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_57_973, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_57_978, Some (_57_980)) -> begin
(FStar_All.failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (_57_985) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_57_988) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_57_991) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_57_995) -> begin
FStar_TypeChecker_Common.t_range
end
| _57_998 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(

let _57_1005 = (FStar_Syntax_Util.type_u ())
in (match (_57_1005) with
| (k, u) -> begin
(

let _57_1010 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_1010) with
| (t, _57_1008, g) -> begin
(let _148_372 = (FStar_Syntax_Syntax.mk_Total t)
in (_148_372, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(

let _57_1015 = (FStar_Syntax_Util.type_u ())
in (match (_57_1015) with
| (k, u) -> begin
(

let _57_1020 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_1020) with
| (t, _57_1018, g) -> begin
(let _148_373 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_148_373, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (

let tc = (let _148_375 = (let _148_374 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_148_374)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _148_375 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let _57_1029 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_57_1029) with
| (tc, _57_1027, f) -> begin
(

let _57_1033 = (FStar_Syntax_Util.head_and_args tc)
in (match (_57_1033) with
| (_57_1031, args) -> begin
(

let _57_1036 = (let _148_377 = (FStar_List.hd args)
in (let _148_376 = (FStar_List.tl args)
in (_148_377, _148_376)))
in (match (_57_1036) with
| (res, args) -> begin
(

let _57_1052 = (let _148_379 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _57_5 -> (match (_57_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _57_1043 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1043) with
| (env, _57_1042) -> begin
(

let _57_1048 = (tc_tot_or_gtot_term env e)
in (match (_57_1048) with
| (e, _57_1046, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _148_379 FStar_List.unzip))
in (match (_57_1052) with
| (flags, guards) -> begin
(

let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| tk -> begin
(FStar_All.failwith "Impossible")
end)
in (let _148_381 = (FStar_Syntax_Syntax.mk_Comp (

let _57_1058 = c
in {FStar_Syntax_Syntax.effect_name = _57_1058.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _57_1058.FStar_Syntax_Syntax.flags}))
in (let _148_380 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_148_381, u, _148_380))))
end))
end))
end))
end))))
end))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_57_1066) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _148_386 = (aux u)
in FStar_Syntax_Syntax.U_succ (_148_386))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _148_387 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_148_387))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _148_391 = (let _148_390 = (let _148_389 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _148_388 = (FStar_TypeChecker_Env.get_range env)
in (_148_389, _148_388)))
in FStar_Syntax_Syntax.Error (_148_390))
in (Prims.raise _148_391))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _148_392 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_392 Prims.snd))
end
| _57_1081 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _148_401 = (let _148_400 = (let _148_399 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_148_399, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_148_400))
in (Prims.raise _148_401)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun _57_1099 bs bs_expected -> (match (_57_1099) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
(

let _57_1130 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _148_418 = (let _148_417 = (let _148_416 = (let _148_414 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _148_414))
in (let _148_415 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_148_416, _148_415)))
in FStar_Syntax_Syntax.Error (_148_417))
in (Prims.raise _148_418))
end
| _57_1129 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _57_1147 = (match ((let _148_419 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _148_419.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _57_1135 -> begin
(

let _57_1136 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_420 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _148_420))
end else begin
()
end
in (

let _57_1142 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_57_1142) with
| (t, _57_1140, g1) -> begin
(

let g2 = (let _148_422 = (FStar_TypeChecker_Env.get_range env)
in (let _148_421 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _148_422 "Type annotation on parameter incompatible with the expected type" _148_421)))
in (

let g = (let _148_423 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _148_423))
in (t, g)))
end)))
end)
in (match (_57_1147) with
| (t, g) -> begin
(

let hd = (

let _57_1148 = hd
in {FStar_Syntax_Syntax.ppname = _57_1148.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1148.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = (hd, imp)
in (

let b_expected = (hd_expected, imp')
in (

let env = (push_binding env b)
in (

let subst = (let _148_424 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _148_424))
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

let _57_1169 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1168 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (

let _57_1176 = (tc_binders env bs)
in (match (_57_1176) with
| (bs, envbody, g, _57_1175) -> begin
(

let _57_1194 = (match ((let _148_431 = (FStar_Syntax_Subst.compress body)
in _148_431.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _57_1181) -> begin
(

let _57_1188 = (tc_comp envbody c)
in (match (_57_1188) with
| (c, _57_1186, g') -> begin
(let _148_432 = (FStar_TypeChecker_Rel.conj_guard g g')
in (Some (c), body, _148_432))
end))
end
| _57_1190 -> begin
(None, body, g)
end)
in (match (_57_1194) with
| (copt, body, g) -> begin
(None, bs, [], copt, envbody, body, g)
end))
end)))
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm t -> (match ((let _148_437 = (FStar_Syntax_Subst.compress t)
in _148_437.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let _57_1221 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1220 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _57_1228 = (tc_binders env bs)
in (match (_57_1228) with
| (bs, envbody, g, _57_1227) -> begin
(

let _57_1232 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_57_1232) with
| (envbody, _57_1231) -> begin
(Some ((t, true)), bs, [], None, envbody, body, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _57_1235) -> begin
(

let _57_1246 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_57_1246) with
| (_57_1239, bs, bs', copt, env, body, g) -> begin
(Some ((t, false)), bs, bs', copt, env, body, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _57_1253 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_57_1253) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun _57_1264 c_expected -> (match (_57_1264) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _148_448 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _148_448))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (let _148_449 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _148_449))
in (let _148_450 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _148_450)))
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

let _57_1285 = (check_binders env more_bs bs_expected)
in (match (_57_1285) with
| (env, bs', more, guard', subst) -> begin
(let _148_452 = (let _148_451 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _148_451, subst))
in (handle_more _148_452 c_expected))
end))
end
| _57_1287 -> begin
(let _148_454 = (let _148_453 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _148_453))
in (fail _148_454 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _148_455 = (check_binders env bs bs_expected)
in (handle_more _148_455 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let _57_1293 = envbody
in {FStar_TypeChecker_Env.solver = _57_1293.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1293.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1293.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1293.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1293.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1293.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1293.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1293.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1293.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1293.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1293.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1293.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_1293.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1293.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1293.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1293.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1293.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1293.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1293.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1293.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _57_1298 _57_1301 -> (match ((_57_1298, _57_1301)) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _57_1307 = (let _148_465 = (let _148_464 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _148_464 Prims.fst))
in (tc_term _148_465 t))
in (match (_57_1307) with
| (t, _57_1304, _57_1306) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _148_466 = (FStar_Syntax_Syntax.mk_binder (

let _57_1311 = x
in {FStar_Syntax_Syntax.ppname = _57_1311.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1311.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_148_466)::letrec_binders)
end
| _57_1314 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (

let _57_1320 = (check_actuals_against_formals env bs bs_expected)
in (match (_57_1320) with
| (envbody, bs, g, c) -> begin
(

let _57_1323 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_57_1323) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, body, g))
end))
end))))
end))
end
| _57_1326 -> begin
if (not (norm)) then begin
(let _148_467 = (unfold_whnf env t)
in (as_function_typ true _148_467))
end else begin
(

let _57_1336 = (expected_function_typ env None body)
in (match (_57_1336) with
| (_57_1328, bs, _57_1331, c_opt, envbody, body, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, body, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let _57_1340 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1340) with
| (env, topt) -> begin
(

let _57_1344 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_468 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _148_468 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (

let _57_1353 = (expected_function_typ env topt body)
in (match (_57_1353) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let _57_1359 = (tc_term (

let _57_1354 = envbody
in {FStar_TypeChecker_Env.solver = _57_1354.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1354.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1354.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1354.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1354.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1354.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1354.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1354.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1354.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1354.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1354.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1354.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1354.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1354.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1354.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1354.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1354.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1354.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1354.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_57_1359) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _57_1361 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _148_471 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _148_470 = (let _148_469 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _148_469))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _148_471 _148_470)))
end else begin
()
end
in (

let _57_1368 = (let _148_473 = (let _148_472 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _148_472))
in (check_expected_effect (

let _57_1363 = envbody
in {FStar_TypeChecker_Env.solver = _57_1363.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1363.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1363.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1363.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1363.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1363.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1363.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1363.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1363.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1363.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1363.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1363.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1363.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1363.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1363.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1363.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1363.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1363.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1363.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1363.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _148_473))
in (match (_57_1368) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _148_474 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _148_474))
end else begin
(

let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _148_477 = (let _148_476 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _148_475 -> FStar_Util.Inl (_148_475)))
in Some (_148_476))
in (FStar_Syntax_Util.abs bs body _148_477))
in (

let _57_1391 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_1380) -> begin
(e, t, guard)
end
| _57_1383 -> begin
(

let _57_1386 = if use_teq then begin
(let _148_478 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _148_478))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_57_1386) with
| (e, guard') -> begin
(let _148_479 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _148_479))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_57_1391) with
| (e, tfun, guard) -> begin
(

let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (

let _57_1395 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_57_1395) with
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

let _57_1405 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_488 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _148_487 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _148_488 _148_487)))
end else begin
()
end
in (

let monadic_application = (fun _57_1412 subst arg_comps_rev arg_rets guard fvs bs -> (match (_57_1412) with
| (head, chead, ghead, cres) -> begin
(

let _57_1419 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let _57_1447 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun _57_6 -> (match (_57_6) with
| (_57_1426, _57_1428, None) -> begin
false
end
| (_57_1432, _57_1434, Some (c)) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _148_504 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _148_504 cres))
end else begin
(

let _57_1439 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_507 = (FStar_Syntax_Print.term_to_string head)
in (let _148_506 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _148_505 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _148_507 _148_506 _148_505))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _57_1443 -> begin
(

let g = (let _148_508 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right _148_508 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _148_513 = (let _148_512 = (let _148_511 = (let _148_510 = (let _148_509 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _148_509))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _148_510))
in (FStar_Syntax_Syntax.mk_Total _148_511))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_512))
in (_148_513, g)))
end)
in (match (_57_1447) with
| (cres, guard) -> begin
(

let _57_1448 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_514 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _148_514))
end else begin
()
end
in (

let _57_1470 = (FStar_List.fold_left (fun _57_1453 _57_1459 -> (match ((_57_1453, _57_1459)) with
| ((args, out_c, monadic), ((e, q), x, c)) -> begin
(match (c) with
| None -> begin
(((e, q))::args, out_c, monadic)
end
| Some (c) -> begin
(

let monadic = (monadic || (not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c))))
in (

let out_c = (FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env None c (x, out_c))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e c.FStar_Syntax_Syntax.eff_name)
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e c.FStar_Syntax_Syntax.eff_name out_c.FStar_Syntax_Syntax.eff_name)
in (((e, q))::args, out_c, monadic)))))
end)
end)) ([], cres, false) arg_comps_rev)
in (match (_57_1470) with
| (args, comp, monadic) -> begin
(

let comp = (FStar_TypeChecker_Util.bind head.FStar_Syntax_Syntax.pos env None chead (None, comp))
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app = if monadic then begin
(FStar_TypeChecker_Util.maybe_monadic env app comp.FStar_Syntax_Syntax.eff_name)
end else begin
app
end
in (

let _57_1476 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (_57_1476) with
| (comp, g) -> begin
(app, comp, g)
end)))))
end)))
end)))
end))
in (

let rec tc_args = (fun head_info _57_1484 bs args -> (match (_57_1484) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match ((bs, args)) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (_57_1490))))::rest, ((_57_1498, None))::_57_1496) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _57_1504 = (check_no_escape (Some (head)) env fvs t)
in (

let _57_1510 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_57_1510) with
| (varg, _57_1508, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (

let arg = (let _148_526 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _148_526))
in (let _148_528 = (let _148_527 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, ((arg, None, None))::outargs, (arg)::arg_rets, _148_527, fvs))
in (tc_args head_info _148_528 rest args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
(

let _57_1542 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _57_1541 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let _57_1545 = x
in {FStar_Syntax_Syntax.ppname = _57_1545.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1545.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (

let _57_1548 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_529 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _148_529))
end else begin
()
end
in (

let _57_1550 = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let _57_1553 = env
in {FStar_TypeChecker_Env.solver = _57_1553.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1553.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1553.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1553.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1553.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1553.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1553.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1553.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1553.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1553.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1553.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1553.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1553.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1553.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1553.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _57_1553.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1553.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1553.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1553.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1553.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_1556 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_532 = (FStar_Syntax_Print.tag_of_term e)
in (let _148_531 = (FStar_Syntax_Print.term_to_string e)
in (let _148_530 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _148_532 _148_531 _148_530))))
end else begin
()
end
in (

let _57_1561 = (tc_term env e)
in (match (_57_1561) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(

let subst = (let _148_533 = (FStar_List.hd bs)
in (maybe_extend_subst subst _148_533 e))
in (tc_args head_info (subst, ((arg, None, None))::outargs, (arg)::arg_rets, g, fvs) rest rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(

let subst = (let _148_534 = (FStar_List.hd bs)
in (maybe_extend_subst subst _148_534 e))
in (tc_args head_info (subst, ((arg, Some (x), Some (c)))::outargs, (arg)::arg_rets, g, fvs) rest rest'))
end else begin
if (let _148_535 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _148_535)) then begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _148_536 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _148_536))
in (tc_args head_info (subst, ((arg, Some (newx), Some (c)))::outargs, (arg')::arg_rets, g, fvs) rest rest')))
end else begin
(let _148_540 = (let _148_539 = (let _148_538 = (let _148_537 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _148_537))
in (_148_538)::arg_rets)
in (subst, ((arg, Some (x), Some (c)))::outargs, _148_539, g, (x)::fvs))
in (tc_args head_info _148_540 rest rest'))
end
end
end))
end))))))))))
end
| (_57_1569, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::_57_1574) -> begin
(

let _57_1581 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (_57_1581) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _148_545 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _148_545 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let _57_1592 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (_57_1592) with
| (bs, cres') -> begin
(

let head_info = (head, chead, ghead, (FStar_Syntax_Util.lcomp_of_comp cres'))
in (

let _57_1594 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_546 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _148_546))
end else begin
()
end
in (tc_args head_info ([], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs args)))
end))
end
| _57_1597 when (not (norm)) -> begin
(let _148_547 = (unfold_whnf env tres)
in (aux true _148_547))
end
| _57_1599 -> begin
(let _148_553 = (let _148_552 = (let _148_551 = (let _148_549 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (let _148_548 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _148_549 _148_548)))
in (let _148_550 = (FStar_Syntax_Syntax.argpos arg)
in (_148_551, _148_550)))
in FStar_Syntax_Syntax.Error (_148_552))
in (Prims.raise _148_553))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (match ((let _148_558 = (FStar_Syntax_Util.unrefine tf)
in _148_558.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| ((e, imp))::tl -> begin
(

let _57_1632 = (tc_term env e)
in (match (_57_1632) with
| (e, c, g_e) -> begin
(

let _57_1636 = (tc_args env tl)
in (match (_57_1636) with
| (args, comps, g_rest) -> begin
(let _148_563 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, ((e.FStar_Syntax_Syntax.pos, c))::comps, _148_563))
end))
end))
end))
in (

let _57_1640 = (tc_args env args)
in (match (_57_1640) with
| (args, comps, g_args) -> begin
(

let bs = (let _148_565 = (FStar_All.pipe_right comps (FStar_List.map (fun _57_1644 -> (match (_57_1644) with
| (_57_1642, c) -> begin
(c.FStar_Syntax_Syntax.res_typ, None)
end))))
in (FStar_Syntax_Util.null_binders_of_tks _148_565))
in (

let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _57_1650 -> begin
FStar_Syntax_Util.ml_comp
end)
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _148_580 = (FStar_Syntax_Subst.compress t)
in _148_580.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_1656) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _57_1661 -> begin
ml_or_tot
end)
end)
in (

let cres = (let _148_585 = (let _148_584 = (let _148_583 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_583 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _148_584))
in (ml_or_tot _148_585 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (

let _57_1665 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _148_588 = (FStar_Syntax_Print.term_to_string head)
in (let _148_587 = (FStar_Syntax_Print.term_to_string tf)
in (let _148_586 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _148_588 _148_587 _148_586))))
end else begin
()
end
in (

let _57_1667 = (let _148_589 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _148_589))
in (

let comp = (let _148_592 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _57_1671 out -> (match (_57_1671) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c (None, out))
end)) (((head.FStar_Syntax_Syntax.pos, chead))::comps) _148_592))
in (let _148_594 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _148_593 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_148_594, comp, _148_593)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _57_1680 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_1680) with
| (bs, c) -> begin
(

let head_info = (head, chead, ghead, (FStar_Syntax_Util.lcomp_of_comp c))
in (tc_args head_info ([], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs args))
end))
end
| _57_1683 -> begin
if (not (norm)) then begin
(let _148_595 = (unfold_whnf env tf)
in (check_function_app true _148_595))
end else begin
(let _148_598 = (let _148_597 = (let _148_596 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_148_596, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_148_597))
in (Prims.raise _148_598))
end
end))
in (let _148_600 = (let _148_599 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _148_599))
in (check_function_app false _148_600))))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let _57_1719 = (FStar_List.fold_left2 (fun _57_1700 _57_1703 _57_1706 -> (match ((_57_1700, _57_1703, _57_1706)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(

let _57_1707 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let _57_1712 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_57_1712) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (let _148_610 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _148_610 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _148_614 = (let _148_612 = (let _148_611 = (FStar_Syntax_Syntax.as_arg e)
in (_148_611)::[])
in (FStar_List.append seen _148_612))
in (let _148_613 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_148_614, _148_613, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_57_1719) with
| (args, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = if ghost then begin
(let _148_615 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _148_615 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (

let _57_1724 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_57_1724) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _57_1726 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let _57_1733 = (FStar_Syntax_Subst.open_branch branch)
in (match (_57_1733) with
| (pattern, when_clause, branch_exp) -> begin
(

let _57_1738 = branch
in (match (_57_1738) with
| (cpat, _57_1736, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _57_1746 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_57_1746) with
| (pat_bvs, exps, p) -> begin
(

let _57_1747 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_627 = (FStar_Syntax_Print.pat_to_string p0)
in (let _148_626 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _148_627 _148_626)))
end else begin
()
end
in (

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let _57_1753 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_57_1753) with
| (env1, _57_1752) -> begin
(

let env1 = (

let _57_1754 = env1
in {FStar_TypeChecker_Env.solver = _57_1754.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1754.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1754.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1754.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1754.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1754.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1754.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1754.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _57_1754.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1754.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1754.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1754.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1754.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1754.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1754.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1754.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1754.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1754.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1754.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1754.FStar_TypeChecker_Env.use_bv_sorts})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _57_1793 = (let _148_650 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _57_1759 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_630 = (FStar_Syntax_Print.term_to_string e)
in (let _148_629 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _148_630 _148_629)))
end else begin
()
end
in (

let _57_1764 = (tc_term env1 e)
in (match (_57_1764) with
| (e, lc, g) -> begin
(

let _57_1765 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_632 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _148_631 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _148_632 _148_631)))
end else begin
()
end
in (

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let _57_1771 = (let _148_633 = (FStar_TypeChecker_Rel.discharge_guard env (

let _57_1769 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_1769.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_1769.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_1769.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _148_633 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _148_638 = (let _148_637 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _148_637 (FStar_List.map (fun _57_1779 -> (match (_57_1779) with
| (u, _57_1778) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _148_638 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _57_1787 = if (let _148_639 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _148_639)) then begin
(

let unresolved = (let _148_640 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _148_640 FStar_Util.set_elements))
in (let _148_648 = (let _148_647 = (let _148_646 = (let _148_645 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _148_644 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _148_643 = (let _148_642 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _57_1786 -> (match (_57_1786) with
| (u, _57_1785) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _148_642 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _148_645 _148_644 _148_643))))
in (_148_646, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_148_647))
in (Prims.raise _148_648)))
end else begin
()
end
in (

let _57_1789 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_649 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _148_649))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _148_650 FStar_List.unzip))
in (match (_57_1793) with
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

let _57_1800 = (let _148_651 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _148_651 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_57_1800) with
| (scrutinee_env, _57_1799) -> begin
(

let _57_1806 = (tc_pat true pat_t pattern)
in (match (_57_1806) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let _57_1816 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(

let _57_1813 = (let _148_652 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _148_652 e))
in (match (_57_1813) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_57_1816) with
| (when_clause, g_when) -> begin
(

let _57_1820 = (tc_term pat_env branch_exp)
in (match (_57_1820) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _148_654 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _148_653 -> Some (_148_653)) _148_654))
end)
in (

let _57_1876 = (

let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _57_1838 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _148_658 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _148_657 -> Some (_148_657)) _148_658))
end))
end))) None))
in (

let _57_1846 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_57_1846) with
| (c, g_branch) -> begin
(

let _57_1871 = (match ((eqs, when_condition)) with
| (None, None) -> begin
(c, g_when)
end
| (Some (f), None) -> begin
(

let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _148_661 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _148_660 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_148_661, _148_660)))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (let _148_662 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_148_662))
in (let _148_665 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _148_664 = (let _148_663 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _148_663 g_when))
in (_148_665, _148_664)))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _148_666 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_148_666, g_when))))
end)
in (match (_57_1871) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _148_668 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _148_667 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_148_668, _148_667, g_branch))))
end))
end)))
in (match (_57_1876) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = (

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> if ((let _148_678 = (let _148_677 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _148_677))
in (FStar_List.length _148_678)) > 1) then begin
(

let disc = (let _148_679 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _148_679 FStar_Syntax_Syntax.Delta_equational None))
in (

let disc = (let _148_681 = (let _148_680 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_148_680)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _148_681 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _148_682 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_148_682)::[])))
end else begin
[]
end)
in (

let fail = (fun _57_1886 -> (match (()) with
| () -> begin
(let _148_688 = (let _148_687 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _148_686 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _148_685 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _148_687 _148_686 _148_685))))
in (FStar_All.failwith _148_688))
end))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _57_1893) -> begin
(head_constructor t)
end
| _57_1897 -> begin
(fail ())
end))
in (

let pat_exp = (let _148_691 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _148_691 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_57_1922) -> begin
(let _148_696 = (let _148_695 = (let _148_694 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _148_693 = (let _148_692 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_148_692)::[])
in (_148_694)::_148_693))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _148_695 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_148_696)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _148_697 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _148_697))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(

let sub_term_guards = (let _148_704 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _57_1940 -> (match (_57_1940) with
| (ei, _57_1939) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _57_1944 -> begin
(

let sub_term = (let _148_703 = (let _148_700 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _148_700 FStar_Syntax_Syntax.Delta_equational None))
in (let _148_702 = (let _148_701 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_148_701)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _148_703 _148_702 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _148_704 FStar_List.flatten))
in (let _148_705 = (discriminate scrutinee_tm f)
in (FStar_List.append _148_705 sub_term_guards)))
end)
end
| _57_1948 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(

let t = (let _148_710 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _148_710))
in (

let _57_1956 = (FStar_Syntax_Util.type_u ())
in (match (_57_1956) with
| (k, _57_1955) -> begin
(

let _57_1962 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_57_1962) with
| (t, _57_1959, _57_1961) -> begin
t
end))
end)))
end)
in (

let branch_guard = (let _148_711 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _148_711 FStar_Syntax_Util.mk_disj_l))
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

let _57_1970 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_712 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _148_712))
end else begin
()
end
in (let _148_713 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_148_713, branch_guard, c, guard)))))
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

let _57_1987 = (check_let_bound_def true env lb)
in (match (_57_1987) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let _57_1999 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(

let g1 = (let _148_716 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _148_716 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _57_1994 = (let _148_720 = (let _148_719 = (let _148_718 = (let _148_717 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _148_717))
in (_148_718)::[])
in (FStar_TypeChecker_Util.generalize env _148_719))
in (FStar_List.hd _148_720))
in (match (_57_1994) with
| (_57_1990, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_57_1999) with
| (g1, e1, univ_vars, c1) -> begin
(

let _57_2009 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(

let _57_2002 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_57_2002) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(

let _57_2003 = if (FStar_Options.warn_top_level_effects ()) then begin
(let _148_721 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _148_721 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _148_722 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_148_722, c1)))
end
end))
end else begin
(

let _57_2005 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _148_723 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _148_723)))
end
in (match (_57_2009) with
| (e2, c1) -> begin
(

let cres = (let _148_724 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_724))
in (

let _57_2011 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _148_725 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_148_725, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _57_2015 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let _57_2026 = env
in {FStar_TypeChecker_Env.solver = _57_2026.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2026.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2026.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2026.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2026.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2026.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2026.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2026.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2026.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2026.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2026.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2026.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2026.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_2026.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2026.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2026.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2026.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2026.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2026.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2026.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_2035 = (let _148_729 = (let _148_728 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _148_728 Prims.fst))
in (check_let_bound_def false _148_729 lb))
in (match (_57_2035) with
| (e1, _57_2031, c1, g1, annotated) -> begin
(

let x = (

let _57_2036 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_2036.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2036.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let _57_2042 = (let _148_731 = (let _148_730 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_730)::[])
in (FStar_Syntax_Subst.open_term _148_731 e2))
in (match (_57_2042) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _57_2048 = (let _148_732 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _148_732 e2))
in (match (_57_2048) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (Some (x), c2))
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e2 = (FStar_TypeChecker_Util.maybe_lift env e2 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e = (let _148_735 = (let _148_734 = (let _148_733 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _148_733))
in FStar_Syntax_Syntax.Tm_let (_148_734))
in (FStar_Syntax_Syntax.mk _148_735 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name)
in (

let x_eq_e1 = (let _148_738 = (let _148_737 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _148_737 e1))
in (FStar_All.pipe_left (fun _148_736 -> FStar_TypeChecker_Common.NonTrivial (_148_736)) _148_738))
in (

let g2 = (let _148_740 = (let _148_739 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _148_739 g2))
in (FStar_TypeChecker_Rel.close_guard xb _148_740))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if (let _148_741 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome _148_741)) then begin
(e, cres, guard)
end else begin
(

let _57_2057 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end))))))))
end))))
end))))
end)))
end
| _57_2060 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _57_2072 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_2072) with
| (lbs, e2) -> begin
(

let _57_2075 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_2075) with
| (env0, topt) -> begin
(

let _57_2078 = (build_let_rec_env true env0 lbs)
in (match (_57_2078) with
| (lbs, rec_env) -> begin
(

let _57_2081 = (check_let_recs rec_env lbs)
in (match (_57_2081) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (let _148_744 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _148_744 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _148_747 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _148_747 (fun _148_746 -> Some (_148_746))))
in (

let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(

let ecs = (let _148_751 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _148_750 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _148_750)))))
in (FStar_TypeChecker_Util.generalize env _148_751))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _57_2092 -> (match (_57_2092) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _148_753 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_753))
in (

let _57_2095 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _57_2099 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_2099) with
| (lbs, e2) -> begin
(let _148_755 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _148_754 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_148_755, cres, _148_754)))
end)))))))
end))
end))
end))
end))
end
| _57_2101 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _57_2113 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_2113) with
| (lbs, e2) -> begin
(

let _57_2116 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_2116) with
| (env0, topt) -> begin
(

let _57_2119 = (build_let_rec_env false env0 lbs)
in (match (_57_2119) with
| (lbs, rec_env) -> begin
(

let _57_2122 = (check_let_recs rec_env lbs)
in (match (_57_2122) with
| (lbs, g_lbs) -> begin
(

let _57_2134 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let _57_2125 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_2125.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2125.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let _57_2128 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _57_2128.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_2128.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_2128.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _57_2128.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], lb.FStar_Syntax_Syntax.lbtyp))
in (env, lb))))) env))
in (match (_57_2134) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let _57_2140 = (tc_term env e2)
in (match (_57_2140) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _57_2144 = cres
in {FStar_Syntax_Syntax.eff_name = _57_2144.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _57_2144.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_2144.FStar_Syntax_Syntax.comp})
in (

let _57_2149 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_2149) with
| (lbs, e2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_57_2152) -> begin
(e, cres, guard)
end
| None -> begin
(

let _57_2155 = (check_no_escape None env bvs tres)
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
| _57_2158 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let _57_2191 = (FStar_List.fold_left (fun _57_2165 lb -> (match (_57_2165) with
| (lbs, env) -> begin
(

let _57_2170 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_57_2170) with
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

let _57_2179 = (let _148_767 = (let _148_766 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _148_766))
in (tc_check_tot_or_gtot_term (

let _57_2173 = env0
in {FStar_TypeChecker_Env.solver = _57_2173.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2173.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2173.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2173.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2173.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2173.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2173.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2173.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2173.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2173.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2173.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2173.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2173.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2173.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _57_2173.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2173.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2173.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2173.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2173.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2173.FStar_TypeChecker_Env.use_bv_sorts}) t _148_767))
in (match (_57_2179) with
| (t, _57_2177, g) -> begin
(

let _57_2180 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (

let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(

let _57_2183 = env
in {FStar_TypeChecker_Env.solver = _57_2183.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2183.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2183.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2183.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2183.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2183.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2183.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2183.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2183.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2183.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2183.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2183.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2183.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_2183.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2183.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2183.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2183.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2183.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2183.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2183.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (

let lb = (

let _57_2186 = lb
in {FStar_Syntax_Syntax.lbname = _57_2186.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _57_2186.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_57_2191) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _57_2204 = (let _148_772 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _57_2198 = (let _148_771 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _148_771 lb.FStar_Syntax_Syntax.lbdef))
in (match (_57_2198) with
| (e, c, g) -> begin
(

let _57_2199 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _148_772 FStar_List.unzip))
in (match (_57_2204) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _57_2212 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_2212) with
| (env1, _57_2211) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _57_2218 = (check_lbtyp top_level env lb)
in (match (_57_2218) with
| (topt, wf_annot, univ_vars, env1) -> begin
(

let _57_2219 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let _57_2226 = (tc_maybe_toplevel_term (

let _57_2221 = env1
in {FStar_TypeChecker_Env.solver = _57_2221.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2221.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2221.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2221.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2221.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2221.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2221.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2221.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2221.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2221.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2221.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2221.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2221.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _57_2221.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2221.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2221.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2221.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2221.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2221.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2221.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_57_2226) with
| (e1, c1, g1) -> begin
(

let _57_2230 = (let _148_779 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_2227 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _148_779 e1 c1 wf_annot))
in (match (_57_2230) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _57_2232 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_780 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _148_780))
end else begin
()
end
in (let _148_781 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _148_781))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _57_2239 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _57_2242 -> begin
(

let _57_2245 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_57_2245) with
| (univ_vars, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _148_785 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _148_785))
end else begin
(

let _57_2250 = (FStar_Syntax_Util.type_u ())
in (match (_57_2250) with
| (k, _57_2249) -> begin
(

let _57_2255 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_57_2255) with
| (t, _57_2253, g) -> begin
(

let _57_2256 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _148_788 = (let _148_786 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _148_786))
in (let _148_787 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _148_788 _148_787)))
end else begin
()
end
in (

let t = (norm env1 t)
in (let _148_789 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _148_789))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _57_2262 -> (match (_57_2262) with
| (x, imp) -> begin
(

let _57_2265 = (FStar_Syntax_Util.type_u ())
in (match (_57_2265) with
| (tu, u) -> begin
(

let _57_2270 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_57_2270) with
| (t, _57_2268, g) -> begin
(

let x = ((

let _57_2271 = x
in {FStar_Syntax_Syntax.ppname = _57_2271.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2271.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (

let _57_2274 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_793 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _148_792 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _148_793 _148_792)))
end else begin
()
end
in (let _148_794 = (push_binding env x)
in (x, _148_794, g, u))))
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

let _57_2289 = (tc_binder env b)
in (match (_57_2289) with
| (b, env', g, u) -> begin
(

let _57_2294 = (aux env' bs)
in (match (_57_2294) with
| (bs, env', g', us) -> begin
(let _148_802 = (let _148_801 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _148_801))
in ((b)::bs, env', _148_802, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun _57_2302 _57_2305 -> (match ((_57_2302, _57_2305)) with
| ((t, imp), (args, g)) -> begin
(

let _57_2310 = (tc_term env t)
in (match (_57_2310) with
| (t, _57_2308, g') -> begin
(let _148_811 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _148_811))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _57_2314 -> (match (_57_2314) with
| (pats, g) -> begin
(

let _57_2317 = (tc_args env p)
in (match (_57_2317) with
| (args, g') -> begin
(let _148_814 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _148_814))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _57_2323 = (tc_maybe_toplevel_term env e)
in (match (_57_2323) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let _57_2326 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_817 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _148_817))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _57_2331 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _148_818 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_148_818, false))
end else begin
(let _148_819 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_148_819, true))
end
in (match (_57_2331) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _148_820 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _148_820))
end
| _57_2335 -> begin
if allow_ghost then begin
(let _148_823 = (let _148_822 = (let _148_821 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_148_821, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_148_822))
in (Prims.raise _148_823))
end else begin
(let _148_826 = (let _148_825 = (let _148_824 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_148_824, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_148_825))
in (Prims.raise _148_826))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let _57_2345 = (tc_tot_or_gtot_term env t)
in (match (_57_2345) with
| (t, c, g) -> begin
(

let _57_2346 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let _57_2354 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_2354) with
| (t, c, g) -> begin
(

let _57_2355 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _148_844 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _148_844)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _148_848 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _148_848))))


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let _57_2370 = (tc_binders env tps)
in (match (_57_2370) with
| (tps, env, g, us) -> begin
(

let _57_2371 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (

let fail = (fun _57_2377 -> (match (()) with
| () -> begin
(let _148_863 = (let _148_862 = (let _148_861 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_148_861, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_148_862))
in (Prims.raise _148_863))
end))
in (

let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _57_2390))::((wp, _57_2386))::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2394 -> begin
(fail ())
end))
end
| _57_2396 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let _57_2403 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_57_2403) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _57_2405 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let _57_2409 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_57_2409) with
| (uvs, t') -> begin
(match ((let _148_870 = (FStar_Syntax_Subst.compress t')
in _148_870.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _57_2415 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))


let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (

let fail = (fun t -> (let _148_881 = (let _148_880 = (let _148_879 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_148_879, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_148_880))
in (Prims.raise _148_881)))
in (match ((let _148_882 = (FStar_Syntax_Subst.compress signature)
in _148_882.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _57_2432))::((wp, _57_2428))::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2436 -> begin
(fail signature)
end))
end
| _57_2438 -> begin
(fail signature)
end)))


let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (

let _57_2443 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_57_2443) with
| (a, wp) -> begin
(

let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _57_2446 -> begin
(

let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (

let op = (fun ts -> (

let _57_2450 = ()
in (

let t0 = (Prims.snd ts)
in (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (

let _57_2454 = ed
in (let _148_898 = (op ed.FStar_Syntax_Syntax.ret_wp)
in (let _148_897 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _148_896 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _148_895 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _148_894 = (op ed.FStar_Syntax_Syntax.stronger)
in (let _148_893 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _148_892 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _148_891 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _148_890 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _148_889 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _57_2454.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2454.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2454.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2454.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2454.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _148_898; FStar_Syntax_Syntax.bind_wp = _148_897; FStar_Syntax_Syntax.if_then_else = _148_896; FStar_Syntax_Syntax.ite_wp = _148_895; FStar_Syntax_Syntax.stronger = _148_894; FStar_Syntax_Syntax.close_wp = _148_893; FStar_Syntax_Syntax.assert_p = _148_892; FStar_Syntax_Syntax.assume_p = _148_891; FStar_Syntax_Syntax.null_wp = _148_890; FStar_Syntax_Syntax.trivial = _148_889; FStar_Syntax_Syntax.repr = _57_2454.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _57_2454.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _57_2454.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _57_2454.FStar_Syntax_Syntax.actions})))))))))))))
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

let n = (match ((let _148_920 = (FStar_Syntax_Subst.compress tm)
in _148_920.FStar_Syntax_Syntax.n)) with
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
| _57_2489 -> begin
tm.FStar_Syntax_Syntax.n
end)
in (

let _57_2491 = tm
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2491.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2491.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2491.FStar_Syntax_Syntax.vars})))
and visit_binder = (fun _57_2495 -> (match (_57_2495) with
| (bv, a) -> begin
(let _148_924 = (

let _57_2496 = bv
in (let _148_922 = (visit_term bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_2496.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2496.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_922}))
in (let _148_923 = (FStar_Syntax_Syntax.as_implicit false)
in (_148_924, _148_923)))
end))
and visit_maybe_lcomp = (fun lcomp -> (match (lcomp) with
| Some (FStar_Util.Inl (lcomp)) -> begin
(let _148_929 = (let _148_928 = (let _148_927 = (let _148_926 = (lcomp.FStar_Syntax_Syntax.comp ())
in (visit_comp _148_926))
in (FStar_Syntax_Util.lcomp_of_comp _148_927))
in FStar_Util.Inl (_148_928))
in Some (_148_929))
end
| comp -> begin
comp
end))
and visit_comp = (fun comp -> (

let n = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tm) -> begin
(let _148_931 = (visit_term tm)
in FStar_Syntax_Syntax.Total (_148_931))
end
| FStar_Syntax_Syntax.GTotal (tm) -> begin
(let _148_932 = (visit_term tm)
in FStar_Syntax_Syntax.GTotal (_148_932))
end
| comp -> begin
comp
end)
in (

let _57_2510 = comp
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2510.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2510.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2510.FStar_Syntax_Syntax.vars})))
and visit_args = (fun args -> (FStar_List.map (fun _57_2515 -> (match (_57_2515) with
| (tm, q) -> begin
(let _148_935 = (visit_term tm)
in (_148_935, q))
end)) args))
in (visit_term tm))))
in (

let check = (fun str t -> if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _57_2519 = (let _148_940 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Generated term for %s: %s\n" str _148_940))
in (

let t = (normalize t)
in (

let t = (FStar_Syntax_Subst.compress t)
in (

let _57_2534 = (tc_term env t)
in (match (_57_2534) with
| (e, {FStar_Syntax_Syntax.eff_name = _57_2530; FStar_Syntax_Syntax.res_typ = res_typ; FStar_Syntax_Syntax.cflags = _57_2527; FStar_Syntax_Syntax.comp = _57_2525}, _57_2533) -> begin
(

let _57_2535 = (let _148_943 = (let _148_942 = (normalize res_typ)
in (FStar_Syntax_Print.term_to_string _148_942))
in (FStar_Util.print2 "Inferred type for %s: %s\n" str _148_943))
in (let _148_945 = (let _148_944 = (normalize e)
in (FStar_Syntax_Print.term_to_string _148_944))
in (FStar_Util.print2 "Elaborated term for %s: %s\n" str _148_945)))
end)))))
end else begin
()
end)
in (

let rec collect_binders = (fun t -> (match ((let _148_948 = (FStar_Syntax_Subst.compress t)
in _148_948.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
t
end
| _57_2546 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _148_949 = (collect_binders rest)
in (FStar_List.append bs _148_949)))
end
| FStar_Syntax_Syntax.Tm_type (_57_2549) -> begin
[]
end
| _57_2552 -> begin
(FStar_All.failwith "wp_a doesn\'t end in Type0")
end))
in (

let _57_2567 = (

let i = (FStar_ST.alloc 0)
in (

let wp_binders = (let _148_956 = (normalize wp_a)
in (collect_binders _148_956))
in ((fun t -> (let _148_962 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow wp_binders _148_962))), (fun t -> (let _148_965 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow wp_binders _148_965))), (fun _57_2557 -> (match (()) with
| () -> begin
(FStar_List.map (fun _57_2561 -> (match (_57_2561) with
| (bv, _57_2560) -> begin
(

let _57_2562 = (let _148_969 = ((FStar_ST.read i) + 1)
in (FStar_ST.op_Colon_Equals i _148_969))
in (let _148_972 = (let _148_971 = (let _148_970 = (FStar_ST.read i)
in (FStar_Util.string_of_int _148_970))
in (Prims.strcat "g" _148_971))
in (FStar_Syntax_Syntax.gen_bv _148_972 None bv.FStar_Syntax_Syntax.sort)))
end)) wp_binders)
end)))))
in (match (_57_2567) with
| (mk_ctx, mk_gctx, mk_gamma) -> begin
(

let binders_of_list = (FStar_List.map (fun _57_2570 -> (match (_57_2570) with
| (t, b) -> begin
(let _148_978 = (FStar_Syntax_Syntax.as_implicit b)
in (t, _148_978))
end)))
in (

let implicit_binders_of_list = (FStar_List.map (fun t -> (let _148_981 = (FStar_Syntax_Syntax.as_implicit true)
in (t, _148_981))))
in (

let args_of_bv = (FStar_List.map (fun bv -> (let _148_984 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_Syntax_Syntax.as_arg _148_984))))
in (

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let x = (let _148_985 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _148_985))
in (

let ret = (let _148_990 = (let _148_989 = (let _148_988 = (let _148_987 = (let _148_986 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx _148_986))
in (FStar_Syntax_Syntax.mk_Total _148_987))
in (FStar_Syntax_Util.lcomp_of_comp _148_988))
in FStar_Util.Inl (_148_989))
in Some (_148_990))
in (

let gamma = (mk_gamma ())
in (

let body = (let _148_992 = (implicit_binders_of_list gamma)
in (let _148_991 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs _148_992 _148_991 ret)))
in (let _148_993 = (binders_of_list (((t, true))::((x, false))::[]))
in (FStar_Syntax_Util.abs _148_993 body ret)))))))
in (

let _57_2582 = (let _148_997 = (let _148_996 = (let _148_995 = (let _148_994 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_994)::[])
in (FStar_List.append binders _148_995))
in (FStar_Syntax_Util.abs _148_996 c_pure None))
in (check "pure" _148_997))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let l = (let _148_1005 = (let _148_1004 = (let _148_1003 = (let _148_1000 = (let _148_999 = (let _148_998 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _148_998))
in (FStar_Syntax_Syntax.mk_binder _148_999))
in (_148_1000)::[])
in (let _148_1002 = (let _148_1001 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _148_1001))
in (FStar_Syntax_Util.arrow _148_1003 _148_1002)))
in (mk_gctx _148_1004))
in (FStar_Syntax_Syntax.gen_bv "l" None _148_1005))
in (

let r = (let _148_1007 = (let _148_1006 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _148_1006))
in (FStar_Syntax_Syntax.gen_bv "r" None _148_1007))
in (

let ret = (let _148_1012 = (let _148_1011 = (let _148_1010 = (let _148_1009 = (let _148_1008 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _148_1008))
in (FStar_Syntax_Syntax.mk_Total _148_1009))
in (FStar_Syntax_Util.lcomp_of_comp _148_1010))
in FStar_Util.Inl (_148_1011))
in Some (_148_1012))
in (

let outer_body = (

let gamma = (mk_gamma ())
in (

let gamma_as_args = (args_of_bv gamma)
in (

let inner_body = (let _148_1018 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _148_1017 = (let _148_1016 = (let _148_1015 = (let _148_1014 = (let _148_1013 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _148_1013 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg _148_1014))
in (_148_1015)::[])
in (FStar_List.append gamma_as_args _148_1016))
in (FStar_Syntax_Util.mk_app _148_1018 _148_1017)))
in (let _148_1019 = (implicit_binders_of_list gamma)
in (FStar_Syntax_Util.abs _148_1019 inner_body ret)))))
in (let _148_1020 = (binders_of_list (((t1, true))::((t2, true))::((l, false))::((r, false))::[]))
in (FStar_Syntax_Util.abs _148_1020 outer_body ret))))))))
in (

let _57_2594 = (let _148_1024 = (let _148_1023 = (let _148_1022 = (let _148_1021 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_1021)::[])
in (FStar_List.append binders _148_1022))
in (FStar_Syntax_Util.abs _148_1023 c_app None))
in (check "app" _148_1024))
in (

let unknown = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _148_1029 = (let _148_1026 = (let _148_1025 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _148_1025))
in (_148_1026)::[])
in (let _148_1028 = (let _148_1027 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _148_1027))
in (FStar_Syntax_Util.arrow _148_1029 _148_1028)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _148_1031 = (let _148_1030 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _148_1030))
in (FStar_Syntax_Syntax.gen_bv "a1" None _148_1031))
in (

let ret = (let _148_1036 = (let _148_1035 = (let _148_1034 = (let _148_1033 = (let _148_1032 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _148_1032))
in (FStar_Syntax_Syntax.mk_Total _148_1033))
in (FStar_Syntax_Util.lcomp_of_comp _148_1034))
in FStar_Util.Inl (_148_1035))
in Some (_148_1036))
in (let _148_1049 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::((a1, false))::[]))
in (let _148_1048 = (let _148_1047 = (let _148_1046 = (let _148_1045 = (let _148_1044 = (let _148_1043 = (let _148_1040 = (let _148_1039 = (let _148_1038 = (let _148_1037 = (FStar_Syntax_Syntax.bv_to_name f)
in (_148_1037)::[])
in (unknown)::_148_1038)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1039))
in (FStar_Syntax_Util.mk_app c_pure _148_1040))
in (let _148_1042 = (let _148_1041 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_148_1041)::[])
in (_148_1043)::_148_1042))
in (unknown)::_148_1044)
in (unknown)::_148_1045)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1046))
in (FStar_Syntax_Util.mk_app c_app _148_1047))
in (FStar_Syntax_Util.abs _148_1049 _148_1048 ret)))))))))
in (

let _57_2604 = (let _148_1053 = (let _148_1052 = (let _148_1051 = (let _148_1050 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_1050)::[])
in (FStar_List.append binders _148_1051))
in (FStar_Syntax_Util.abs _148_1052 c_lift1 None))
in (check "lift1" _148_1053))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _148_1061 = (let _148_1058 = (let _148_1054 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _148_1054))
in (let _148_1057 = (let _148_1056 = (let _148_1055 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder _148_1055))
in (_148_1056)::[])
in (_148_1058)::_148_1057))
in (let _148_1060 = (let _148_1059 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal _148_1059))
in (FStar_Syntax_Util.arrow _148_1061 _148_1060)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _148_1063 = (let _148_1062 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _148_1062))
in (FStar_Syntax_Syntax.gen_bv "a1" None _148_1063))
in (

let a2 = (let _148_1065 = (let _148_1064 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _148_1064))
in (FStar_Syntax_Syntax.gen_bv "a2" None _148_1065))
in (

let ret = (let _148_1070 = (let _148_1069 = (let _148_1068 = (let _148_1067 = (let _148_1066 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx _148_1066))
in (FStar_Syntax_Syntax.mk_Total _148_1067))
in (FStar_Syntax_Util.lcomp_of_comp _148_1068))
in FStar_Util.Inl (_148_1069))
in Some (_148_1070))
in (let _148_1090 = (binders_of_list (((t1, true))::((t2, true))::((t3, true))::((f, false))::((a1, false))::((a2, false))::[]))
in (let _148_1089 = (let _148_1088 = (let _148_1087 = (let _148_1086 = (let _148_1085 = (let _148_1084 = (let _148_1081 = (let _148_1080 = (let _148_1079 = (let _148_1078 = (let _148_1077 = (let _148_1074 = (let _148_1073 = (let _148_1072 = (let _148_1071 = (FStar_Syntax_Syntax.bv_to_name f)
in (_148_1071)::[])
in (unknown)::_148_1072)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1073))
in (FStar_Syntax_Util.mk_app c_pure _148_1074))
in (let _148_1076 = (let _148_1075 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_148_1075)::[])
in (_148_1077)::_148_1076))
in (unknown)::_148_1078)
in (unknown)::_148_1079)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1080))
in (FStar_Syntax_Util.mk_app c_app _148_1081))
in (let _148_1083 = (let _148_1082 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_148_1082)::[])
in (_148_1084)::_148_1083))
in (unknown)::_148_1085)
in (unknown)::_148_1086)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1087))
in (FStar_Syntax_Util.mk_app c_app _148_1088))
in (FStar_Syntax_Util.abs _148_1090 _148_1089 ret)))))))))))
in (

let _57_2615 = (let _148_1094 = (let _148_1093 = (let _148_1092 = (let _148_1091 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_1091)::[])
in (FStar_List.append binders _148_1092))
in (FStar_Syntax_Util.abs _148_1093 c_lift2 None))
in (check "lift2" _148_1094))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _148_1100 = (let _148_1096 = (let _148_1095 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _148_1095))
in (_148_1096)::[])
in (let _148_1099 = (let _148_1098 = (let _148_1097 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _148_1097))
in (FStar_Syntax_Syntax.mk_Total _148_1098))
in (FStar_Syntax_Util.arrow _148_1100 _148_1099)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let ret = (let _148_1110 = (let _148_1109 = (let _148_1108 = (let _148_1107 = (let _148_1106 = (let _148_1105 = (let _148_1102 = (let _148_1101 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _148_1101))
in (_148_1102)::[])
in (let _148_1104 = (let _148_1103 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _148_1103))
in (FStar_Syntax_Util.arrow _148_1105 _148_1104)))
in (mk_ctx _148_1106))
in (FStar_Syntax_Syntax.mk_Total _148_1107))
in (FStar_Syntax_Util.lcomp_of_comp _148_1108))
in FStar_Util.Inl (_148_1109))
in Some (_148_1110))
in (

let e1 = (let _148_1111 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _148_1111))
in (

let gamma = (mk_gamma ())
in (

let body = (let _148_1121 = (let _148_1114 = (FStar_Syntax_Syntax.binders_of_list gamma)
in (let _148_1113 = (let _148_1112 = (FStar_Syntax_Syntax.mk_binder e1)
in (_148_1112)::[])
in (FStar_List.append _148_1114 _148_1113)))
in (let _148_1120 = (let _148_1119 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _148_1118 = (let _148_1117 = (let _148_1115 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _148_1115))
in (let _148_1116 = (args_of_bv gamma)
in (_148_1117)::_148_1116))
in (FStar_Syntax_Util.mk_app _148_1119 _148_1118)))
in (FStar_Syntax_Util.abs _148_1121 _148_1120 ret)))
in (let _148_1122 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::[]))
in (FStar_Syntax_Util.abs _148_1122 body ret))))))))))
in (

let _57_2626 = (let _148_1126 = (let _148_1125 = (let _148_1124 = (let _148_1123 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_1123)::[])
in (FStar_List.append binders _148_1124))
in (FStar_Syntax_Util.abs _148_1125 c_push None))
in (check "push" _148_1126))
in (

let ret_tot_wp_a = (let _148_1129 = (let _148_1128 = (let _148_1127 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _148_1127))
in FStar_Util.Inl (_148_1128))
in Some (_148_1129))
in (

let wp_if_then_else = (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _148_1140 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (let _148_1139 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_unfoldable (2)) None)
in (let _148_1138 = (let _148_1137 = (let _148_1136 = (let _148_1135 = (let _148_1134 = (let _148_1133 = (let _148_1132 = (let _148_1131 = (let _148_1130 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _148_1130))
in (_148_1131)::[])
in (FStar_Syntax_Util.mk_app l_ite _148_1132))
in (_148_1133)::[])
in (unknown)::_148_1134)
in (unknown)::_148_1135)
in (unknown)::_148_1136)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1137))
in (FStar_Syntax_Util.mk_app c_lift2 _148_1138)))
in (FStar_Syntax_Util.abs _148_1140 _148_1139 ret_tot_wp_a))))
in (

let wp_if_then_else = (normalize_and_make_binders_explicit wp_if_then_else)
in (

let _57_2633 = (let _148_1141 = (FStar_Syntax_Util.abs binders wp_if_then_else None)
in (check "wp_if_then_else" _148_1141))
in (

let wp_assert = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_and = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (

let body = (let _148_1155 = (let _148_1154 = (let _148_1153 = (let _148_1152 = (let _148_1151 = (let _148_1148 = (let _148_1147 = (let _148_1146 = (let _148_1145 = (let _148_1144 = (let _148_1143 = (let _148_1142 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _148_1142))
in (_148_1143)::[])
in (FStar_Syntax_Util.mk_app l_and _148_1144))
in (_148_1145)::[])
in (unknown)::_148_1146)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1147))
in (FStar_Syntax_Util.mk_app c_pure _148_1148))
in (let _148_1150 = (let _148_1149 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_148_1149)::[])
in (_148_1151)::_148_1150))
in (unknown)::_148_1152)
in (unknown)::_148_1153)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1154))
in (FStar_Syntax_Util.mk_app c_app _148_1155))
in (let _148_1156 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _148_1156 body ret_tot_wp_a))))))
in (

let wp_assert = (normalize_and_make_binders_explicit wp_assert)
in (

let _57_2641 = (let _148_1157 = (FStar_Syntax_Util.abs binders wp_assert None)
in (check "wp_assert" _148_1157))
in (

let wp_assume = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_imp = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (

let body = (let _148_1171 = (let _148_1170 = (let _148_1169 = (let _148_1168 = (let _148_1167 = (let _148_1164 = (let _148_1163 = (let _148_1162 = (let _148_1161 = (let _148_1160 = (let _148_1159 = (let _148_1158 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _148_1158))
in (_148_1159)::[])
in (FStar_Syntax_Util.mk_app l_imp _148_1160))
in (_148_1161)::[])
in (unknown)::_148_1162)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1163))
in (FStar_Syntax_Util.mk_app c_pure _148_1164))
in (let _148_1166 = (let _148_1165 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_148_1165)::[])
in (_148_1167)::_148_1166))
in (unknown)::_148_1168)
in (unknown)::_148_1169)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1170))
in (FStar_Syntax_Util.mk_app c_app _148_1171))
in (let _148_1172 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _148_1172 body ret_tot_wp_a))))))
in (

let wp_assume = (normalize_and_make_binders_explicit wp_assume)
in (

let _57_2649 = (let _148_1173 = (FStar_Syntax_Util.abs binders wp_assume None)
in (check "wp_assume" _148_1173))
in (

let tforall = (let _148_1176 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _148_1175 = (let _148_1174 = (FStar_Syntax_Syntax.as_arg unknown)
in (_148_1174)::[])
in (FStar_Syntax_Util.mk_app _148_1176 _148_1175)))
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _148_1180 = (let _148_1178 = (let _148_1177 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _148_1177))
in (_148_1178)::[])
in (let _148_1179 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1180 _148_1179)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (let _148_1193 = (let _148_1192 = (let _148_1191 = (let _148_1190 = (let _148_1189 = (let _148_1181 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((unknown)::(tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _148_1181))
in (let _148_1188 = (let _148_1187 = (let _148_1186 = (let _148_1185 = (let _148_1184 = (let _148_1183 = (let _148_1182 = (FStar_Syntax_Syntax.bv_to_name f)
in (_148_1182)::[])
in (unknown)::_148_1183)
in (unknown)::_148_1184)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1185))
in (FStar_Syntax_Util.mk_app c_push _148_1186))
in (_148_1187)::[])
in (_148_1189)::_148_1188))
in (unknown)::_148_1190)
in (unknown)::_148_1191)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1192))
in (FStar_Syntax_Util.mk_app c_app _148_1193))
in (let _148_1194 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_Syntax_Util.abs _148_1194 body ret_tot_wp_a))))))
in (

let wp_close = (normalize_and_make_binders_explicit wp_close)
in (

let _57_2658 = (let _148_1195 = (FStar_Syntax_Util.abs binders wp_close None)
in (check "wp_close" _148_1195))
in (

let ret_tot_type0 = (let _148_1198 = (let _148_1197 = (let _148_1196 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_1196))
in FStar_Util.Inl (_148_1197))
in Some (_148_1198))
in (

let mk_forall = (fun x body -> (

let tforall = (let _148_1205 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _148_1204 = (let _148_1203 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (_148_1203)::[])
in (FStar_Syntax_Util.mk_app _148_1205 _148_1204)))
in (let _148_1212 = (let _148_1211 = (let _148_1210 = (let _148_1209 = (let _148_1208 = (let _148_1207 = (let _148_1206 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_1206)::[])
in (FStar_Syntax_Util.abs _148_1207 body ret_tot_type0))
in (FStar_Syntax_Syntax.as_arg _148_1208))
in (_148_1209)::[])
in (tforall, _148_1210))
in FStar_Syntax_Syntax.Tm_app (_148_1211))
in (FStar_Syntax_Syntax.mk _148_1212 None FStar_Range.dummyRange))))
in (

let rec mk_leq = (fun t x y -> (match ((let _148_1220 = (let _148_1219 = (FStar_Syntax_Subst.compress t)
in (normalize _148_1219))
in _148_1220.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_2670) -> begin
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

let body = (let _148_1232 = (let _148_1222 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _148_1221 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_leq a _148_1222 _148_1221)))
in (let _148_1231 = (let _148_1230 = (let _148_1225 = (let _148_1224 = (let _148_1223 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _148_1223))
in (_148_1224)::[])
in (FStar_Syntax_Util.mk_app x _148_1225))
in (let _148_1229 = (let _148_1228 = (let _148_1227 = (let _148_1226 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _148_1226))
in (_148_1227)::[])
in (FStar_Syntax_Util.mk_app y _148_1228))
in (mk_leq b _148_1230 _148_1229)))
in (FStar_Syntax_Util.mk_imp _148_1232 _148_1231)))
in (let _148_1233 = (mk_forall a2 body)
in (mk_forall a1 _148_1233))))))
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let _57_2706 = t
in (let _148_1237 = (let _148_1236 = (let _148_1235 = (let _148_1234 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _148_1234))
in ((binder)::[], _148_1235))
in FStar_Syntax_Syntax.Tm_arrow (_148_1236))
in {FStar_Syntax_Syntax.n = _148_1237; FStar_Syntax_Syntax.tk = _57_2706.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2706.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2706.FStar_Syntax_Syntax.vars}))
in (mk_leq t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_57_2710) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _57_2713 -> begin
(FStar_Syntax_Util.mk_eq t t x y)
end))
in (

let stronger = (

let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (

let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (

let body = (let _148_1239 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _148_1238 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_leq wp_a _148_1239 _148_1238)))
in (let _148_1240 = (FStar_Syntax_Syntax.binders_of_list ((wp1)::(wp2)::[]))
in (FStar_Syntax_Util.abs _148_1240 body ret_tot_type0)))))
in (

let _57_2718 = (let _148_1244 = (let _148_1243 = (let _148_1242 = (let _148_1241 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_1241)::[])
in (FStar_List.append binders _148_1242))
in (FStar_Syntax_Util.abs _148_1243 stronger None))
in (check "stronger" _148_1244))
in (

let null_wp = (Prims.snd ed.FStar_Syntax_Syntax.null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (let _148_1252 = (let _148_1251 = (let _148_1250 = (let _148_1247 = (let _148_1246 = (let _148_1245 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _148_1245))
in (_148_1246)::[])
in (FStar_Syntax_Util.mk_app null_wp _148_1247))
in (let _148_1249 = (let _148_1248 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_148_1248)::[])
in (_148_1250)::_148_1249))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1251))
in (FStar_Syntax_Util.mk_app stronger _148_1252))
in (let _148_1253 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_Syntax_Util.abs _148_1253 body ret_tot_type0))))
in (

let wp_trivial = (normalize_and_make_binders_explicit wp_trivial)
in (

let _57_2725 = (let _148_1254 = (FStar_Syntax_Util.abs binders wp_trivial None)
in (check "wp_trivial" _148_1254))
in (

let _57_2727 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2727.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2727.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2727.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2727.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2727.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _57_2727.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _57_2727.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = ([], wp_if_then_else); FStar_Syntax_Syntax.ite_wp = _57_2727.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _57_2727.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = ([], wp_close); FStar_Syntax_Syntax.assert_p = ([], wp_assert); FStar_Syntax_Syntax.assume_p = ([], wp_assume); FStar_Syntax_Syntax.null_wp = _57_2727.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = ([], wp_trivial); FStar_Syntax_Syntax.repr = _57_2727.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _57_2727.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _57_2727.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _57_2727.FStar_Syntax_Syntax.actions}))))))))))))))))))))))))))))))))))))))
end))))))))


let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  effect_cost  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed is_for_free -> (

let _57_2732 = ()
in (

let _57_2736 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_57_2736) with
| (binders_un, signature_un) -> begin
(

let _57_2741 = (tc_tparams env0 binders_un)
in (match (_57_2741) with
| (binders, env, _57_2740) -> begin
(

let _57_2745 = (tc_trivial_guard env signature_un)
in (match (_57_2745) with
| (signature, _57_2744) -> begin
(

let ed = (

let _57_2746 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2746.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2746.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2746.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _57_2746.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _57_2746.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _57_2746.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _57_2746.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _57_2746.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _57_2746.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _57_2746.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _57_2746.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _57_2746.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _57_2746.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _57_2746.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _57_2746.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _57_2746.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _57_2746.FStar_Syntax_Syntax.actions})
in (

let _57_2752 = (open_effect_decl env ed)
in (match (_57_2752) with
| (ed, a, wp_a) -> begin
(

let get_effect_signature = (fun _57_2754 -> (match (()) with
| () -> begin
(

let _57_2758 = (tc_trivial_guard env signature_un)
in (match (_57_2758) with
| (signature, _57_2757) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (

let env = (let _148_1263 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _148_1263))
in (

let _57_2760 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _148_1266 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _148_1265 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _148_1264 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checking effect signature: %s %s : %s\n" _148_1266 _148_1265 _148_1264))))
end else begin
()
end
in (

let check_and_gen' = (fun env _57_2767 k -> (match (_57_2767) with
| (_57_2765, t) -> begin
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

let return_wp = (

let expected_k = (let _148_1278 = (let _148_1276 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1275 = (let _148_1274 = (let _148_1273 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _148_1273))
in (_148_1274)::[])
in (_148_1276)::_148_1275))
in (let _148_1277 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _148_1278 _148_1277)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let _57_2776 = (get_effect_signature ())
in (match (_57_2776) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _148_1282 = (let _148_1280 = (let _148_1279 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _148_1279))
in (_148_1280)::[])
in (let _148_1281 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _148_1282 _148_1281)))
in (

let expected_k = (let _148_1293 = (let _148_1291 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _148_1290 = (let _148_1289 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1288 = (let _148_1287 = (FStar_Syntax_Syntax.mk_binder b)
in (let _148_1286 = (let _148_1285 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _148_1284 = (let _148_1283 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (_148_1283)::[])
in (_148_1285)::_148_1284))
in (_148_1287)::_148_1286))
in (_148_1289)::_148_1288))
in (_148_1291)::_148_1290))
in (let _148_1292 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _148_1293 _148_1292)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (let _148_1295 = (let _148_1294 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_1294 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _148_1295))
in (

let expected_k = (let _148_1304 = (let _148_1302 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1301 = (let _148_1300 = (FStar_Syntax_Syntax.mk_binder p)
in (let _148_1299 = (let _148_1298 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _148_1297 = (let _148_1296 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1296)::[])
in (_148_1298)::_148_1297))
in (_148_1300)::_148_1299))
in (_148_1302)::_148_1301))
in (let _148_1303 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1304 _148_1303)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (let _148_1309 = (let _148_1307 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1306 = (let _148_1305 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1305)::[])
in (_148_1307)::_148_1306))
in (let _148_1308 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1309 _148_1308)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let _57_2788 = (FStar_Syntax_Util.type_u ())
in (match (_57_2788) with
| (t, _57_2787) -> begin
(

let expected_k = (let _148_1316 = (let _148_1314 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1313 = (let _148_1312 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _148_1311 = (let _148_1310 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1310)::[])
in (_148_1312)::_148_1311))
in (_148_1314)::_148_1313))
in (let _148_1315 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _148_1316 _148_1315)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (let _148_1318 = (let _148_1317 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_1317 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _148_1318))
in (

let b_wp_a = (let _148_1322 = (let _148_1320 = (let _148_1319 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _148_1319))
in (_148_1320)::[])
in (let _148_1321 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1322 _148_1321)))
in (

let expected_k = (let _148_1329 = (let _148_1327 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1326 = (let _148_1325 = (FStar_Syntax_Syntax.mk_binder b)
in (let _148_1324 = (let _148_1323 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_148_1323)::[])
in (_148_1325)::_148_1324))
in (_148_1327)::_148_1326))
in (let _148_1328 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1329 _148_1328)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (let _148_1338 = (let _148_1336 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1335 = (let _148_1334 = (let _148_1331 = (let _148_1330 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_1330 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _148_1331))
in (let _148_1333 = (let _148_1332 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1332)::[])
in (_148_1334)::_148_1333))
in (_148_1336)::_148_1335))
in (let _148_1337 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1338 _148_1337)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _148_1347 = (let _148_1345 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1344 = (let _148_1343 = (let _148_1340 = (let _148_1339 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _148_1339 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _148_1340))
in (let _148_1342 = (let _148_1341 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1341)::[])
in (_148_1343)::_148_1342))
in (_148_1345)::_148_1344))
in (let _148_1346 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1347 _148_1346)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _148_1350 = (let _148_1348 = (FStar_Syntax_Syntax.mk_binder a)
in (_148_1348)::[])
in (let _148_1349 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _148_1350 _148_1349)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let _57_2804 = (FStar_Syntax_Util.type_u ())
in (match (_57_2804) with
| (t, _57_2803) -> begin
(

let expected_k = (let _148_1355 = (let _148_1353 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1352 = (let _148_1351 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1351)::[])
in (_148_1353)::_148_1352))
in (let _148_1354 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _148_1355 _148_1354)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let _57_2928 = if ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) || (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable))) then begin
(

let repr = (

let _57_2810 = (FStar_Syntax_Util.type_u ())
in (match (_57_2810) with
| (t, _57_2809) -> begin
(

let expected_k = (let _148_1360 = (let _148_1358 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1357 = (let _148_1356 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_148_1356)::[])
in (_148_1358)::_148_1357))
in (let _148_1359 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _148_1360 _148_1359)))
in (tc_check_trivial_guard env ed.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (let _148_1371 = (let _148_1370 = (let _148_1369 = (FStar_Syntax_Util.un_uinst repr)
in (let _148_1368 = (let _148_1367 = (FStar_Syntax_Syntax.as_arg t)
in (let _148_1366 = (let _148_1365 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_1365)::[])
in (_148_1367)::_148_1366))
in (_148_1369, _148_1368)))
in FStar_Syntax_Syntax.Tm_app (_148_1370))
in (FStar_Syntax_Syntax.mk _148_1371 None FStar_Range.dummyRange)))
in (

let mk_repr = (fun a wp -> (let _148_1376 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_repr' _148_1376 wp)))
in (

let destruct_repr = (fun t -> (match ((let _148_1379 = (FStar_Syntax_Subst.compress t)
in _148_1379.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_57_2822, ((t, _57_2829))::((wp, _57_2825))::[]) -> begin
(t, wp)
end
| _57_2835 -> begin
(FStar_All.failwith "Unexpected repr type")
end))
in (

let bind_repr = (

let r = (let _148_1380 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_0 FStar_Syntax_Syntax.Delta_constant None)
in (FStar_All.pipe_right _148_1380 FStar_Syntax_Syntax.fv_to_tm))
in (

let _57_2839 = (get_effect_signature ())
in (match (_57_2839) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _148_1384 = (let _148_1382 = (let _148_1381 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _148_1381))
in (_148_1382)::[])
in (let _148_1383 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _148_1384 _148_1383)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" None a_wp_b)
in (

let x_a = (let _148_1385 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _148_1385))
in (

let wp_g_x = (let _148_1389 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (let _148_1388 = (let _148_1387 = (let _148_1386 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _148_1386))
in (_148_1387)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _148_1389 _148_1388 None FStar_Range.dummyRange)))
in (

let res = (

let wp = (let _148_1401 = (let _148_1390 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right _148_1390 Prims.snd))
in (let _148_1400 = (let _148_1399 = (let _148_1398 = (let _148_1397 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _148_1396 = (let _148_1395 = (FStar_Syntax_Syntax.bv_to_name b)
in (let _148_1394 = (let _148_1393 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (let _148_1392 = (let _148_1391 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (_148_1391)::[])
in (_148_1393)::_148_1392))
in (_148_1395)::_148_1394))
in (_148_1397)::_148_1396))
in (r)::_148_1398)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1399))
in (FStar_Syntax_Syntax.mk_Tm_app _148_1401 _148_1400 None FStar_Range.dummyRange)))
in (mk_repr b wp))
in (

let expected_k = (let _148_1421 = (let _148_1419 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1418 = (let _148_1417 = (FStar_Syntax_Syntax.mk_binder b)
in (let _148_1416 = (let _148_1415 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (let _148_1414 = (let _148_1413 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (let _148_1412 = (let _148_1411 = (let _148_1403 = (let _148_1402 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a _148_1402))
in (FStar_Syntax_Syntax.null_binder _148_1403))
in (let _148_1410 = (let _148_1409 = (let _148_1408 = (let _148_1407 = (let _148_1404 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_148_1404)::[])
in (let _148_1406 = (let _148_1405 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _148_1405))
in (FStar_Syntax_Util.arrow _148_1407 _148_1406)))
in (FStar_Syntax_Syntax.null_binder _148_1408))
in (_148_1409)::[])
in (_148_1411)::_148_1410))
in (_148_1413)::_148_1412))
in (_148_1415)::_148_1414))
in (_148_1417)::_148_1416))
in (_148_1419)::_148_1418))
in (let _148_1420 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _148_1421 _148_1420)))
in (

let _57_2853 = (tc_tot_or_gtot_term env expected_k)
in (match (_57_2853) with
| (expected_k, _57_2850, _57_2852) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_repr expected_k))
end)))))))))
end)))
in (

let return_repr = (

let x_a = (let _148_1422 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _148_1422))
in (

let res = (

let wp = (let _148_1429 = (let _148_1423 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right _148_1423 Prims.snd))
in (let _148_1428 = (let _148_1427 = (let _148_1426 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _148_1425 = (let _148_1424 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (_148_1424)::[])
in (_148_1426)::_148_1425))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _148_1427))
in (FStar_Syntax_Syntax.mk_Tm_app _148_1429 _148_1428 None FStar_Range.dummyRange)))
in (mk_repr a wp))
in (

let expected_k = (let _148_1434 = (let _148_1432 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1431 = (let _148_1430 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_148_1430)::[])
in (_148_1432)::_148_1431))
in (let _148_1433 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _148_1434 _148_1433)))
in (

let _57_2865 = (tc_tot_or_gtot_term env expected_k)
in (match (_57_2865) with
| (expected_k, _57_2862, _57_2864) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let _57_2869 = (check_and_gen' env ed.FStar_Syntax_Syntax.return_repr expected_k)
in (match (_57_2869) with
| (univs, repr) -> begin
(match (univs) with
| [] -> begin
([], repr)
end
| _57_2872 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected universe-polymorphic return for effect", repr.FStar_Syntax_Syntax.pos))))
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let _57_2879 = (tc_tot_or_gtot_term env act.FStar_Syntax_Syntax.action_defn)
in (match (_57_2879) with
| (act_defn, c, g_a) -> begin
(

let _57_2899 = (match ((let _148_1437 = (FStar_Syntax_Subst.compress c.FStar_Syntax_Syntax.res_typ)
in _148_1437.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _57_2887 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_2887) with
| (bs, _57_2886) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (let _148_1438 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs _148_1438))
in (

let _57_2894 = (tc_tot_or_gtot_term env k)
in (match (_57_2894) with
| (k, _57_2892, g) -> begin
(k, g)
end))))
end))
end
| _57_2896 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Actions must have function types", act_defn.FStar_Syntax_Syntax.pos))))
end)
in (match (_57_2899) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env c.FStar_Syntax_Syntax.res_typ expected_k)
in (

let _57_2901 = (let _148_1440 = (let _148_1439 = (FStar_TypeChecker_Rel.conj_guard g_k g)
in (FStar_TypeChecker_Rel.conj_guard g_a _148_1439))
in (FStar_TypeChecker_Rel.force_trivial_guard env _148_1440))
in (

let act_ty = (match ((let _148_1441 = (FStar_Syntax_Subst.compress expected_k)
in _148_1441.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _57_2909 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_2909) with
| (bs, c) -> begin
(

let _57_2912 = (destruct_repr (FStar_Syntax_Util.comp_result c))
in (match (_57_2912) with
| (a, wp) -> begin
(

let c = (let _148_1443 = (let _148_1442 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_1442)::[])
in {FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a; FStar_Syntax_Syntax.effect_args = _148_1443; FStar_Syntax_Syntax.flags = []})
in (let _148_1444 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Util.arrow bs _148_1444)))
end))
end))
end
| _57_2915 -> begin
(FStar_All.failwith "")
end)
in (

let _57_2919 = (FStar_TypeChecker_Util.generalize_universes env act_defn)
in (match (_57_2919) with
| (univs, act_defn) -> begin
(

let act_ty = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env act_ty)
in (

let _57_2921 = act
in {FStar_Syntax_Syntax.action_name = _57_2921.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = act_defn; FStar_Syntax_Syntax.action_typ = act_ty}))
end)))))
end))
end)))
in (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.map check_action)))
in (repr, bind_repr, return_repr, actions))))))))
end else begin
(ed.FStar_Syntax_Syntax.repr, ed.FStar_Syntax_Syntax.bind_repr, ed.FStar_Syntax_Syntax.return_repr, ed.FStar_Syntax_Syntax.actions)
end
in (match (_57_2928) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t = (let _148_1445 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _148_1445))
in (

let _57_2932 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_57_2932) with
| (univs, t) -> begin
(

let _57_2948 = (match ((let _148_1447 = (let _148_1446 = (FStar_Syntax_Subst.compress t)
in _148_1446.FStar_Syntax_Syntax.n)
in (binders, _148_1447))) with
| ([], _57_2935) -> begin
([], t)
end
| (_57_2938, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _57_2945 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_2948) with
| (binders, signature) -> begin
(

let close = (fun n ts -> (

let ts = (let _148_1452 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _148_1452))
in (

let _57_2953 = ()
in ts)))
in (

let close_action = (fun act -> (

let _57_2959 = (close (- (1)) (act.FStar_Syntax_Syntax.action_univs, act.FStar_Syntax_Syntax.action_defn))
in (match (_57_2959) with
| (univs, defn) -> begin
(

let _57_2962 = (close (- (1)) (act.FStar_Syntax_Syntax.action_univs, act.FStar_Syntax_Syntax.action_typ))
in (match (_57_2962) with
| (univs', typ) -> begin
(

let _57_2963 = ()
in (

let _57_2965 = act
in {FStar_Syntax_Syntax.action_name = _57_2965.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ}))
end))
end)))
in (

let ed = (

let _57_2967 = ed
in (let _148_1469 = (close 0 return_wp)
in (let _148_1468 = (close 1 bind_wp)
in (let _148_1467 = (close 0 if_then_else)
in (let _148_1466 = (close 0 ite_wp)
in (let _148_1465 = (close 0 stronger)
in (let _148_1464 = (close 1 close_wp)
in (let _148_1463 = (close 0 assert_p)
in (let _148_1462 = (close 0 assume_p)
in (let _148_1461 = (close 0 null_wp)
in (let _148_1460 = (close 0 trivial_wp)
in (let _148_1459 = (let _148_1455 = (close 0 ([], repr))
in (Prims.snd _148_1455))
in (let _148_1458 = (close 0 return_repr)
in (let _148_1457 = (close 1 bind_repr)
in (let _148_1456 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.qualifiers = _57_2967.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2967.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _148_1469; FStar_Syntax_Syntax.bind_wp = _148_1468; FStar_Syntax_Syntax.if_then_else = _148_1467; FStar_Syntax_Syntax.ite_wp = _148_1466; FStar_Syntax_Syntax.stronger = _148_1465; FStar_Syntax_Syntax.close_wp = _148_1464; FStar_Syntax_Syntax.assert_p = _148_1463; FStar_Syntax_Syntax.assume_p = _148_1462; FStar_Syntax_Syntax.null_wp = _148_1461; FStar_Syntax_Syntax.trivial = _148_1460; FStar_Syntax_Syntax.repr = _148_1459; FStar_Syntax_Syntax.return_repr = _148_1458; FStar_Syntax_Syntax.bind_repr = _148_1457; FStar_Syntax_Syntax.actions = _148_1456})))))))))))))))
in (

let _57_2970 = if ((FStar_TypeChecker_Env.debug env FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EffDecl")))) then begin
(let _148_1470 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _148_1470))
end else begin
()
end
in ed))))
end))
end)))
end)))))))))))))))))
end)))
end))
end))
end))))


let tc_lex_t = (fun env ses quals lids -> (

let _57_2976 = ()
in (

let _57_2984 = ()
in (match (ses) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _57_3013, _57_3015, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _57_3004, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _57_2993, r2))::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
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

let lex_top_t = (let _148_1478 = (let _148_1477 = (let _148_1476 = (let _148_1475 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _148_1475 FStar_Syntax_Syntax.Delta_constant None))
in (_148_1476, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_148_1477))
in (FStar_Syntax_Syntax.mk _148_1478 None r1))
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

let a = (let _148_1479 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _148_1479))
in (

let hd = (let _148_1480 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _148_1480))
in (

let tl = (let _148_1485 = (let _148_1484 = (let _148_1483 = (let _148_1482 = (let _148_1481 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _148_1481 FStar_Syntax_Syntax.Delta_constant None))
in (_148_1482, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_148_1483))
in (FStar_Syntax_Syntax.mk _148_1484 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _148_1485))
in (

let res = (let _148_1489 = (let _148_1488 = (let _148_1487 = (let _148_1486 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _148_1486 FStar_Syntax_Syntax.Delta_constant None))
in (_148_1487, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_148_1488))
in (FStar_Syntax_Syntax.mk _148_1489 None r2))
in (let _148_1490 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _148_1490))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _148_1492 = (let _148_1491 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _148_1491))
in FStar_Syntax_Syntax.Sig_bundle (_148_1492)))))))))))))))
end
| _57_3039 -> begin
(let _148_1494 = (let _148_1493 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _148_1493))
in (FStar_All.failwith _148_1494))
end))))


let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _148_1508 = (let _148_1507 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _148_1507))
in (FStar_TypeChecker_Errors.diag r _148_1508)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let _57_3061 = ()
in (

let _57_3063 = (warn_positivity tc r)
in (

let _57_3067 = (FStar_Syntax_Subst.open_term tps k)
in (match (_57_3067) with
| (tps, k) -> begin
(

let _57_3072 = (tc_binders env tps)
in (match (_57_3072) with
| (tps, env_tps, guard_params, us) -> begin
(

let _57_3075 = (FStar_Syntax_Util.arrow_formals k)
in (match (_57_3075) with
| (indices, t) -> begin
(

let _57_3080 = (tc_binders env_tps indices)
in (match (_57_3080) with
| (indices, env', guard_indices, us') -> begin
(

let _57_3088 = (

let _57_3085 = (tc_tot_or_gtot_term env' t)
in (match (_57_3085) with
| (t, _57_3083, g) -> begin
(let _148_1515 = (let _148_1514 = (let _148_1513 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params _148_1513))
in (FStar_TypeChecker_Rel.discharge_guard env' _148_1514))
in (t, _148_1515))
end))
in (match (_57_3088) with
| (t, guard) -> begin
(

let k = (let _148_1516 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _148_1516))
in (

let _57_3092 = (FStar_Syntax_Util.type_u ())
in (match (_57_3092) with
| (t_type, u) -> begin
(

let _57_3093 = (let _148_1517 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _148_1517))
in (

let t_tc = (let _148_1518 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _148_1518))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _148_1519 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) ([], t_tc))
in (_148_1519, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u, guard)))))))
end)))
end))
end))
end))
end))
end))))
end
| _57_3100 -> begin
(FStar_All.failwith "impossible")
end))
in (

let positive_if_pure = (fun _57_3102 l -> ())
in (

let tc_data = (fun env tcs _57_7 -> (match (_57_7) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let _57_3119 = ()
in (

let _57_3154 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _57_3123 -> (match (_57_3123) with
| (se, u_tc) -> begin
if (let _148_1532 = (let _148_1531 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _148_1531))
in (FStar_Ident.lid_equals tc_lid _148_1532)) then begin
(

let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_3125, _57_3127, tps, _57_3130, _57_3132, _57_3134, _57_3136, _57_3138) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _57_3144 -> (match (_57_3144) with
| (x, _57_3143) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _57_3146 -> begin
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
in (match (_57_3154) with
| (tps, u_tc) -> begin
(

let _57_3174 = (match ((let _148_1534 = (FStar_Syntax_Subst.compress t)
in _148_1534.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _57_3162 = (FStar_Util.first_N ntps bs)
in (match (_57_3162) with
| (_57_3160, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _57_3168 -> (match (_57_3168) with
| (x, _57_3167) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _148_1537 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _148_1537))))
end))
end
| _57_3171 -> begin
([], t)
end)
in (match (_57_3174) with
| (arguments, result) -> begin
(

let _57_3175 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1540 = (FStar_Syntax_Print.lid_to_string c)
in (let _148_1539 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _148_1538 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _148_1540 _148_1539 _148_1538))))
end else begin
()
end
in (

let _57_3180 = (tc_tparams env arguments)
in (match (_57_3180) with
| (arguments, env', us) -> begin
(

let _57_3184 = (tc_trivial_guard env' result)
in (match (_57_3184) with
| (result, _57_3183) -> begin
(

let _57_3188 = (FStar_Syntax_Util.head_and_args result)
in (match (_57_3188) with
| (head, _57_3187) -> begin
(

let _57_3193 = (match ((let _148_1541 = (FStar_Syntax_Subst.compress head)
in _148_1541.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _57_3192 -> begin
(let _148_1546 = (let _148_1545 = (let _148_1544 = (let _148_1543 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _148_1542 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _148_1543 _148_1542)))
in (_148_1544, r))
in FStar_Syntax_Syntax.Error (_148_1545))
in (Prims.raise _148_1546))
end)
in (

let g = (FStar_List.fold_left2 (fun g _57_3199 u_x -> (match (_57_3199) with
| (x, _57_3198) -> begin
(

let _57_3201 = ()
in (let _148_1550 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _148_1550)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _148_1554 = (let _148_1552 = (FStar_All.pipe_right tps (FStar_List.map (fun _57_3207 -> (match (_57_3207) with
| (x, _57_3206) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _148_1552 arguments))
in (let _148_1553 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _148_1554 _148_1553)))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _57_3210 -> begin
(FStar_All.failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let _57_3216 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_8 -> (match (_57_8) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_3220, _57_3222, tps, k, _57_3226, _57_3228, _57_3230, _57_3232) -> begin
(let _148_1565 = (let _148_1564 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _148_1564))
in (FStar_Syntax_Syntax.null_binder _148_1565))
end
| _57_3236 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _57_9 -> (match (_57_9) with
| FStar_Syntax_Syntax.Sig_datacon (_57_3240, _57_3242, t, _57_3245, _57_3247, _57_3249, _57_3251, _57_3253) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _57_3257 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let t = (let _148_1567 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _148_1567))
in (

let _57_3260 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1568 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _148_1568))
end else begin
()
end
in (

let _57_3264 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_57_3264) with
| (uvs, t) -> begin
(

let _57_3266 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1572 = (let _148_1570 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _148_1570 (FStar_String.concat ", ")))
in (let _148_1571 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _148_1572 _148_1571)))
end else begin
()
end
in (

let _57_3270 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_57_3270) with
| (uvs, t) -> begin
(

let _57_3274 = (FStar_Syntax_Util.arrow_formals t)
in (match (_57_3274) with
| (args, _57_3273) -> begin
(

let _57_3277 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_57_3277) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _57_3281 se -> (match (_57_3281) with
| (x, _57_3280) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3285, tps, _57_3288, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let _57_3311 = (match ((let _148_1575 = (FStar_Syntax_Subst.compress ty)
in _148_1575.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _57_3302 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_57_3302) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _57_3305 -> begin
(let _148_1576 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _148_1576 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _57_3308 -> begin
([], ty)
end)
in (match (_57_3311) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _57_3313 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| _57_3317 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _148_1577 -> FStar_Syntax_Syntax.U_name (_148_1577))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_10 -> (match (_57_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3322, _57_3324, _57_3326, _57_3328, _57_3330, _57_3332, _57_3334) -> begin
(tc, uvs_universes)
end
| _57_3338 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _57_3343 d -> (match (_57_3343) with
| (t, _57_3342) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _57_3347, _57_3349, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _148_1581 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _148_1581 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _57_3359 -> begin
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

let _57_3369 = (FStar_All.pipe_right ses (FStar_List.partition (fun _57_11 -> (match (_57_11) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_3363) -> begin
true
end
| _57_3366 -> begin
false
end))))
in (match (_57_3369) with
| (tys, datas) -> begin
(

let _57_3376 = if (FStar_All.pipe_right datas (FStar_Util.for_some (fun _57_12 -> (match (_57_12) with
| FStar_Syntax_Syntax.Sig_datacon (_57_3372) -> begin
false
end
| _57_3375 -> begin
true
end)))) then begin
(let _148_1586 = (let _148_1585 = (let _148_1584 = (FStar_TypeChecker_Env.get_range env)
in ("Mutually defined type contains a non-inductive element", _148_1584))
in FStar_Syntax_Syntax.Error (_148_1585))
in (Prims.raise _148_1586))
end else begin
()
end
in (

let env0 = env
in (

let _57_3395 = (FStar_List.fold_right (fun tc _57_3383 -> (match (_57_3383) with
| (env, all_tcs, g) -> begin
(

let _57_3388 = (tc_tycon env tc)
in (match (_57_3388) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (

let _57_3390 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1589 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _148_1589))
end else begin
()
end
in (let _148_1591 = (let _148_1590 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g _148_1590))
in (env, ((tc, tc_u))::all_tcs, _148_1591))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_3395) with
| (env, tcs, g) -> begin
(

let _57_3405 = (FStar_List.fold_right (fun se _57_3399 -> (match (_57_3399) with
| (datas, g) -> begin
(

let _57_3402 = (tc_data env tcs se)
in (match (_57_3402) with
| (data, g') -> begin
(let _148_1594 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _148_1594))
end))
end)) datas ([], g))
in (match (_57_3405) with
| (datas, g) -> begin
(

let _57_3408 = (let _148_1595 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _148_1595 datas))
in (match (_57_3408) with
| (tcs, datas) -> begin
(let _148_1597 = (let _148_1596 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _148_1596))
in FStar_Syntax_Syntax.Sig_bundle (_148_1597))
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
in (let _148_1602 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _148_1602))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let se = (tc_inductive env ses quals lids)
in (let _148_1603 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _148_1603))))
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

let _57_3446 = (set_options FStar_Options.Set o)
in (se, env))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(

let _57_3450 = (let _148_1608 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _148_1608 Prims.ignore))
in (

let _57_3455 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _57_3457 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
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
in (

let _57_3480 = (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun _57_3475 a -> (match (_57_3475) with
| (env, ses) -> begin
(

let se_let = (FStar_Syntax_Util.action_as_lb a)
in (let _148_1611 = (FStar_TypeChecker_Env.push_sigelt env se_let)
in (_148_1611, (se_let)::ses)))
end)) (env, (se)::[])))
in (match (_57_3480) with
| (env, ses) -> begin
(se, env)
end)))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(

let ed_src = (FStar_TypeChecker_Env.get_effect_decl env sub.FStar_Syntax_Syntax.source)
in (

let ed_tgt = (FStar_TypeChecker_Env.get_effect_decl env sub.FStar_Syntax_Syntax.target)
in (

let _57_3489 = (let _148_1612 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _148_1612))
in (match (_57_3489) with
| (a, wp_a_src) -> begin
(

let _57_3492 = (let _148_1613 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _148_1613))
in (match (_57_3492) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _148_1617 = (let _148_1616 = (let _148_1615 = (let _148_1614 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _148_1614))
in FStar_Syntax_Syntax.NT (_148_1615))
in (_148_1616)::[])
in (FStar_Syntax_Subst.subst _148_1617 wp_b_tgt))
in (

let expected_k = (let _148_1622 = (let _148_1620 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1619 = (let _148_1618 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_148_1618)::[])
in (_148_1620)::_148_1619))
in (let _148_1621 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _148_1622 _148_1621)))
in (

let lift_wp = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift_wp) expected_k)
in (

let repr_type = (fun eff_name a wp -> (

let no_reify = (fun l -> (let _148_1634 = (let _148_1633 = (let _148_1632 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _148_1631 = (FStar_TypeChecker_Env.get_range env)
in (_148_1632, _148_1631)))
in FStar_Syntax_Syntax.Error (_148_1633))
in (Prims.raise _148_1634)))
in (match ((FStar_TypeChecker_Env.effect_decl_opt env eff_name)) with
| None -> begin
(no_reify eff_name)
end
| Some (ed) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((FStar_Syntax_Syntax.U_unknown)::[]) env ed ([], ed.FStar_Syntax_Syntax.repr))
in if (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)))) then begin
(no_reify eff_name)
end else begin
(let _148_1641 = (let _148_1639 = (let _148_1638 = (let _148_1637 = (FStar_Syntax_Syntax.as_arg a)
in (let _148_1636 = (let _148_1635 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_1635)::[])
in (_148_1637)::_148_1636))
in (repr, _148_1638))
in FStar_Syntax_Syntax.Tm_app (_148_1639))
in (let _148_1640 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _148_1641 None _148_1640)))
end)
end)))
in (

let lift = (match (sub.FStar_Syntax_Syntax.lift) with
| None -> begin
None
end
| Some (_57_3508, lift) -> begin
(

let _57_3514 = (let _148_1642 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _148_1642))
in (match (_57_3514) with
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

let lift_wp_a = (let _148_1649 = (let _148_1647 = (let _148_1646 = (let _148_1645 = (FStar_Syntax_Syntax.as_arg a_typ)
in (let _148_1644 = (let _148_1643 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (_148_1643)::[])
in (_148_1645)::_148_1644))
in ((Prims.snd sub.FStar_Syntax_Syntax.lift_wp), _148_1646))
in FStar_Syntax_Syntax.Tm_app (_148_1647))
in (let _148_1648 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _148_1649 None _148_1648)))
in (repr_type sub.FStar_Syntax_Syntax.target a_typ lift_wp_a))
in (

let expected_k = (let _148_1656 = (let _148_1654 = (FStar_Syntax_Syntax.mk_binder a)
in (let _148_1653 = (let _148_1652 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (let _148_1651 = (let _148_1650 = (FStar_Syntax_Syntax.null_binder repr_f)
in (_148_1650)::[])
in (_148_1652)::_148_1651))
in (_148_1654)::_148_1653))
in (let _148_1655 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow _148_1656 _148_1655)))
in (

let _57_3527 = (tc_tot_or_gtot_term env expected_k)
in (match (_57_3527) with
| (expected_k, _57_3524, _57_3526) -> begin
(

let lift = (check_and_gen env lift expected_k)
in Some (lift))
end))))))))
end))
end)
in (

let sub = (

let _57_3530 = sub
in {FStar_Syntax_Syntax.source = _57_3530.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _57_3530.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift})
in (

let se = FStar_Syntax_Syntax.Sig_sub_effect ((sub, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(

let _57_3543 = ()
in (

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _57_3549 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_57_3549) with
| (tps, c) -> begin
(

let _57_3553 = (tc_tparams env tps)
in (match (_57_3553) with
| (tps, env, us) -> begin
(

let _57_3557 = (tc_comp env c)
in (match (_57_3557) with
| (c, u, g) -> begin
(

let _57_3558 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let _57_3564 = (let _148_1657 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _148_1657))
in (match (_57_3564) with
| (uvs, t) -> begin
(

let _57_3583 = (match ((let _148_1659 = (let _148_1658 = (FStar_Syntax_Subst.compress t)
in _148_1658.FStar_Syntax_Syntax.n)
in (tps, _148_1659))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_57_3567, c)) -> begin
([], c)
end
| (_57_3573, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _57_3580 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_3583) with
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

let _57_3594 = ()
in (

let _57_3598 = (let _148_1661 = (let _148_1660 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _148_1660))
in (check_and_gen env t _148_1661))
in (match (_57_3598) with
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

let _57_3611 = (FStar_Syntax_Util.type_u ())
in (match (_57_3611) with
| (k, _57_3610) -> begin
(

let phi = (let _148_1662 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _148_1662 (norm env)))
in (

let _57_3613 = (FStar_TypeChecker_Util.check_uvars r phi)
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

let _57_3626 = (tc_term env e)
in (match (_57_3626) with
| (e, c, g1) -> begin
(

let _57_3631 = (let _148_1666 = (let _148_1663 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_148_1663))
in (let _148_1665 = (let _148_1664 = (c.FStar_Syntax_Syntax.comp ())
in (e, _148_1664))
in (check_expected_effect env _148_1666 _148_1665)))
in (match (_57_3631) with
| (e, _57_3629, g) -> begin
(

let _57_3632 = (let _148_1667 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _148_1667))
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
(let _148_1679 = (let _148_1678 = (let _148_1677 = (let _148_1676 = (FStar_Syntax_Print.lid_to_string l)
in (let _148_1675 = (FStar_Syntax_Print.quals_to_string q)
in (let _148_1674 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _148_1676 _148_1675 _148_1674))))
in (_148_1677, r))
in FStar_Syntax_Syntax.Error (_148_1678))
in (Prims.raise _148_1679))
end
end))
in (

let _57_3676 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _57_3653 lb -> (match (_57_3653) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _57_3672 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (

let _57_3667 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _57_3666 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _148_1682 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _148_1682, quals_opt))))
end)
in (match (_57_3672) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_57_3676) with
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
| _57_3685 -> begin
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

let e = (let _148_1686 = (let _148_1685 = (let _148_1684 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _148_1684))
in FStar_Syntax_Syntax.Tm_let (_148_1685))
in (FStar_Syntax_Syntax.mk _148_1686 None r))
in (

let _57_3719 = (match ((tc_maybe_toplevel_term (

let _57_3689 = env
in {FStar_TypeChecker_Env.solver = _57_3689.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3689.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3689.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3689.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3689.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3689.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3689.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3689.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3689.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3689.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3689.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _57_3689.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _57_3689.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3689.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3689.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3689.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3689.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3689.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3689.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _57_3696; FStar_Syntax_Syntax.pos = _57_3694; FStar_Syntax_Syntax.vars = _57_3692}, _57_3703, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_57_3707, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _57_3713 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _57_3716 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_57_3719) with
| (se, lbs) -> begin
(

let _57_3725 = if (log env) then begin
(let _148_1694 = (let _148_1693 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _148_1690 = (let _148_1689 = (let _148_1688 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _148_1688.FStar_Syntax_Syntax.fv_name)
in _148_1689.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _148_1690))) with
| None -> begin
true
end
| _57_3723 -> begin
false
end)
in if should_log then begin
(let _148_1692 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _148_1691 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _148_1692 _148_1691)))
end else begin
""
end))))
in (FStar_All.pipe_right _148_1693 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _148_1694))
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
| _57_3735 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _57_3745 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_57_3747) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _57_3758, _57_3760) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _57_3766 -> (match (_57_3766) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _57_3772, _57_3774, quals, r) -> begin
(

let dec = (let _148_1710 = (let _148_1709 = (let _148_1708 = (let _148_1707 = (let _148_1706 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _148_1706))
in FStar_Syntax_Syntax.Tm_arrow (_148_1707))
in (FStar_Syntax_Syntax.mk _148_1708 None r))
in (l, us, _148_1709, (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_148_1710))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _57_3784, _57_3786, _57_3788, _57_3790, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _57_3796 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_57_3798, _57_3800, quals, _57_3803) -> begin
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
| _57_3822 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_57_3824) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _57_3843, _57_3845, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
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
(let _148_1717 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _148_1716 = (let _148_1715 = (let _148_1714 = (let _148_1713 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _148_1713.FStar_Syntax_Syntax.fv_name)
in _148_1714.FStar_Syntax_Syntax.v)
in (_148_1715, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_148_1716)))))
in (_148_1717, hidden))
end else begin
((se)::[], hidden)
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let _57_3884 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _57_3865 se -> (match (_57_3865) with
| (ses, exports, env, hidden) -> begin
(

let _57_3867 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_1724 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _148_1724))
end else begin
()
end
in (

let _57_3871 = (tc_decl env se)
in (match (_57_3871) with
| (se, env) -> begin
(

let _57_3872 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _148_1725 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _148_1725))
end else begin
()
end
in (

let _57_3874 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (

let _57_3878 = (for_export hidden se)
in (match (_57_3878) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_57_3884) with
| (ses, exports, env, _57_3883) -> begin
(let _148_1726 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _148_1726, env))
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

let _57_3889 = env
in (let _148_1731 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _57_3889.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3889.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3889.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3889.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3889.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3889.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3889.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3889.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3889.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3889.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3889.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3889.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3889.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_3889.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_3889.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3889.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _148_1731; FStar_TypeChecker_Env.type_of = _57_3889.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3889.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3889.FStar_TypeChecker_Env.use_bv_sorts}))
in (

let _57_3892 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let _57_3898 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_57_3898) with
| (ses, exports, env) -> begin
((

let _57_3899 = modul
in {FStar_Syntax_Syntax.name = _57_3899.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _57_3899.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3899.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let _57_3907 = (tc_decls env decls)
in (match (_57_3907) with
| (ses, exports, env) -> begin
(

let modul = (

let _57_3908 = modul
in {FStar_Syntax_Syntax.name = _57_3908.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _57_3908.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3908.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul = (

let _57_3914 = modul
in {FStar_Syntax_Syntax.name = _57_3914.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _57_3914.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in (

let _57_3924 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(

let _57_3918 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let _57_3920 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (

let _57_3922 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _148_1744 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _148_1744 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let _57_3931 = (tc_partial_modul env modul)
in (match (_57_3931) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _57_3934 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _148_1753 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _148_1753))
end else begin
()
end
in (

let env = (

let _57_3936 = env
in {FStar_TypeChecker_Env.solver = _57_3936.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3936.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3936.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3936.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3936.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3936.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3936.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3936.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3936.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3936.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3936.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3936.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3936.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_3936.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3936.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3936.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3936.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3936.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3936.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3936.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_3952 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _57_3944) -> begin
(let _148_1758 = (let _148_1757 = (let _148_1756 = (FStar_TypeChecker_Env.get_range env)
in ((Prims.strcat "Implicit argument: " msg), _148_1756))
in FStar_Syntax_Syntax.Error (_148_1757))
in (Prims.raise _148_1758))
end
in (match (_57_3952) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(t, c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(let _148_1763 = (let _148_1762 = (let _148_1761 = (let _148_1759 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _148_1759))
in (let _148_1760 = (FStar_TypeChecker_Env.get_range env)
in (_148_1761, _148_1760)))
in FStar_Syntax_Syntax.Error (_148_1762))
in (Prims.raise _148_1763))
end
end)))))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

let _57_3955 = if (FStar_Options.debug_any ()) then begin
(let _148_1768 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _148_1768))
end else begin
()
end
in (

let _57_3959 = (tc_modul env m)
in (match (_57_3959) with
| (m, env) -> begin
(

let _57_3960 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _148_1769 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _148_1769))
end else begin
()
end
in (m, env))
end))))




