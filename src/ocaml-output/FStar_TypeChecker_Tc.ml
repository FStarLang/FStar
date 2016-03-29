
open Prims
# 42 "FStar.TypeChecker.Tc.fst"
let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_ST.read FStar_Options.log_types) && (not ((let _137_3 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _137_3))))))

# 43 "FStar.TypeChecker.Tc.fst"
let rng : FStar_TypeChecker_Env.env  ->  FStar_Range.range = (fun env -> (FStar_TypeChecker_Env.get_range env))

# 44 "FStar.TypeChecker.Tc.fst"
let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (
# 44 "FStar.TypeChecker.Tc.fst"
let _58_18 = env
in {FStar_TypeChecker_Env.solver = _58_18.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_18.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_18.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_18.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_18.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_18.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_18.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_18.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_18.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _58_18.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_18.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_18.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_18.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_18.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_18.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_18.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_18.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_18.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_18.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_18.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_18.FStar_TypeChecker_Env.use_bv_sorts}))

# 45 "FStar.TypeChecker.Tc.fst"
let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (
# 45 "FStar.TypeChecker.Tc.fst"
let _58_21 = env
in {FStar_TypeChecker_Env.solver = _58_21.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_21.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_21.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_21.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_21.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_21.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_21.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_21.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_21.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _58_21.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_21.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_21.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_21.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_21.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_21.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_21.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_21.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_21.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_21.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_21.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_21.FStar_TypeChecker_Env.use_bv_sorts}))

# 46 "FStar.TypeChecker.Tc.fst"
let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (
# 48 "FStar.TypeChecker.Tc.fst"
let r = if (tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
v.FStar_Syntax_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos tl.FStar_Syntax_Syntax.pos)
end
in (let _137_17 = (let _137_16 = (FStar_Syntax_Syntax.as_arg v)
in (let _137_15 = (let _137_14 = (FStar_Syntax_Syntax.as_arg tl)
in (_137_14)::[])
in (_137_16)::_137_15))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _137_17 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))

# 51 "FStar.TypeChecker.Tc.fst"
let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _58_1 -> (match (_58_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _58_31 -> begin
false
end))

# 54 "FStar.TypeChecker.Tc.fst"
let steps : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Normalize.step Prims.list = (fun env -> if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::[]
end else begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]
end)

# 58 "FStar.TypeChecker.Tc.fst"
let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Beta)::[]) env t))

# 59 "FStar.TypeChecker.Tc.fst"
let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _137_30 = (steps env)
in (FStar_TypeChecker_Normalize.normalize _137_30 env t)))

# 60 "FStar.TypeChecker.Tc.fst"
let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _137_35 = (steps env)
in (FStar_TypeChecker_Normalize.normalize_comp _137_35 env c)))

# 61 "FStar.TypeChecker.Tc.fst"
let check_no_escape : FStar_Syntax_Syntax.term Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun head_opt env fvs kt -> (
# 62 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
()
end
| _58_48 -> begin
(
# 65 "FStar.TypeChecker.Tc.fst"
let fvs' = (let _137_48 = if try_norm then begin
(norm env t)
end else begin
t
end
in (FStar_Syntax_Free.names _137_48))
in (match ((FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)) with
| None -> begin
()
end
| Some (x) -> begin
if (not (try_norm)) then begin
(aux true t)
end else begin
(
# 71 "FStar.TypeChecker.Tc.fst"
let fail = (fun _58_55 -> (match (()) with
| () -> begin
(
# 72 "FStar.TypeChecker.Tc.fst"
let msg = (match (head_opt) with
| None -> begin
(let _137_52 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _137_52))
end
| Some (head) -> begin
(let _137_54 = (FStar_Syntax_Print.bv_to_string x)
in (let _137_53 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _137_54 _137_53)))
end)
in (let _137_57 = (let _137_56 = (let _137_55 = (FStar_TypeChecker_Env.get_range env)
in (msg, _137_55))
in FStar_Syntax_Syntax.Error (_137_56))
in (Prims.raise _137_57)))
end))
in (
# 77 "FStar.TypeChecker.Tc.fst"
let s = (let _137_59 = (let _137_58 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _137_58))
in (FStar_TypeChecker_Util.new_uvar env _137_59))
in (match ((FStar_TypeChecker_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g)
end
| _58_64 -> begin
(fail ())
end)))
end
end))
end))
in (aux false kt)))

# 84 "FStar.TypeChecker.Tc.fst"
let maybe_push_binding : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder  ->  FStar_TypeChecker_Env.env = (fun env b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
env
end else begin
(
# 86 "FStar.TypeChecker.Tc.fst"
let _58_67 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_65 = (FStar_Syntax_Print.bv_to_string (Prims.fst b))
in (let _137_64 = (FStar_Syntax_Print.term_to_string (Prims.fst b).FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _137_65 _137_64)))
end else begin
()
end
in (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))
end)

# 90 "FStar.TypeChecker.Tc.fst"
let maybe_make_subst = (fun _58_2 -> (match (_58_2) with
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Syntax_Syntax.NT ((x, e)))::[]
end
| _58_76 -> begin
[]
end))

# 94 "FStar.TypeChecker.Tc.fst"
let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.subst_t = (fun s b v -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
s
end else begin
(FStar_Syntax_Syntax.NT (((Prims.fst b), v)))::s
end)

# 98 "FStar.TypeChecker.Tc.fst"
let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (
# 99 "FStar.TypeChecker.Tc.fst"
let _58_82 = lc
in {FStar_Syntax_Syntax.eff_name = _58_82.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_82.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _58_84 -> (match (()) with
| () -> begin
(let _137_78 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _137_78 t))
end))}))

# 101 "FStar.TypeChecker.Tc.fst"
let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (
# 102 "FStar.TypeChecker.Tc.fst"
let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _137_87 = if (not ((FStar_Syntax_Util.is_pure_or_ghost_function t))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _137_87))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (
# 107 "FStar.TypeChecker.Tc.fst"
let t = lc.FStar_Syntax_Syntax.res_typ
in (
# 108 "FStar.TypeChecker.Tc.fst"
let _58_116 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, guard)
end
| Some (t') -> begin
(
# 111 "FStar.TypeChecker.Tc.fst"
let _58_98 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_89 = (FStar_Syntax_Print.term_to_string t)
in (let _137_88 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _137_89 _137_88)))
end else begin
()
end
in (
# 113 "FStar.TypeChecker.Tc.fst"
let _58_102 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_58_102) with
| (e, lc) -> begin
(
# 114 "FStar.TypeChecker.Tc.fst"
let t = lc.FStar_Syntax_Syntax.res_typ
in (
# 115 "FStar.TypeChecker.Tc.fst"
let _58_106 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_58_106) with
| (e, g) -> begin
(
# 116 "FStar.TypeChecker.Tc.fst"
let _58_107 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_91 = (FStar_Syntax_Print.term_to_string t)
in (let _137_90 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _137_91 _137_90)))
end else begin
()
end
in (
# 118 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (
# 119 "FStar.TypeChecker.Tc.fst"
let _58_112 = (let _137_97 = (FStar_All.pipe_left (fun _137_96 -> Some (_137_96)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _137_97 env e lc g))
in (match (_58_112) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))))
end)))
end)))
end)
in (match (_58_116) with
| (e, lc, g) -> begin
(
# 121 "FStar.TypeChecker.Tc.fst"
let _58_117 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_98 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _137_98))
end else begin
()
end
in (e, lc, g))
end)))))

# 125 "FStar.TypeChecker.Tc.fst"
let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (t) -> begin
(
# 129 "FStar.TypeChecker.Tc.fst"
let _58_127 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_58_127) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))

# 132 "FStar.TypeChecker.Tc.fst"
let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _58_132 -> (match (_58_132) with
| (e, c) -> begin
(
# 133 "FStar.TypeChecker.Tc.fst"
let expected_c_opt = (match (copt) with
| Some (_58_134) -> begin
copt
end
| None -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
(
# 138 "FStar.TypeChecker.Tc.fst"
let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 139 "FStar.TypeChecker.Tc.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (match ((FStar_TypeChecker_Env.default_effect env md.FStar_Syntax_Syntax.mname)) with
| None -> begin
None
end
| Some (l) -> begin
(
# 143 "FStar.TypeChecker.Tc.fst"
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
# 147 "FStar.TypeChecker.Tc.fst"
let def = (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.effect_name = l; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = flags})
in Some (def)))
end)))
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _137_111 = (norm_c env c)
in (e, _137_111, FStar_TypeChecker_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(
# 156 "FStar.TypeChecker.Tc.fst"
let _58_148 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_114 = (FStar_Syntax_Print.term_to_string e)
in (let _137_113 = (FStar_Syntax_Print.comp_to_string c)
in (let _137_112 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _137_114 _137_113 _137_112))))
end else begin
()
end
in (
# 159 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 160 "FStar.TypeChecker.Tc.fst"
let _58_151 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_117 = (FStar_Syntax_Print.term_to_string e)
in (let _137_116 = (FStar_Syntax_Print.comp_to_string c)
in (let _137_115 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _137_117 _137_116 _137_115))))
end else begin
()
end
in (
# 165 "FStar.TypeChecker.Tc.fst"
let _58_157 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_58_157) with
| (e, _58_155, g) -> begin
(
# 166 "FStar.TypeChecker.Tc.fst"
let g = (let _137_118 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _137_118 "could not prove post-condition" g))
in (
# 167 "FStar.TypeChecker.Tc.fst"
let _58_159 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_120 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _137_119 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _137_120 _137_119)))
end else begin
()
end
in (e, expected_c, g)))
end)))))
end))
end))

# 170 "FStar.TypeChecker.Tc.fst"
let no_logical_guard = (fun env _58_165 -> (match (_58_165) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
(te, kt, f)
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _137_126 = (let _137_125 = (let _137_124 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _137_123 = (FStar_TypeChecker_Env.get_range env)
in (_137_124, _137_123)))
in FStar_Syntax_Syntax.Error (_137_125))
in (Prims.raise _137_126))
end)
end))

# 175 "FStar.TypeChecker.Tc.fst"
let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _137_129 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _137_129))
end))

# 182 "FStar.TypeChecker.Tc.fst"
let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _58_189; FStar_Syntax_Syntax.result_typ = _58_187; FStar_Syntax_Syntax.effect_args = _pre::_post::(pats, _58_181)::[]; FStar_Syntax_Syntax.flags = _58_178}) -> begin
(
# 186 "FStar.TypeChecker.Tc.fst"
let pat_vars = (FStar_Syntax_Free.names pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _58_196 -> (match (_58_196) with
| (b, _58_195) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _58_200) -> begin
(let _137_136 = (let _137_135 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _137_135))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _137_136))
end))
end
| _58_204 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end)

# 197 "FStar.TypeChecker.Tc.fst"
let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun env actuals expected_c -> (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(
# 201 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 202 "FStar.TypeChecker.Tc.fst"
let env = (
# 202 "FStar.TypeChecker.Tc.fst"
let _58_211 = env
in {FStar_TypeChecker_Env.solver = _58_211.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_211.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_211.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_211.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_211.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_211.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_211.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_211.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_211.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_211.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_211.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_211.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _58_211.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_211.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_211.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_211.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_211.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_211.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_211.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_211.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_211.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 203 "FStar.TypeChecker.Tc.fst"
let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (
# 205 "FStar.TypeChecker.Tc.fst"
let decreases_clause = (fun bs c -> (
# 207 "FStar.TypeChecker.Tc.fst"
let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _58_223 -> (match (_58_223) with
| (b, _58_222) -> begin
(
# 209 "FStar.TypeChecker.Tc.fst"
let t = (let _137_150 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _137_150))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _58_232 -> begin
(let _137_151 = (FStar_Syntax_Syntax.bv_to_name b)
in (_137_151)::[])
end))
end)))))
in (
# 214 "FStar.TypeChecker.Tc.fst"
let as_lex_list = (fun dec -> (
# 215 "FStar.TypeChecker.Tc.fst"
let _58_238 = (FStar_Syntax_Util.head_and_args dec)
in (match (_58_238) with
| (head, _58_237) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _58_242 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (
# 219 "FStar.TypeChecker.Tc.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _58_3 -> (match (_58_3) with
| FStar_Syntax_Syntax.DECREASES (_58_246) -> begin
true
end
| _58_249 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _58_254 -> begin
(
# 223 "FStar.TypeChecker.Tc.fst"
let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| x::[] -> begin
x
end
| _58_259 -> begin
(mk_lex_list xs)
end))
end)))))
in (
# 228 "FStar.TypeChecker.Tc.fst"
let previous_dec = (decreases_clause actuals expected_c)
in (
# 229 "FStar.TypeChecker.Tc.fst"
let guard_one_letrec = (fun _58_264 -> (match (_58_264) with
| (l, t) -> begin
(match ((let _137_157 = (FStar_Syntax_Subst.compress t)
in _137_157.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 233 "FStar.TypeChecker.Tc.fst"
let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _58_271 -> (match (_58_271) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _137_161 = (let _137_160 = (let _137_159 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_137_159))
in (FStar_Syntax_Syntax.new_bv _137_160 x.FStar_Syntax_Syntax.sort))
in (_137_161, imp))
end else begin
(x, imp)
end
end))))
in (
# 234 "FStar.TypeChecker.Tc.fst"
let _58_275 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_58_275) with
| (formals, c) -> begin
(
# 235 "FStar.TypeChecker.Tc.fst"
let dec = (decreases_clause formals c)
in (
# 236 "FStar.TypeChecker.Tc.fst"
let precedes = (let _137_165 = (let _137_164 = (FStar_Syntax_Syntax.as_arg dec)
in (let _137_163 = (let _137_162 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_137_162)::[])
in (_137_164)::_137_163))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _137_165 None r))
in (
# 237 "FStar.TypeChecker.Tc.fst"
let _58_282 = (FStar_Util.prefix formals)
in (match (_58_282) with
| (bs, (last, imp)) -> begin
(
# 238 "FStar.TypeChecker.Tc.fst"
let last = (
# 238 "FStar.TypeChecker.Tc.fst"
let _58_283 = last
in (let _137_166 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _58_283.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_283.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _137_166}))
in (
# 239 "FStar.TypeChecker.Tc.fst"
let refined_formals = (FStar_List.append bs (((last, imp))::[]))
in (
# 240 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (
# 241 "FStar.TypeChecker.Tc.fst"
let _58_288 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_169 = (FStar_Syntax_Print.lbname_to_string l)
in (let _137_168 = (FStar_Syntax_Print.term_to_string t)
in (let _137_167 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _137_169 _137_168 _137_167))))
end else begin
()
end
in (l, t')))))
end))))
end)))
end
| _58_291 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end))

# 253 "FStar.TypeChecker.Tc.fst"
let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (
# 253 "FStar.TypeChecker.Tc.fst"
let _58_294 = env
in {FStar_TypeChecker_Env.solver = _58_294.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_294.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_294.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_294.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_294.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_294.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_294.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_294.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_294.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_294.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_294.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_294.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_294.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_294.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_294.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_294.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_294.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_294.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_294.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_294.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_294.FStar_TypeChecker_Env.use_bv_sorts}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 258 "FStar.TypeChecker.Tc.fst"
let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (
# 259 "FStar.TypeChecker.Tc.fst"
let _58_299 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_238 = (let _137_236 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _137_236))
in (let _137_237 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _137_238 _137_237)))
end else begin
()
end
in (
# 260 "FStar.TypeChecker.Tc.fst"
let top = e
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_58_303) -> begin
(let _137_242 = (FStar_Syntax_Subst.compress e)
in (tc_term env _137_242))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(
# 277 "FStar.TypeChecker.Tc.fst"
let _58_344 = (tc_tot_or_gtot_term env e)
in (match (_58_344) with
| (e, c, g) -> begin
(
# 278 "FStar.TypeChecker.Tc.fst"
let g = (
# 278 "FStar.TypeChecker.Tc.fst"
let _58_345 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_345.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_345.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_345.FStar_TypeChecker_Env.implicits})
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(
# 282 "FStar.TypeChecker.Tc.fst"
let _58_355 = (FStar_Syntax_Util.type_u ())
in (match (_58_355) with
| (t, u) -> begin
(
# 283 "FStar.TypeChecker.Tc.fst"
let _58_359 = (tc_check_tot_or_gtot_term env e t)
in (match (_58_359) with
| (e, c, g) -> begin
(
# 284 "FStar.TypeChecker.Tc.fst"
let _58_366 = (
# 285 "FStar.TypeChecker.Tc.fst"
let _58_363 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_363) with
| (env, _58_362) -> begin
(tc_pats env pats)
end))
in (match (_58_366) with
| (pats, g') -> begin
(
# 287 "FStar.TypeChecker.Tc.fst"
let g' = (
# 287 "FStar.TypeChecker.Tc.fst"
let _58_367 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_367.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_367.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_367.FStar_TypeChecker_Env.implicits})
in (let _137_244 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_pattern (pats)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _137_243 = (FStar_TypeChecker_Rel.conj_guard g g')
in (_137_244, c, _137_243))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _137_245 = (FStar_Syntax_Subst.compress e)
in _137_245.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_58_376, {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _58_383; FStar_Syntax_Syntax.lbtyp = _58_381; FStar_Syntax_Syntax.lbeff = _58_379; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 295 "FStar.TypeChecker.Tc.fst"
let _58_394 = (let _137_246 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _137_246 e1))
in (match (_58_394) with
| (e1, c1, g1) -> begin
(
# 296 "FStar.TypeChecker.Tc.fst"
let _58_398 = (tc_term env e2)
in (match (_58_398) with
| (e2, c2, g2) -> begin
(
# 297 "FStar.TypeChecker.Tc.fst"
let c = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (None, c2))
in (
# 298 "FStar.TypeChecker.Tc.fst"
let e = (let _137_251 = (let _137_250 = (let _137_249 = (let _137_248 = (let _137_247 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Common.t_unit, e1))
in (_137_247)::[])
in (false, _137_248))
in (_137_249, e2))
in FStar_Syntax_Syntax.Tm_let (_137_250))
in (FStar_Syntax_Syntax.mk _137_251 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 299 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _137_252 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _137_252)))))
end))
end))
end
| _58_403 -> begin
(
# 302 "FStar.TypeChecker.Tc.fst"
let _58_407 = (tc_term env e)
in (match (_58_407) with
| (e, c, g) -> begin
(
# 303 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(
# 308 "FStar.TypeChecker.Tc.fst"
let _58_416 = (tc_term env e)
in (match (_58_416) with
| (e, c, g) -> begin
(
# 309 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, m))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _58_422) -> begin
(
# 313 "FStar.TypeChecker.Tc.fst"
let _58_429 = (tc_comp env expected_c)
in (match (_58_429) with
| (expected_c, _58_427, g) -> begin
(
# 314 "FStar.TypeChecker.Tc.fst"
let _58_433 = (tc_term env e)
in (match (_58_433) with
| (e, c', g') -> begin
(
# 315 "FStar.TypeChecker.Tc.fst"
let _58_437 = (let _137_254 = (let _137_253 = (c'.FStar_Syntax_Syntax.comp ())
in (e, _137_253))
in (check_expected_effect env (Some (expected_c)) _137_254))
in (match (_58_437) with
| (e, expected_c, g'') -> begin
(
# 316 "FStar.TypeChecker.Tc.fst"
let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (let _137_257 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t_res), Some ((FStar_Syntax_Util.comp_effect_name expected_c))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _137_256 = (let _137_255 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _137_255))
in (_137_257, (FStar_Syntax_Util.lcomp_of_comp expected_c), _137_256))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _58_443) -> begin
(
# 322 "FStar.TypeChecker.Tc.fst"
let _58_448 = (FStar_Syntax_Util.type_u ())
in (match (_58_448) with
| (k, u) -> begin
(
# 323 "FStar.TypeChecker.Tc.fst"
let _58_453 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_453) with
| (t, _58_451, f) -> begin
(
# 324 "FStar.TypeChecker.Tc.fst"
let _58_457 = (let _137_258 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _137_258 e))
in (match (_58_457) with
| (e, c, g) -> begin
(
# 325 "FStar.TypeChecker.Tc.fst"
let _58_461 = (let _137_262 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_458 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _137_262 e c f))
in (match (_58_461) with
| (c, f) -> begin
(
# 326 "FStar.TypeChecker.Tc.fst"
let _58_465 = (let _137_263 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t), Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _137_263 c))
in (match (_58_465) with
| (e, c, f2) -> begin
(let _137_265 = (let _137_264 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _137_264))
in (e, c, _137_265))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 330 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 331 "FStar.TypeChecker.Tc.fst"
let env = (let _137_267 = (let _137_266 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _137_266 Prims.fst))
in (FStar_All.pipe_right _137_267 instantiate_both))
in (
# 332 "FStar.TypeChecker.Tc.fst"
let _58_472 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_269 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _137_268 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _137_269 _137_268)))
end else begin
()
end
in (
# 336 "FStar.TypeChecker.Tc.fst"
let _58_477 = (tc_term (no_inst env) head)
in (match (_58_477) with
| (head, chead, g_head) -> begin
(
# 337 "FStar.TypeChecker.Tc.fst"
let _58_481 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _137_270 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _137_270))
end else begin
(let _137_271 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _137_271))
end
in (match (_58_481) with
| (e, c, g) -> begin
(
# 340 "FStar.TypeChecker.Tc.fst"
let _58_482 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _137_272 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _137_272))
end else begin
()
end
in (
# 342 "FStar.TypeChecker.Tc.fst"
let c = if (((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) && (not ((FStar_Syntax_Util.is_lcomp_partial_return c)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)) then begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e c)
end else begin
c
end
in (
# 347 "FStar.TypeChecker.Tc.fst"
let _58_489 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_278 = (FStar_Syntax_Print.term_to_string e)
in (let _137_277 = (let _137_273 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _137_273))
in (let _137_276 = (let _137_275 = (FStar_TypeChecker_Env.expected_typ env0)
in (FStar_All.pipe_right _137_275 (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end))))
in (FStar_Util.print3 "(%s) About to check %s against expected typ %s\n" _137_278 _137_277 _137_276))))
end else begin
()
end
in (
# 352 "FStar.TypeChecker.Tc.fst"
let _58_494 = (comp_check_expected_typ env0 e c)
in (match (_58_494) with
| (e, c, g') -> begin
(
# 353 "FStar.TypeChecker.Tc.fst"
let _58_495 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_281 = (FStar_Syntax_Print.term_to_string e)
in (let _137_280 = (let _137_279 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _137_279))
in (FStar_Util.print2 "(%s) checked ... got %s\n" _137_281 _137_280)))
end else begin
()
end
in (
# 357 "FStar.TypeChecker.Tc.fst"
let gimp = (match ((let _137_282 = (FStar_Syntax_Subst.compress head)
in _137_282.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _58_499) -> begin
(
# 360 "FStar.TypeChecker.Tc.fst"
let imp = ("head of application is a uvar", env0, u, e, c.FStar_Syntax_Syntax.res_typ, head.FStar_Syntax_Syntax.pos)
in (
# 361 "FStar.TypeChecker.Tc.fst"
let _58_503 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_503.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_503.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_503.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _58_506 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (
# 363 "FStar.TypeChecker.Tc.fst"
let gres = (let _137_283 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _137_283))
in (
# 364 "FStar.TypeChecker.Tc.fst"
let _58_509 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _137_284 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print1 "Guard from application node is %s\n" _137_284))
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
# 369 "FStar.TypeChecker.Tc.fst"
let _58_517 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_517) with
| (env1, topt) -> begin
(
# 370 "FStar.TypeChecker.Tc.fst"
let env1 = (instantiate_both env1)
in (
# 371 "FStar.TypeChecker.Tc.fst"
let _58_522 = (tc_term env1 e1)
in (match (_58_522) with
| (e1, c1, g1) -> begin
(
# 372 "FStar.TypeChecker.Tc.fst"
let _58_533 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(
# 375 "FStar.TypeChecker.Tc.fst"
let _58_529 = (FStar_Syntax_Util.type_u ())
in (match (_58_529) with
| (k, _58_528) -> begin
(
# 376 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _137_285 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_137_285, res_t)))
end))
end)
in (match (_58_533) with
| (env_branches, res_t) -> begin
(
# 379 "FStar.TypeChecker.Tc.fst"
let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (
# 380 "FStar.TypeChecker.Tc.fst"
let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (
# 381 "FStar.TypeChecker.Tc.fst"
let _58_550 = (
# 382 "FStar.TypeChecker.Tc.fst"
let _58_547 = (FStar_List.fold_right (fun _58_541 _58_544 -> (match ((_58_541, _58_544)) with
| ((_58_537, f, c, g), (caccum, gaccum)) -> begin
(let _137_288 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _137_288))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_58_547) with
| (cases, g) -> begin
(let _137_289 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_137_289, g))
end))
in (match (_58_550) with
| (c_branches, g_branches) -> begin
(
# 386 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (guard_x), c_branches))
in (
# 387 "FStar.TypeChecker.Tc.fst"
let e = (let _137_293 = (let _137_292 = (let _137_291 = (FStar_List.map (fun _58_559 -> (match (_58_559) with
| (f, _58_554, _58_556, _58_558) -> begin
f
end)) t_eqns)
in (e1, _137_291))
in FStar_Syntax_Syntax.Tm_match (_137_292))
in (FStar_Syntax_Syntax.mk _137_293 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (
# 389 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ), Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (
# 390 "FStar.TypeChecker.Tc.fst"
let _58_562 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _137_296 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _137_295 = (let _137_294 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _137_294))
in (FStar_Util.print2 "(%s) comp type = %s\n" _137_296 _137_295)))
end else begin
()
end
in (let _137_297 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _137_297))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_574); FStar_Syntax_Syntax.lbunivs = _58_572; FStar_Syntax_Syntax.lbtyp = _58_570; FStar_Syntax_Syntax.lbeff = _58_568; FStar_Syntax_Syntax.lbdef = _58_566}::[]), _58_580) -> begin
(
# 397 "FStar.TypeChecker.Tc.fst"
let _58_583 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_298 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _137_298))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _58_587), _58_590) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_605); FStar_Syntax_Syntax.lbunivs = _58_603; FStar_Syntax_Syntax.lbtyp = _58_601; FStar_Syntax_Syntax.lbeff = _58_599; FStar_Syntax_Syntax.lbdef = _58_597}::_58_595), _58_611) -> begin
(
# 404 "FStar.TypeChecker.Tc.fst"
let _58_614 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_299 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _137_299))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _58_618), _58_621) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 417 "FStar.TypeChecker.Tc.fst"
let check_instantiated_fvar = (fun env v dc e t -> (
# 418 "FStar.TypeChecker.Tc.fst"
let _58_635 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_635) with
| (e, t, implicits) -> begin
(
# 420 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _137_313 = (let _137_312 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _137_312))
in FStar_Util.Inr (_137_313))
end
in (
# 421 "FStar.TypeChecker.Tc.fst"
let is_data_ctor = (fun _58_4 -> (match (_58_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _58_645 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _137_319 = (let _137_318 = (let _137_317 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _137_316 = (FStar_TypeChecker_Env.get_range env)
in (_137_317, _137_316)))
in FStar_Syntax_Syntax.Error (_137_318))
in (Prims.raise _137_319))
end else begin
(value_check_expected_typ env e tc implicits)
end))
end)))
in (
# 431 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (
# 432 "FStar.TypeChecker.Tc.fst"
let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(FStar_All.failwith "Impossible: Violation of locally nameless convention")
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(
# 438 "FStar.TypeChecker.Tc.fst"
let g = (match ((let _137_320 = (FStar_Syntax_Subst.compress t1)
in _137_320.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_656) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _58_659 -> begin
(
# 440 "FStar.TypeChecker.Tc.fst"
let imp = ("uvar in term", env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (
# 441 "FStar.TypeChecker.Tc.fst"
let _58_661 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_661.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_661.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_661.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 446 "FStar.TypeChecker.Tc.fst"
let _58_667 = (FStar_Syntax_Util.type_u ())
in (match (_58_667) with
| (t, u) -> begin
(
# 447 "FStar.TypeChecker.Tc.fst"
let e = (FStar_TypeChecker_Util.new_uvar env t)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))
end))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 451 "FStar.TypeChecker.Tc.fst"
let t = if env.FStar_TypeChecker_Env.use_bv_sorts then begin
x.FStar_Syntax_Syntax.sort
end else begin
(FStar_TypeChecker_Env.lookup_bv env x)
end
in (
# 452 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.bv_to_name (
# 452 "FStar.TypeChecker.Tc.fst"
let _58_672 = x
in {FStar_Syntax_Syntax.ppname = _58_672.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_672.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (
# 453 "FStar.TypeChecker.Tc.fst"
let _58_678 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_678) with
| (e, t, implicits) -> begin
(
# 454 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _137_322 = (let _137_321 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _137_321))
in FStar_Util.Inr (_137_322))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _58_685; FStar_Syntax_Syntax.pos = _58_683; FStar_Syntax_Syntax.vars = _58_681}, us) -> begin
(
# 458 "FStar.TypeChecker.Tc.fst"
let us = (FStar_List.map (tc_universe env) us)
in (
# 459 "FStar.TypeChecker.Tc.fst"
let _58_695 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_695) with
| (us', t) -> begin
(
# 460 "FStar.TypeChecker.Tc.fst"
let _58_702 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _137_325 = (let _137_324 = (let _137_323 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _137_323))
in FStar_Syntax_Syntax.Error (_137_324))
in (Prims.raise _137_325))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _58_701 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (
# 465 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 465 "FStar.TypeChecker.Tc.fst"
let _58_704 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 465 "FStar.TypeChecker.Tc.fst"
let _58_706 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_706.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_706.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_704.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_704.FStar_Syntax_Syntax.fv_qual})
in (
# 466 "FStar.TypeChecker.Tc.fst"
let e = (let _137_328 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _137_328 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(
# 470 "FStar.TypeChecker.Tc.fst"
let _58_714 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_714) with
| (us, t) -> begin
(
# 471 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 471 "FStar.TypeChecker.Tc.fst"
let _58_715 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 471 "FStar.TypeChecker.Tc.fst"
let _58_717 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_717.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_717.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_715.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_715.FStar_Syntax_Syntax.fv_qual})
in (
# 472 "FStar.TypeChecker.Tc.fst"
let e = (let _137_329 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _137_329 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t)))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(
# 476 "FStar.TypeChecker.Tc.fst"
let t = (tc_constant env top.FStar_Syntax_Syntax.pos c)
in (
# 477 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 481 "FStar.TypeChecker.Tc.fst"
let _58_731 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_731) with
| (bs, c) -> begin
(
# 482 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 483 "FStar.TypeChecker.Tc.fst"
let _58_736 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_736) with
| (env, _58_735) -> begin
(
# 484 "FStar.TypeChecker.Tc.fst"
let _58_741 = (tc_binders env bs)
in (match (_58_741) with
| (bs, env, g, us) -> begin
(
# 485 "FStar.TypeChecker.Tc.fst"
let _58_745 = (tc_comp env c)
in (match (_58_745) with
| (c, uc, f) -> begin
(
# 486 "FStar.TypeChecker.Tc.fst"
let e = (
# 486 "FStar.TypeChecker.Tc.fst"
let _58_746 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _58_746.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_746.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_746.FStar_Syntax_Syntax.vars})
in (
# 487 "FStar.TypeChecker.Tc.fst"
let _58_749 = (check_smt_pat env e bs c)
in (
# 488 "FStar.TypeChecker.Tc.fst"
let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (
# 489 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 490 "FStar.TypeChecker.Tc.fst"
let g = (let _137_330 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _137_330))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(
# 494 "FStar.TypeChecker.Tc.fst"
let u = (tc_universe env u)
in (
# 495 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) None top.FStar_Syntax_Syntax.pos)
in (
# 496 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 500 "FStar.TypeChecker.Tc.fst"
let _58_765 = (let _137_332 = (let _137_331 = (FStar_Syntax_Syntax.mk_binder x)
in (_137_331)::[])
in (FStar_Syntax_Subst.open_term _137_332 phi))
in (match (_58_765) with
| (x, phi) -> begin
(
# 501 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 502 "FStar.TypeChecker.Tc.fst"
let _58_770 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_770) with
| (env, _58_769) -> begin
(
# 503 "FStar.TypeChecker.Tc.fst"
let _58_775 = (let _137_333 = (FStar_List.hd x)
in (tc_binder env _137_333))
in (match (_58_775) with
| (x, env, f1, u) -> begin
(
# 504 "FStar.TypeChecker.Tc.fst"
let _58_776 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_336 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _137_335 = (FStar_Syntax_Print.term_to_string phi)
in (let _137_334 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _137_336 _137_335 _137_334))))
end else begin
()
end
in (
# 507 "FStar.TypeChecker.Tc.fst"
let _58_781 = (FStar_Syntax_Util.type_u ())
in (match (_58_781) with
| (t_phi, _58_780) -> begin
(
# 508 "FStar.TypeChecker.Tc.fst"
let _58_786 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_58_786) with
| (phi, _58_784, f2) -> begin
(
# 509 "FStar.TypeChecker.Tc.fst"
let e = (
# 509 "FStar.TypeChecker.Tc.fst"
let _58_787 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _58_787.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_787.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_787.FStar_Syntax_Syntax.vars})
in (
# 510 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 511 "FStar.TypeChecker.Tc.fst"
let g = (let _137_337 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _137_337))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _58_795) -> begin
(
# 515 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (
# 516 "FStar.TypeChecker.Tc.fst"
let _58_801 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_338 = (FStar_Syntax_Print.term_to_string (
# 517 "FStar.TypeChecker.Tc.fst"
let _58_799 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _58_799.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _58_799.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_799.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _137_338))
end else begin
()
end
in (
# 518 "FStar.TypeChecker.Tc.fst"
let _58_805 = (FStar_Syntax_Subst.open_term bs body)
in (match (_58_805) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _58_807 -> begin
(let _137_340 = (let _137_339 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _137_339))
in (FStar_All.failwith _137_340))
end)))))
and tc_constant : FStar_TypeChecker_Env.env  ->  FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun env r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_58_813) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_58_816) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int32 (_58_819) -> begin
FStar_TypeChecker_Common.t_int32
end
| FStar_Const.Const_int64 (_58_822) -> begin
FStar_TypeChecker_Common.t_int64
end
| FStar_Const.Const_string (_58_825) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_58_828) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_58_831) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_uint8 (_58_834) -> begin
FStar_TypeChecker_Common.t_uint8
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_58_838) -> begin
(
# 537 "FStar.TypeChecker.Tc.fst"
let fail = (fun _58_841 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Range constant cannot be checked in this context; expected an instance of \'range_of\'", r))))
end))
in (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(fail ())
end
| Some (t) -> begin
if (let _137_346 = (FStar_Syntax_Util.destruct t FStar_Syntax_Const.range_of_lid)
in (FStar_Option.isSome _137_346)) then begin
t
end else begin
(fail ())
end
end))
end
| _58_846 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 558 "FStar.TypeChecker.Tc.fst"
let _58_853 = (FStar_Syntax_Util.type_u ())
in (match (_58_853) with
| (k, u) -> begin
(
# 559 "FStar.TypeChecker.Tc.fst"
let _58_858 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_858) with
| (t, _58_856, g) -> begin
(let _137_349 = (FStar_Syntax_Syntax.mk_Total t)
in (_137_349, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 563 "FStar.TypeChecker.Tc.fst"
let _58_863 = (FStar_Syntax_Util.type_u ())
in (match (_58_863) with
| (k, u) -> begin
(
# 564 "FStar.TypeChecker.Tc.fst"
let _58_868 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_868) with
| (t, _58_866, g) -> begin
(let _137_350 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_137_350, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 568 "FStar.TypeChecker.Tc.fst"
let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (
# 569 "FStar.TypeChecker.Tc.fst"
let tc = (let _137_352 = (let _137_351 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_137_351)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _137_352 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 570 "FStar.TypeChecker.Tc.fst"
let _58_877 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_58_877) with
| (tc, _58_875, f) -> begin
(
# 571 "FStar.TypeChecker.Tc.fst"
let _58_881 = (FStar_Syntax_Util.head_and_args tc)
in (match (_58_881) with
| (_58_879, args) -> begin
(
# 572 "FStar.TypeChecker.Tc.fst"
let _58_884 = (let _137_354 = (FStar_List.hd args)
in (let _137_353 = (FStar_List.tl args)
in (_137_354, _137_353)))
in (match (_58_884) with
| (res, args) -> begin
(
# 573 "FStar.TypeChecker.Tc.fst"
let _58_900 = (let _137_356 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _58_5 -> (match (_58_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(
# 575 "FStar.TypeChecker.Tc.fst"
let _58_891 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_891) with
| (env, _58_890) -> begin
(
# 576 "FStar.TypeChecker.Tc.fst"
let _58_896 = (tc_tot_or_gtot_term env e)
in (match (_58_896) with
| (e, _58_894, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _137_356 FStar_List.unzip))
in (match (_58_900) with
| (flags, guards) -> begin
(
# 579 "FStar.TypeChecker.Tc.fst"
let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| _58_905 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _137_358 = (FStar_Syntax_Syntax.mk_Comp (
# 582 "FStar.TypeChecker.Tc.fst"
let _58_907 = c
in {FStar_Syntax_Syntax.effect_name = _58_907.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _58_907.FStar_Syntax_Syntax.flags}))
in (let _137_357 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_137_358, u, _137_357))))
end))
end))
end))
end))))
end))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (
# 589 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun u -> (
# 590 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_58_915) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _137_363 = (aux u)
in FStar_Syntax_Syntax.U_succ (_137_363))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _137_364 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_137_364))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _137_368 = (let _137_367 = (let _137_366 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _137_365 = (FStar_TypeChecker_Env.get_range env)
in (_137_366, _137_365)))
in FStar_Syntax_Syntax.Error (_137_367))
in (Prims.raise _137_368))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _137_369 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _137_369 Prims.snd))
end
| _58_930 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (
# 612 "FStar.TypeChecker.Tc.fst"
let fail = (fun msg t -> (let _137_378 = (let _137_377 = (let _137_376 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_137_376, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_137_377))
in (Prims.raise _137_378)))
in (
# 621 "FStar.TypeChecker.Tc.fst"
let check_binders = (fun env bs bs_expected -> (
# 626 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun _58_948 bs bs_expected -> (match (_58_948) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| ((hd, imp)::bs, (hd_expected, imp')::bs_expected) -> begin
(
# 630 "FStar.TypeChecker.Tc.fst"
let _58_979 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _137_395 = (let _137_394 = (let _137_393 = (let _137_391 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _137_391))
in (let _137_392 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_137_393, _137_392)))
in FStar_Syntax_Syntax.Error (_137_394))
in (Prims.raise _137_395))
end
| _58_978 -> begin
()
end)
in (
# 637 "FStar.TypeChecker.Tc.fst"
let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (
# 638 "FStar.TypeChecker.Tc.fst"
let _58_996 = (match ((let _137_396 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _137_396.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _58_984 -> begin
(
# 641 "FStar.TypeChecker.Tc.fst"
let _58_985 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_397 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _137_397))
end else begin
()
end
in (
# 642 "FStar.TypeChecker.Tc.fst"
let _58_991 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_58_991) with
| (t, _58_989, g1) -> begin
(
# 643 "FStar.TypeChecker.Tc.fst"
let g2 = (let _137_399 = (FStar_TypeChecker_Env.get_range env)
in (let _137_398 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _137_399 "Type annotation on parameter incompatible with the expected type" _137_398)))
in (
# 647 "FStar.TypeChecker.Tc.fst"
let g = (let _137_400 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _137_400))
in (t, g)))
end)))
end)
in (match (_58_996) with
| (t, g) -> begin
(
# 649 "FStar.TypeChecker.Tc.fst"
let hd = (
# 649 "FStar.TypeChecker.Tc.fst"
let _58_997 = hd
in {FStar_Syntax_Syntax.ppname = _58_997.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_997.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 650 "FStar.TypeChecker.Tc.fst"
let b = (hd, imp)
in (
# 651 "FStar.TypeChecker.Tc.fst"
let b_expected = (hd_expected, imp')
in (
# 652 "FStar.TypeChecker.Tc.fst"
let env = (maybe_push_binding env b)
in (
# 653 "FStar.TypeChecker.Tc.fst"
let subst = (let _137_401 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _137_401))
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
# 663 "FStar.TypeChecker.Tc.fst"
let rec expected_function_typ = (fun env t0 body -> (match (t0) with
| None -> begin
(
# 674 "FStar.TypeChecker.Tc.fst"
let _58_1018 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _58_1017 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (
# 677 "FStar.TypeChecker.Tc.fst"
let _58_1025 = (tc_binders env bs)
in (match (_58_1025) with
| (bs, envbody, g, _58_1024) -> begin
(
# 678 "FStar.TypeChecker.Tc.fst"
let _58_1043 = (match ((let _137_408 = (FStar_Syntax_Subst.compress body)
in _137_408.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _58_1030) -> begin
(
# 680 "FStar.TypeChecker.Tc.fst"
let _58_1037 = (tc_comp envbody c)
in (match (_58_1037) with
| (c, _58_1035, g') -> begin
(let _137_409 = (FStar_TypeChecker_Rel.conj_guard g g')
in (Some (c), body, _137_409))
end))
end
| _58_1039 -> begin
(None, body, g)
end)
in (match (_58_1043) with
| (copt, body, g) -> begin
(None, bs, [], copt, envbody, body, g)
end))
end)))
end
| Some (t) -> begin
(
# 686 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 687 "FStar.TypeChecker.Tc.fst"
let rec as_function_typ = (fun norm t -> (match ((let _137_414 = (FStar_Syntax_Subst.compress t)
in _137_414.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 691 "FStar.TypeChecker.Tc.fst"
let _58_1070 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _58_1069 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 692 "FStar.TypeChecker.Tc.fst"
let _58_1077 = (tc_binders env bs)
in (match (_58_1077) with
| (bs, envbody, g, _58_1076) -> begin
(
# 693 "FStar.TypeChecker.Tc.fst"
let _58_1081 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_58_1081) with
| (envbody, _58_1080) -> begin
(Some ((t, true)), bs, [], None, envbody, body, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _58_1084) -> begin
(
# 699 "FStar.TypeChecker.Tc.fst"
let _58_1095 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_58_1095) with
| (_58_1088, bs, bs', copt, env, body, g) -> begin
(Some ((t, false)), bs, bs', copt, env, body, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 703 "FStar.TypeChecker.Tc.fst"
let _58_1102 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_58_1102) with
| (bs_expected, c_expected) -> begin
(
# 710 "FStar.TypeChecker.Tc.fst"
let check_actuals_against_formals = (fun env bs bs_expected -> (
# 711 "FStar.TypeChecker.Tc.fst"
let rec handle_more = (fun _58_1113 c_expected -> (match (_58_1113) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _137_425 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _137_425))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(
# 716 "FStar.TypeChecker.Tc.fst"
let c = (let _137_426 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _137_426))
in (let _137_427 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _137_427)))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(
# 720 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.subst_comp subst c_expected)
in if (FStar_Syntax_Util.is_total_comp c) then begin
(
# 723 "FStar.TypeChecker.Tc.fst"
let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 726 "FStar.TypeChecker.Tc.fst"
let _58_1134 = (check_binders env more_bs bs_expected)
in (match (_58_1134) with
| (env, bs', more, guard', subst) -> begin
(let _137_429 = (let _137_428 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _137_428, subst))
in (handle_more _137_429 c_expected))
end))
end
| _58_1136 -> begin
(let _137_431 = (let _137_430 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _137_430))
in (fail _137_431 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _137_432 = (check_binders env bs bs_expected)
in (handle_more _137_432 c_expected))))
in (
# 733 "FStar.TypeChecker.Tc.fst"
let mk_letrec_env = (fun envbody bs c -> (
# 734 "FStar.TypeChecker.Tc.fst"
let letrecs = (guard_letrecs envbody bs c)
in (
# 735 "FStar.TypeChecker.Tc.fst"
let envbody = (
# 735 "FStar.TypeChecker.Tc.fst"
let _58_1142 = envbody
in {FStar_TypeChecker_Env.solver = _58_1142.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1142.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1142.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1142.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1142.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1142.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1142.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1142.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1142.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1142.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1142.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1142.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _58_1142.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1142.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1142.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1142.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1142.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_1142.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_1142.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1142.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1142.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _58_1147 _58_1150 -> (match ((_58_1147, _58_1150)) with
| ((env, letrec_binders), (l, t)) -> begin
(
# 739 "FStar.TypeChecker.Tc.fst"
let _58_1156 = (let _137_442 = (let _137_441 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _137_441 Prims.fst))
in (tc_term _137_442 t))
in (match (_58_1156) with
| (t, _58_1153, _58_1155) -> begin
(
# 740 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (
# 741 "FStar.TypeChecker.Tc.fst"
let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _137_443 = (FStar_Syntax_Syntax.mk_binder (
# 742 "FStar.TypeChecker.Tc.fst"
let _58_1160 = x
in {FStar_Syntax_Syntax.ppname = _58_1160.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1160.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_137_443)::letrec_binders)
end
| _58_1163 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (
# 747 "FStar.TypeChecker.Tc.fst"
let _58_1169 = (check_actuals_against_formals env bs bs_expected)
in (match (_58_1169) with
| (envbody, bs, g, c) -> begin
(
# 748 "FStar.TypeChecker.Tc.fst"
let _58_1172 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_58_1172) with
| (envbody, letrecs) -> begin
(
# 749 "FStar.TypeChecker.Tc.fst"
let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, body, g))
end))
end))))
end))
end
| _58_1175 -> begin
if (not (norm)) then begin
(let _137_444 = (unfold_whnf env t)
in (as_function_typ true _137_444))
end else begin
(
# 757 "FStar.TypeChecker.Tc.fst"
let _58_1185 = (expected_function_typ env None body)
in (match (_58_1185) with
| (_58_1177, bs, _58_1180, c_opt, envbody, body, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, body, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (
# 761 "FStar.TypeChecker.Tc.fst"
let use_eq = env.FStar_TypeChecker_Env.use_eq
in (
# 762 "FStar.TypeChecker.Tc.fst"
let _58_1189 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1189) with
| (env, topt) -> begin
(
# 764 "FStar.TypeChecker.Tc.fst"
let _58_1193 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_445 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _137_445 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (
# 769 "FStar.TypeChecker.Tc.fst"
let _58_1202 = (expected_function_typ env topt body)
in (match (_58_1202) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(
# 770 "FStar.TypeChecker.Tc.fst"
let _58_1208 = (tc_term (
# 770 "FStar.TypeChecker.Tc.fst"
let _58_1203 = envbody
in {FStar_TypeChecker_Env.solver = _58_1203.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1203.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1203.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1203.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1203.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1203.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1203.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1203.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1203.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1203.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1203.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1203.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1203.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_1203.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1203.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1203.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_1203.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_1203.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1203.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1203.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_58_1208) with
| (body, cbody, guard_body) -> begin
(
# 772 "FStar.TypeChecker.Tc.fst"
let _58_1209 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_449 = (FStar_Syntax_Print.term_to_string body)
in (let _137_448 = (let _137_446 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _137_446))
in (let _137_447 = (FStar_TypeChecker_Rel.guard_to_string env guard_body)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _137_449 _137_448 _137_447))))
end else begin
()
end
in (
# 778 "FStar.TypeChecker.Tc.fst"
let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (
# 781 "FStar.TypeChecker.Tc.fst"
let _58_1212 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _137_452 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _137_451 = (let _137_450 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _137_450))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _137_452 _137_451)))
end else begin
()
end
in (
# 786 "FStar.TypeChecker.Tc.fst"
let _58_1219 = (let _137_454 = (let _137_453 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _137_453))
in (check_expected_effect (
# 786 "FStar.TypeChecker.Tc.fst"
let _58_1214 = envbody
in {FStar_TypeChecker_Env.solver = _58_1214.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1214.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1214.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1214.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1214.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1214.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1214.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1214.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1214.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1214.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1214.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1214.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1214.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1214.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1214.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1214.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1214.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_1214.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_1214.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1214.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1214.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _137_454))
in (match (_58_1219) with
| (body, cbody, guard) -> begin
(
# 787 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (
# 788 "FStar.TypeChecker.Tc.fst"
let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _137_455 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _137_455))
end else begin
(
# 790 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (
# 793 "FStar.TypeChecker.Tc.fst"
let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (
# 794 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.abs bs body (Some ((FStar_Syntax_Util.lcomp_of_comp cbody))))
in (
# 795 "FStar.TypeChecker.Tc.fst"
let _58_1242 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(
# 797 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_58_1231) -> begin
(e, t, guard)
end
| _58_1234 -> begin
(
# 804 "FStar.TypeChecker.Tc.fst"
let _58_1237 = if use_teq then begin
(let _137_456 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _137_456))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_58_1237) with
| (e, guard') -> begin
(let _137_457 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _137_457))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_58_1242) with
| (e, tfun, guard) -> begin
(
# 813 "FStar.TypeChecker.Tc.fst"
let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (
# 814 "FStar.TypeChecker.Tc.fst"
let _58_1246 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_58_1246) with
| (c, g) -> begin
(e, c, g)
end)))
end))))))
end)))))
end))
end)))
end)))))))
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead ghead args expected_topt -> (
# 822 "FStar.TypeChecker.Tc.fst"
let n_args = (FStar_List.length args)
in (
# 823 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 824 "FStar.TypeChecker.Tc.fst"
let thead = chead.FStar_Syntax_Syntax.res_typ
in (
# 825 "FStar.TypeChecker.Tc.fst"
let _58_1256 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_466 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _137_465 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _137_466 _137_465)))
end else begin
()
end
in (
# 826 "FStar.TypeChecker.Tc.fst"
let rec check_function_app = (fun norm tf -> (match ((let _137_471 = (FStar_Syntax_Util.unrefine tf)
in _137_471.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 830 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| (e, imp)::tl -> begin
(
# 833 "FStar.TypeChecker.Tc.fst"
let _58_1290 = (tc_term env e)
in (match (_58_1290) with
| (e, c, g_e) -> begin
(
# 834 "FStar.TypeChecker.Tc.fst"
let _58_1294 = (tc_args env tl)
in (match (_58_1294) with
| (args, comps, g_rest) -> begin
(let _137_476 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, (c)::comps, _137_476))
end))
end))
end))
in (
# 842 "FStar.TypeChecker.Tc.fst"
let _58_1298 = (tc_args env args)
in (match (_58_1298) with
| (args, comps, g_args) -> begin
(
# 843 "FStar.TypeChecker.Tc.fst"
let bs = (let _137_478 = (FStar_All.pipe_right comps (FStar_List.map (fun c -> (c.FStar_Syntax_Syntax.res_typ, None))))
in (FStar_Syntax_Util.null_binders_of_tks _137_478))
in (
# 844 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _58_1305 -> begin
FStar_Syntax_Util.ml_comp
end)
in (
# 847 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _137_493 = (FStar_Syntax_Subst.compress t)
in _137_493.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_58_1311) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _58_1316 -> begin
ml_or_tot
end)
end)
in (
# 854 "FStar.TypeChecker.Tc.fst"
let cres = (let _137_498 = (let _137_497 = (let _137_496 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _137_496 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _137_497))
in (ml_or_tot _137_498 r))
in (
# 855 "FStar.TypeChecker.Tc.fst"
let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (
# 856 "FStar.TypeChecker.Tc.fst"
let _58_1320 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _137_501 = (FStar_Syntax_Print.term_to_string head)
in (let _137_500 = (FStar_Syntax_Print.term_to_string tf)
in (let _137_499 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _137_501 _137_500 _137_499))))
end else begin
()
end
in (
# 861 "FStar.TypeChecker.Tc.fst"
let _58_1322 = (let _137_502 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _137_502))
in (
# 862 "FStar.TypeChecker.Tc.fst"
let comp = (let _137_505 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_TypeChecker_Util.bind env None c (None, out))) ((chead)::comps) _137_505))
in (let _137_507 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _137_506 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_137_507, comp, _137_506)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 866 "FStar.TypeChecker.Tc.fst"
let _58_1333 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_1333) with
| (bs, c) -> begin
(
# 868 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun _58_1341 bs cres args -> (match (_58_1341) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (_58_1348)))::rest, (_58_1356, None)::_58_1354) -> begin
(
# 879 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 880 "FStar.TypeChecker.Tc.fst"
let _58_1362 = (check_no_escape (Some (head)) env fvs t)
in (
# 881 "FStar.TypeChecker.Tc.fst"
let _58_1368 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_58_1368) with
| (varg, _58_1366, implicits) -> begin
(
# 882 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (
# 883 "FStar.TypeChecker.Tc.fst"
let arg = (let _137_516 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _137_516))
in (let _137_518 = (let _137_517 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _137_517, fvs))
in (tc_args _137_518 rest cres args))))
end))))
end
| ((x, aqual)::rest, (e, aq)::rest') -> begin
(
# 887 "FStar.TypeChecker.Tc.fst"
let _58_1400 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _58_1399 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (
# 892 "FStar.TypeChecker.Tc.fst"
let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 893 "FStar.TypeChecker.Tc.fst"
let x = (
# 893 "FStar.TypeChecker.Tc.fst"
let _58_1403 = x
in {FStar_Syntax_Syntax.ppname = _58_1403.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1403.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (
# 894 "FStar.TypeChecker.Tc.fst"
let _58_1406 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _137_519 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _137_519))
end else begin
()
end
in (
# 895 "FStar.TypeChecker.Tc.fst"
let _58_1408 = (check_no_escape (Some (head)) env fvs targ)
in (
# 896 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (
# 897 "FStar.TypeChecker.Tc.fst"
let env = (
# 897 "FStar.TypeChecker.Tc.fst"
let _58_1411 = env
in {FStar_TypeChecker_Env.solver = _58_1411.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1411.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1411.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1411.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1411.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1411.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1411.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1411.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1411.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1411.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1411.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1411.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1411.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1411.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1411.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _58_1411.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1411.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_1411.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_1411.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1411.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1411.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 898 "FStar.TypeChecker.Tc.fst"
let _58_1414 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_522 = (FStar_Syntax_Print.tag_of_term e)
in (let _137_521 = (FStar_Syntax_Print.term_to_string e)
in (let _137_520 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _137_522 _137_521 _137_520))))
end else begin
()
end
in (
# 899 "FStar.TypeChecker.Tc.fst"
let _58_1419 = (tc_term env e)
in (match (_58_1419) with
| (e, c, g_e) -> begin
(
# 900 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (
# 902 "FStar.TypeChecker.Tc.fst"
let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(
# 904 "FStar.TypeChecker.Tc.fst"
let subst = (let _137_523 = (FStar_List.hd bs)
in (maybe_extend_subst subst _137_523 e))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(
# 907 "FStar.TypeChecker.Tc.fst"
let subst = (let _137_524 = (FStar_List.hd bs)
in (maybe_extend_subst subst _137_524 e))
in (
# 908 "FStar.TypeChecker.Tc.fst"
let _58_1426 = (((Some (x), c))::comps, g)
in (match (_58_1426) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _137_525 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _137_525)) then begin
(
# 912 "FStar.TypeChecker.Tc.fst"
let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (
# 913 "FStar.TypeChecker.Tc.fst"
let arg' = (let _137_526 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _137_526))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (newx), c))::comps, g, fvs) rest cres rest')))
end else begin
(let _137_530 = (let _137_529 = (let _137_528 = (let _137_527 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _137_527))
in (_137_528)::arg_rets)
in (subst, (arg)::outargs, _137_529, ((Some (x), c))::comps, g, (x)::fvs))
in (tc_args _137_530 rest cres rest'))
end
end
end))
end))))))))))
end
| (_58_1430, []) -> begin
(
# 922 "FStar.TypeChecker.Tc.fst"
let _58_1433 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (
# 923 "FStar.TypeChecker.Tc.fst"
let _58_1451 = (match (bs) with
| [] -> begin
(
# 926 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (
# 932 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (
# 934 "FStar.TypeChecker.Tc.fst"
let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _58_1441 -> (match (_58_1441) with
| (_58_1439, c) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (
# 941 "FStar.TypeChecker.Tc.fst"
let cres = if refine_with_equality then begin
(let _137_532 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _137_532 cres))
end else begin
(
# 947 "FStar.TypeChecker.Tc.fst"
let _58_1443 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_535 = (FStar_Syntax_Print.term_to_string head)
in (let _137_534 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _137_533 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _137_535 _137_534 _137_533))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _58_1447 -> begin
(
# 956 "FStar.TypeChecker.Tc.fst"
let g = (let _137_536 = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (FStar_All.pipe_right _137_536 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _137_541 = (let _137_540 = (let _137_539 = (let _137_538 = (let _137_537 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _137_537))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _137_538))
in (FStar_Syntax_Syntax.mk_Total _137_539))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _137_540))
in (_137_541, g)))
end)
in (match (_58_1451) with
| (cres, g) -> begin
(
# 959 "FStar.TypeChecker.Tc.fst"
let _58_1452 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_542 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _137_542))
end else begin
()
end
in (
# 960 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_List.fold_left (fun out c -> (FStar_TypeChecker_Util.bind env None (Prims.snd c) ((Prims.fst c), out))) cres comps)
in (
# 961 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.bind env None chead (None, comp))
in (
# 962 "FStar.TypeChecker.Tc.fst"
let app = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev outargs) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (
# 963 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.record_application_site env app comp)
in (
# 964 "FStar.TypeChecker.Tc.fst"
let _58_1462 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp g)
in (match (_58_1462) with
| (comp, g) -> begin
(
# 965 "FStar.TypeChecker.Tc.fst"
let _58_1463 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_548 = (FStar_TypeChecker_Normalize.term_to_string env app)
in (let _137_547 = (let _137_546 = (comp.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Print.comp_to_string _137_546))
in (FStar_Util.print2 "\t Type of app term %s is %s\n" _137_548 _137_547)))
end else begin
()
end
in (app, comp, g))
end)))))))
end)))
end
| ([], arg::_58_1467) -> begin
(
# 971 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun norm tres -> (
# 972 "FStar.TypeChecker.Tc.fst"
let tres = (let _137_553 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _137_553 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(
# 975 "FStar.TypeChecker.Tc.fst"
let _58_1479 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_554 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _137_554))
end else begin
()
end
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs (FStar_Syntax_Util.lcomp_of_comp cres') args))
end
| _58_1482 when (not (norm)) -> begin
(let _137_555 = (unfold_whnf env tres)
in (aux true _137_555))
end
| _58_1484 -> begin
(let _137_561 = (let _137_560 = (let _137_559 = (let _137_557 = (FStar_TypeChecker_Normalize.term_to_string env tf)
in (let _137_556 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _137_557 _137_556)))
in (let _137_558 = (FStar_Syntax_Syntax.argpos arg)
in (_137_559, _137_558)))
in FStar_Syntax_Syntax.Error (_137_560))
in (Prims.raise _137_561))
end)))
in (aux false cres.FStar_Syntax_Syntax.res_typ))
end)
end))
in (tc_args ([], [], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs (FStar_Syntax_Util.lcomp_of_comp c) args))
end))
end
| _58_1486 -> begin
if (not (norm)) then begin
(let _137_562 = (unfold_whnf env tf)
in (check_function_app true _137_562))
end else begin
(let _137_565 = (let _137_564 = (let _137_563 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_137_563, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_137_564))
in (Prims.raise _137_565))
end
end))
in (let _137_567 = (let _137_566 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _137_566))
in (check_function_app false _137_567))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (
# 1001 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1002 "FStar.TypeChecker.Tc.fst"
let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(
# 1005 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in (
# 1006 "FStar.TypeChecker.Tc.fst"
let _58_1522 = (FStar_List.fold_left2 (fun _58_1503 _58_1506 _58_1509 -> (match ((_58_1503, _58_1506, _58_1509)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(
# 1007 "FStar.TypeChecker.Tc.fst"
let _58_1510 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1008 "FStar.TypeChecker.Tc.fst"
let _58_1515 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_58_1515) with
| (e, c, g) -> begin
(
# 1009 "FStar.TypeChecker.Tc.fst"
let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (
# 1010 "FStar.TypeChecker.Tc.fst"
let g = (let _137_577 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _137_577 g))
in (
# 1011 "FStar.TypeChecker.Tc.fst"
let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _137_581 = (let _137_579 = (let _137_578 = (FStar_Syntax_Syntax.as_arg e)
in (_137_578)::[])
in (FStar_List.append seen _137_579))
in (let _137_580 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_137_581, _137_580, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_58_1522) with
| (args, guard, ghost) -> begin
(
# 1015 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (
# 1016 "FStar.TypeChecker.Tc.fst"
let c = if ghost then begin
(let _137_582 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _137_582 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (
# 1017 "FStar.TypeChecker.Tc.fst"
let _58_1527 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_58_1527) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _58_1529 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (
# 1037 "FStar.TypeChecker.Tc.fst"
let _58_1536 = (FStar_Syntax_Subst.open_branch branch)
in (match (_58_1536) with
| (pattern, when_clause, branch_exp) -> begin
(
# 1038 "FStar.TypeChecker.Tc.fst"
let _58_1541 = branch
in (match (_58_1541) with
| (cpat, _58_1539, cbr) -> begin
(
# 1041 "FStar.TypeChecker.Tc.fst"
let tc_pat = (fun allow_implicits pat_t p0 -> (
# 1048 "FStar.TypeChecker.Tc.fst"
let _58_1549 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_58_1549) with
| (pat_bvs, exps, p) -> begin
(
# 1049 "FStar.TypeChecker.Tc.fst"
let _58_1550 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_594 = (FStar_Syntax_Print.pat_to_string p0)
in (let _137_593 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _137_594 _137_593)))
end else begin
()
end
in (
# 1051 "FStar.TypeChecker.Tc.fst"
let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (
# 1052 "FStar.TypeChecker.Tc.fst"
let _58_1556 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_58_1556) with
| (env1, _58_1555) -> begin
(
# 1053 "FStar.TypeChecker.Tc.fst"
let env1 = (
# 1053 "FStar.TypeChecker.Tc.fst"
let _58_1557 = env1
in {FStar_TypeChecker_Env.solver = _58_1557.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1557.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1557.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1557.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1557.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1557.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1557.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1557.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _58_1557.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1557.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1557.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1557.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1557.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1557.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1557.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1557.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1557.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_1557.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_1557.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1557.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1557.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1054 "FStar.TypeChecker.Tc.fst"
let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (
# 1055 "FStar.TypeChecker.Tc.fst"
let _58_1596 = (let _137_617 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (
# 1056 "FStar.TypeChecker.Tc.fst"
let _58_1562 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_597 = (FStar_Syntax_Print.term_to_string e)
in (let _137_596 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _137_597 _137_596)))
end else begin
()
end
in (
# 1059 "FStar.TypeChecker.Tc.fst"
let _58_1567 = (tc_term env1 e)
in (match (_58_1567) with
| (e, lc, g) -> begin
(
# 1061 "FStar.TypeChecker.Tc.fst"
let _58_1568 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_599 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _137_598 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _137_599 _137_598)))
end else begin
()
end
in (
# 1064 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (
# 1065 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (
# 1066 "FStar.TypeChecker.Tc.fst"
let _58_1574 = (let _137_600 = (FStar_TypeChecker_Rel.discharge_guard env (
# 1066 "FStar.TypeChecker.Tc.fst"
let _58_1572 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_1572.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_1572.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_1572.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _137_600 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1067 "FStar.TypeChecker.Tc.fst"
let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (
# 1068 "FStar.TypeChecker.Tc.fst"
let uvars_to_string = (fun uvs -> (let _137_605 = (let _137_604 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _137_604 (FStar_List.map (fun _58_1582 -> (match (_58_1582) with
| (u, _58_1581) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _137_605 (FStar_String.concat ", "))))
in (
# 1069 "FStar.TypeChecker.Tc.fst"
let uvs1 = (FStar_Syntax_Free.uvars e')
in (
# 1070 "FStar.TypeChecker.Tc.fst"
let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (
# 1071 "FStar.TypeChecker.Tc.fst"
let _58_1590 = if (let _137_606 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _137_606)) then begin
(
# 1072 "FStar.TypeChecker.Tc.fst"
let unresolved = (let _137_607 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _137_607 FStar_Util.set_elements))
in (let _137_615 = (let _137_614 = (let _137_613 = (let _137_612 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _137_611 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _137_610 = (let _137_609 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _58_1589 -> (match (_58_1589) with
| (u, _58_1588) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _137_609 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _137_612 _137_611 _137_610))))
in (_137_613, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_137_614))
in (Prims.raise _137_615)))
end else begin
()
end
in (
# 1079 "FStar.TypeChecker.Tc.fst"
let _58_1592 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_616 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _137_616))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _137_617 FStar_List.unzip))
in (match (_58_1596) with
| (exps, norm_exps) -> begin
(
# 1084 "FStar.TypeChecker.Tc.fst"
let p = (FStar_TypeChecker_Util.decorate_pattern env p exps)
in (p, pat_bvs, pat_env, exps, norm_exps))
end))))
end))))
end)))
in (
# 1088 "FStar.TypeChecker.Tc.fst"
let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (
# 1089 "FStar.TypeChecker.Tc.fst"
let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (
# 1090 "FStar.TypeChecker.Tc.fst"
let _58_1603 = (let _137_618 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _137_618 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_58_1603) with
| (scrutinee_env, _58_1602) -> begin
(
# 1093 "FStar.TypeChecker.Tc.fst"
let _58_1609 = (tc_pat true pat_t pattern)
in (match (_58_1609) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(
# 1096 "FStar.TypeChecker.Tc.fst"
let _58_1619 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(
# 1103 "FStar.TypeChecker.Tc.fst"
let _58_1616 = (let _137_619 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _137_619 e))
in (match (_58_1616) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_58_1619) with
| (when_clause, g_when) -> begin
(
# 1107 "FStar.TypeChecker.Tc.fst"
let _58_1623 = (tc_term pat_env branch_exp)
in (match (_58_1623) with
| (branch_exp, c, g_branch) -> begin
(
# 1111 "FStar.TypeChecker.Tc.fst"
let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _137_621 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _137_620 -> Some (_137_620)) _137_621))
end)
in (
# 1118 "FStar.TypeChecker.Tc.fst"
let _58_1679 = (
# 1121 "FStar.TypeChecker.Tc.fst"
let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (
# 1122 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _58_1641 -> begin
(
# 1128 "FStar.TypeChecker.Tc.fst"
let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _137_625 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _137_624 -> Some (_137_624)) _137_625))
end))
end))) None))
in (
# 1133 "FStar.TypeChecker.Tc.fst"
let _58_1649 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_58_1649) with
| (c, g_branch) -> begin
(
# 1137 "FStar.TypeChecker.Tc.fst"
let _58_1674 = (match ((eqs, when_condition)) with
| (None, None) -> begin
(c, g_when)
end
| (Some (f), None) -> begin
(
# 1143 "FStar.TypeChecker.Tc.fst"
let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1144 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _137_628 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _137_627 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_137_628, _137_627)))))
end
| (Some (f), Some (w)) -> begin
(
# 1149 "FStar.TypeChecker.Tc.fst"
let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1150 "FStar.TypeChecker.Tc.fst"
let g_fw = (let _137_629 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_137_629))
in (let _137_632 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _137_631 = (let _137_630 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _137_630 g_when))
in (_137_632, _137_631)))))
end
| (None, Some (w)) -> begin
(
# 1155 "FStar.TypeChecker.Tc.fst"
let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (
# 1156 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _137_633 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_137_633, g_when))))
end)
in (match (_58_1674) with
| (c_weak, g_when_weak) -> begin
(
# 1161 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _137_635 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _137_634 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_137_635, _137_634, g_branch))))
end))
end)))
in (match (_58_1679) with
| (c, g_when, g_branch) -> begin
(
# 1179 "FStar.TypeChecker.Tc.fst"
let branch_guard = (
# 1181 "FStar.TypeChecker.Tc.fst"
let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (
# 1182 "FStar.TypeChecker.Tc.fst"
let discriminate = (fun scrutinee_tm f -> if ((let _137_645 = (let _137_644 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _137_644))
in (FStar_List.length _137_645)) > 1) then begin
(
# 1185 "FStar.TypeChecker.Tc.fst"
let disc = (let _137_646 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _137_646 FStar_Syntax_Syntax.Delta_equational None))
in (
# 1186 "FStar.TypeChecker.Tc.fst"
let disc = (let _137_648 = (let _137_647 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_137_647)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _137_648 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _137_649 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_137_649)::[])))
end else begin
[]
end)
in (
# 1190 "FStar.TypeChecker.Tc.fst"
let fail = (fun _58_1689 -> (match (()) with
| () -> begin
(let _137_655 = (let _137_654 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _137_653 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _137_652 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _137_654 _137_653 _137_652))))
in (FStar_All.failwith _137_655))
end))
in (
# 1196 "FStar.TypeChecker.Tc.fst"
let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _58_1696) -> begin
(head_constructor t)
end
| _58_1700 -> begin
(fail ())
end))
in (
# 1201 "FStar.TypeChecker.Tc.fst"
let pat_exp = (let _137_658 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _137_658 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_58_1725) -> begin
(let _137_663 = (let _137_662 = (let _137_661 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _137_660 = (let _137_659 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_137_659)::[])
in (_137_661)::_137_660))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _137_662 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_137_663)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 1210 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _137_664 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _137_664))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 1215 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(
# 1218 "FStar.TypeChecker.Tc.fst"
let sub_term_guards = (let _137_671 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _58_1743 -> (match (_58_1743) with
| (ei, _58_1742) -> begin
(
# 1219 "FStar.TypeChecker.Tc.fst"
let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _58_1747 -> begin
(
# 1223 "FStar.TypeChecker.Tc.fst"
let sub_term = (let _137_670 = (let _137_667 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _137_667 FStar_Syntax_Syntax.Delta_equational None))
in (let _137_669 = (let _137_668 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_137_668)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _137_670 _137_669 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _137_671 FStar_List.flatten))
in (let _137_672 = (discriminate scrutinee_tm f)
in (FStar_List.append _137_672 sub_term_guards)))
end)
end
| _58_1751 -> begin
[]
end))))))
in (
# 1229 "FStar.TypeChecker.Tc.fst"
let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(
# 1232 "FStar.TypeChecker.Tc.fst"
let t = (let _137_677 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _137_677))
in (
# 1233 "FStar.TypeChecker.Tc.fst"
let _58_1759 = (FStar_Syntax_Util.type_u ())
in (match (_58_1759) with
| (k, _58_1758) -> begin
(
# 1234 "FStar.TypeChecker.Tc.fst"
let _58_1765 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_58_1765) with
| (t, _58_1762, _58_1764) -> begin
t
end))
end)))
end)
in (
# 1238 "FStar.TypeChecker.Tc.fst"
let branch_guard = (let _137_678 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _137_678 FStar_Syntax_Util.mk_disj_l))
in (
# 1241 "FStar.TypeChecker.Tc.fst"
let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
in (
# 1247 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (
# 1249 "FStar.TypeChecker.Tc.fst"
let _58_1773 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_679 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _137_679))
end else begin
()
end
in (let _137_680 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_137_680, branch_guard, c, guard)))))
end)))
end))
end))
end))
end)))))
end))
end)))
and check_top_level_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1263 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1266 "FStar.TypeChecker.Tc.fst"
let _58_1790 = (check_let_bound_def true env lb)
in (match (_58_1790) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(
# 1268 "FStar.TypeChecker.Tc.fst"
let _58_1802 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(
# 1271 "FStar.TypeChecker.Tc.fst"
let g1 = (let _137_683 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _137_683 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1272 "FStar.TypeChecker.Tc.fst"
let _58_1797 = (let _137_687 = (let _137_686 = (let _137_685 = (let _137_684 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _137_684))
in (_137_685)::[])
in (FStar_TypeChecker_Util.generalize env _137_686))
in (FStar_List.hd _137_687))
in (match (_58_1797) with
| (_58_1793, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_58_1802) with
| (g1, e1, univ_vars, c1) -> begin
(
# 1276 "FStar.TypeChecker.Tc.fst"
let _58_1812 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(
# 1278 "FStar.TypeChecker.Tc.fst"
let _58_1805 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_58_1805) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(
# 1281 "FStar.TypeChecker.Tc.fst"
let _58_1806 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _137_688 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _137_688 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _137_689 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_137_689, c1)))
end
end))
end else begin
(
# 1285 "FStar.TypeChecker.Tc.fst"
let _58_1808 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _137_690 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _137_690)))
end
in (match (_58_1812) with
| (e2, c1) -> begin
(
# 1290 "FStar.TypeChecker.Tc.fst"
let cres = (let _137_691 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _137_691))
in (
# 1291 "FStar.TypeChecker.Tc.fst"
let _58_1814 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1293 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _137_692 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_137_692, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _58_1818 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1310 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1313 "FStar.TypeChecker.Tc.fst"
let env = (
# 1313 "FStar.TypeChecker.Tc.fst"
let _58_1829 = env
in {FStar_TypeChecker_Env.solver = _58_1829.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1829.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1829.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1829.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1829.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1829.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1829.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1829.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1829.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1829.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1829.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1829.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1829.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_1829.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1829.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1829.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1829.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_1829.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_1829.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1829.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1829.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1314 "FStar.TypeChecker.Tc.fst"
let _58_1838 = (let _137_696 = (let _137_695 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _137_695 Prims.fst))
in (check_let_bound_def false _137_696 lb))
in (match (_58_1838) with
| (e1, _58_1834, c1, g1, annotated) -> begin
(
# 1315 "FStar.TypeChecker.Tc.fst"
let x = (
# 1315 "FStar.TypeChecker.Tc.fst"
let _58_1839 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_1839.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1839.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (
# 1316 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (
# 1317 "FStar.TypeChecker.Tc.fst"
let _58_1845 = (let _137_698 = (let _137_697 = (FStar_Syntax_Syntax.mk_binder x)
in (_137_697)::[])
in (FStar_Syntax_Subst.open_term _137_698 e2))
in (match (_58_1845) with
| (xb, e2) -> begin
(
# 1318 "FStar.TypeChecker.Tc.fst"
let xbinder = (FStar_List.hd xb)
in (
# 1319 "FStar.TypeChecker.Tc.fst"
let x = (Prims.fst xbinder)
in (
# 1320 "FStar.TypeChecker.Tc.fst"
let _58_1851 = (let _137_699 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _137_699 e2))
in (match (_58_1851) with
| (e2, c2, g2) -> begin
(
# 1321 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (x), c2))
in (
# 1322 "FStar.TypeChecker.Tc.fst"
let e = (let _137_702 = (let _137_701 = (let _137_700 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _137_700))
in FStar_Syntax_Syntax.Tm_let (_137_701))
in (FStar_Syntax_Syntax.mk _137_702 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 1323 "FStar.TypeChecker.Tc.fst"
let x_eq_e1 = (let _137_705 = (let _137_704 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _137_704 e1))
in (FStar_All.pipe_left (fun _137_703 -> FStar_TypeChecker_Common.NonTrivial (_137_703)) _137_705))
in (
# 1324 "FStar.TypeChecker.Tc.fst"
let g2 = (let _137_707 = (let _137_706 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _137_706 g2))
in (FStar_TypeChecker_Rel.close_guard xb _137_707))
in (
# 1326 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if annotated then begin
(e, cres, guard)
end else begin
(
# 1330 "FStar.TypeChecker.Tc.fst"
let _58_1857 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end)))))
end))))
end))))
end)))
end
| _58_1860 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1339 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1342 "FStar.TypeChecker.Tc.fst"
let _58_1872 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_58_1872) with
| (lbs, e2) -> begin
(
# 1344 "FStar.TypeChecker.Tc.fst"
let _58_1875 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1875) with
| (env0, topt) -> begin
(
# 1345 "FStar.TypeChecker.Tc.fst"
let _58_1878 = (build_let_rec_env true env0 lbs)
in (match (_58_1878) with
| (lbs, rec_env) -> begin
(
# 1346 "FStar.TypeChecker.Tc.fst"
let _58_1881 = (check_let_recs rec_env lbs)
in (match (_58_1881) with
| (lbs, g_lbs) -> begin
(
# 1347 "FStar.TypeChecker.Tc.fst"
let g_lbs = (let _137_710 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _137_710 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1349 "FStar.TypeChecker.Tc.fst"
let all_lb_names = (let _137_713 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _137_713 (fun _137_712 -> Some (_137_712))))
in (
# 1351 "FStar.TypeChecker.Tc.fst"
let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(
# 1357 "FStar.TypeChecker.Tc.fst"
let ecs = (let _137_717 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _137_716 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _137_716)))))
in (FStar_TypeChecker_Util.generalize env _137_717))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _58_1892 -> (match (_58_1892) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (
# 1364 "FStar.TypeChecker.Tc.fst"
let cres = (let _137_719 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _137_719))
in (
# 1365 "FStar.TypeChecker.Tc.fst"
let _58_1895 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1367 "FStar.TypeChecker.Tc.fst"
let _58_1899 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_1899) with
| (lbs, e2) -> begin
(let _137_721 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _137_720 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_137_721, cres, _137_720)))
end)))))))
end))
end))
end))
end))
end
| _58_1901 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1378 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1381 "FStar.TypeChecker.Tc.fst"
let _58_1913 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_58_1913) with
| (lbs, e2) -> begin
(
# 1383 "FStar.TypeChecker.Tc.fst"
let _58_1916 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1916) with
| (env0, topt) -> begin
(
# 1384 "FStar.TypeChecker.Tc.fst"
let _58_1919 = (build_let_rec_env false env0 lbs)
in (match (_58_1919) with
| (lbs, rec_env) -> begin
(
# 1385 "FStar.TypeChecker.Tc.fst"
let _58_1922 = (check_let_recs rec_env lbs)
in (match (_58_1922) with
| (lbs, g_lbs) -> begin
(
# 1387 "FStar.TypeChecker.Tc.fst"
let _58_1934 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (
# 1388 "FStar.TypeChecker.Tc.fst"
let x = (
# 1388 "FStar.TypeChecker.Tc.fst"
let _58_1925 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_1925.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1925.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (
# 1389 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1389 "FStar.TypeChecker.Tc.fst"
let _58_1928 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _58_1928.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _58_1928.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _58_1928.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _58_1928.FStar_Syntax_Syntax.lbdef})
in (
# 1390 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], lb.FStar_Syntax_Syntax.lbtyp))
in (env, lb))))) env))
in (match (_58_1934) with
| (env, lbs) -> begin
(
# 1393 "FStar.TypeChecker.Tc.fst"
let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (
# 1395 "FStar.TypeChecker.Tc.fst"
let _58_1940 = (tc_term env e2)
in (match (_58_1940) with
| (e2, cres, g2) -> begin
(
# 1396 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (
# 1397 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (
# 1398 "FStar.TypeChecker.Tc.fst"
let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (
# 1399 "FStar.TypeChecker.Tc.fst"
let cres = (
# 1399 "FStar.TypeChecker.Tc.fst"
let _58_1944 = cres
in {FStar_Syntax_Syntax.eff_name = _58_1944.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _58_1944.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_1944.FStar_Syntax_Syntax.comp})
in (
# 1401 "FStar.TypeChecker.Tc.fst"
let _58_1949 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_1949) with
| (lbs, e2) -> begin
(
# 1402 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_58_1952) -> begin
(e, cres, guard)
end
| None -> begin
(
# 1406 "FStar.TypeChecker.Tc.fst"
let _58_1955 = (check_no_escape None env bvs tres)
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
| _58_1958 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (
# 1417 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1418 "FStar.TypeChecker.Tc.fst"
let _58_1991 = (FStar_List.fold_left (fun _58_1965 lb -> (match (_58_1965) with
| (lbs, env) -> begin
(
# 1419 "FStar.TypeChecker.Tc.fst"
let _58_1970 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_58_1970) with
| (univ_vars, t, check_t) -> begin
(
# 1420 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (
# 1421 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (
# 1422 "FStar.TypeChecker.Tc.fst"
let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(
# 1427 "FStar.TypeChecker.Tc.fst"
let _58_1979 = (let _137_733 = (let _137_732 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _137_732))
in (tc_check_tot_or_gtot_term (
# 1427 "FStar.TypeChecker.Tc.fst"
let _58_1973 = env0
in {FStar_TypeChecker_Env.solver = _58_1973.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1973.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1973.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1973.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1973.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1973.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1973.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1973.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1973.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1973.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1973.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1973.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1973.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1973.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _58_1973.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1973.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1973.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_1973.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_1973.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1973.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1973.FStar_TypeChecker_Env.use_bv_sorts}) t _137_733))
in (match (_58_1979) with
| (t, _58_1977, g) -> begin
(
# 1428 "FStar.TypeChecker.Tc.fst"
let _58_1980 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (
# 1430 "FStar.TypeChecker.Tc.fst"
let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(
# 1432 "FStar.TypeChecker.Tc.fst"
let _58_1983 = env
in {FStar_TypeChecker_Env.solver = _58_1983.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1983.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1983.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1983.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1983.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1983.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1983.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1983.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1983.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1983.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1983.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1983.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1983.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1983.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1983.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1983.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1983.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_1983.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_1983.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1983.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1983.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (
# 1434 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1434 "FStar.TypeChecker.Tc.fst"
let _58_1986 = lb
in {FStar_Syntax_Syntax.lbname = _58_1986.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _58_1986.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_58_1991) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (
# 1441 "FStar.TypeChecker.Tc.fst"
let _58_2004 = (let _137_738 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 1442 "FStar.TypeChecker.Tc.fst"
let _58_1998 = (let _137_737 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _137_737 lb.FStar_Syntax_Syntax.lbdef))
in (match (_58_1998) with
| (e, c, g) -> begin
(
# 1443 "FStar.TypeChecker.Tc.fst"
let _58_1999 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1445 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _137_738 FStar_List.unzip))
in (match (_58_2004) with
| (lbs, gs) -> begin
(
# 1447 "FStar.TypeChecker.Tc.fst"
let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (
# 1461 "FStar.TypeChecker.Tc.fst"
let _58_2012 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2012) with
| (env1, _58_2011) -> begin
(
# 1462 "FStar.TypeChecker.Tc.fst"
let e1 = lb.FStar_Syntax_Syntax.lbdef
in (
# 1465 "FStar.TypeChecker.Tc.fst"
let _58_2018 = (check_lbtyp top_level env lb)
in (match (_58_2018) with
| (topt, wf_annot, univ_vars, env1) -> begin
(
# 1467 "FStar.TypeChecker.Tc.fst"
let _58_2019 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1471 "FStar.TypeChecker.Tc.fst"
let _58_2026 = (tc_maybe_toplevel_term (
# 1471 "FStar.TypeChecker.Tc.fst"
let _58_2021 = env1
in {FStar_TypeChecker_Env.solver = _58_2021.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2021.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2021.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2021.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2021.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2021.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2021.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2021.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2021.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2021.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2021.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2021.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2021.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _58_2021.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2021.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2021.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2021.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_2021.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_2021.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2021.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2021.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_58_2026) with
| (e1, c1, g1) -> begin
(
# 1474 "FStar.TypeChecker.Tc.fst"
let _58_2030 = (let _137_745 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_2027 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _137_745 e1 c1 wf_annot))
in (match (_58_2030) with
| (c1, guard_f) -> begin
(
# 1477 "FStar.TypeChecker.Tc.fst"
let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (
# 1479 "FStar.TypeChecker.Tc.fst"
let _58_2032 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _137_746 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _137_746))
end else begin
()
end
in (let _137_747 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _137_747))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (
# 1491 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 1494 "FStar.TypeChecker.Tc.fst"
let _58_2039 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _58_2042 -> begin
(
# 1498 "FStar.TypeChecker.Tc.fst"
let _58_2045 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_58_2045) with
| (univ_vars, t) -> begin
(
# 1499 "FStar.TypeChecker.Tc.fst"
let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _137_751 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _137_751))
end else begin
(
# 1506 "FStar.TypeChecker.Tc.fst"
let _58_2050 = (FStar_Syntax_Util.type_u ())
in (match (_58_2050) with
| (k, _58_2049) -> begin
(
# 1507 "FStar.TypeChecker.Tc.fst"
let _58_2055 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_58_2055) with
| (t, _58_2053, g) -> begin
(
# 1508 "FStar.TypeChecker.Tc.fst"
let _58_2056 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _137_754 = (let _137_752 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _137_752))
in (let _137_753 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _137_754 _137_753)))
end else begin
()
end
in (
# 1512 "FStar.TypeChecker.Tc.fst"
let t = (norm env1 t)
in (let _137_755 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _137_755))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _58_2062 -> (match (_58_2062) with
| (x, imp) -> begin
(
# 1517 "FStar.TypeChecker.Tc.fst"
let _58_2065 = (FStar_Syntax_Util.type_u ())
in (match (_58_2065) with
| (tu, u) -> begin
(
# 1518 "FStar.TypeChecker.Tc.fst"
let _58_2070 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_58_2070) with
| (t, _58_2068, g) -> begin
(
# 1519 "FStar.TypeChecker.Tc.fst"
let x = ((
# 1519 "FStar.TypeChecker.Tc.fst"
let _58_2071 = x
in {FStar_Syntax_Syntax.ppname = _58_2071.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2071.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (
# 1520 "FStar.TypeChecker.Tc.fst"
let _58_2074 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_759 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _137_758 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _137_759 _137_758)))
end else begin
()
end
in (let _137_760 = (maybe_push_binding env x)
in (x, _137_760, g, u))))
end))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe Prims.list) = (fun env bs -> (
# 1525 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_TypeChecker_Rel.trivial_guard, [])
end
| b::bs -> begin
(
# 1528 "FStar.TypeChecker.Tc.fst"
let _58_2089 = (tc_binder env b)
in (match (_58_2089) with
| (b, env', g, u) -> begin
(
# 1529 "FStar.TypeChecker.Tc.fst"
let _58_2094 = (aux env' bs)
in (match (_58_2094) with
| (bs, env', g', us) -> begin
(let _137_768 = (let _137_767 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _137_767))
in ((b)::bs, env', _137_768, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (
# 1534 "FStar.TypeChecker.Tc.fst"
let tc_args = (fun env args -> (FStar_List.fold_right (fun _58_2102 _58_2105 -> (match ((_58_2102, _58_2105)) with
| ((t, imp), (args, g)) -> begin
(
# 1538 "FStar.TypeChecker.Tc.fst"
let _58_2110 = (tc_term env t)
in (match (_58_2110) with
| (t, _58_2108, g') -> begin
(let _137_777 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _137_777))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _58_2114 -> (match (_58_2114) with
| (pats, g) -> begin
(
# 1541 "FStar.TypeChecker.Tc.fst"
let _58_2117 = (tc_args env p)
in (match (_58_2117) with
| (args, g') -> begin
(let _137_780 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _137_780))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1546 "FStar.TypeChecker.Tc.fst"
let _58_2123 = (tc_maybe_toplevel_term env e)
in (match (_58_2123) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(
# 1549 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (
# 1550 "FStar.TypeChecker.Tc.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 1551 "FStar.TypeChecker.Tc.fst"
let _58_2126 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_783 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _137_783))
end else begin
()
end
in (
# 1552 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 1553 "FStar.TypeChecker.Tc.fst"
let _58_2131 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _137_784 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_137_784, false))
end else begin
(let _137_785 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_137_785, true))
end
in (match (_58_2131) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _137_786 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _137_786))
end
| _58_2135 -> begin
if allow_ghost then begin
(let _137_789 = (let _137_788 = (let _137_787 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_137_787, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_137_788))
in (Prims.raise _137_789))
end else begin
(let _137_792 = (let _137_791 = (let _137_790 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_137_790, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_137_791))
in (Prims.raise _137_792))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 1567 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))

# 1571 "FStar.TypeChecker.Tc.fst"
let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (
# 1572 "FStar.TypeChecker.Tc.fst"
let _58_2145 = (tc_tot_or_gtot_term env t)
in (match (_58_2145) with
| (t, c, g) -> begin
(
# 1573 "FStar.TypeChecker.Tc.fst"
let _58_2146 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))

# 1576 "FStar.TypeChecker.Tc.fst"
let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (
# 1577 "FStar.TypeChecker.Tc.fst"
let _58_2154 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_2154) with
| (t, c, g) -> begin
(
# 1578 "FStar.TypeChecker.Tc.fst"
let _58_2155 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))

# 1581 "FStar.TypeChecker.Tc.fst"
let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _137_812 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _137_812)))

# 1584 "FStar.TypeChecker.Tc.fst"
let check_nogen = (fun env t k -> (
# 1585 "FStar.TypeChecker.Tc.fst"
let t = (tc_check_trivial_guard env t k)
in (let _137_816 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _137_816))))

# 1588 "FStar.TypeChecker.Tc.fst"
let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (
# 1589 "FStar.TypeChecker.Tc.fst"
let _58_2170 = (tc_binders env tps)
in (match (_58_2170) with
| (tps, env, g, us) -> begin
(
# 1590 "FStar.TypeChecker.Tc.fst"
let _58_2171 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))

# 1593 "FStar.TypeChecker.Tc.fst"
let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (
# 1594 "FStar.TypeChecker.Tc.fst"
let fail = (fun _58_2177 -> (match (()) with
| () -> begin
(let _137_831 = (let _137_830 = (let _137_829 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_137_829, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_137_830))
in (Prims.raise _137_831))
end))
in (
# 1595 "FStar.TypeChecker.Tc.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1598 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _58_2194)::(wp, _58_2190)::(_wlp, _58_2186)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _58_2198 -> begin
(fail ())
end))
end
| _58_2200 -> begin
(fail ())
end))))

# 1605 "FStar.TypeChecker.Tc.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 1608 "FStar.TypeChecker.Tc.fst"
let _58_2207 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_58_2207) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _58_2209 -> begin
(
# 1611 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow binders c)
in (
# 1612 "FStar.TypeChecker.Tc.fst"
let _58_2213 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_58_2213) with
| (uvs, t') -> begin
(match ((let _137_838 = (FStar_Syntax_Subst.compress t')
in _137_838.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _58_2219 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 1617 "FStar.TypeChecker.Tc.fst"
let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (
# 1618 "FStar.TypeChecker.Tc.fst"
let fail = (fun t -> (let _137_849 = (let _137_848 = (let _137_847 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_137_847, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_137_848))
in (Prims.raise _137_849)))
in (match ((let _137_850 = (FStar_Syntax_Subst.compress signature)
in _137_850.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1621 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _58_2240)::(wp, _58_2236)::(_wlp, _58_2232)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _58_2244 -> begin
(fail signature)
end))
end
| _58_2246 -> begin
(fail signature)
end)))

# 1628 "FStar.TypeChecker.Tc.fst"
let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (
# 1629 "FStar.TypeChecker.Tc.fst"
let _58_2251 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_58_2251) with
| (a, wp) -> begin
(
# 1630 "FStar.TypeChecker.Tc.fst"
let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _58_2254 -> begin
(
# 1634 "FStar.TypeChecker.Tc.fst"
let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (
# 1635 "FStar.TypeChecker.Tc.fst"
let op = (fun ts -> (
# 1636 "FStar.TypeChecker.Tc.fst"
let _58_2258 = ()
in (
# 1637 "FStar.TypeChecker.Tc.fst"
let t0 = (Prims.snd ts)
in (
# 1638 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (
# 1640 "FStar.TypeChecker.Tc.fst"
let _58_2262 = ed
in (let _137_869 = (op ed.FStar_Syntax_Syntax.ret)
in (let _137_868 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _137_867 = (op ed.FStar_Syntax_Syntax.bind_wlp)
in (let _137_866 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _137_865 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _137_864 = (op ed.FStar_Syntax_Syntax.ite_wlp)
in (let _137_863 = (op ed.FStar_Syntax_Syntax.wp_binop)
in (let _137_862 = (op ed.FStar_Syntax_Syntax.wp_as_type)
in (let _137_861 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _137_860 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _137_859 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _137_858 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _137_857 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _58_2262.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2262.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _58_2262.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _58_2262.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _58_2262.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _137_869; FStar_Syntax_Syntax.bind_wp = _137_868; FStar_Syntax_Syntax.bind_wlp = _137_867; FStar_Syntax_Syntax.if_then_else = _137_866; FStar_Syntax_Syntax.ite_wp = _137_865; FStar_Syntax_Syntax.ite_wlp = _137_864; FStar_Syntax_Syntax.wp_binop = _137_863; FStar_Syntax_Syntax.wp_as_type = _137_862; FStar_Syntax_Syntax.close_wp = _137_861; FStar_Syntax_Syntax.assert_p = _137_860; FStar_Syntax_Syntax.assume_p = _137_859; FStar_Syntax_Syntax.null_wp = _137_858; FStar_Syntax_Syntax.trivial = _137_857}))))))))))))))))
end)
in (ed, a, wp))
end)))

# 1656 "FStar.TypeChecker.Tc.fst"
let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (
# 1657 "FStar.TypeChecker.Tc.fst"
let _58_2267 = ()
in (
# 1658 "FStar.TypeChecker.Tc.fst"
let _58_2271 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_58_2271) with
| (binders_un, signature_un) -> begin
(
# 1659 "FStar.TypeChecker.Tc.fst"
let _58_2276 = (tc_tparams env0 binders_un)
in (match (_58_2276) with
| (binders, env, _58_2275) -> begin
(
# 1660 "FStar.TypeChecker.Tc.fst"
let _58_2280 = (tc_trivial_guard env signature_un)
in (match (_58_2280) with
| (signature, _58_2279) -> begin
(
# 1661 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1661 "FStar.TypeChecker.Tc.fst"
let _58_2281 = ed
in {FStar_Syntax_Syntax.qualifiers = _58_2281.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2281.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _58_2281.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _58_2281.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _58_2281.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _58_2281.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = _58_2281.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _58_2281.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _58_2281.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = _58_2281.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _58_2281.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _58_2281.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _58_2281.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _58_2281.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _58_2281.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _58_2281.FStar_Syntax_Syntax.trivial})
in (
# 1664 "FStar.TypeChecker.Tc.fst"
let _58_2287 = (open_effect_decl env ed)
in (match (_58_2287) with
| (ed, a, wp_a) -> begin
(
# 1665 "FStar.TypeChecker.Tc.fst"
let get_effect_signature = (fun _58_2289 -> (match (()) with
| () -> begin
(
# 1666 "FStar.TypeChecker.Tc.fst"
let _58_2293 = (tc_trivial_guard env signature_un)
in (match (_58_2293) with
| (signature, _58_2292) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (
# 1670 "FStar.TypeChecker.Tc.fst"
let env = (let _137_876 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _137_876))
in (
# 1672 "FStar.TypeChecker.Tc.fst"
let _58_2295 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _137_879 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _137_878 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _137_877 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checked effect signature: %s %s : %s\n" _137_879 _137_878 _137_877))))
end else begin
()
end
in (
# 1678 "FStar.TypeChecker.Tc.fst"
let check_and_gen' = (fun env _58_2302 k -> (match (_58_2302) with
| (_58_2300, t) -> begin
(check_and_gen env t k)
end))
in (
# 1681 "FStar.TypeChecker.Tc.fst"
let ret = (
# 1682 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_891 = (let _137_889 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_888 = (let _137_887 = (let _137_886 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _137_886))
in (_137_887)::[])
in (_137_889)::_137_888))
in (let _137_890 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _137_891 _137_890)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (
# 1685 "FStar.TypeChecker.Tc.fst"
let bind_wp = (
# 1686 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1687 "FStar.TypeChecker.Tc.fst"
let _58_2309 = (get_effect_signature ())
in (match (_58_2309) with
| (b, wp_b) -> begin
(
# 1688 "FStar.TypeChecker.Tc.fst"
let a_wp_b = (let _137_895 = (let _137_893 = (let _137_892 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _137_892))
in (_137_893)::[])
in (let _137_894 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _137_895 _137_894)))
in (
# 1689 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = a_wp_b
in (
# 1690 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_908 = (let _137_906 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_905 = (let _137_904 = (FStar_Syntax_Syntax.mk_binder b)
in (let _137_903 = (let _137_902 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _137_901 = (let _137_900 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _137_899 = (let _137_898 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (let _137_897 = (let _137_896 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_137_896)::[])
in (_137_898)::_137_897))
in (_137_900)::_137_899))
in (_137_902)::_137_901))
in (_137_904)::_137_903))
in (_137_906)::_137_905))
in (let _137_907 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _137_908 _137_907)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k))))
end)))
in (
# 1696 "FStar.TypeChecker.Tc.fst"
let bind_wlp = (
# 1697 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1698 "FStar.TypeChecker.Tc.fst"
let _58_2317 = (get_effect_signature ())
in (match (_58_2317) with
| (b, wlp_b) -> begin
(
# 1699 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = (let _137_912 = (let _137_910 = (let _137_909 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _137_909))
in (_137_910)::[])
in (let _137_911 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _137_912 _137_911)))
in (
# 1700 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_921 = (let _137_919 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_918 = (let _137_917 = (FStar_Syntax_Syntax.mk_binder b)
in (let _137_916 = (let _137_915 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _137_914 = (let _137_913 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_137_913)::[])
in (_137_915)::_137_914))
in (_137_917)::_137_916))
in (_137_919)::_137_918))
in (let _137_920 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _137_921 _137_920)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wlp expected_k)))
end)))
in (
# 1706 "FStar.TypeChecker.Tc.fst"
let if_then_else = (
# 1707 "FStar.TypeChecker.Tc.fst"
let p = (let _137_923 = (let _137_922 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _137_922 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _137_923))
in (
# 1708 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_932 = (let _137_930 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_929 = (let _137_928 = (FStar_Syntax_Syntax.mk_binder p)
in (let _137_927 = (let _137_926 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _137_925 = (let _137_924 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_137_924)::[])
in (_137_926)::_137_925))
in (_137_928)::_137_927))
in (_137_930)::_137_929))
in (let _137_931 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _137_932 _137_931)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (
# 1714 "FStar.TypeChecker.Tc.fst"
let ite_wp = (
# 1715 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1716 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_939 = (let _137_937 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_936 = (let _137_935 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _137_934 = (let _137_933 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_137_933)::[])
in (_137_935)::_137_934))
in (_137_937)::_137_936))
in (let _137_938 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _137_939 _137_938)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k)))
in (
# 1722 "FStar.TypeChecker.Tc.fst"
let ite_wlp = (
# 1723 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1724 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_944 = (let _137_942 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_941 = (let _137_940 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (_137_940)::[])
in (_137_942)::_137_941))
in (let _137_943 = (FStar_Syntax_Syntax.mk_Total wlp_a)
in (FStar_Syntax_Util.arrow _137_944 _137_943)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wlp expected_k)))
in (
# 1729 "FStar.TypeChecker.Tc.fst"
let wp_binop = (
# 1730 "FStar.TypeChecker.Tc.fst"
let bin_op = (
# 1731 "FStar.TypeChecker.Tc.fst"
let _58_2332 = (FStar_Syntax_Util.type_u ())
in (match (_58_2332) with
| (t1, u1) -> begin
(
# 1732 "FStar.TypeChecker.Tc.fst"
let _58_2335 = (FStar_Syntax_Util.type_u ())
in (match (_58_2335) with
| (t2, u2) -> begin
(
# 1733 "FStar.TypeChecker.Tc.fst"
let t = (let _137_945 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_max ((u1)::(u2)::[]))) None _137_945))
in (let _137_950 = (let _137_948 = (FStar_Syntax_Syntax.null_binder t1)
in (let _137_947 = (let _137_946 = (FStar_Syntax_Syntax.null_binder t2)
in (_137_946)::[])
in (_137_948)::_137_947))
in (let _137_949 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _137_950 _137_949))))
end))
end))
in (
# 1735 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_959 = (let _137_957 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_956 = (let _137_955 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _137_954 = (let _137_953 = (FStar_Syntax_Syntax.null_binder bin_op)
in (let _137_952 = (let _137_951 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_137_951)::[])
in (_137_953)::_137_952))
in (_137_955)::_137_954))
in (_137_957)::_137_956))
in (let _137_958 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _137_959 _137_958)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_binop expected_k)))
in (
# 1742 "FStar.TypeChecker.Tc.fst"
let wp_as_type = (
# 1743 "FStar.TypeChecker.Tc.fst"
let _58_2343 = (FStar_Syntax_Util.type_u ())
in (match (_58_2343) with
| (t, _58_2342) -> begin
(
# 1744 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_964 = (let _137_962 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_961 = (let _137_960 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_137_960)::[])
in (_137_962)::_137_961))
in (let _137_963 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _137_964 _137_963)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (
# 1749 "FStar.TypeChecker.Tc.fst"
let close_wp = (
# 1750 "FStar.TypeChecker.Tc.fst"
let b = (let _137_966 = (let _137_965 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _137_965 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _137_966))
in (
# 1751 "FStar.TypeChecker.Tc.fst"
let b_wp_a = (let _137_970 = (let _137_968 = (let _137_967 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _137_967))
in (_137_968)::[])
in (let _137_969 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _137_970 _137_969)))
in (
# 1752 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_977 = (let _137_975 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_974 = (let _137_973 = (FStar_Syntax_Syntax.mk_binder b)
in (let _137_972 = (let _137_971 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_137_971)::[])
in (_137_973)::_137_972))
in (_137_975)::_137_974))
in (let _137_976 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _137_977 _137_976)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (
# 1756 "FStar.TypeChecker.Tc.fst"
let assert_p = (
# 1757 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_986 = (let _137_984 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_983 = (let _137_982 = (let _137_979 = (let _137_978 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _137_978 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _137_979))
in (let _137_981 = (let _137_980 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_137_980)::[])
in (_137_982)::_137_981))
in (_137_984)::_137_983))
in (let _137_985 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _137_986 _137_985)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (
# 1763 "FStar.TypeChecker.Tc.fst"
let assume_p = (
# 1764 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_995 = (let _137_993 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_992 = (let _137_991 = (let _137_988 = (let _137_987 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _137_987 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _137_988))
in (let _137_990 = (let _137_989 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_137_989)::[])
in (_137_991)::_137_990))
in (_137_993)::_137_992))
in (let _137_994 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _137_995 _137_994)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (
# 1770 "FStar.TypeChecker.Tc.fst"
let null_wp = (
# 1771 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_998 = (let _137_996 = (FStar_Syntax_Syntax.mk_binder a)
in (_137_996)::[])
in (let _137_997 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _137_998 _137_997)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (
# 1775 "FStar.TypeChecker.Tc.fst"
let trivial_wp = (
# 1776 "FStar.TypeChecker.Tc.fst"
let _58_2359 = (FStar_Syntax_Util.type_u ())
in (match (_58_2359) with
| (t, _58_2358) -> begin
(
# 1777 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_1003 = (let _137_1001 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_1000 = (let _137_999 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_137_999)::[])
in (_137_1001)::_137_1000))
in (let _137_1002 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _137_1003 _137_1002)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (
# 1783 "FStar.TypeChecker.Tc.fst"
let t = (let _137_1004 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _137_1004))
in (
# 1784 "FStar.TypeChecker.Tc.fst"
let _58_2365 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_58_2365) with
| (univs, t) -> begin
(
# 1785 "FStar.TypeChecker.Tc.fst"
let _58_2381 = (match ((let _137_1006 = (let _137_1005 = (FStar_Syntax_Subst.compress t)
in _137_1005.FStar_Syntax_Syntax.n)
in (binders, _137_1006))) with
| ([], _58_2368) -> begin
([], t)
end
| (_58_2371, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _58_2378 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_58_2381) with
| (binders, signature) -> begin
(
# 1789 "FStar.TypeChecker.Tc.fst"
let close = (fun ts -> (let _137_1009 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _137_1009)))
in (
# 1790 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1790 "FStar.TypeChecker.Tc.fst"
let _58_2384 = ed
in (let _137_1022 = (close ret)
in (let _137_1021 = (close bind_wp)
in (let _137_1020 = (close bind_wlp)
in (let _137_1019 = (close if_then_else)
in (let _137_1018 = (close ite_wp)
in (let _137_1017 = (close ite_wlp)
in (let _137_1016 = (close wp_binop)
in (let _137_1015 = (close wp_as_type)
in (let _137_1014 = (close close_wp)
in (let _137_1013 = (close assert_p)
in (let _137_1012 = (close assume_p)
in (let _137_1011 = (close null_wp)
in (let _137_1010 = (close trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _58_2384.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2384.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _137_1022; FStar_Syntax_Syntax.bind_wp = _137_1021; FStar_Syntax_Syntax.bind_wlp = _137_1020; FStar_Syntax_Syntax.if_then_else = _137_1019; FStar_Syntax_Syntax.ite_wp = _137_1018; FStar_Syntax_Syntax.ite_wlp = _137_1017; FStar_Syntax_Syntax.wp_binop = _137_1016; FStar_Syntax_Syntax.wp_as_type = _137_1015; FStar_Syntax_Syntax.close_wp = _137_1014; FStar_Syntax_Syntax.assert_p = _137_1013; FStar_Syntax_Syntax.assume_p = _137_1012; FStar_Syntax_Syntax.null_wp = _137_1011; FStar_Syntax_Syntax.trivial = _137_1010}))))))))))))))
in (
# 1808 "FStar.TypeChecker.Tc.fst"
let _58_2387 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_1023 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _137_1023))
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

# 1812 "FStar.TypeChecker.Tc.fst"
let tc_lex_t = (fun env ses quals lids -> (
# 1819 "FStar.TypeChecker.Tc.fst"
let _58_2393 = ()
in (
# 1820 "FStar.TypeChecker.Tc.fst"
let _58_2401 = ()
in (match (ses) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _58_2430, _58_2432, [], r)::FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _58_2421, r1)::FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _58_2410, r2)::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(
# 1835 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (
# 1836 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (
# 1837 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (
# 1838 "FStar.TypeChecker.Tc.fst"
let tc = FStar_Syntax_Syntax.Sig_inductive_typ ((lex_t, (u)::[], [], t, [], (FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[], [], r))
in (
# 1840 "FStar.TypeChecker.Tc.fst"
let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (
# 1841 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (let _137_1031 = (let _137_1030 = (let _137_1029 = (let _137_1028 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _137_1028 FStar_Syntax_Syntax.Delta_constant None))
in (_137_1029, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_137_1030))
in (FStar_Syntax_Syntax.mk _137_1031 None r1))
in (
# 1842 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (
# 1843 "FStar.TypeChecker.Tc.fst"
let dc_lextop = FStar_Syntax_Syntax.Sig_datacon ((lex_top, (utop)::[], lex_top_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r1))
in (
# 1845 "FStar.TypeChecker.Tc.fst"
let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1846 "FStar.TypeChecker.Tc.fst"
let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1847 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (
# 1848 "FStar.TypeChecker.Tc.fst"
let a = (let _137_1032 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _137_1032))
in (
# 1849 "FStar.TypeChecker.Tc.fst"
let hd = (let _137_1033 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _137_1033))
in (
# 1850 "FStar.TypeChecker.Tc.fst"
let tl = (let _137_1038 = (let _137_1037 = (let _137_1036 = (let _137_1035 = (let _137_1034 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _137_1034 FStar_Syntax_Syntax.Delta_constant None))
in (_137_1035, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_137_1036))
in (FStar_Syntax_Syntax.mk _137_1037 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _137_1038))
in (
# 1851 "FStar.TypeChecker.Tc.fst"
let res = (let _137_1042 = (let _137_1041 = (let _137_1040 = (let _137_1039 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _137_1039 FStar_Syntax_Syntax.Delta_constant None))
in (_137_1040, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_137_1041))
in (FStar_Syntax_Syntax.mk _137_1042 None r2))
in (let _137_1043 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _137_1043))))))
in (
# 1853 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (
# 1854 "FStar.TypeChecker.Tc.fst"
let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _137_1045 = (let _137_1044 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _137_1044))
in FStar_Syntax_Syntax.Sig_bundle (_137_1045)))))))))))))))
end
| _58_2456 -> begin
(let _137_1047 = (let _137_1046 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _137_1046))
in (FStar_All.failwith _137_1047))
end))))

# 1860 "FStar.TypeChecker.Tc.fst"
let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (
# 1923 "FStar.TypeChecker.Tc.fst"
let warn_positivity = (fun l r -> (let _137_1061 = (let _137_1060 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _137_1060))
in (FStar_TypeChecker_Errors.diag r _137_1061)))
in (
# 1925 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1928 "FStar.TypeChecker.Tc.fst"
let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(
# 1933 "FStar.TypeChecker.Tc.fst"
let _58_2478 = ()
in (
# 1934 "FStar.TypeChecker.Tc.fst"
let _58_2480 = (warn_positivity tc r)
in (
# 1935 "FStar.TypeChecker.Tc.fst"
let _58_2484 = (FStar_Syntax_Subst.open_term tps k)
in (match (_58_2484) with
| (tps, k) -> begin
(
# 1936 "FStar.TypeChecker.Tc.fst"
let _58_2488 = (tc_tparams env tps)
in (match (_58_2488) with
| (tps, env_tps, us) -> begin
(
# 1937 "FStar.TypeChecker.Tc.fst"
let _58_2491 = (FStar_Syntax_Util.arrow_formals k)
in (match (_58_2491) with
| (indices, t) -> begin
(
# 1938 "FStar.TypeChecker.Tc.fst"
let _58_2495 = (tc_tparams env_tps indices)
in (match (_58_2495) with
| (indices, env', us') -> begin
(
# 1939 "FStar.TypeChecker.Tc.fst"
let _58_2499 = (tc_trivial_guard env' t)
in (match (_58_2499) with
| (t, _58_2498) -> begin
(
# 1940 "FStar.TypeChecker.Tc.fst"
let k = (let _137_1066 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _137_1066))
in (
# 1941 "FStar.TypeChecker.Tc.fst"
let _58_2503 = (FStar_Syntax_Util.type_u ())
in (match (_58_2503) with
| (t_type, u) -> begin
(
# 1942 "FStar.TypeChecker.Tc.fst"
let _58_2504 = (let _137_1067 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _137_1067))
in (
# 1944 "FStar.TypeChecker.Tc.fst"
let t_tc = (let _137_1068 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _137_1068))
in (
# 1945 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 1946 "FStar.TypeChecker.Tc.fst"
let k = (FStar_Syntax_Subst.close tps k)
in (
# 1947 "FStar.TypeChecker.Tc.fst"
let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _137_1069 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) ([], t_tc))
in (_137_1069, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u)))))))
end)))
end))
end))
end))
end))
end))))
end
| _58_2511 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1954 "FStar.TypeChecker.Tc.fst"
let positive_if_pure = (fun _58_2513 l -> ())
in (
# 1957 "FStar.TypeChecker.Tc.fst"
let tc_data = (fun env tcs _58_6 -> (match (_58_6) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(
# 1959 "FStar.TypeChecker.Tc.fst"
let _58_2530 = ()
in (
# 1961 "FStar.TypeChecker.Tc.fst"
let _58_2565 = (
# 1962 "FStar.TypeChecker.Tc.fst"
let tps_u_opt = (FStar_Util.find_map tcs (fun _58_2534 -> (match (_58_2534) with
| (se, u_tc) -> begin
if (let _137_1082 = (let _137_1081 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _137_1081))
in (FStar_Ident.lid_equals tc_lid _137_1082)) then begin
(
# 1964 "FStar.TypeChecker.Tc.fst"
let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_2536, _58_2538, tps, _58_2541, _58_2543, _58_2545, _58_2547, _58_2549) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _58_2555 -> (match (_58_2555) with
| (x, _58_2554) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _58_2557 -> begin
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
in (match (_58_2565) with
| (tps, u_tc) -> begin
(
# 1977 "FStar.TypeChecker.Tc.fst"
let _58_2585 = (match ((let _137_1084 = (FStar_Syntax_Subst.compress t)
in _137_1084.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(
# 1982 "FStar.TypeChecker.Tc.fst"
let _58_2573 = (FStar_Util.first_N ntps bs)
in (match (_58_2573) with
| (_58_2571, bs') -> begin
(
# 1983 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (
# 1984 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _58_2579 -> (match (_58_2579) with
| (x, _58_2578) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _137_1087 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _137_1087))))
end))
end
| _58_2582 -> begin
([], t)
end)
in (match (_58_2585) with
| (arguments, result) -> begin
(
# 1988 "FStar.TypeChecker.Tc.fst"
let _58_2586 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_1090 = (FStar_Syntax_Print.lid_to_string c)
in (let _137_1089 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _137_1088 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _137_1090 _137_1089 _137_1088))))
end else begin
()
end
in (
# 1994 "FStar.TypeChecker.Tc.fst"
let _58_2591 = (tc_tparams env arguments)
in (match (_58_2591) with
| (arguments, env', us) -> begin
(
# 1995 "FStar.TypeChecker.Tc.fst"
let _58_2595 = (tc_trivial_guard env' result)
in (match (_58_2595) with
| (result, _58_2594) -> begin
(
# 1996 "FStar.TypeChecker.Tc.fst"
let _58_2599 = (FStar_Syntax_Util.head_and_args result)
in (match (_58_2599) with
| (head, _58_2598) -> begin
(
# 1997 "FStar.TypeChecker.Tc.fst"
let _58_2604 = (match ((let _137_1091 = (FStar_Syntax_Subst.compress head)
in _137_1091.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _58_2603 -> begin
(let _137_1095 = (let _137_1094 = (let _137_1093 = (let _137_1092 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _137_1092))
in (_137_1093, r))
in FStar_Syntax_Syntax.Error (_137_1094))
in (Prims.raise _137_1095))
end)
in (
# 2000 "FStar.TypeChecker.Tc.fst"
let g = (FStar_List.fold_left2 (fun g _58_2610 u_x -> (match (_58_2610) with
| (x, _58_2609) -> begin
(
# 2001 "FStar.TypeChecker.Tc.fst"
let _58_2612 = ()
in (let _137_1099 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _137_1099)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (
# 2007 "FStar.TypeChecker.Tc.fst"
let t = (let _137_1103 = (let _137_1101 = (FStar_All.pipe_right tps (FStar_List.map (fun _58_2618 -> (match (_58_2618) with
| (x, _58_2617) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _137_1101 arguments))
in (let _137_1102 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _137_1103 _137_1102)))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _58_2621 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 2015 "FStar.TypeChecker.Tc.fst"
let generalize_and_inst_within = (fun env g tcs datas -> (
# 2016 "FStar.TypeChecker.Tc.fst"
let _58_2627 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2017 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _58_7 -> (match (_58_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_2631, _58_2633, tps, k, _58_2637, _58_2639, _58_2641, _58_2643) -> begin
(let _137_1114 = (let _137_1113 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _137_1113))
in (FStar_Syntax_Syntax.null_binder _137_1114))
end
| _58_2647 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2020 "FStar.TypeChecker.Tc.fst"
let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _58_8 -> (match (_58_8) with
| FStar_Syntax_Syntax.Sig_datacon (_58_2651, _58_2653, t, _58_2656, _58_2658, _58_2660, _58_2662, _58_2664) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _58_2668 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2023 "FStar.TypeChecker.Tc.fst"
let t = (let _137_1116 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _137_1116))
in (
# 2024 "FStar.TypeChecker.Tc.fst"
let _58_2671 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_1117 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _137_1117))
end else begin
()
end
in (
# 2025 "FStar.TypeChecker.Tc.fst"
let _58_2675 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_58_2675) with
| (uvs, t) -> begin
(
# 2026 "FStar.TypeChecker.Tc.fst"
let _58_2677 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_1121 = (let _137_1119 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _137_1119 (FStar_String.concat ", ")))
in (let _137_1120 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _137_1121 _137_1120)))
end else begin
()
end
in (
# 2029 "FStar.TypeChecker.Tc.fst"
let _58_2681 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_58_2681) with
| (uvs, t) -> begin
(
# 2030 "FStar.TypeChecker.Tc.fst"
let _58_2685 = (FStar_Syntax_Util.arrow_formals t)
in (match (_58_2685) with
| (args, _58_2684) -> begin
(
# 2031 "FStar.TypeChecker.Tc.fst"
let _58_2688 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_58_2688) with
| (tc_types, data_types) -> begin
(
# 2032 "FStar.TypeChecker.Tc.fst"
let tcs = (FStar_List.map2 (fun _58_2692 se -> (match (_58_2692) with
| (x, _58_2691) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _58_2696, tps, _58_2699, mutuals, datas, quals, r) -> begin
(
# 2034 "FStar.TypeChecker.Tc.fst"
let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (
# 2035 "FStar.TypeChecker.Tc.fst"
let _58_2722 = (match ((let _137_1124 = (FStar_Syntax_Subst.compress ty)
in _137_1124.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 2037 "FStar.TypeChecker.Tc.fst"
let _58_2713 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_58_2713) with
| (tps, rest) -> begin
(
# 2038 "FStar.TypeChecker.Tc.fst"
let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _58_2716 -> begin
(let _137_1125 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _137_1125 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _58_2719 -> begin
([], ty)
end)
in (match (_58_2722) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _58_2724 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (
# 2048 "FStar.TypeChecker.Tc.fst"
let datas = (match (uvs) with
| [] -> begin
datas
end
| _58_2728 -> begin
(
# 2051 "FStar.TypeChecker.Tc.fst"
let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _137_1126 -> FStar_Syntax_Syntax.U_name (_137_1126))))
in (
# 2052 "FStar.TypeChecker.Tc.fst"
let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _58_9 -> (match (_58_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _58_2733, _58_2735, _58_2737, _58_2739, _58_2741, _58_2743, _58_2745) -> begin
(tc, uvs_universes)
end
| _58_2749 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _58_2754 d -> (match (_58_2754) with
| (t, _58_2753) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _58_2758, _58_2760, tc, ntps, quals, mutuals, r) -> begin
(
# 2056 "FStar.TypeChecker.Tc.fst"
let ty = (let _137_1130 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _137_1130 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _58_2770 -> begin
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
# 2062 "FStar.TypeChecker.Tc.fst"
let _58_2780 = (FStar_All.pipe_right ses (FStar_List.partition (fun _58_10 -> (match (_58_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_2774) -> begin
true
end
| _58_2777 -> begin
false
end))))
in (match (_58_2780) with
| (tys, datas) -> begin
(
# 2064 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2067 "FStar.TypeChecker.Tc.fst"
let _58_2797 = (FStar_List.fold_right (fun tc _58_2786 -> (match (_58_2786) with
| (env, all_tcs, g) -> begin
(
# 2068 "FStar.TypeChecker.Tc.fst"
let _58_2790 = (tc_tycon env tc)
in (match (_58_2790) with
| (env, tc, tc_u) -> begin
(
# 2069 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (
# 2070 "FStar.TypeChecker.Tc.fst"
let _58_2792 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_1134 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _137_1134))
end else begin
()
end
in (let _137_1135 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _137_1135))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_58_2797) with
| (env, tcs, g) -> begin
(
# 2077 "FStar.TypeChecker.Tc.fst"
let _58_2807 = (FStar_List.fold_right (fun se _58_2801 -> (match (_58_2801) with
| (datas, g) -> begin
(
# 2078 "FStar.TypeChecker.Tc.fst"
let _58_2804 = (tc_data env tcs se)
in (match (_58_2804) with
| (data, g') -> begin
(let _137_1138 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _137_1138))
end))
end)) datas ([], g))
in (match (_58_2807) with
| (datas, g) -> begin
(
# 2083 "FStar.TypeChecker.Tc.fst"
let _58_2810 = (let _137_1139 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _137_1139 datas))
in (match (_58_2810) with
| (tcs, datas) -> begin
(let _137_1141 = (let _137_1140 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _137_1140))
in FStar_Syntax_Syntax.Sig_bundle (_137_1141))
end))
end))
end)))
end)))))))))

# 2086 "FStar.TypeChecker.Tc.fst"
let rec tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.env) = (fun env se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(
# 2099 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2100 "FStar.TypeChecker.Tc.fst"
let se = (tc_lex_t env ses quals lids)
in (let _137_1146 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _137_1146))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(
# 2104 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2105 "FStar.TypeChecker.Tc.fst"
let se = (tc_inductive env ses quals lids)
in (let _137_1147 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _137_1147))))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(
# 2109 "FStar.TypeChecker.Tc.fst"
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
# 2115 "FStar.TypeChecker.Tc.fst"
let _58_2848 = (set_options FStar_Options.Set o)
in (se, env))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(
# 2118 "FStar.TypeChecker.Tc.fst"
let _58_2852 = (let _137_1152 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _137_1152 Prims.ignore))
in (
# 2119 "FStar.TypeChecker.Tc.fst"
let _58_2857 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (
# 2122 "FStar.TypeChecker.Tc.fst"
let _58_2859 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (se, env))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(
# 2127 "FStar.TypeChecker.Tc.fst"
let ne = (tc_eff_decl env ne)
in (
# 2128 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (
# 2129 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(
# 2133 "FStar.TypeChecker.Tc.fst"
let _58_2874 = (let _137_1153 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _137_1153))
in (match (_58_2874) with
| (a, wp_a_src) -> begin
(
# 2134 "FStar.TypeChecker.Tc.fst"
let _58_2877 = (let _137_1154 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _137_1154))
in (match (_58_2877) with
| (b, wp_b_tgt) -> begin
(
# 2135 "FStar.TypeChecker.Tc.fst"
let wp_a_tgt = (let _137_1158 = (let _137_1157 = (let _137_1156 = (let _137_1155 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _137_1155))
in FStar_Syntax_Syntax.NT (_137_1156))
in (_137_1157)::[])
in (FStar_Syntax_Subst.subst _137_1158 wp_b_tgt))
in (
# 2136 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_1163 = (let _137_1161 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_1160 = (let _137_1159 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_137_1159)::[])
in (_137_1161)::_137_1160))
in (let _137_1162 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _137_1163 _137_1162)))
in (
# 2137 "FStar.TypeChecker.Tc.fst"
let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (
# 2138 "FStar.TypeChecker.Tc.fst"
let sub = (
# 2138 "FStar.TypeChecker.Tc.fst"
let _58_2881 = sub
in {FStar_Syntax_Syntax.source = _58_2881.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _58_2881.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
in (
# 2139 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect ((sub, r))
in (
# 2140 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(
# 2144 "FStar.TypeChecker.Tc.fst"
let _58_2894 = ()
in (
# 2145 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2146 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2147 "FStar.TypeChecker.Tc.fst"
let _58_2900 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_58_2900) with
| (tps, c) -> begin
(
# 2148 "FStar.TypeChecker.Tc.fst"
let _58_2904 = (tc_tparams env tps)
in (match (_58_2904) with
| (tps, env, us) -> begin
(
# 2149 "FStar.TypeChecker.Tc.fst"
let _58_2908 = (tc_comp env c)
in (match (_58_2908) with
| (c, u, g) -> begin
(
# 2150 "FStar.TypeChecker.Tc.fst"
let _58_2909 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2151 "FStar.TypeChecker.Tc.fst"
let tags = (FStar_All.pipe_right tags (FStar_List.map (fun _58_11 -> (match (_58_11) with
| FStar_Syntax_Syntax.DefaultEffect (None) -> begin
(
# 2153 "FStar.TypeChecker.Tc.fst"
let c' = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let _137_1166 = (FStar_All.pipe_right c'.FStar_Syntax_Syntax.effect_name (fun _137_1165 -> Some (_137_1165)))
in FStar_Syntax_Syntax.DefaultEffect (_137_1166)))
end
| t -> begin
t
end))))
in (
# 2156 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 2157 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.close_comp tps c)
in (
# 2158 "FStar.TypeChecker.Tc.fst"
let _58_2921 = (let _137_1167 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _137_1167))
in (match (_58_2921) with
| (uvs, t) -> begin
(
# 2159 "FStar.TypeChecker.Tc.fst"
let _58_2940 = (match ((let _137_1169 = (let _137_1168 = (FStar_Syntax_Subst.compress t)
in _137_1168.FStar_Syntax_Syntax.n)
in (tps, _137_1169))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_58_2924, c)) -> begin
([], c)
end
| (_58_2930, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _58_2937 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_58_2940) with
| (tps, c) -> begin
(
# 2163 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_effect_abbrev ((lid, uvs, tps, c, tags, r))
in (
# 2164 "FStar.TypeChecker.Tc.fst"
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
# 2168 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2169 "FStar.TypeChecker.Tc.fst"
let _58_2951 = ()
in (
# 2170 "FStar.TypeChecker.Tc.fst"
let k = (let _137_1170 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _137_1170))
in (
# 2171 "FStar.TypeChecker.Tc.fst"
let _58_2956 = (check_and_gen env t k)
in (match (_58_2956) with
| (uvs, t) -> begin
(
# 2172 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (
# 2173 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(
# 2177 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2178 "FStar.TypeChecker.Tc.fst"
let _58_2969 = (FStar_Syntax_Util.type_u ())
in (match (_58_2969) with
| (k, _58_2968) -> begin
(
# 2179 "FStar.TypeChecker.Tc.fst"
let phi = (let _137_1171 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _137_1171 (norm env)))
in (
# 2180 "FStar.TypeChecker.Tc.fst"
let _58_2971 = (FStar_TypeChecker_Util.check_uvars r phi)
in (
# 2181 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))
in (
# 2182 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(
# 2186 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2187 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (
# 2188 "FStar.TypeChecker.Tc.fst"
let _58_2984 = (tc_term env e)
in (match (_58_2984) with
| (e, c, g1) -> begin
(
# 2189 "FStar.TypeChecker.Tc.fst"
let _58_2989 = (let _137_1175 = (let _137_1172 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_137_1172))
in (let _137_1174 = (let _137_1173 = (c.FStar_Syntax_Syntax.comp ())
in (e, _137_1173))
in (check_expected_effect env _137_1175 _137_1174)))
in (match (_58_2989) with
| (e, _58_2987, g) -> begin
(
# 2190 "FStar.TypeChecker.Tc.fst"
let _58_2990 = (let _137_1176 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _137_1176))
in (
# 2191 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, r))
in (
# 2192 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(
# 2196 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2197 "FStar.TypeChecker.Tc.fst"
let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
if (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q')) then begin
Some (q)
end else begin
(let _137_1188 = (let _137_1187 = (let _137_1186 = (let _137_1185 = (FStar_Syntax_Print.lid_to_string l)
in (let _137_1184 = (FStar_Syntax_Print.quals_to_string q)
in (let _137_1183 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _137_1185 _137_1184 _137_1183))))
in (_137_1186, r))
in FStar_Syntax_Syntax.Error (_137_1187))
in (Prims.raise _137_1188))
end
end))
in (
# 2211 "FStar.TypeChecker.Tc.fst"
let _58_3034 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _58_3011 lb -> (match (_58_3011) with
| (gen, lbs, quals_opt) -> begin
(
# 2212 "FStar.TypeChecker.Tc.fst"
let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2213 "FStar.TypeChecker.Tc.fst"
let _58_3030 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(
# 2217 "FStar.TypeChecker.Tc.fst"
let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (
# 2218 "FStar.TypeChecker.Tc.fst"
let _58_3025 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _58_3024 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _137_1191 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _137_1191, quals_opt))))
end)
in (match (_58_3030) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_58_3034) with
| (should_generalize, lbs', quals_opt) -> begin
(
# 2227 "FStar.TypeChecker.Tc.fst"
let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _58_12 -> (match (_58_12) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _58_3043 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (
# 2234 "FStar.TypeChecker.Tc.fst"
let lbs' = (FStar_List.rev lbs')
in (
# 2237 "FStar.TypeChecker.Tc.fst"
let e = (let _137_1195 = (let _137_1194 = (let _137_1193 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _137_1193))
in FStar_Syntax_Syntax.Tm_let (_137_1194))
in (FStar_Syntax_Syntax.mk _137_1195 None r))
in (
# 2240 "FStar.TypeChecker.Tc.fst"
let _58_3077 = (match ((tc_maybe_toplevel_term (
# 2240 "FStar.TypeChecker.Tc.fst"
let _58_3047 = env
in {FStar_TypeChecker_Env.solver = _58_3047.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_3047.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_3047.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_3047.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_3047.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_3047.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_3047.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_3047.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_3047.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_3047.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_3047.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _58_3047.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _58_3047.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_3047.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_3047.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_3047.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_3047.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_3047.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_3047.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_3047.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _58_3054; FStar_Syntax_Syntax.pos = _58_3052; FStar_Syntax_Syntax.vars = _58_3050}, _58_3061, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(
# 2243 "FStar.TypeChecker.Tc.fst"
let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_58_3065, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _58_3071 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _58_3074 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_58_3077) with
| (se, lbs) -> begin
(
# 2250 "FStar.TypeChecker.Tc.fst"
let _58_3083 = if (log env) then begin
(let _137_1203 = (let _137_1202 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 2252 "FStar.TypeChecker.Tc.fst"
let should_log = (match ((let _137_1199 = (let _137_1198 = (let _137_1197 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _137_1197.FStar_Syntax_Syntax.fv_name)
in _137_1198.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _137_1199))) with
| None -> begin
true
end
| _58_3081 -> begin
false
end)
in if should_log then begin
(let _137_1201 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _137_1200 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _137_1201 _137_1200)))
end else begin
""
end))))
in (FStar_All.pipe_right _137_1202 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _137_1203))
end else begin
()
end
in (
# 2259 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end))))
end))

# 2263 "FStar.TypeChecker.Tc.fst"
let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (
# 2287 "FStar.TypeChecker.Tc.fst"
let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _58_13 -> (match (_58_13) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _58_3093 -> begin
false
end)))))
in (
# 2288 "FStar.TypeChecker.Tc.fst"
let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _58_3103 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_58_3105) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _58_3116, _58_3118) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _58_3124 -> (match (_58_3124) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _58_3130, _58_3132, quals, r) -> begin
(
# 2302 "FStar.TypeChecker.Tc.fst"
let dec = (let _137_1219 = (let _137_1218 = (let _137_1217 = (let _137_1216 = (let _137_1215 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _137_1215))
in FStar_Syntax_Syntax.Tm_arrow (_137_1216))
in (FStar_Syntax_Syntax.mk _137_1217 None r))
in (l, us, _137_1218, (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_137_1219))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _58_3142, _58_3144, _58_3146, _58_3148, r) -> begin
(
# 2305 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _58_3154 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_58_3156, _58_3158, quals, _58_3161) -> begin
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
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _58_14 -> (match (_58_14) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _58_3180 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_58_3182) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _58_3198, _58_3200, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(
# 2335 "FStar.TypeChecker.Tc.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2336 "FStar.TypeChecker.Tc.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))) then begin
([], hidden)
end else begin
(
# 2339 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::[], (FStar_Ident.range_of_lid lid)))
in ((dec)::[], (lid)::hidden))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (is_abstract quals) then begin
(let _137_1226 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _137_1225 = (let _137_1224 = (let _137_1223 = (let _137_1222 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _137_1222.FStar_Syntax_Syntax.fv_name)
in _137_1223.FStar_Syntax_Syntax.v)
in (_137_1224, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_137_1225)))))
in (_137_1226, hidden))
end else begin
((se)::[], hidden)
end
end))))

# 2348 "FStar.TypeChecker.Tc.fst"
let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (
# 2349 "FStar.TypeChecker.Tc.fst"
let _58_3239 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _58_3220 se -> (match (_58_3220) with
| (ses, exports, env, hidden) -> begin
(
# 2351 "FStar.TypeChecker.Tc.fst"
let _58_3222 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_1233 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _137_1233))
end else begin
()
end
in (
# 2354 "FStar.TypeChecker.Tc.fst"
let _58_3226 = (tc_decl env se)
in (match (_58_3226) with
| (se, env) -> begin
(
# 2356 "FStar.TypeChecker.Tc.fst"
let _58_3227 = if ((FStar_ST.read FStar_Options.log_types) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _137_1234 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _137_1234))
end else begin
()
end
in (
# 2359 "FStar.TypeChecker.Tc.fst"
let _58_3229 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (
# 2361 "FStar.TypeChecker.Tc.fst"
let _58_3233 = (for_export hidden se)
in (match (_58_3233) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_58_3239) with
| (ses, exports, env, _58_3238) -> begin
(let _137_1235 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _137_1235, env))
end)))

# 2366 "FStar.TypeChecker.Tc.fst"
let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2367 "FStar.TypeChecker.Tc.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 2368 "FStar.TypeChecker.Tc.fst"
let msg = (Prims.strcat "Internals for " name)
in (
# 2369 "FStar.TypeChecker.Tc.fst"
let env = (
# 2369 "FStar.TypeChecker.Tc.fst"
let _58_3244 = env
in (let _137_1240 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _58_3244.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_3244.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_3244.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_3244.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_3244.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_3244.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_3244.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_3244.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_3244.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_3244.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_3244.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_3244.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_3244.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_3244.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_3244.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_3244.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _137_1240; FStar_TypeChecker_Env.default_effects = _58_3244.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_3244.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_3244.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_3244.FStar_TypeChecker_Env.use_bv_sorts}))
in (
# 2370 "FStar.TypeChecker.Tc.fst"
let _58_3247 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (
# 2371 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (
# 2372 "FStar.TypeChecker.Tc.fst"
let _58_3253 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_58_3253) with
| (ses, exports, env) -> begin
((
# 2373 "FStar.TypeChecker.Tc.fst"
let _58_3254 = modul
in {FStar_Syntax_Syntax.name = _58_3254.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _58_3254.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _58_3254.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))

# 2375 "FStar.TypeChecker.Tc.fst"
let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (
# 2376 "FStar.TypeChecker.Tc.fst"
let _58_3262 = (tc_decls env decls)
in (match (_58_3262) with
| (ses, exports, env) -> begin
(
# 2377 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2377 "FStar.TypeChecker.Tc.fst"
let _58_3263 = modul
in {FStar_Syntax_Syntax.name = _58_3263.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _58_3263.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _58_3263.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))

# 2380 "FStar.TypeChecker.Tc.fst"
let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (
# 2381 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2381 "FStar.TypeChecker.Tc.fst"
let _58_3269 = modul
in {FStar_Syntax_Syntax.name = _58_3269.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _58_3269.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (
# 2382 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.finish_module env modul)
in (
# 2383 "FStar.TypeChecker.Tc.fst"
let _58_3279 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(
# 2385 "FStar.TypeChecker.Tc.fst"
let _58_3273 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (
# 2386 "FStar.TypeChecker.Tc.fst"
let _58_3275 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (
# 2387 "FStar.TypeChecker.Tc.fst"
let _58_3277 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _137_1253 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _137_1253 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))

# 2392 "FStar.TypeChecker.Tc.fst"
let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2393 "FStar.TypeChecker.Tc.fst"
let _58_3286 = (tc_partial_modul env modul)
in (match (_58_3286) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

# 2396 "FStar.TypeChecker.Tc.fst"
let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 2397 "FStar.TypeChecker.Tc.fst"
let _58_3289 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _137_1262 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _137_1262))
end else begin
()
end
in (
# 2399 "FStar.TypeChecker.Tc.fst"
let env = (
# 2399 "FStar.TypeChecker.Tc.fst"
let _58_3291 = env
in {FStar_TypeChecker_Env.solver = _58_3291.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_3291.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_3291.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_3291.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_3291.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_3291.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_3291.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_3291.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_3291.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_3291.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_3291.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_3291.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_3291.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_3291.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_3291.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_3291.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_3291.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_3291.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_3291.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_3291.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_3291.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 2400 "FStar.TypeChecker.Tc.fst"
let _58_3307 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _58_3299) -> begin
(let _137_1267 = (let _137_1266 = (let _137_1265 = (FStar_TypeChecker_Env.get_range env)
in ((Prims.strcat "Implicit argument: " msg), _137_1265))
in FStar_Syntax_Syntax.Error (_137_1266))
in (Prims.raise _137_1267))
end
in (match (_58_3307) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(let _137_1272 = (let _137_1271 = (let _137_1270 = (let _137_1268 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _137_1268))
in (let _137_1269 = (FStar_TypeChecker_Env.get_range env)
in (_137_1270, _137_1269)))
in FStar_Syntax_Syntax.Error (_137_1271))
in (Prims.raise _137_1272))
end
end)))))

# 2407 "FStar.TypeChecker.Tc.fst"
let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (
# 2408 "FStar.TypeChecker.Tc.fst"
let _58_3310 = if ((let _137_1277 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _137_1277)) <> 0) then begin
(let _137_1278 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _137_1278))
end else begin
()
end
in (
# 2410 "FStar.TypeChecker.Tc.fst"
let _58_3314 = (tc_modul env m)
in (match (_58_3314) with
| (m, env) -> begin
(
# 2411 "FStar.TypeChecker.Tc.fst"
let _58_3315 = if (FStar_Options.should_dump m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _137_1279 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _137_1279))
end else begin
()
end
in (m, env))
end))))




