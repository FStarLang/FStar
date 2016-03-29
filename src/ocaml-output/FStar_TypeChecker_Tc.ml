
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

# 179 "FStar.TypeChecker.Tc.fst"
let with_implicits = (fun imps _58_177 -> (match (_58_177) with
| (e, l, g) -> begin
(e, l, (
# 179 "FStar.TypeChecker.Tc.fst"
let _58_178 = g
in {FStar_TypeChecker_Env.guard_f = _58_178.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_178.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_178.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (FStar_List.append imps g.FStar_TypeChecker_Env.implicits)}))
end))

# 180 "FStar.TypeChecker.Tc.fst"
let add_implicit : (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun u g -> (
# 180 "FStar.TypeChecker.Tc.fst"
let _58_182 = g
in {FStar_TypeChecker_Env.guard_f = _58_182.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_182.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_182.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (u)::g.FStar_TypeChecker_Env.implicits}))

# 185 "FStar.TypeChecker.Tc.fst"
let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _58_200; FStar_Syntax_Syntax.result_typ = _58_198; FStar_Syntax_Syntax.effect_args = _pre::_post::(pats, _58_192)::[]; FStar_Syntax_Syntax.flags = _58_189}) -> begin
(
# 189 "FStar.TypeChecker.Tc.fst"
let pat_vars = (FStar_Syntax_Free.names pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _58_207 -> (match (_58_207) with
| (b, _58_206) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _58_211) -> begin
(let _137_142 = (let _137_141 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _137_141))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _137_142))
end))
end
| _58_215 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end)

# 200 "FStar.TypeChecker.Tc.fst"
let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun env actuals expected_c -> (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(
# 204 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 205 "FStar.TypeChecker.Tc.fst"
let env = (
# 205 "FStar.TypeChecker.Tc.fst"
let _58_222 = env
in {FStar_TypeChecker_Env.solver = _58_222.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_222.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_222.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_222.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_222.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_222.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_222.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_222.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_222.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_222.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_222.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_222.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _58_222.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_222.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_222.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_222.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_222.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_222.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_222.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_222.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_222.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 206 "FStar.TypeChecker.Tc.fst"
let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (
# 208 "FStar.TypeChecker.Tc.fst"
let decreases_clause = (fun bs c -> (
# 210 "FStar.TypeChecker.Tc.fst"
let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _58_234 -> (match (_58_234) with
| (b, _58_233) -> begin
(
# 212 "FStar.TypeChecker.Tc.fst"
let t = (let _137_156 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _137_156))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _58_243 -> begin
(let _137_157 = (FStar_Syntax_Syntax.bv_to_name b)
in (_137_157)::[])
end))
end)))))
in (
# 217 "FStar.TypeChecker.Tc.fst"
let as_lex_list = (fun dec -> (
# 218 "FStar.TypeChecker.Tc.fst"
let _58_249 = (FStar_Syntax_Util.head_and_args dec)
in (match (_58_249) with
| (head, _58_248) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _58_253 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (
# 222 "FStar.TypeChecker.Tc.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _58_3 -> (match (_58_3) with
| FStar_Syntax_Syntax.DECREASES (_58_257) -> begin
true
end
| _58_260 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _58_265 -> begin
(
# 226 "FStar.TypeChecker.Tc.fst"
let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| x::[] -> begin
x
end
| _58_270 -> begin
(mk_lex_list xs)
end))
end)))))
in (
# 231 "FStar.TypeChecker.Tc.fst"
let previous_dec = (decreases_clause actuals expected_c)
in (
# 232 "FStar.TypeChecker.Tc.fst"
let guard_one_letrec = (fun _58_275 -> (match (_58_275) with
| (l, t) -> begin
(match ((let _137_163 = (FStar_Syntax_Subst.compress t)
in _137_163.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 236 "FStar.TypeChecker.Tc.fst"
let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _58_282 -> (match (_58_282) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _137_167 = (let _137_166 = (let _137_165 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_137_165))
in (FStar_Syntax_Syntax.new_bv _137_166 x.FStar_Syntax_Syntax.sort))
in (_137_167, imp))
end else begin
(x, imp)
end
end))))
in (
# 237 "FStar.TypeChecker.Tc.fst"
let _58_286 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_58_286) with
| (formals, c) -> begin
(
# 238 "FStar.TypeChecker.Tc.fst"
let dec = (decreases_clause formals c)
in (
# 239 "FStar.TypeChecker.Tc.fst"
let precedes = (let _137_171 = (let _137_170 = (FStar_Syntax_Syntax.as_arg dec)
in (let _137_169 = (let _137_168 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_137_168)::[])
in (_137_170)::_137_169))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _137_171 None r))
in (
# 240 "FStar.TypeChecker.Tc.fst"
let _58_293 = (FStar_Util.prefix formals)
in (match (_58_293) with
| (bs, (last, imp)) -> begin
(
# 241 "FStar.TypeChecker.Tc.fst"
let last = (
# 241 "FStar.TypeChecker.Tc.fst"
let _58_294 = last
in (let _137_172 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _58_294.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_294.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _137_172}))
in (
# 242 "FStar.TypeChecker.Tc.fst"
let refined_formals = (FStar_List.append bs (((last, imp))::[]))
in (
# 243 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (
# 244 "FStar.TypeChecker.Tc.fst"
let _58_299 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_175 = (FStar_Syntax_Print.lbname_to_string l)
in (let _137_174 = (FStar_Syntax_Print.term_to_string t)
in (let _137_173 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _137_175 _137_174 _137_173))))
end else begin
()
end
in (l, t')))))
end))))
end)))
end
| _58_302 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end))

# 256 "FStar.TypeChecker.Tc.fst"
let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (
# 256 "FStar.TypeChecker.Tc.fst"
let _58_305 = env
in {FStar_TypeChecker_Env.solver = _58_305.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_305.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_305.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_305.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_305.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_305.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_305.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_305.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_305.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_305.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_305.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_305.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_305.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_305.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_305.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_305.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_305.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_305.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_305.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_305.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_305.FStar_TypeChecker_Env.use_bv_sorts}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 261 "FStar.TypeChecker.Tc.fst"
let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (
# 262 "FStar.TypeChecker.Tc.fst"
let _58_310 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_244 = (let _137_242 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _137_242))
in (let _137_243 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _137_244 _137_243)))
end else begin
()
end
in (
# 263 "FStar.TypeChecker.Tc.fst"
let top = e
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_58_314) -> begin
(let _137_248 = (FStar_Syntax_Subst.compress e)
in (tc_term env _137_248))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(
# 280 "FStar.TypeChecker.Tc.fst"
let _58_355 = (tc_tot_or_gtot_term env e)
in (match (_58_355) with
| (e, c, g) -> begin
(
# 281 "FStar.TypeChecker.Tc.fst"
let g = (
# 281 "FStar.TypeChecker.Tc.fst"
let _58_356 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_356.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_356.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_356.FStar_TypeChecker_Env.implicits})
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(
# 285 "FStar.TypeChecker.Tc.fst"
let _58_366 = (FStar_Syntax_Util.type_u ())
in (match (_58_366) with
| (t, u) -> begin
(
# 286 "FStar.TypeChecker.Tc.fst"
let _58_370 = (tc_check_tot_or_gtot_term env e t)
in (match (_58_370) with
| (e, c, g) -> begin
(
# 287 "FStar.TypeChecker.Tc.fst"
let _58_377 = (
# 288 "FStar.TypeChecker.Tc.fst"
let _58_374 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_374) with
| (env, _58_373) -> begin
(tc_pats env pats)
end))
in (match (_58_377) with
| (pats, g') -> begin
(
# 290 "FStar.TypeChecker.Tc.fst"
let g' = (
# 290 "FStar.TypeChecker.Tc.fst"
let _58_378 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_378.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_378.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_378.FStar_TypeChecker_Env.implicits})
in (let _137_250 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_pattern (pats)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _137_249 = (FStar_TypeChecker_Rel.conj_guard g g')
in (_137_250, c, _137_249))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _137_251 = (FStar_Syntax_Subst.compress e)
in _137_251.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_58_387, {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _58_394; FStar_Syntax_Syntax.lbtyp = _58_392; FStar_Syntax_Syntax.lbeff = _58_390; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 298 "FStar.TypeChecker.Tc.fst"
let _58_405 = (let _137_252 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _137_252 e1))
in (match (_58_405) with
| (e1, c1, g1) -> begin
(
# 299 "FStar.TypeChecker.Tc.fst"
let _58_409 = (tc_term env e2)
in (match (_58_409) with
| (e2, c2, g2) -> begin
(
# 300 "FStar.TypeChecker.Tc.fst"
let c = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (None, c2))
in (
# 301 "FStar.TypeChecker.Tc.fst"
let e = (let _137_257 = (let _137_256 = (let _137_255 = (let _137_254 = (let _137_253 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Common.t_unit, e1))
in (_137_253)::[])
in (false, _137_254))
in (_137_255, e2))
in FStar_Syntax_Syntax.Tm_let (_137_256))
in (FStar_Syntax_Syntax.mk _137_257 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 302 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _137_258 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _137_258)))))
end))
end))
end
| _58_414 -> begin
(
# 305 "FStar.TypeChecker.Tc.fst"
let _58_418 = (tc_term env e)
in (match (_58_418) with
| (e, c, g) -> begin
(
# 306 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(
# 311 "FStar.TypeChecker.Tc.fst"
let _58_427 = (tc_term env e)
in (match (_58_427) with
| (e, c, g) -> begin
(
# 312 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, m))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _58_433) -> begin
(
# 316 "FStar.TypeChecker.Tc.fst"
let _58_440 = (tc_comp env expected_c)
in (match (_58_440) with
| (expected_c, _58_438, g) -> begin
(
# 317 "FStar.TypeChecker.Tc.fst"
let _58_444 = (tc_term env e)
in (match (_58_444) with
| (e, c', g') -> begin
(
# 318 "FStar.TypeChecker.Tc.fst"
let _58_448 = (let _137_260 = (let _137_259 = (c'.FStar_Syntax_Syntax.comp ())
in (e, _137_259))
in (check_expected_effect env (Some (expected_c)) _137_260))
in (match (_58_448) with
| (e, expected_c, g'') -> begin
(
# 319 "FStar.TypeChecker.Tc.fst"
let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (let _137_263 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t_res), Some ((FStar_Syntax_Util.comp_effect_name expected_c))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _137_262 = (let _137_261 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _137_261))
in (_137_263, (FStar_Syntax_Util.lcomp_of_comp expected_c), _137_262))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _58_454) -> begin
(
# 325 "FStar.TypeChecker.Tc.fst"
let _58_459 = (FStar_Syntax_Util.type_u ())
in (match (_58_459) with
| (k, u) -> begin
(
# 326 "FStar.TypeChecker.Tc.fst"
let _58_464 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_464) with
| (t, _58_462, f) -> begin
(
# 327 "FStar.TypeChecker.Tc.fst"
let _58_468 = (let _137_264 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _137_264 e))
in (match (_58_468) with
| (e, c, g) -> begin
(
# 328 "FStar.TypeChecker.Tc.fst"
let _58_472 = (let _137_268 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_469 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _137_268 e c f))
in (match (_58_472) with
| (c, f) -> begin
(
# 329 "FStar.TypeChecker.Tc.fst"
let _58_476 = (let _137_269 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t), Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _137_269 c))
in (match (_58_476) with
| (e, c, f2) -> begin
(let _137_271 = (let _137_270 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _137_270))
in (e, c, _137_271))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 333 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 334 "FStar.TypeChecker.Tc.fst"
let env = (let _137_273 = (let _137_272 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _137_272 Prims.fst))
in (FStar_All.pipe_right _137_273 instantiate_both))
in (
# 335 "FStar.TypeChecker.Tc.fst"
let _58_483 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_275 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _137_274 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _137_275 _137_274)))
end else begin
()
end
in (
# 339 "FStar.TypeChecker.Tc.fst"
let _58_488 = (tc_term (no_inst env) head)
in (match (_58_488) with
| (head, chead, g_head) -> begin
(
# 340 "FStar.TypeChecker.Tc.fst"
let _58_492 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _137_276 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _137_276))
end else begin
(let _137_277 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _137_277))
end
in (match (_58_492) with
| (e, c, g) -> begin
(
# 343 "FStar.TypeChecker.Tc.fst"
let _58_493 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _137_278 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _137_278))
end else begin
()
end
in (
# 345 "FStar.TypeChecker.Tc.fst"
let c = if (((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) && (not ((FStar_Syntax_Util.is_lcomp_partial_return c)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)) then begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e c)
end else begin
c
end
in (
# 350 "FStar.TypeChecker.Tc.fst"
let _58_500 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_284 = (FStar_Syntax_Print.term_to_string e)
in (let _137_283 = (let _137_279 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _137_279))
in (let _137_282 = (let _137_281 = (FStar_TypeChecker_Env.expected_typ env0)
in (FStar_All.pipe_right _137_281 (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end))))
in (FStar_Util.print3 "(%s) About to check %s against expected typ %s\n" _137_284 _137_283 _137_282))))
end else begin
()
end
in (
# 355 "FStar.TypeChecker.Tc.fst"
let _58_505 = (comp_check_expected_typ env0 e c)
in (match (_58_505) with
| (e, c, g') -> begin
(
# 356 "FStar.TypeChecker.Tc.fst"
let _58_506 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_287 = (FStar_Syntax_Print.term_to_string e)
in (let _137_286 = (let _137_285 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _137_285))
in (FStar_Util.print2 "(%s) checked ... got %s\n" _137_287 _137_286)))
end else begin
()
end
in (
# 360 "FStar.TypeChecker.Tc.fst"
let gimp = (match ((let _137_288 = (FStar_Syntax_Subst.compress head)
in _137_288.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _58_510) -> begin
(
# 363 "FStar.TypeChecker.Tc.fst"
let imp = (env0, u, e, c.FStar_Syntax_Syntax.res_typ, e.FStar_Syntax_Syntax.pos)
in (
# 364 "FStar.TypeChecker.Tc.fst"
let _58_514 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_514.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_514.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_514.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _58_517 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (
# 366 "FStar.TypeChecker.Tc.fst"
let gres = (let _137_289 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _137_289))
in (
# 367 "FStar.TypeChecker.Tc.fst"
let _58_520 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _137_290 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print1 "Guard from application node is %s\n" _137_290))
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
# 372 "FStar.TypeChecker.Tc.fst"
let _58_528 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_528) with
| (env1, topt) -> begin
(
# 373 "FStar.TypeChecker.Tc.fst"
let env1 = (instantiate_both env1)
in (
# 374 "FStar.TypeChecker.Tc.fst"
let _58_533 = (tc_term env1 e1)
in (match (_58_533) with
| (e1, c1, g1) -> begin
(
# 375 "FStar.TypeChecker.Tc.fst"
let _58_544 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(
# 378 "FStar.TypeChecker.Tc.fst"
let _58_540 = (FStar_Syntax_Util.type_u ())
in (match (_58_540) with
| (k, _58_539) -> begin
(
# 379 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _137_291 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_137_291, res_t)))
end))
end)
in (match (_58_544) with
| (env_branches, res_t) -> begin
(
# 382 "FStar.TypeChecker.Tc.fst"
let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (
# 383 "FStar.TypeChecker.Tc.fst"
let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (
# 384 "FStar.TypeChecker.Tc.fst"
let _58_561 = (
# 385 "FStar.TypeChecker.Tc.fst"
let _58_558 = (FStar_List.fold_right (fun _58_552 _58_555 -> (match ((_58_552, _58_555)) with
| ((_58_548, f, c, g), (caccum, gaccum)) -> begin
(let _137_294 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _137_294))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_58_558) with
| (cases, g) -> begin
(let _137_295 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_137_295, g))
end))
in (match (_58_561) with
| (c_branches, g_branches) -> begin
(
# 389 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (guard_x), c_branches))
in (
# 390 "FStar.TypeChecker.Tc.fst"
let e = (let _137_299 = (let _137_298 = (let _137_297 = (FStar_List.map (fun _58_570 -> (match (_58_570) with
| (f, _58_565, _58_567, _58_569) -> begin
f
end)) t_eqns)
in (e1, _137_297))
in FStar_Syntax_Syntax.Tm_match (_137_298))
in (FStar_Syntax_Syntax.mk _137_299 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (
# 392 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ), Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (
# 393 "FStar.TypeChecker.Tc.fst"
let _58_573 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _137_302 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _137_301 = (let _137_300 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _137_300))
in (FStar_Util.print2 "(%s) comp type = %s\n" _137_302 _137_301)))
end else begin
()
end
in (let _137_303 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _137_303))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_585); FStar_Syntax_Syntax.lbunivs = _58_583; FStar_Syntax_Syntax.lbtyp = _58_581; FStar_Syntax_Syntax.lbeff = _58_579; FStar_Syntax_Syntax.lbdef = _58_577}::[]), _58_591) -> begin
(
# 400 "FStar.TypeChecker.Tc.fst"
let _58_594 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_304 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _137_304))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _58_598), _58_601) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_616); FStar_Syntax_Syntax.lbunivs = _58_614; FStar_Syntax_Syntax.lbtyp = _58_612; FStar_Syntax_Syntax.lbeff = _58_610; FStar_Syntax_Syntax.lbdef = _58_608}::_58_606), _58_622) -> begin
(
# 407 "FStar.TypeChecker.Tc.fst"
let _58_625 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_305 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _137_305))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _58_629), _58_632) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 420 "FStar.TypeChecker.Tc.fst"
let check_instantiated_fvar = (fun env v dc e t -> (
# 421 "FStar.TypeChecker.Tc.fst"
let _58_646 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_646) with
| (e, t, implicits) -> begin
(
# 423 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _137_319 = (let _137_318 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _137_318))
in FStar_Util.Inr (_137_319))
end
in (
# 424 "FStar.TypeChecker.Tc.fst"
let is_data_ctor = (fun _58_4 -> (match (_58_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _58_656 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _137_325 = (let _137_324 = (let _137_323 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _137_322 = (FStar_TypeChecker_Env.get_range env)
in (_137_323, _137_322)))
in FStar_Syntax_Syntax.Error (_137_324))
in (Prims.raise _137_325))
end else begin
(value_check_expected_typ env e tc implicits)
end))
end)))
in (
# 434 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (
# 435 "FStar.TypeChecker.Tc.fst"
let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(FStar_All.failwith "Impossible: Violation of locally nameless convention")
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(
# 441 "FStar.TypeChecker.Tc.fst"
let g = (match ((let _137_326 = (FStar_Syntax_Subst.compress t1)
in _137_326.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_667) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _58_670 -> begin
(
# 443 "FStar.TypeChecker.Tc.fst"
let imp = (env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (
# 444 "FStar.TypeChecker.Tc.fst"
let _58_672 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_672.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_672.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_672.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 449 "FStar.TypeChecker.Tc.fst"
let _58_678 = (FStar_Syntax_Util.type_u ())
in (match (_58_678) with
| (t, u) -> begin
(
# 450 "FStar.TypeChecker.Tc.fst"
let e = (FStar_TypeChecker_Util.new_uvar env t)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))
end))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 454 "FStar.TypeChecker.Tc.fst"
let t = if env.FStar_TypeChecker_Env.use_bv_sorts then begin
x.FStar_Syntax_Syntax.sort
end else begin
(FStar_TypeChecker_Env.lookup_bv env x)
end
in (
# 455 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.bv_to_name (
# 455 "FStar.TypeChecker.Tc.fst"
let _58_683 = x
in {FStar_Syntax_Syntax.ppname = _58_683.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_683.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (
# 456 "FStar.TypeChecker.Tc.fst"
let _58_689 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_689) with
| (e, t, implicits) -> begin
(
# 457 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _137_328 = (let _137_327 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _137_327))
in FStar_Util.Inr (_137_328))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _58_696; FStar_Syntax_Syntax.pos = _58_694; FStar_Syntax_Syntax.vars = _58_692}, us) -> begin
(
# 461 "FStar.TypeChecker.Tc.fst"
let us = (FStar_List.map (tc_universe env) us)
in (
# 462 "FStar.TypeChecker.Tc.fst"
let _58_706 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_706) with
| (us', t) -> begin
(
# 463 "FStar.TypeChecker.Tc.fst"
let _58_713 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _137_331 = (let _137_330 = (let _137_329 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _137_329))
in FStar_Syntax_Syntax.Error (_137_330))
in (Prims.raise _137_331))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _58_712 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (
# 468 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 468 "FStar.TypeChecker.Tc.fst"
let _58_715 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 468 "FStar.TypeChecker.Tc.fst"
let _58_717 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_717.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_717.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_715.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_715.FStar_Syntax_Syntax.fv_qual})
in (
# 469 "FStar.TypeChecker.Tc.fst"
let e = (let _137_334 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _137_334 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(
# 473 "FStar.TypeChecker.Tc.fst"
let _58_725 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_725) with
| (us, t) -> begin
(
# 474 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 474 "FStar.TypeChecker.Tc.fst"
let _58_726 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 474 "FStar.TypeChecker.Tc.fst"
let _58_728 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_728.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_728.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_726.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_726.FStar_Syntax_Syntax.fv_qual})
in (
# 475 "FStar.TypeChecker.Tc.fst"
let e = (let _137_335 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _137_335 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t)))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(
# 479 "FStar.TypeChecker.Tc.fst"
let t = (tc_constant env top.FStar_Syntax_Syntax.pos c)
in (
# 480 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 484 "FStar.TypeChecker.Tc.fst"
let _58_742 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_742) with
| (bs, c) -> begin
(
# 485 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 486 "FStar.TypeChecker.Tc.fst"
let _58_747 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_747) with
| (env, _58_746) -> begin
(
# 487 "FStar.TypeChecker.Tc.fst"
let _58_752 = (tc_binders env bs)
in (match (_58_752) with
| (bs, env, g, us) -> begin
(
# 488 "FStar.TypeChecker.Tc.fst"
let _58_756 = (tc_comp env c)
in (match (_58_756) with
| (c, uc, f) -> begin
(
# 489 "FStar.TypeChecker.Tc.fst"
let e = (
# 489 "FStar.TypeChecker.Tc.fst"
let _58_757 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _58_757.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_757.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_757.FStar_Syntax_Syntax.vars})
in (
# 490 "FStar.TypeChecker.Tc.fst"
let _58_760 = (check_smt_pat env e bs c)
in (
# 491 "FStar.TypeChecker.Tc.fst"
let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (
# 492 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 493 "FStar.TypeChecker.Tc.fst"
let g = (let _137_336 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _137_336))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(
# 497 "FStar.TypeChecker.Tc.fst"
let u = (tc_universe env u)
in (
# 498 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) None top.FStar_Syntax_Syntax.pos)
in (
# 499 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 503 "FStar.TypeChecker.Tc.fst"
let _58_776 = (let _137_338 = (let _137_337 = (FStar_Syntax_Syntax.mk_binder x)
in (_137_337)::[])
in (FStar_Syntax_Subst.open_term _137_338 phi))
in (match (_58_776) with
| (x, phi) -> begin
(
# 504 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 505 "FStar.TypeChecker.Tc.fst"
let _58_781 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_781) with
| (env, _58_780) -> begin
(
# 506 "FStar.TypeChecker.Tc.fst"
let _58_786 = (let _137_339 = (FStar_List.hd x)
in (tc_binder env _137_339))
in (match (_58_786) with
| (x, env, f1, u) -> begin
(
# 507 "FStar.TypeChecker.Tc.fst"
let _58_787 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_342 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _137_341 = (FStar_Syntax_Print.term_to_string phi)
in (let _137_340 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _137_342 _137_341 _137_340))))
end else begin
()
end
in (
# 510 "FStar.TypeChecker.Tc.fst"
let _58_792 = (FStar_Syntax_Util.type_u ())
in (match (_58_792) with
| (t_phi, _58_791) -> begin
(
# 511 "FStar.TypeChecker.Tc.fst"
let _58_797 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_58_797) with
| (phi, _58_795, f2) -> begin
(
# 512 "FStar.TypeChecker.Tc.fst"
let e = (
# 512 "FStar.TypeChecker.Tc.fst"
let _58_798 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _58_798.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_798.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_798.FStar_Syntax_Syntax.vars})
in (
# 513 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 514 "FStar.TypeChecker.Tc.fst"
let g = (let _137_343 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _137_343))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _58_806) -> begin
(
# 518 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (
# 519 "FStar.TypeChecker.Tc.fst"
let _58_812 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_344 = (FStar_Syntax_Print.term_to_string (
# 520 "FStar.TypeChecker.Tc.fst"
let _58_810 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _58_810.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _58_810.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_810.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _137_344))
end else begin
()
end
in (
# 521 "FStar.TypeChecker.Tc.fst"
let _58_816 = (FStar_Syntax_Subst.open_term bs body)
in (match (_58_816) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _58_818 -> begin
(let _137_346 = (let _137_345 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _137_345))
in (FStar_All.failwith _137_346))
end)))))
and tc_constant : FStar_TypeChecker_Env.env  ->  FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun env r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_58_824) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_58_827) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int32 (_58_830) -> begin
FStar_TypeChecker_Common.t_int32
end
| FStar_Const.Const_int64 (_58_833) -> begin
FStar_TypeChecker_Common.t_int64
end
| FStar_Const.Const_string (_58_836) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_58_839) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_58_842) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_uint8 (_58_845) -> begin
FStar_TypeChecker_Common.t_uint8
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_58_849) -> begin
(
# 540 "FStar.TypeChecker.Tc.fst"
let fail = (fun _58_852 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Range constant cannot be checked in this context; expected an instance of \'range_of\'", r))))
end))
in (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(fail ())
end
| Some (t) -> begin
if (let _137_352 = (FStar_Syntax_Util.destruct t FStar_Syntax_Const.range_of_lid)
in (FStar_Option.isSome _137_352)) then begin
t
end else begin
(fail ())
end
end))
end
| _58_857 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 561 "FStar.TypeChecker.Tc.fst"
let _58_864 = (FStar_Syntax_Util.type_u ())
in (match (_58_864) with
| (k, u) -> begin
(
# 562 "FStar.TypeChecker.Tc.fst"
let _58_869 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_869) with
| (t, _58_867, g) -> begin
(let _137_355 = (FStar_Syntax_Syntax.mk_Total t)
in (_137_355, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 566 "FStar.TypeChecker.Tc.fst"
let _58_874 = (FStar_Syntax_Util.type_u ())
in (match (_58_874) with
| (k, u) -> begin
(
# 567 "FStar.TypeChecker.Tc.fst"
let _58_879 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_879) with
| (t, _58_877, g) -> begin
(let _137_356 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_137_356, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 571 "FStar.TypeChecker.Tc.fst"
let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (
# 572 "FStar.TypeChecker.Tc.fst"
let tc = (let _137_358 = (let _137_357 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_137_357)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _137_358 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 573 "FStar.TypeChecker.Tc.fst"
let _58_888 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_58_888) with
| (tc, _58_886, f) -> begin
(
# 574 "FStar.TypeChecker.Tc.fst"
let _58_892 = (FStar_Syntax_Util.head_and_args tc)
in (match (_58_892) with
| (_58_890, args) -> begin
(
# 575 "FStar.TypeChecker.Tc.fst"
let _58_895 = (let _137_360 = (FStar_List.hd args)
in (let _137_359 = (FStar_List.tl args)
in (_137_360, _137_359)))
in (match (_58_895) with
| (res, args) -> begin
(
# 576 "FStar.TypeChecker.Tc.fst"
let _58_911 = (let _137_362 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _58_5 -> (match (_58_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(
# 578 "FStar.TypeChecker.Tc.fst"
let _58_902 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_902) with
| (env, _58_901) -> begin
(
# 579 "FStar.TypeChecker.Tc.fst"
let _58_907 = (tc_tot_or_gtot_term env e)
in (match (_58_907) with
| (e, _58_905, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _137_362 FStar_List.unzip))
in (match (_58_911) with
| (flags, guards) -> begin
(
# 582 "FStar.TypeChecker.Tc.fst"
let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| _58_916 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _137_364 = (FStar_Syntax_Syntax.mk_Comp (
# 585 "FStar.TypeChecker.Tc.fst"
let _58_918 = c
in {FStar_Syntax_Syntax.effect_name = _58_918.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _58_918.FStar_Syntax_Syntax.flags}))
in (let _137_363 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_137_364, u, _137_363))))
end))
end))
end))
end))))
end))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (
# 592 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun u -> (
# 593 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_58_926) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _137_369 = (aux u)
in FStar_Syntax_Syntax.U_succ (_137_369))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _137_370 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_137_370))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _137_374 = (let _137_373 = (let _137_372 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _137_371 = (FStar_TypeChecker_Env.get_range env)
in (_137_372, _137_371)))
in FStar_Syntax_Syntax.Error (_137_373))
in (Prims.raise _137_374))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _137_375 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _137_375 Prims.snd))
end
| _58_941 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (
# 615 "FStar.TypeChecker.Tc.fst"
let fail = (fun msg t -> (let _137_384 = (let _137_383 = (let _137_382 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_137_382, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_137_383))
in (Prims.raise _137_384)))
in (
# 624 "FStar.TypeChecker.Tc.fst"
let check_binders = (fun env bs bs_expected -> (
# 629 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun _58_959 bs bs_expected -> (match (_58_959) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| ((hd, imp)::bs, (hd_expected, imp')::bs_expected) -> begin
(
# 633 "FStar.TypeChecker.Tc.fst"
let _58_990 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _137_401 = (let _137_400 = (let _137_399 = (let _137_397 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _137_397))
in (let _137_398 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_137_399, _137_398)))
in FStar_Syntax_Syntax.Error (_137_400))
in (Prims.raise _137_401))
end
| _58_989 -> begin
()
end)
in (
# 640 "FStar.TypeChecker.Tc.fst"
let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (
# 641 "FStar.TypeChecker.Tc.fst"
let _58_1007 = (match ((let _137_402 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _137_402.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _58_995 -> begin
(
# 644 "FStar.TypeChecker.Tc.fst"
let _58_996 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_403 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _137_403))
end else begin
()
end
in (
# 645 "FStar.TypeChecker.Tc.fst"
let _58_1002 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_58_1002) with
| (t, _58_1000, g1) -> begin
(
# 646 "FStar.TypeChecker.Tc.fst"
let g2 = (let _137_405 = (FStar_TypeChecker_Env.get_range env)
in (let _137_404 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _137_405 "Type annotation on parameter incompatible with the expected type" _137_404)))
in (
# 650 "FStar.TypeChecker.Tc.fst"
let g = (let _137_406 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _137_406))
in (t, g)))
end)))
end)
in (match (_58_1007) with
| (t, g) -> begin
(
# 652 "FStar.TypeChecker.Tc.fst"
let hd = (
# 652 "FStar.TypeChecker.Tc.fst"
let _58_1008 = hd
in {FStar_Syntax_Syntax.ppname = _58_1008.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1008.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 653 "FStar.TypeChecker.Tc.fst"
let b = (hd, imp)
in (
# 654 "FStar.TypeChecker.Tc.fst"
let b_expected = (hd_expected, imp')
in (
# 655 "FStar.TypeChecker.Tc.fst"
let env = (maybe_push_binding env b)
in (
# 656 "FStar.TypeChecker.Tc.fst"
let subst = (let _137_407 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _137_407))
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
# 666 "FStar.TypeChecker.Tc.fst"
let rec expected_function_typ = (fun env t0 body -> (match (t0) with
| None -> begin
(
# 677 "FStar.TypeChecker.Tc.fst"
let _58_1029 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _58_1028 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (
# 680 "FStar.TypeChecker.Tc.fst"
let _58_1036 = (tc_binders env bs)
in (match (_58_1036) with
| (bs, envbody, g, _58_1035) -> begin
(
# 681 "FStar.TypeChecker.Tc.fst"
let _58_1054 = (match ((let _137_414 = (FStar_Syntax_Subst.compress body)
in _137_414.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _58_1041) -> begin
(
# 683 "FStar.TypeChecker.Tc.fst"
let _58_1048 = (tc_comp envbody c)
in (match (_58_1048) with
| (c, _58_1046, g') -> begin
(let _137_415 = (FStar_TypeChecker_Rel.conj_guard g g')
in (Some (c), body, _137_415))
end))
end
| _58_1050 -> begin
(None, body, g)
end)
in (match (_58_1054) with
| (copt, body, g) -> begin
(None, bs, [], copt, envbody, body, g)
end))
end)))
end
| Some (t) -> begin
(
# 689 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 690 "FStar.TypeChecker.Tc.fst"
let rec as_function_typ = (fun norm t -> (match ((let _137_420 = (FStar_Syntax_Subst.compress t)
in _137_420.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 694 "FStar.TypeChecker.Tc.fst"
let _58_1081 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _58_1080 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 695 "FStar.TypeChecker.Tc.fst"
let _58_1088 = (tc_binders env bs)
in (match (_58_1088) with
| (bs, envbody, g, _58_1087) -> begin
(
# 696 "FStar.TypeChecker.Tc.fst"
let _58_1092 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_58_1092) with
| (envbody, _58_1091) -> begin
(Some ((t, true)), bs, [], None, envbody, body, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _58_1095) -> begin
(
# 702 "FStar.TypeChecker.Tc.fst"
let _58_1106 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_58_1106) with
| (_58_1099, bs, bs', copt, env, body, g) -> begin
(Some ((t, false)), bs, bs', copt, env, body, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 706 "FStar.TypeChecker.Tc.fst"
let _58_1113 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_58_1113) with
| (bs_expected, c_expected) -> begin
(
# 713 "FStar.TypeChecker.Tc.fst"
let check_actuals_against_formals = (fun env bs bs_expected -> (
# 714 "FStar.TypeChecker.Tc.fst"
let rec handle_more = (fun _58_1124 c_expected -> (match (_58_1124) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _137_431 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _137_431))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(
# 719 "FStar.TypeChecker.Tc.fst"
let c = (let _137_432 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _137_432))
in (let _137_433 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _137_433)))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(
# 723 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.subst_comp subst c_expected)
in if (FStar_Syntax_Util.is_total_comp c) then begin
(
# 726 "FStar.TypeChecker.Tc.fst"
let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 729 "FStar.TypeChecker.Tc.fst"
let _58_1145 = (check_binders env more_bs bs_expected)
in (match (_58_1145) with
| (env, bs', more, guard', subst) -> begin
(let _137_435 = (let _137_434 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _137_434, subst))
in (handle_more _137_435 c_expected))
end))
end
| _58_1147 -> begin
(let _137_437 = (let _137_436 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _137_436))
in (fail _137_437 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _137_438 = (check_binders env bs bs_expected)
in (handle_more _137_438 c_expected))))
in (
# 736 "FStar.TypeChecker.Tc.fst"
let mk_letrec_env = (fun envbody bs c -> (
# 737 "FStar.TypeChecker.Tc.fst"
let letrecs = (guard_letrecs envbody bs c)
in (
# 738 "FStar.TypeChecker.Tc.fst"
let envbody = (
# 738 "FStar.TypeChecker.Tc.fst"
let _58_1153 = envbody
in {FStar_TypeChecker_Env.solver = _58_1153.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1153.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1153.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1153.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1153.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1153.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1153.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1153.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1153.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1153.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1153.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1153.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _58_1153.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1153.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1153.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1153.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1153.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_1153.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_1153.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1153.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1153.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _58_1158 _58_1161 -> (match ((_58_1158, _58_1161)) with
| ((env, letrec_binders), (l, t)) -> begin
(
# 742 "FStar.TypeChecker.Tc.fst"
let _58_1167 = (let _137_448 = (let _137_447 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _137_447 Prims.fst))
in (tc_term _137_448 t))
in (match (_58_1167) with
| (t, _58_1164, _58_1166) -> begin
(
# 743 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (
# 744 "FStar.TypeChecker.Tc.fst"
let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _137_449 = (FStar_Syntax_Syntax.mk_binder (
# 745 "FStar.TypeChecker.Tc.fst"
let _58_1171 = x
in {FStar_Syntax_Syntax.ppname = _58_1171.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1171.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_137_449)::letrec_binders)
end
| _58_1174 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (
# 750 "FStar.TypeChecker.Tc.fst"
let _58_1180 = (check_actuals_against_formals env bs bs_expected)
in (match (_58_1180) with
| (envbody, bs, g, c) -> begin
(
# 751 "FStar.TypeChecker.Tc.fst"
let _58_1183 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_58_1183) with
| (envbody, letrecs) -> begin
(
# 752 "FStar.TypeChecker.Tc.fst"
let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, body, g))
end))
end))))
end))
end
| _58_1186 -> begin
if (not (norm)) then begin
(let _137_450 = (unfold_whnf env t)
in (as_function_typ true _137_450))
end else begin
(
# 760 "FStar.TypeChecker.Tc.fst"
let _58_1196 = (expected_function_typ env None body)
in (match (_58_1196) with
| (_58_1188, bs, _58_1191, c_opt, envbody, body, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, body, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (
# 764 "FStar.TypeChecker.Tc.fst"
let use_eq = env.FStar_TypeChecker_Env.use_eq
in (
# 765 "FStar.TypeChecker.Tc.fst"
let _58_1200 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1200) with
| (env, topt) -> begin
(
# 767 "FStar.TypeChecker.Tc.fst"
let _58_1204 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_451 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _137_451 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (
# 772 "FStar.TypeChecker.Tc.fst"
let _58_1213 = (expected_function_typ env topt body)
in (match (_58_1213) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(
# 773 "FStar.TypeChecker.Tc.fst"
let _58_1219 = (tc_term (
# 773 "FStar.TypeChecker.Tc.fst"
let _58_1214 = envbody
in {FStar_TypeChecker_Env.solver = _58_1214.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1214.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1214.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1214.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1214.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1214.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1214.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1214.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1214.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1214.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1214.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1214.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1214.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_1214.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1214.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1214.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_1214.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_1214.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1214.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1214.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_58_1219) with
| (body, cbody, guard_body) -> begin
(
# 775 "FStar.TypeChecker.Tc.fst"
let _58_1220 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_455 = (FStar_Syntax_Print.term_to_string body)
in (let _137_454 = (let _137_452 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _137_452))
in (let _137_453 = (FStar_TypeChecker_Rel.guard_to_string env guard_body)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _137_455 _137_454 _137_453))))
end else begin
()
end
in (
# 781 "FStar.TypeChecker.Tc.fst"
let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (
# 784 "FStar.TypeChecker.Tc.fst"
let _58_1223 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _137_458 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _137_457 = (let _137_456 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _137_456))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _137_458 _137_457)))
end else begin
()
end
in (
# 789 "FStar.TypeChecker.Tc.fst"
let _58_1230 = (let _137_460 = (let _137_459 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _137_459))
in (check_expected_effect (
# 789 "FStar.TypeChecker.Tc.fst"
let _58_1225 = envbody
in {FStar_TypeChecker_Env.solver = _58_1225.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1225.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1225.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1225.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1225.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1225.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1225.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1225.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1225.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1225.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1225.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1225.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1225.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1225.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1225.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1225.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1225.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_1225.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_1225.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1225.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1225.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _137_460))
in (match (_58_1230) with
| (body, cbody, guard) -> begin
(
# 790 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (
# 791 "FStar.TypeChecker.Tc.fst"
let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _137_461 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _137_461))
end else begin
(
# 793 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (
# 796 "FStar.TypeChecker.Tc.fst"
let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (
# 797 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.abs bs body (Some ((FStar_Syntax_Util.lcomp_of_comp cbody))))
in (
# 798 "FStar.TypeChecker.Tc.fst"
let _58_1253 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(
# 800 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_58_1242) -> begin
(e, t, guard)
end
| _58_1245 -> begin
(
# 807 "FStar.TypeChecker.Tc.fst"
let _58_1248 = if use_teq then begin
(let _137_462 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _137_462))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_58_1248) with
| (e, guard') -> begin
(let _137_463 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _137_463))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_58_1253) with
| (e, tfun, guard) -> begin
(
# 816 "FStar.TypeChecker.Tc.fst"
let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (
# 817 "FStar.TypeChecker.Tc.fst"
let _58_1257 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_58_1257) with
| (c, g) -> begin
(e, c, g)
end)))
end))))))
end)))))
end))
end)))
end)))))))
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead ghead args expected_topt -> (
# 825 "FStar.TypeChecker.Tc.fst"
let n_args = (FStar_List.length args)
in (
# 826 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 827 "FStar.TypeChecker.Tc.fst"
let thead = chead.FStar_Syntax_Syntax.res_typ
in (
# 828 "FStar.TypeChecker.Tc.fst"
let _58_1267 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_472 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _137_471 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _137_472 _137_471)))
end else begin
()
end
in (
# 829 "FStar.TypeChecker.Tc.fst"
let rec check_function_app = (fun norm tf -> (match ((let _137_477 = (FStar_Syntax_Util.unrefine tf)
in _137_477.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 833 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| (e, imp)::tl -> begin
(
# 836 "FStar.TypeChecker.Tc.fst"
let _58_1301 = (tc_term env e)
in (match (_58_1301) with
| (e, c, g_e) -> begin
(
# 837 "FStar.TypeChecker.Tc.fst"
let _58_1305 = (tc_args env tl)
in (match (_58_1305) with
| (args, comps, g_rest) -> begin
(let _137_482 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, (c)::comps, _137_482))
end))
end))
end))
in (
# 845 "FStar.TypeChecker.Tc.fst"
let _58_1309 = (tc_args env args)
in (match (_58_1309) with
| (args, comps, g_args) -> begin
(
# 846 "FStar.TypeChecker.Tc.fst"
let bs = (let _137_484 = (FStar_All.pipe_right comps (FStar_List.map (fun c -> (c.FStar_Syntax_Syntax.res_typ, None))))
in (FStar_Syntax_Util.null_binders_of_tks _137_484))
in (
# 847 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _58_1316 -> begin
FStar_Syntax_Util.ml_comp
end)
in (
# 850 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _137_499 = (FStar_Syntax_Subst.compress t)
in _137_499.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_58_1322) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _58_1327 -> begin
ml_or_tot
end)
end)
in (
# 857 "FStar.TypeChecker.Tc.fst"
let cres = (let _137_504 = (let _137_503 = (let _137_502 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _137_502 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _137_503))
in (ml_or_tot _137_504 r))
in (
# 858 "FStar.TypeChecker.Tc.fst"
let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (
# 859 "FStar.TypeChecker.Tc.fst"
let _58_1331 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _137_507 = (FStar_Syntax_Print.term_to_string head)
in (let _137_506 = (FStar_Syntax_Print.term_to_string tf)
in (let _137_505 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _137_507 _137_506 _137_505))))
end else begin
()
end
in (
# 864 "FStar.TypeChecker.Tc.fst"
let _58_1333 = (let _137_508 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _137_508))
in (
# 865 "FStar.TypeChecker.Tc.fst"
let comp = (let _137_511 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_TypeChecker_Util.bind env None c (None, out))) ((chead)::comps) _137_511))
in (let _137_513 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _137_512 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_137_513, comp, _137_512)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 869 "FStar.TypeChecker.Tc.fst"
let _58_1344 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_1344) with
| (bs, c) -> begin
(
# 871 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun _58_1352 bs cres args -> (match (_58_1352) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (_58_1359)))::rest, (_58_1367, None)::_58_1365) -> begin
(
# 882 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 883 "FStar.TypeChecker.Tc.fst"
let _58_1373 = (check_no_escape (Some (head)) env fvs t)
in (
# 884 "FStar.TypeChecker.Tc.fst"
let _58_1379 = (FStar_TypeChecker_Util.new_implicit_var env t)
in (match (_58_1379) with
| (varg, _58_1377, implicits) -> begin
(
# 885 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (
# 886 "FStar.TypeChecker.Tc.fst"
let arg = (let _137_522 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _137_522))
in (let _137_524 = (let _137_523 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _137_523, fvs))
in (tc_args _137_524 rest cres args))))
end))))
end
| ((x, aqual)::rest, (e, aq)::rest') -> begin
(
# 890 "FStar.TypeChecker.Tc.fst"
let _58_1411 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _58_1410 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (
# 895 "FStar.TypeChecker.Tc.fst"
let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 896 "FStar.TypeChecker.Tc.fst"
let x = (
# 896 "FStar.TypeChecker.Tc.fst"
let _58_1414 = x
in {FStar_Syntax_Syntax.ppname = _58_1414.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1414.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (
# 897 "FStar.TypeChecker.Tc.fst"
let _58_1417 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _137_525 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _137_525))
end else begin
()
end
in (
# 898 "FStar.TypeChecker.Tc.fst"
let _58_1419 = (check_no_escape (Some (head)) env fvs targ)
in (
# 899 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (
# 900 "FStar.TypeChecker.Tc.fst"
let env = (
# 900 "FStar.TypeChecker.Tc.fst"
let _58_1422 = env
in {FStar_TypeChecker_Env.solver = _58_1422.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1422.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1422.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1422.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1422.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1422.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1422.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1422.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1422.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1422.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1422.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1422.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1422.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1422.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1422.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _58_1422.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1422.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_1422.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_1422.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1422.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1422.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 901 "FStar.TypeChecker.Tc.fst"
let _58_1425 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_528 = (FStar_Syntax_Print.tag_of_term e)
in (let _137_527 = (FStar_Syntax_Print.term_to_string e)
in (let _137_526 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _137_528 _137_527 _137_526))))
end else begin
()
end
in (
# 902 "FStar.TypeChecker.Tc.fst"
let _58_1430 = (tc_term env e)
in (match (_58_1430) with
| (e, c, g_e) -> begin
(
# 903 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (
# 905 "FStar.TypeChecker.Tc.fst"
let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(
# 907 "FStar.TypeChecker.Tc.fst"
let subst = (let _137_529 = (FStar_List.hd bs)
in (maybe_extend_subst subst _137_529 e))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(
# 910 "FStar.TypeChecker.Tc.fst"
let subst = (let _137_530 = (FStar_List.hd bs)
in (maybe_extend_subst subst _137_530 e))
in (
# 911 "FStar.TypeChecker.Tc.fst"
let _58_1437 = (((Some (x), c))::comps, g)
in (match (_58_1437) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _137_531 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _137_531)) then begin
(
# 915 "FStar.TypeChecker.Tc.fst"
let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (
# 916 "FStar.TypeChecker.Tc.fst"
let arg' = (let _137_532 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _137_532))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (newx), c))::comps, g, fvs) rest cres rest')))
end else begin
(let _137_536 = (let _137_535 = (let _137_534 = (let _137_533 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _137_533))
in (_137_534)::arg_rets)
in (subst, (arg)::outargs, _137_535, ((Some (x), c))::comps, g, (x)::fvs))
in (tc_args _137_536 rest cres rest'))
end
end
end))
end))))))))))
end
| (_58_1441, []) -> begin
(
# 925 "FStar.TypeChecker.Tc.fst"
let _58_1444 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (
# 926 "FStar.TypeChecker.Tc.fst"
let _58_1462 = (match (bs) with
| [] -> begin
(
# 929 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (
# 935 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (
# 937 "FStar.TypeChecker.Tc.fst"
let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _58_1452 -> (match (_58_1452) with
| (_58_1450, c) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (
# 944 "FStar.TypeChecker.Tc.fst"
let cres = if refine_with_equality then begin
(let _137_538 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _137_538 cres))
end else begin
(
# 950 "FStar.TypeChecker.Tc.fst"
let _58_1454 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_541 = (FStar_Syntax_Print.term_to_string head)
in (let _137_540 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _137_539 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _137_541 _137_540 _137_539))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _58_1458 -> begin
(
# 959 "FStar.TypeChecker.Tc.fst"
let g = (let _137_542 = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (FStar_All.pipe_right _137_542 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _137_547 = (let _137_546 = (let _137_545 = (let _137_544 = (let _137_543 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _137_543))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _137_544))
in (FStar_Syntax_Syntax.mk_Total _137_545))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _137_546))
in (_137_547, g)))
end)
in (match (_58_1462) with
| (cres, g) -> begin
(
# 962 "FStar.TypeChecker.Tc.fst"
let _58_1463 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_548 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _137_548))
end else begin
()
end
in (
# 963 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_List.fold_left (fun out c -> (FStar_TypeChecker_Util.bind env None (Prims.snd c) ((Prims.fst c), out))) cres comps)
in (
# 964 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.bind env None chead (None, comp))
in (
# 965 "FStar.TypeChecker.Tc.fst"
let app = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev outargs) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (
# 966 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.record_application_site env app comp)
in (
# 967 "FStar.TypeChecker.Tc.fst"
let _58_1473 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp g)
in (match (_58_1473) with
| (comp, g) -> begin
(
# 968 "FStar.TypeChecker.Tc.fst"
let _58_1474 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_554 = (FStar_TypeChecker_Normalize.term_to_string env app)
in (let _137_553 = (let _137_552 = (comp.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Print.comp_to_string _137_552))
in (FStar_Util.print2 "\t Type of app term %s is %s\n" _137_554 _137_553)))
end else begin
()
end
in (app, comp, g))
end)))))))
end)))
end
| ([], arg::_58_1478) -> begin
(
# 974 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun norm tres -> (
# 975 "FStar.TypeChecker.Tc.fst"
let tres = (let _137_559 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _137_559 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(
# 978 "FStar.TypeChecker.Tc.fst"
let _58_1490 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_560 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _137_560))
end else begin
()
end
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs (FStar_Syntax_Util.lcomp_of_comp cres') args))
end
| _58_1493 when (not (norm)) -> begin
(let _137_561 = (unfold_whnf env tres)
in (aux true _137_561))
end
| _58_1495 -> begin
(let _137_567 = (let _137_566 = (let _137_565 = (let _137_563 = (FStar_TypeChecker_Normalize.term_to_string env tf)
in (let _137_562 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _137_563 _137_562)))
in (let _137_564 = (FStar_Syntax_Syntax.argpos arg)
in (_137_565, _137_564)))
in FStar_Syntax_Syntax.Error (_137_566))
in (Prims.raise _137_567))
end)))
in (aux false cres.FStar_Syntax_Syntax.res_typ))
end)
end))
in (tc_args ([], [], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs (FStar_Syntax_Util.lcomp_of_comp c) args))
end))
end
| _58_1497 -> begin
if (not (norm)) then begin
(let _137_568 = (unfold_whnf env tf)
in (check_function_app true _137_568))
end else begin
(let _137_571 = (let _137_570 = (let _137_569 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_137_569, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_137_570))
in (Prims.raise _137_571))
end
end))
in (let _137_573 = (let _137_572 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _137_572))
in (check_function_app false _137_573))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (
# 1004 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1005 "FStar.TypeChecker.Tc.fst"
let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(
# 1008 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in (
# 1009 "FStar.TypeChecker.Tc.fst"
let _58_1533 = (FStar_List.fold_left2 (fun _58_1514 _58_1517 _58_1520 -> (match ((_58_1514, _58_1517, _58_1520)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(
# 1010 "FStar.TypeChecker.Tc.fst"
let _58_1521 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1011 "FStar.TypeChecker.Tc.fst"
let _58_1526 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_58_1526) with
| (e, c, g) -> begin
(
# 1012 "FStar.TypeChecker.Tc.fst"
let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (
# 1013 "FStar.TypeChecker.Tc.fst"
let g = (let _137_583 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _137_583 g))
in (
# 1014 "FStar.TypeChecker.Tc.fst"
let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _137_587 = (let _137_585 = (let _137_584 = (FStar_Syntax_Syntax.as_arg e)
in (_137_584)::[])
in (FStar_List.append seen _137_585))
in (let _137_586 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_137_587, _137_586, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_58_1533) with
| (args, guard, ghost) -> begin
(
# 1018 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (
# 1019 "FStar.TypeChecker.Tc.fst"
let c = if ghost then begin
(let _137_588 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _137_588 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (
# 1020 "FStar.TypeChecker.Tc.fst"
let _58_1538 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_58_1538) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _58_1540 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (
# 1040 "FStar.TypeChecker.Tc.fst"
let _58_1547 = (FStar_Syntax_Subst.open_branch branch)
in (match (_58_1547) with
| (pattern, when_clause, branch_exp) -> begin
(
# 1041 "FStar.TypeChecker.Tc.fst"
let _58_1552 = branch
in (match (_58_1552) with
| (cpat, _58_1550, cbr) -> begin
(
# 1044 "FStar.TypeChecker.Tc.fst"
let tc_pat = (fun allow_implicits pat_t p0 -> (
# 1051 "FStar.TypeChecker.Tc.fst"
let _58_1560 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_58_1560) with
| (pat_bvs, exps, p) -> begin
(
# 1052 "FStar.TypeChecker.Tc.fst"
let _58_1561 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_600 = (FStar_Syntax_Print.pat_to_string p0)
in (let _137_599 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _137_600 _137_599)))
end else begin
()
end
in (
# 1054 "FStar.TypeChecker.Tc.fst"
let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (
# 1055 "FStar.TypeChecker.Tc.fst"
let _58_1567 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_58_1567) with
| (env1, _58_1566) -> begin
(
# 1056 "FStar.TypeChecker.Tc.fst"
let env1 = (
# 1056 "FStar.TypeChecker.Tc.fst"
let _58_1568 = env1
in {FStar_TypeChecker_Env.solver = _58_1568.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1568.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1568.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1568.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1568.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1568.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1568.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1568.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _58_1568.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1568.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1568.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1568.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1568.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1568.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1568.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1568.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1568.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_1568.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_1568.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1568.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1568.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1057 "FStar.TypeChecker.Tc.fst"
let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (
# 1058 "FStar.TypeChecker.Tc.fst"
let _58_1607 = (let _137_623 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (
# 1059 "FStar.TypeChecker.Tc.fst"
let _58_1573 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_603 = (FStar_Syntax_Print.term_to_string e)
in (let _137_602 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _137_603 _137_602)))
end else begin
()
end
in (
# 1062 "FStar.TypeChecker.Tc.fst"
let _58_1578 = (tc_term env1 e)
in (match (_58_1578) with
| (e, lc, g) -> begin
(
# 1064 "FStar.TypeChecker.Tc.fst"
let _58_1579 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_605 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _137_604 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _137_605 _137_604)))
end else begin
()
end
in (
# 1067 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (
# 1068 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (
# 1069 "FStar.TypeChecker.Tc.fst"
let _58_1585 = (let _137_606 = (FStar_TypeChecker_Rel.discharge_guard env (
# 1069 "FStar.TypeChecker.Tc.fst"
let _58_1583 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_1583.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_1583.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_1583.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _137_606 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1070 "FStar.TypeChecker.Tc.fst"
let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (
# 1071 "FStar.TypeChecker.Tc.fst"
let uvars_to_string = (fun uvs -> (let _137_611 = (let _137_610 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _137_610 (FStar_List.map (fun _58_1593 -> (match (_58_1593) with
| (u, _58_1592) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _137_611 (FStar_String.concat ", "))))
in (
# 1072 "FStar.TypeChecker.Tc.fst"
let uvs1 = (FStar_Syntax_Free.uvars e')
in (
# 1073 "FStar.TypeChecker.Tc.fst"
let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (
# 1074 "FStar.TypeChecker.Tc.fst"
let _58_1601 = if (let _137_612 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _137_612)) then begin
(
# 1075 "FStar.TypeChecker.Tc.fst"
let unresolved = (let _137_613 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _137_613 FStar_Util.set_elements))
in (let _137_621 = (let _137_620 = (let _137_619 = (let _137_618 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _137_617 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _137_616 = (let _137_615 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _58_1600 -> (match (_58_1600) with
| (u, _58_1599) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _137_615 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _137_618 _137_617 _137_616))))
in (_137_619, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_137_620))
in (Prims.raise _137_621)))
end else begin
()
end
in (
# 1082 "FStar.TypeChecker.Tc.fst"
let _58_1603 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_622 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _137_622))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _137_623 FStar_List.unzip))
in (match (_58_1607) with
| (exps, norm_exps) -> begin
(
# 1087 "FStar.TypeChecker.Tc.fst"
let p = (FStar_TypeChecker_Util.decorate_pattern env p exps)
in (p, pat_bvs, pat_env, exps, norm_exps))
end))))
end))))
end)))
in (
# 1091 "FStar.TypeChecker.Tc.fst"
let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (
# 1092 "FStar.TypeChecker.Tc.fst"
let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (
# 1093 "FStar.TypeChecker.Tc.fst"
let _58_1614 = (let _137_624 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _137_624 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_58_1614) with
| (scrutinee_env, _58_1613) -> begin
(
# 1096 "FStar.TypeChecker.Tc.fst"
let _58_1620 = (tc_pat true pat_t pattern)
in (match (_58_1620) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(
# 1099 "FStar.TypeChecker.Tc.fst"
let _58_1630 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(
# 1106 "FStar.TypeChecker.Tc.fst"
let _58_1627 = (let _137_625 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _137_625 e))
in (match (_58_1627) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_58_1630) with
| (when_clause, g_when) -> begin
(
# 1110 "FStar.TypeChecker.Tc.fst"
let _58_1634 = (tc_term pat_env branch_exp)
in (match (_58_1634) with
| (branch_exp, c, g_branch) -> begin
(
# 1114 "FStar.TypeChecker.Tc.fst"
let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _137_627 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _137_626 -> Some (_137_626)) _137_627))
end)
in (
# 1121 "FStar.TypeChecker.Tc.fst"
let _58_1690 = (
# 1124 "FStar.TypeChecker.Tc.fst"
let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (
# 1125 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _58_1652 -> begin
(
# 1131 "FStar.TypeChecker.Tc.fst"
let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _137_631 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _137_630 -> Some (_137_630)) _137_631))
end))
end))) None))
in (
# 1136 "FStar.TypeChecker.Tc.fst"
let _58_1660 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_58_1660) with
| (c, g_branch) -> begin
(
# 1140 "FStar.TypeChecker.Tc.fst"
let _58_1685 = (match ((eqs, when_condition)) with
| (None, None) -> begin
(c, g_when)
end
| (Some (f), None) -> begin
(
# 1146 "FStar.TypeChecker.Tc.fst"
let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1147 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _137_634 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _137_633 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_137_634, _137_633)))))
end
| (Some (f), Some (w)) -> begin
(
# 1152 "FStar.TypeChecker.Tc.fst"
let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1153 "FStar.TypeChecker.Tc.fst"
let g_fw = (let _137_635 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_137_635))
in (let _137_638 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _137_637 = (let _137_636 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _137_636 g_when))
in (_137_638, _137_637)))))
end
| (None, Some (w)) -> begin
(
# 1158 "FStar.TypeChecker.Tc.fst"
let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (
# 1159 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _137_639 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_137_639, g_when))))
end)
in (match (_58_1685) with
| (c_weak, g_when_weak) -> begin
(
# 1164 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _137_641 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _137_640 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_137_641, _137_640, g_branch))))
end))
end)))
in (match (_58_1690) with
| (c, g_when, g_branch) -> begin
(
# 1182 "FStar.TypeChecker.Tc.fst"
let branch_guard = (
# 1184 "FStar.TypeChecker.Tc.fst"
let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (
# 1185 "FStar.TypeChecker.Tc.fst"
let discriminate = (fun scrutinee_tm f -> if ((let _137_651 = (let _137_650 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _137_650))
in (FStar_List.length _137_651)) > 1) then begin
(
# 1188 "FStar.TypeChecker.Tc.fst"
let disc = (let _137_652 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _137_652 FStar_Syntax_Syntax.Delta_equational None))
in (
# 1189 "FStar.TypeChecker.Tc.fst"
let disc = (let _137_654 = (let _137_653 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_137_653)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _137_654 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _137_655 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_137_655)::[])))
end else begin
[]
end)
in (
# 1193 "FStar.TypeChecker.Tc.fst"
let fail = (fun _58_1700 -> (match (()) with
| () -> begin
(let _137_661 = (let _137_660 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _137_659 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _137_658 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _137_660 _137_659 _137_658))))
in (FStar_All.failwith _137_661))
end))
in (
# 1199 "FStar.TypeChecker.Tc.fst"
let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _58_1707) -> begin
(head_constructor t)
end
| _58_1711 -> begin
(fail ())
end))
in (
# 1204 "FStar.TypeChecker.Tc.fst"
let pat_exp = (let _137_664 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _137_664 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_58_1736) -> begin
(let _137_669 = (let _137_668 = (let _137_667 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _137_666 = (let _137_665 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_137_665)::[])
in (_137_667)::_137_666))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _137_668 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_137_669)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 1213 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _137_670 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _137_670))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 1218 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(
# 1221 "FStar.TypeChecker.Tc.fst"
let sub_term_guards = (let _137_677 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _58_1754 -> (match (_58_1754) with
| (ei, _58_1753) -> begin
(
# 1222 "FStar.TypeChecker.Tc.fst"
let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _58_1758 -> begin
(
# 1226 "FStar.TypeChecker.Tc.fst"
let sub_term = (let _137_676 = (let _137_673 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _137_673 FStar_Syntax_Syntax.Delta_equational None))
in (let _137_675 = (let _137_674 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_137_674)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _137_676 _137_675 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _137_677 FStar_List.flatten))
in (let _137_678 = (discriminate scrutinee_tm f)
in (FStar_List.append _137_678 sub_term_guards)))
end)
end
| _58_1762 -> begin
[]
end))))))
in (
# 1232 "FStar.TypeChecker.Tc.fst"
let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(
# 1235 "FStar.TypeChecker.Tc.fst"
let t = (let _137_683 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _137_683))
in (
# 1236 "FStar.TypeChecker.Tc.fst"
let _58_1770 = (FStar_Syntax_Util.type_u ())
in (match (_58_1770) with
| (k, _58_1769) -> begin
(
# 1237 "FStar.TypeChecker.Tc.fst"
let _58_1776 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_58_1776) with
| (t, _58_1773, _58_1775) -> begin
t
end))
end)))
end)
in (
# 1241 "FStar.TypeChecker.Tc.fst"
let branch_guard = (let _137_684 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _137_684 FStar_Syntax_Util.mk_disj_l))
in (
# 1244 "FStar.TypeChecker.Tc.fst"
let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
in (
# 1250 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (
# 1252 "FStar.TypeChecker.Tc.fst"
let _58_1784 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_685 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _137_685))
end else begin
()
end
in (let _137_686 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_137_686, branch_guard, c, guard)))))
end)))
end))
end))
end))
end)))))
end))
end)))
and check_top_level_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1266 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1269 "FStar.TypeChecker.Tc.fst"
let _58_1801 = (check_let_bound_def true env lb)
in (match (_58_1801) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(
# 1271 "FStar.TypeChecker.Tc.fst"
let _58_1813 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(
# 1274 "FStar.TypeChecker.Tc.fst"
let g1 = (let _137_689 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _137_689 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1275 "FStar.TypeChecker.Tc.fst"
let _58_1808 = (let _137_693 = (let _137_692 = (let _137_691 = (let _137_690 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _137_690))
in (_137_691)::[])
in (FStar_TypeChecker_Util.generalize env _137_692))
in (FStar_List.hd _137_693))
in (match (_58_1808) with
| (_58_1804, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_58_1813) with
| (g1, e1, univ_vars, c1) -> begin
(
# 1279 "FStar.TypeChecker.Tc.fst"
let _58_1823 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(
# 1281 "FStar.TypeChecker.Tc.fst"
let _58_1816 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_58_1816) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(
# 1284 "FStar.TypeChecker.Tc.fst"
let _58_1817 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _137_694 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _137_694 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _137_695 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_137_695, c1)))
end
end))
end else begin
(
# 1288 "FStar.TypeChecker.Tc.fst"
let _58_1819 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _137_696 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _137_696)))
end
in (match (_58_1823) with
| (e2, c1) -> begin
(
# 1293 "FStar.TypeChecker.Tc.fst"
let cres = (let _137_697 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _137_697))
in (
# 1294 "FStar.TypeChecker.Tc.fst"
let _58_1825 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1296 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _137_698 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_137_698, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _58_1829 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1313 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1316 "FStar.TypeChecker.Tc.fst"
let env = (
# 1316 "FStar.TypeChecker.Tc.fst"
let _58_1840 = env
in {FStar_TypeChecker_Env.solver = _58_1840.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1840.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1840.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1840.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1840.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1840.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1840.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1840.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1840.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1840.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1840.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1840.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1840.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_1840.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1840.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1840.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1840.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_1840.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_1840.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1840.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1840.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1317 "FStar.TypeChecker.Tc.fst"
let _58_1849 = (let _137_702 = (let _137_701 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _137_701 Prims.fst))
in (check_let_bound_def false _137_702 lb))
in (match (_58_1849) with
| (e1, _58_1845, c1, g1, annotated) -> begin
(
# 1318 "FStar.TypeChecker.Tc.fst"
let x = (
# 1318 "FStar.TypeChecker.Tc.fst"
let _58_1850 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_1850.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1850.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (
# 1319 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (
# 1320 "FStar.TypeChecker.Tc.fst"
let _58_1856 = (let _137_704 = (let _137_703 = (FStar_Syntax_Syntax.mk_binder x)
in (_137_703)::[])
in (FStar_Syntax_Subst.open_term _137_704 e2))
in (match (_58_1856) with
| (xb, e2) -> begin
(
# 1321 "FStar.TypeChecker.Tc.fst"
let xbinder = (FStar_List.hd xb)
in (
# 1322 "FStar.TypeChecker.Tc.fst"
let x = (Prims.fst xbinder)
in (
# 1323 "FStar.TypeChecker.Tc.fst"
let _58_1862 = (let _137_705 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _137_705 e2))
in (match (_58_1862) with
| (e2, c2, g2) -> begin
(
# 1324 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (x), c2))
in (
# 1325 "FStar.TypeChecker.Tc.fst"
let e = (let _137_708 = (let _137_707 = (let _137_706 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _137_706))
in FStar_Syntax_Syntax.Tm_let (_137_707))
in (FStar_Syntax_Syntax.mk _137_708 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 1326 "FStar.TypeChecker.Tc.fst"
let x_eq_e1 = (let _137_711 = (let _137_710 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _137_710 e1))
in (FStar_All.pipe_left (fun _137_709 -> FStar_TypeChecker_Common.NonTrivial (_137_709)) _137_711))
in (
# 1327 "FStar.TypeChecker.Tc.fst"
let g2 = (let _137_713 = (let _137_712 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _137_712 g2))
in (FStar_TypeChecker_Rel.close_guard xb _137_713))
in (
# 1329 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if annotated then begin
(e, cres, guard)
end else begin
(
# 1333 "FStar.TypeChecker.Tc.fst"
let _58_1868 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end)))))
end))))
end))))
end)))
end
| _58_1871 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1342 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1345 "FStar.TypeChecker.Tc.fst"
let _58_1883 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_58_1883) with
| (lbs, e2) -> begin
(
# 1347 "FStar.TypeChecker.Tc.fst"
let _58_1886 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1886) with
| (env0, topt) -> begin
(
# 1348 "FStar.TypeChecker.Tc.fst"
let _58_1889 = (build_let_rec_env true env0 lbs)
in (match (_58_1889) with
| (lbs, rec_env) -> begin
(
# 1349 "FStar.TypeChecker.Tc.fst"
let _58_1892 = (check_let_recs rec_env lbs)
in (match (_58_1892) with
| (lbs, g_lbs) -> begin
(
# 1350 "FStar.TypeChecker.Tc.fst"
let g_lbs = (let _137_716 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _137_716 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1352 "FStar.TypeChecker.Tc.fst"
let all_lb_names = (let _137_719 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _137_719 (fun _137_718 -> Some (_137_718))))
in (
# 1354 "FStar.TypeChecker.Tc.fst"
let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(
# 1360 "FStar.TypeChecker.Tc.fst"
let ecs = (let _137_723 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _137_722 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _137_722)))))
in (FStar_TypeChecker_Util.generalize env _137_723))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _58_1903 -> (match (_58_1903) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (
# 1367 "FStar.TypeChecker.Tc.fst"
let cres = (let _137_725 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _137_725))
in (
# 1368 "FStar.TypeChecker.Tc.fst"
let _58_1906 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1370 "FStar.TypeChecker.Tc.fst"
let _58_1910 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_1910) with
| (lbs, e2) -> begin
(let _137_727 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _137_726 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_137_727, cres, _137_726)))
end)))))))
end))
end))
end))
end))
end
| _58_1912 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1381 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1384 "FStar.TypeChecker.Tc.fst"
let _58_1924 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_58_1924) with
| (lbs, e2) -> begin
(
# 1386 "FStar.TypeChecker.Tc.fst"
let _58_1927 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1927) with
| (env0, topt) -> begin
(
# 1387 "FStar.TypeChecker.Tc.fst"
let _58_1930 = (build_let_rec_env false env0 lbs)
in (match (_58_1930) with
| (lbs, rec_env) -> begin
(
# 1388 "FStar.TypeChecker.Tc.fst"
let _58_1933 = (check_let_recs rec_env lbs)
in (match (_58_1933) with
| (lbs, g_lbs) -> begin
(
# 1390 "FStar.TypeChecker.Tc.fst"
let _58_1945 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (
# 1391 "FStar.TypeChecker.Tc.fst"
let x = (
# 1391 "FStar.TypeChecker.Tc.fst"
let _58_1936 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_1936.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1936.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (
# 1392 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1392 "FStar.TypeChecker.Tc.fst"
let _58_1939 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _58_1939.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _58_1939.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _58_1939.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _58_1939.FStar_Syntax_Syntax.lbdef})
in (
# 1393 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], lb.FStar_Syntax_Syntax.lbtyp))
in (env, lb))))) env))
in (match (_58_1945) with
| (env, lbs) -> begin
(
# 1396 "FStar.TypeChecker.Tc.fst"
let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (
# 1398 "FStar.TypeChecker.Tc.fst"
let _58_1951 = (tc_term env e2)
in (match (_58_1951) with
| (e2, cres, g2) -> begin
(
# 1399 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (
# 1400 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (
# 1401 "FStar.TypeChecker.Tc.fst"
let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (
# 1402 "FStar.TypeChecker.Tc.fst"
let cres = (
# 1402 "FStar.TypeChecker.Tc.fst"
let _58_1955 = cres
in {FStar_Syntax_Syntax.eff_name = _58_1955.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _58_1955.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_1955.FStar_Syntax_Syntax.comp})
in (
# 1404 "FStar.TypeChecker.Tc.fst"
let _58_1960 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_1960) with
| (lbs, e2) -> begin
(
# 1405 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_58_1963) -> begin
(e, cres, guard)
end
| None -> begin
(
# 1409 "FStar.TypeChecker.Tc.fst"
let _58_1966 = (check_no_escape None env bvs tres)
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
| _58_1969 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (
# 1420 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1421 "FStar.TypeChecker.Tc.fst"
let _58_2002 = (FStar_List.fold_left (fun _58_1976 lb -> (match (_58_1976) with
| (lbs, env) -> begin
(
# 1422 "FStar.TypeChecker.Tc.fst"
let _58_1981 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_58_1981) with
| (univ_vars, t, check_t) -> begin
(
# 1423 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (
# 1424 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (
# 1425 "FStar.TypeChecker.Tc.fst"
let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(
# 1430 "FStar.TypeChecker.Tc.fst"
let _58_1990 = (let _137_739 = (let _137_738 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _137_738))
in (tc_check_tot_or_gtot_term (
# 1430 "FStar.TypeChecker.Tc.fst"
let _58_1984 = env0
in {FStar_TypeChecker_Env.solver = _58_1984.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1984.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1984.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1984.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1984.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1984.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1984.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1984.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1984.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1984.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1984.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1984.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1984.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1984.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _58_1984.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1984.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1984.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_1984.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_1984.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1984.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1984.FStar_TypeChecker_Env.use_bv_sorts}) t _137_739))
in (match (_58_1990) with
| (t, _58_1988, g) -> begin
(
# 1431 "FStar.TypeChecker.Tc.fst"
let _58_1991 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (
# 1433 "FStar.TypeChecker.Tc.fst"
let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(
# 1435 "FStar.TypeChecker.Tc.fst"
let _58_1994 = env
in {FStar_TypeChecker_Env.solver = _58_1994.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1994.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1994.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1994.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1994.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1994.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1994.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1994.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1994.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1994.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1994.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1994.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1994.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1994.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1994.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1994.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1994.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_1994.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_1994.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1994.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1994.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (
# 1437 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1437 "FStar.TypeChecker.Tc.fst"
let _58_1997 = lb
in {FStar_Syntax_Syntax.lbname = _58_1997.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _58_1997.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_58_2002) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (
# 1444 "FStar.TypeChecker.Tc.fst"
let _58_2015 = (let _137_744 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 1445 "FStar.TypeChecker.Tc.fst"
let _58_2009 = (let _137_743 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _137_743 lb.FStar_Syntax_Syntax.lbdef))
in (match (_58_2009) with
| (e, c, g) -> begin
(
# 1446 "FStar.TypeChecker.Tc.fst"
let _58_2010 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1448 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _137_744 FStar_List.unzip))
in (match (_58_2015) with
| (lbs, gs) -> begin
(
# 1450 "FStar.TypeChecker.Tc.fst"
let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (
# 1464 "FStar.TypeChecker.Tc.fst"
let _58_2023 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2023) with
| (env1, _58_2022) -> begin
(
# 1465 "FStar.TypeChecker.Tc.fst"
let e1 = lb.FStar_Syntax_Syntax.lbdef
in (
# 1468 "FStar.TypeChecker.Tc.fst"
let _58_2029 = (check_lbtyp top_level env lb)
in (match (_58_2029) with
| (topt, wf_annot, univ_vars, env1) -> begin
(
# 1470 "FStar.TypeChecker.Tc.fst"
let _58_2030 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1474 "FStar.TypeChecker.Tc.fst"
let _58_2037 = (tc_maybe_toplevel_term (
# 1474 "FStar.TypeChecker.Tc.fst"
let _58_2032 = env1
in {FStar_TypeChecker_Env.solver = _58_2032.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2032.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2032.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2032.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2032.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2032.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2032.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2032.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2032.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2032.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2032.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2032.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2032.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _58_2032.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2032.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2032.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2032.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_2032.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_2032.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2032.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2032.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_58_2037) with
| (e1, c1, g1) -> begin
(
# 1477 "FStar.TypeChecker.Tc.fst"
let _58_2041 = (let _137_751 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_2038 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _137_751 e1 c1 wf_annot))
in (match (_58_2041) with
| (c1, guard_f) -> begin
(
# 1480 "FStar.TypeChecker.Tc.fst"
let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (
# 1482 "FStar.TypeChecker.Tc.fst"
let _58_2043 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _137_752 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _137_752))
end else begin
()
end
in (let _137_753 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _137_753))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (
# 1494 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 1497 "FStar.TypeChecker.Tc.fst"
let _58_2050 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _58_2053 -> begin
(
# 1501 "FStar.TypeChecker.Tc.fst"
let _58_2056 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_58_2056) with
| (univ_vars, t) -> begin
(
# 1502 "FStar.TypeChecker.Tc.fst"
let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _137_757 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _137_757))
end else begin
(
# 1509 "FStar.TypeChecker.Tc.fst"
let _58_2061 = (FStar_Syntax_Util.type_u ())
in (match (_58_2061) with
| (k, _58_2060) -> begin
(
# 1510 "FStar.TypeChecker.Tc.fst"
let _58_2066 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_58_2066) with
| (t, _58_2064, g) -> begin
(
# 1511 "FStar.TypeChecker.Tc.fst"
let _58_2067 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _137_760 = (let _137_758 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _137_758))
in (let _137_759 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _137_760 _137_759)))
end else begin
()
end
in (
# 1515 "FStar.TypeChecker.Tc.fst"
let t = (norm env1 t)
in (let _137_761 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _137_761))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _58_2073 -> (match (_58_2073) with
| (x, imp) -> begin
(
# 1520 "FStar.TypeChecker.Tc.fst"
let _58_2076 = (FStar_Syntax_Util.type_u ())
in (match (_58_2076) with
| (tu, u) -> begin
(
# 1521 "FStar.TypeChecker.Tc.fst"
let _58_2081 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_58_2081) with
| (t, _58_2079, g) -> begin
(
# 1522 "FStar.TypeChecker.Tc.fst"
let x = ((
# 1522 "FStar.TypeChecker.Tc.fst"
let _58_2082 = x
in {FStar_Syntax_Syntax.ppname = _58_2082.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2082.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (
# 1523 "FStar.TypeChecker.Tc.fst"
let _58_2085 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_765 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _137_764 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _137_765 _137_764)))
end else begin
()
end
in (let _137_766 = (maybe_push_binding env x)
in (x, _137_766, g, u))))
end))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe Prims.list) = (fun env bs -> (
# 1528 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_TypeChecker_Rel.trivial_guard, [])
end
| b::bs -> begin
(
# 1531 "FStar.TypeChecker.Tc.fst"
let _58_2100 = (tc_binder env b)
in (match (_58_2100) with
| (b, env', g, u) -> begin
(
# 1532 "FStar.TypeChecker.Tc.fst"
let _58_2105 = (aux env' bs)
in (match (_58_2105) with
| (bs, env', g', us) -> begin
(let _137_774 = (let _137_773 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _137_773))
in ((b)::bs, env', _137_774, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (
# 1537 "FStar.TypeChecker.Tc.fst"
let tc_args = (fun env args -> (FStar_List.fold_right (fun _58_2113 _58_2116 -> (match ((_58_2113, _58_2116)) with
| ((t, imp), (args, g)) -> begin
(
# 1541 "FStar.TypeChecker.Tc.fst"
let _58_2121 = (tc_term env t)
in (match (_58_2121) with
| (t, _58_2119, g') -> begin
(let _137_783 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _137_783))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _58_2125 -> (match (_58_2125) with
| (pats, g) -> begin
(
# 1544 "FStar.TypeChecker.Tc.fst"
let _58_2128 = (tc_args env p)
in (match (_58_2128) with
| (args, g') -> begin
(let _137_786 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _137_786))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1549 "FStar.TypeChecker.Tc.fst"
let _58_2134 = (tc_maybe_toplevel_term env e)
in (match (_58_2134) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(
# 1552 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (
# 1553 "FStar.TypeChecker.Tc.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 1554 "FStar.TypeChecker.Tc.fst"
let _58_2137 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _137_789 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _137_789))
end else begin
()
end
in (
# 1555 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 1556 "FStar.TypeChecker.Tc.fst"
let _58_2142 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _137_790 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_137_790, false))
end else begin
(let _137_791 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_137_791, true))
end
in (match (_58_2142) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _137_792 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _137_792))
end
| _58_2146 -> begin
if allow_ghost then begin
(let _137_795 = (let _137_794 = (let _137_793 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_137_793, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_137_794))
in (Prims.raise _137_795))
end else begin
(let _137_798 = (let _137_797 = (let _137_796 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_137_796, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_137_797))
in (Prims.raise _137_798))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 1570 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))

# 1574 "FStar.TypeChecker.Tc.fst"
let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (
# 1575 "FStar.TypeChecker.Tc.fst"
let _58_2156 = (tc_tot_or_gtot_term env t)
in (match (_58_2156) with
| (t, c, g) -> begin
(
# 1576 "FStar.TypeChecker.Tc.fst"
let _58_2157 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))

# 1579 "FStar.TypeChecker.Tc.fst"
let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (
# 1580 "FStar.TypeChecker.Tc.fst"
let _58_2165 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_2165) with
| (t, c, g) -> begin
(
# 1581 "FStar.TypeChecker.Tc.fst"
let _58_2166 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))

# 1584 "FStar.TypeChecker.Tc.fst"
let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _137_818 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _137_818)))

# 1587 "FStar.TypeChecker.Tc.fst"
let check_nogen = (fun env t k -> (
# 1588 "FStar.TypeChecker.Tc.fst"
let t = (tc_check_trivial_guard env t k)
in (let _137_822 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _137_822))))

# 1591 "FStar.TypeChecker.Tc.fst"
let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (
# 1592 "FStar.TypeChecker.Tc.fst"
let _58_2181 = (tc_binders env tps)
in (match (_58_2181) with
| (tps, env, g, us) -> begin
(
# 1593 "FStar.TypeChecker.Tc.fst"
let _58_2182 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))

# 1596 "FStar.TypeChecker.Tc.fst"
let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (
# 1597 "FStar.TypeChecker.Tc.fst"
let fail = (fun _58_2188 -> (match (()) with
| () -> begin
(let _137_837 = (let _137_836 = (let _137_835 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_137_835, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_137_836))
in (Prims.raise _137_837))
end))
in (
# 1598 "FStar.TypeChecker.Tc.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1601 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _58_2205)::(wp, _58_2201)::(_wlp, _58_2197)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _58_2209 -> begin
(fail ())
end))
end
| _58_2211 -> begin
(fail ())
end))))

# 1608 "FStar.TypeChecker.Tc.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 1611 "FStar.TypeChecker.Tc.fst"
let _58_2218 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_58_2218) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _58_2220 -> begin
(
# 1614 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow binders c)
in (
# 1615 "FStar.TypeChecker.Tc.fst"
let _58_2224 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_58_2224) with
| (uvs, t') -> begin
(match ((let _137_844 = (FStar_Syntax_Subst.compress t')
in _137_844.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _58_2230 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 1620 "FStar.TypeChecker.Tc.fst"
let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (
# 1621 "FStar.TypeChecker.Tc.fst"
let fail = (fun t -> (let _137_855 = (let _137_854 = (let _137_853 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_137_853, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_137_854))
in (Prims.raise _137_855)))
in (match ((let _137_856 = (FStar_Syntax_Subst.compress signature)
in _137_856.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1624 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _58_2251)::(wp, _58_2247)::(_wlp, _58_2243)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _58_2255 -> begin
(fail signature)
end))
end
| _58_2257 -> begin
(fail signature)
end)))

# 1631 "FStar.TypeChecker.Tc.fst"
let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (
# 1632 "FStar.TypeChecker.Tc.fst"
let _58_2262 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_58_2262) with
| (a, wp) -> begin
(
# 1633 "FStar.TypeChecker.Tc.fst"
let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _58_2265 -> begin
(
# 1637 "FStar.TypeChecker.Tc.fst"
let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (
# 1638 "FStar.TypeChecker.Tc.fst"
let op = (fun ts -> (
# 1639 "FStar.TypeChecker.Tc.fst"
let _58_2269 = ()
in (
# 1640 "FStar.TypeChecker.Tc.fst"
let t0 = (Prims.snd ts)
in (
# 1641 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (
# 1643 "FStar.TypeChecker.Tc.fst"
let _58_2273 = ed
in (let _137_875 = (op ed.FStar_Syntax_Syntax.ret)
in (let _137_874 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _137_873 = (op ed.FStar_Syntax_Syntax.bind_wlp)
in (let _137_872 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _137_871 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _137_870 = (op ed.FStar_Syntax_Syntax.ite_wlp)
in (let _137_869 = (op ed.FStar_Syntax_Syntax.wp_binop)
in (let _137_868 = (op ed.FStar_Syntax_Syntax.wp_as_type)
in (let _137_867 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _137_866 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _137_865 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _137_864 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _137_863 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _58_2273.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2273.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _58_2273.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _58_2273.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _58_2273.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _137_875; FStar_Syntax_Syntax.bind_wp = _137_874; FStar_Syntax_Syntax.bind_wlp = _137_873; FStar_Syntax_Syntax.if_then_else = _137_872; FStar_Syntax_Syntax.ite_wp = _137_871; FStar_Syntax_Syntax.ite_wlp = _137_870; FStar_Syntax_Syntax.wp_binop = _137_869; FStar_Syntax_Syntax.wp_as_type = _137_868; FStar_Syntax_Syntax.close_wp = _137_867; FStar_Syntax_Syntax.assert_p = _137_866; FStar_Syntax_Syntax.assume_p = _137_865; FStar_Syntax_Syntax.null_wp = _137_864; FStar_Syntax_Syntax.trivial = _137_863}))))))))))))))))
end)
in (ed, a, wp))
end)))

# 1659 "FStar.TypeChecker.Tc.fst"
let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (
# 1660 "FStar.TypeChecker.Tc.fst"
let _58_2278 = ()
in (
# 1661 "FStar.TypeChecker.Tc.fst"
let _58_2282 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_58_2282) with
| (binders_un, signature_un) -> begin
(
# 1662 "FStar.TypeChecker.Tc.fst"
let _58_2287 = (tc_tparams env0 binders_un)
in (match (_58_2287) with
| (binders, env, _58_2286) -> begin
(
# 1663 "FStar.TypeChecker.Tc.fst"
let _58_2291 = (tc_trivial_guard env signature_un)
in (match (_58_2291) with
| (signature, _58_2290) -> begin
(
# 1664 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1664 "FStar.TypeChecker.Tc.fst"
let _58_2292 = ed
in {FStar_Syntax_Syntax.qualifiers = _58_2292.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2292.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _58_2292.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _58_2292.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _58_2292.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _58_2292.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = _58_2292.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _58_2292.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _58_2292.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = _58_2292.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _58_2292.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _58_2292.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _58_2292.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _58_2292.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _58_2292.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _58_2292.FStar_Syntax_Syntax.trivial})
in (
# 1667 "FStar.TypeChecker.Tc.fst"
let _58_2298 = (open_effect_decl env ed)
in (match (_58_2298) with
| (ed, a, wp_a) -> begin
(
# 1668 "FStar.TypeChecker.Tc.fst"
let get_effect_signature = (fun _58_2300 -> (match (()) with
| () -> begin
(
# 1669 "FStar.TypeChecker.Tc.fst"
let _58_2304 = (tc_trivial_guard env signature_un)
in (match (_58_2304) with
| (signature, _58_2303) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (
# 1673 "FStar.TypeChecker.Tc.fst"
let env = (let _137_882 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _137_882))
in (
# 1675 "FStar.TypeChecker.Tc.fst"
let _58_2306 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _137_885 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _137_884 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _137_883 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checked effect signature: %s %s : %s\n" _137_885 _137_884 _137_883))))
end else begin
()
end
in (
# 1681 "FStar.TypeChecker.Tc.fst"
let check_and_gen' = (fun env _58_2313 k -> (match (_58_2313) with
| (_58_2311, t) -> begin
(check_and_gen env t k)
end))
in (
# 1684 "FStar.TypeChecker.Tc.fst"
let ret = (
# 1685 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_897 = (let _137_895 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_894 = (let _137_893 = (let _137_892 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _137_892))
in (_137_893)::[])
in (_137_895)::_137_894))
in (let _137_896 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _137_897 _137_896)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (
# 1688 "FStar.TypeChecker.Tc.fst"
let bind_wp = (
# 1689 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1690 "FStar.TypeChecker.Tc.fst"
let _58_2320 = (get_effect_signature ())
in (match (_58_2320) with
| (b, wp_b) -> begin
(
# 1691 "FStar.TypeChecker.Tc.fst"
let a_wp_b = (let _137_901 = (let _137_899 = (let _137_898 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _137_898))
in (_137_899)::[])
in (let _137_900 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _137_901 _137_900)))
in (
# 1692 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = a_wp_b
in (
# 1693 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_914 = (let _137_912 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_911 = (let _137_910 = (FStar_Syntax_Syntax.mk_binder b)
in (let _137_909 = (let _137_908 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _137_907 = (let _137_906 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _137_905 = (let _137_904 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (let _137_903 = (let _137_902 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_137_902)::[])
in (_137_904)::_137_903))
in (_137_906)::_137_905))
in (_137_908)::_137_907))
in (_137_910)::_137_909))
in (_137_912)::_137_911))
in (let _137_913 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _137_914 _137_913)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k))))
end)))
in (
# 1699 "FStar.TypeChecker.Tc.fst"
let bind_wlp = (
# 1700 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1701 "FStar.TypeChecker.Tc.fst"
let _58_2328 = (get_effect_signature ())
in (match (_58_2328) with
| (b, wlp_b) -> begin
(
# 1702 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = (let _137_918 = (let _137_916 = (let _137_915 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _137_915))
in (_137_916)::[])
in (let _137_917 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _137_918 _137_917)))
in (
# 1703 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_927 = (let _137_925 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_924 = (let _137_923 = (FStar_Syntax_Syntax.mk_binder b)
in (let _137_922 = (let _137_921 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _137_920 = (let _137_919 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_137_919)::[])
in (_137_921)::_137_920))
in (_137_923)::_137_922))
in (_137_925)::_137_924))
in (let _137_926 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _137_927 _137_926)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wlp expected_k)))
end)))
in (
# 1709 "FStar.TypeChecker.Tc.fst"
let if_then_else = (
# 1710 "FStar.TypeChecker.Tc.fst"
let p = (let _137_929 = (let _137_928 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _137_928 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _137_929))
in (
# 1711 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_938 = (let _137_936 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_935 = (let _137_934 = (FStar_Syntax_Syntax.mk_binder p)
in (let _137_933 = (let _137_932 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _137_931 = (let _137_930 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_137_930)::[])
in (_137_932)::_137_931))
in (_137_934)::_137_933))
in (_137_936)::_137_935))
in (let _137_937 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _137_938 _137_937)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (
# 1717 "FStar.TypeChecker.Tc.fst"
let ite_wp = (
# 1718 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1719 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_945 = (let _137_943 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_942 = (let _137_941 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _137_940 = (let _137_939 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_137_939)::[])
in (_137_941)::_137_940))
in (_137_943)::_137_942))
in (let _137_944 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _137_945 _137_944)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k)))
in (
# 1725 "FStar.TypeChecker.Tc.fst"
let ite_wlp = (
# 1726 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1727 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_950 = (let _137_948 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_947 = (let _137_946 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (_137_946)::[])
in (_137_948)::_137_947))
in (let _137_949 = (FStar_Syntax_Syntax.mk_Total wlp_a)
in (FStar_Syntax_Util.arrow _137_950 _137_949)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wlp expected_k)))
in (
# 1732 "FStar.TypeChecker.Tc.fst"
let wp_binop = (
# 1733 "FStar.TypeChecker.Tc.fst"
let bin_op = (
# 1734 "FStar.TypeChecker.Tc.fst"
let _58_2343 = (FStar_Syntax_Util.type_u ())
in (match (_58_2343) with
| (t1, u1) -> begin
(
# 1735 "FStar.TypeChecker.Tc.fst"
let _58_2346 = (FStar_Syntax_Util.type_u ())
in (match (_58_2346) with
| (t2, u2) -> begin
(
# 1736 "FStar.TypeChecker.Tc.fst"
let t = (let _137_951 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_max ((u1)::(u2)::[]))) None _137_951))
in (let _137_956 = (let _137_954 = (FStar_Syntax_Syntax.null_binder t1)
in (let _137_953 = (let _137_952 = (FStar_Syntax_Syntax.null_binder t2)
in (_137_952)::[])
in (_137_954)::_137_953))
in (let _137_955 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _137_956 _137_955))))
end))
end))
in (
# 1738 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_965 = (let _137_963 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_962 = (let _137_961 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _137_960 = (let _137_959 = (FStar_Syntax_Syntax.null_binder bin_op)
in (let _137_958 = (let _137_957 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_137_957)::[])
in (_137_959)::_137_958))
in (_137_961)::_137_960))
in (_137_963)::_137_962))
in (let _137_964 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _137_965 _137_964)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_binop expected_k)))
in (
# 1745 "FStar.TypeChecker.Tc.fst"
let wp_as_type = (
# 1746 "FStar.TypeChecker.Tc.fst"
let _58_2354 = (FStar_Syntax_Util.type_u ())
in (match (_58_2354) with
| (t, _58_2353) -> begin
(
# 1747 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_970 = (let _137_968 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_967 = (let _137_966 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_137_966)::[])
in (_137_968)::_137_967))
in (let _137_969 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _137_970 _137_969)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (
# 1752 "FStar.TypeChecker.Tc.fst"
let close_wp = (
# 1753 "FStar.TypeChecker.Tc.fst"
let b = (let _137_972 = (let _137_971 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _137_971 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _137_972))
in (
# 1754 "FStar.TypeChecker.Tc.fst"
let b_wp_a = (let _137_976 = (let _137_974 = (let _137_973 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _137_973))
in (_137_974)::[])
in (let _137_975 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _137_976 _137_975)))
in (
# 1755 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_983 = (let _137_981 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_980 = (let _137_979 = (FStar_Syntax_Syntax.mk_binder b)
in (let _137_978 = (let _137_977 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_137_977)::[])
in (_137_979)::_137_978))
in (_137_981)::_137_980))
in (let _137_982 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _137_983 _137_982)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (
# 1759 "FStar.TypeChecker.Tc.fst"
let assert_p = (
# 1760 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_992 = (let _137_990 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_989 = (let _137_988 = (let _137_985 = (let _137_984 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _137_984 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _137_985))
in (let _137_987 = (let _137_986 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_137_986)::[])
in (_137_988)::_137_987))
in (_137_990)::_137_989))
in (let _137_991 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _137_992 _137_991)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (
# 1766 "FStar.TypeChecker.Tc.fst"
let assume_p = (
# 1767 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_1001 = (let _137_999 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_998 = (let _137_997 = (let _137_994 = (let _137_993 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _137_993 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _137_994))
in (let _137_996 = (let _137_995 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_137_995)::[])
in (_137_997)::_137_996))
in (_137_999)::_137_998))
in (let _137_1000 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _137_1001 _137_1000)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (
# 1773 "FStar.TypeChecker.Tc.fst"
let null_wp = (
# 1774 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_1004 = (let _137_1002 = (FStar_Syntax_Syntax.mk_binder a)
in (_137_1002)::[])
in (let _137_1003 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _137_1004 _137_1003)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (
# 1778 "FStar.TypeChecker.Tc.fst"
let trivial_wp = (
# 1779 "FStar.TypeChecker.Tc.fst"
let _58_2370 = (FStar_Syntax_Util.type_u ())
in (match (_58_2370) with
| (t, _58_2369) -> begin
(
# 1780 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_1009 = (let _137_1007 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_1006 = (let _137_1005 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_137_1005)::[])
in (_137_1007)::_137_1006))
in (let _137_1008 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _137_1009 _137_1008)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (
# 1786 "FStar.TypeChecker.Tc.fst"
let t = (let _137_1010 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _137_1010))
in (
# 1787 "FStar.TypeChecker.Tc.fst"
let _58_2376 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_58_2376) with
| (univs, t) -> begin
(
# 1788 "FStar.TypeChecker.Tc.fst"
let _58_2392 = (match ((let _137_1012 = (let _137_1011 = (FStar_Syntax_Subst.compress t)
in _137_1011.FStar_Syntax_Syntax.n)
in (binders, _137_1012))) with
| ([], _58_2379) -> begin
([], t)
end
| (_58_2382, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _58_2389 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_58_2392) with
| (binders, signature) -> begin
(
# 1792 "FStar.TypeChecker.Tc.fst"
let close = (fun ts -> (let _137_1015 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _137_1015)))
in (
# 1793 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1793 "FStar.TypeChecker.Tc.fst"
let _58_2395 = ed
in (let _137_1028 = (close ret)
in (let _137_1027 = (close bind_wp)
in (let _137_1026 = (close bind_wlp)
in (let _137_1025 = (close if_then_else)
in (let _137_1024 = (close ite_wp)
in (let _137_1023 = (close ite_wlp)
in (let _137_1022 = (close wp_binop)
in (let _137_1021 = (close wp_as_type)
in (let _137_1020 = (close close_wp)
in (let _137_1019 = (close assert_p)
in (let _137_1018 = (close assume_p)
in (let _137_1017 = (close null_wp)
in (let _137_1016 = (close trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _58_2395.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2395.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _137_1028; FStar_Syntax_Syntax.bind_wp = _137_1027; FStar_Syntax_Syntax.bind_wlp = _137_1026; FStar_Syntax_Syntax.if_then_else = _137_1025; FStar_Syntax_Syntax.ite_wp = _137_1024; FStar_Syntax_Syntax.ite_wlp = _137_1023; FStar_Syntax_Syntax.wp_binop = _137_1022; FStar_Syntax_Syntax.wp_as_type = _137_1021; FStar_Syntax_Syntax.close_wp = _137_1020; FStar_Syntax_Syntax.assert_p = _137_1019; FStar_Syntax_Syntax.assume_p = _137_1018; FStar_Syntax_Syntax.null_wp = _137_1017; FStar_Syntax_Syntax.trivial = _137_1016}))))))))))))))
in (
# 1811 "FStar.TypeChecker.Tc.fst"
let _58_2398 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_1029 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _137_1029))
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

# 1815 "FStar.TypeChecker.Tc.fst"
let tc_lex_t = (fun env ses quals lids -> (
# 1822 "FStar.TypeChecker.Tc.fst"
let _58_2404 = ()
in (
# 1823 "FStar.TypeChecker.Tc.fst"
let _58_2412 = ()
in (match (ses) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _58_2441, _58_2443, [], r)::FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _58_2432, r1)::FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _58_2421, r2)::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(
# 1838 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (
# 1839 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (
# 1840 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (
# 1841 "FStar.TypeChecker.Tc.fst"
let tc = FStar_Syntax_Syntax.Sig_inductive_typ ((lex_t, (u)::[], [], t, [], (FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[], [], r))
in (
# 1843 "FStar.TypeChecker.Tc.fst"
let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (
# 1844 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (let _137_1037 = (let _137_1036 = (let _137_1035 = (let _137_1034 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _137_1034 FStar_Syntax_Syntax.Delta_constant None))
in (_137_1035, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_137_1036))
in (FStar_Syntax_Syntax.mk _137_1037 None r1))
in (
# 1845 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (
# 1846 "FStar.TypeChecker.Tc.fst"
let dc_lextop = FStar_Syntax_Syntax.Sig_datacon ((lex_top, (utop)::[], lex_top_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r1))
in (
# 1848 "FStar.TypeChecker.Tc.fst"
let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1849 "FStar.TypeChecker.Tc.fst"
let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1850 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (
# 1851 "FStar.TypeChecker.Tc.fst"
let a = (let _137_1038 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _137_1038))
in (
# 1852 "FStar.TypeChecker.Tc.fst"
let hd = (let _137_1039 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _137_1039))
in (
# 1853 "FStar.TypeChecker.Tc.fst"
let tl = (let _137_1044 = (let _137_1043 = (let _137_1042 = (let _137_1041 = (let _137_1040 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _137_1040 FStar_Syntax_Syntax.Delta_constant None))
in (_137_1041, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_137_1042))
in (FStar_Syntax_Syntax.mk _137_1043 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _137_1044))
in (
# 1854 "FStar.TypeChecker.Tc.fst"
let res = (let _137_1048 = (let _137_1047 = (let _137_1046 = (let _137_1045 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _137_1045 FStar_Syntax_Syntax.Delta_constant None))
in (_137_1046, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_137_1047))
in (FStar_Syntax_Syntax.mk _137_1048 None r2))
in (let _137_1049 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _137_1049))))))
in (
# 1856 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (
# 1857 "FStar.TypeChecker.Tc.fst"
let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _137_1051 = (let _137_1050 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _137_1050))
in FStar_Syntax_Syntax.Sig_bundle (_137_1051)))))))))))))))
end
| _58_2467 -> begin
(let _137_1053 = (let _137_1052 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _137_1052))
in (FStar_All.failwith _137_1053))
end))))

# 1863 "FStar.TypeChecker.Tc.fst"
let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (
# 1926 "FStar.TypeChecker.Tc.fst"
let warn_positivity = (fun l r -> (let _137_1067 = (let _137_1066 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _137_1066))
in (FStar_TypeChecker_Errors.diag r _137_1067)))
in (
# 1928 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1931 "FStar.TypeChecker.Tc.fst"
let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(
# 1936 "FStar.TypeChecker.Tc.fst"
let _58_2489 = ()
in (
# 1937 "FStar.TypeChecker.Tc.fst"
let _58_2491 = (warn_positivity tc r)
in (
# 1938 "FStar.TypeChecker.Tc.fst"
let _58_2495 = (FStar_Syntax_Subst.open_term tps k)
in (match (_58_2495) with
| (tps, k) -> begin
(
# 1939 "FStar.TypeChecker.Tc.fst"
let _58_2499 = (tc_tparams env tps)
in (match (_58_2499) with
| (tps, env_tps, us) -> begin
(
# 1940 "FStar.TypeChecker.Tc.fst"
let _58_2502 = (FStar_Syntax_Util.arrow_formals k)
in (match (_58_2502) with
| (indices, t) -> begin
(
# 1941 "FStar.TypeChecker.Tc.fst"
let _58_2506 = (tc_tparams env_tps indices)
in (match (_58_2506) with
| (indices, env', us') -> begin
(
# 1942 "FStar.TypeChecker.Tc.fst"
let _58_2510 = (tc_trivial_guard env' t)
in (match (_58_2510) with
| (t, _58_2509) -> begin
(
# 1943 "FStar.TypeChecker.Tc.fst"
let k = (let _137_1072 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _137_1072))
in (
# 1944 "FStar.TypeChecker.Tc.fst"
let _58_2514 = (FStar_Syntax_Util.type_u ())
in (match (_58_2514) with
| (t_type, u) -> begin
(
# 1945 "FStar.TypeChecker.Tc.fst"
let _58_2515 = (let _137_1073 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _137_1073))
in (
# 1947 "FStar.TypeChecker.Tc.fst"
let t_tc = (let _137_1074 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _137_1074))
in (
# 1948 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 1949 "FStar.TypeChecker.Tc.fst"
let k = (FStar_Syntax_Subst.close tps k)
in (
# 1950 "FStar.TypeChecker.Tc.fst"
let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _137_1075 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) ([], t_tc))
in (_137_1075, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u)))))))
end)))
end))
end))
end))
end))
end))))
end
| _58_2522 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1957 "FStar.TypeChecker.Tc.fst"
let positive_if_pure = (fun _58_2524 l -> ())
in (
# 1960 "FStar.TypeChecker.Tc.fst"
let tc_data = (fun env tcs _58_6 -> (match (_58_6) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(
# 1962 "FStar.TypeChecker.Tc.fst"
let _58_2541 = ()
in (
# 1964 "FStar.TypeChecker.Tc.fst"
let _58_2576 = (
# 1965 "FStar.TypeChecker.Tc.fst"
let tps_u_opt = (FStar_Util.find_map tcs (fun _58_2545 -> (match (_58_2545) with
| (se, u_tc) -> begin
if (let _137_1088 = (let _137_1087 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _137_1087))
in (FStar_Ident.lid_equals tc_lid _137_1088)) then begin
(
# 1967 "FStar.TypeChecker.Tc.fst"
let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_2547, _58_2549, tps, _58_2552, _58_2554, _58_2556, _58_2558, _58_2560) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _58_2566 -> (match (_58_2566) with
| (x, _58_2565) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _58_2568 -> begin
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
in (match (_58_2576) with
| (tps, u_tc) -> begin
(
# 1980 "FStar.TypeChecker.Tc.fst"
let _58_2596 = (match ((let _137_1090 = (FStar_Syntax_Subst.compress t)
in _137_1090.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(
# 1985 "FStar.TypeChecker.Tc.fst"
let _58_2584 = (FStar_Util.first_N ntps bs)
in (match (_58_2584) with
| (_58_2582, bs') -> begin
(
# 1986 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (
# 1987 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _58_2590 -> (match (_58_2590) with
| (x, _58_2589) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _137_1093 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _137_1093))))
end))
end
| _58_2593 -> begin
([], t)
end)
in (match (_58_2596) with
| (arguments, result) -> begin
(
# 1991 "FStar.TypeChecker.Tc.fst"
let _58_2597 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_1096 = (FStar_Syntax_Print.lid_to_string c)
in (let _137_1095 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _137_1094 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _137_1096 _137_1095 _137_1094))))
end else begin
()
end
in (
# 1997 "FStar.TypeChecker.Tc.fst"
let _58_2602 = (tc_tparams env arguments)
in (match (_58_2602) with
| (arguments, env', us) -> begin
(
# 1998 "FStar.TypeChecker.Tc.fst"
let _58_2606 = (tc_trivial_guard env' result)
in (match (_58_2606) with
| (result, _58_2605) -> begin
(
# 1999 "FStar.TypeChecker.Tc.fst"
let _58_2610 = (FStar_Syntax_Util.head_and_args result)
in (match (_58_2610) with
| (head, _58_2609) -> begin
(
# 2000 "FStar.TypeChecker.Tc.fst"
let _58_2615 = (match ((let _137_1097 = (FStar_Syntax_Subst.compress head)
in _137_1097.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _58_2614 -> begin
(let _137_1101 = (let _137_1100 = (let _137_1099 = (let _137_1098 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _137_1098))
in (_137_1099, r))
in FStar_Syntax_Syntax.Error (_137_1100))
in (Prims.raise _137_1101))
end)
in (
# 2003 "FStar.TypeChecker.Tc.fst"
let g = (FStar_List.fold_left2 (fun g _58_2621 u_x -> (match (_58_2621) with
| (x, _58_2620) -> begin
(
# 2004 "FStar.TypeChecker.Tc.fst"
let _58_2623 = ()
in (let _137_1105 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _137_1105)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (
# 2010 "FStar.TypeChecker.Tc.fst"
let t = (let _137_1109 = (let _137_1107 = (FStar_All.pipe_right tps (FStar_List.map (fun _58_2629 -> (match (_58_2629) with
| (x, _58_2628) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _137_1107 arguments))
in (let _137_1108 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _137_1109 _137_1108)))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _58_2632 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 2018 "FStar.TypeChecker.Tc.fst"
let generalize_and_inst_within = (fun env g tcs datas -> (
# 2019 "FStar.TypeChecker.Tc.fst"
let _58_2638 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2020 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _58_7 -> (match (_58_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_2642, _58_2644, tps, k, _58_2648, _58_2650, _58_2652, _58_2654) -> begin
(let _137_1120 = (let _137_1119 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _137_1119))
in (FStar_Syntax_Syntax.null_binder _137_1120))
end
| _58_2658 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2023 "FStar.TypeChecker.Tc.fst"
let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _58_8 -> (match (_58_8) with
| FStar_Syntax_Syntax.Sig_datacon (_58_2662, _58_2664, t, _58_2667, _58_2669, _58_2671, _58_2673, _58_2675) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _58_2679 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2026 "FStar.TypeChecker.Tc.fst"
let t = (let _137_1122 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _137_1122))
in (
# 2027 "FStar.TypeChecker.Tc.fst"
let _58_2682 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_1123 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _137_1123))
end else begin
()
end
in (
# 2028 "FStar.TypeChecker.Tc.fst"
let _58_2686 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_58_2686) with
| (uvs, t) -> begin
(
# 2029 "FStar.TypeChecker.Tc.fst"
let _58_2688 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_1127 = (let _137_1125 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _137_1125 (FStar_String.concat ", ")))
in (let _137_1126 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _137_1127 _137_1126)))
end else begin
()
end
in (
# 2032 "FStar.TypeChecker.Tc.fst"
let _58_2692 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_58_2692) with
| (uvs, t) -> begin
(
# 2033 "FStar.TypeChecker.Tc.fst"
let _58_2696 = (FStar_Syntax_Util.arrow_formals t)
in (match (_58_2696) with
| (args, _58_2695) -> begin
(
# 2034 "FStar.TypeChecker.Tc.fst"
let _58_2699 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_58_2699) with
| (tc_types, data_types) -> begin
(
# 2035 "FStar.TypeChecker.Tc.fst"
let tcs = (FStar_List.map2 (fun _58_2703 se -> (match (_58_2703) with
| (x, _58_2702) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _58_2707, tps, _58_2710, mutuals, datas, quals, r) -> begin
(
# 2037 "FStar.TypeChecker.Tc.fst"
let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (
# 2038 "FStar.TypeChecker.Tc.fst"
let _58_2733 = (match ((let _137_1130 = (FStar_Syntax_Subst.compress ty)
in _137_1130.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 2040 "FStar.TypeChecker.Tc.fst"
let _58_2724 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_58_2724) with
| (tps, rest) -> begin
(
# 2041 "FStar.TypeChecker.Tc.fst"
let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _58_2727 -> begin
(let _137_1131 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _137_1131 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _58_2730 -> begin
([], ty)
end)
in (match (_58_2733) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _58_2735 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (
# 2051 "FStar.TypeChecker.Tc.fst"
let datas = (match (uvs) with
| [] -> begin
datas
end
| _58_2739 -> begin
(
# 2054 "FStar.TypeChecker.Tc.fst"
let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _137_1132 -> FStar_Syntax_Syntax.U_name (_137_1132))))
in (
# 2055 "FStar.TypeChecker.Tc.fst"
let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _58_9 -> (match (_58_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _58_2744, _58_2746, _58_2748, _58_2750, _58_2752, _58_2754, _58_2756) -> begin
(tc, uvs_universes)
end
| _58_2760 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _58_2765 d -> (match (_58_2765) with
| (t, _58_2764) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _58_2769, _58_2771, tc, ntps, quals, mutuals, r) -> begin
(
# 2059 "FStar.TypeChecker.Tc.fst"
let ty = (let _137_1136 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _137_1136 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _58_2781 -> begin
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
# 2065 "FStar.TypeChecker.Tc.fst"
let _58_2791 = (FStar_All.pipe_right ses (FStar_List.partition (fun _58_10 -> (match (_58_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_2785) -> begin
true
end
| _58_2788 -> begin
false
end))))
in (match (_58_2791) with
| (tys, datas) -> begin
(
# 2067 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2070 "FStar.TypeChecker.Tc.fst"
let _58_2808 = (FStar_List.fold_right (fun tc _58_2797 -> (match (_58_2797) with
| (env, all_tcs, g) -> begin
(
# 2071 "FStar.TypeChecker.Tc.fst"
let _58_2801 = (tc_tycon env tc)
in (match (_58_2801) with
| (env, tc, tc_u) -> begin
(
# 2072 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (
# 2073 "FStar.TypeChecker.Tc.fst"
let _58_2803 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_1140 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _137_1140))
end else begin
()
end
in (let _137_1141 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _137_1141))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_58_2808) with
| (env, tcs, g) -> begin
(
# 2080 "FStar.TypeChecker.Tc.fst"
let _58_2818 = (FStar_List.fold_right (fun se _58_2812 -> (match (_58_2812) with
| (datas, g) -> begin
(
# 2081 "FStar.TypeChecker.Tc.fst"
let _58_2815 = (tc_data env tcs se)
in (match (_58_2815) with
| (data, g') -> begin
(let _137_1144 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _137_1144))
end))
end)) datas ([], g))
in (match (_58_2818) with
| (datas, g) -> begin
(
# 2086 "FStar.TypeChecker.Tc.fst"
let _58_2821 = (let _137_1145 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _137_1145 datas))
in (match (_58_2821) with
| (tcs, datas) -> begin
(let _137_1147 = (let _137_1146 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _137_1146))
in FStar_Syntax_Syntax.Sig_bundle (_137_1147))
end))
end))
end)))
end)))))))))

# 2089 "FStar.TypeChecker.Tc.fst"
let rec tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.env) = (fun env se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(
# 2102 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2103 "FStar.TypeChecker.Tc.fst"
let se = (tc_lex_t env ses quals lids)
in (let _137_1152 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _137_1152))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(
# 2107 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2108 "FStar.TypeChecker.Tc.fst"
let se = (tc_inductive env ses quals lids)
in (let _137_1153 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _137_1153))))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(
# 2112 "FStar.TypeChecker.Tc.fst"
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
# 2118 "FStar.TypeChecker.Tc.fst"
let _58_2859 = (set_options FStar_Options.Set o)
in (se, env))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(
# 2121 "FStar.TypeChecker.Tc.fst"
let _58_2863 = (let _137_1158 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _137_1158 Prims.ignore))
in (
# 2122 "FStar.TypeChecker.Tc.fst"
let _58_2868 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (
# 2125 "FStar.TypeChecker.Tc.fst"
let _58_2870 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (se, env))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(
# 2130 "FStar.TypeChecker.Tc.fst"
let ne = (tc_eff_decl env ne)
in (
# 2131 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (
# 2132 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(
# 2136 "FStar.TypeChecker.Tc.fst"
let _58_2885 = (let _137_1159 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _137_1159))
in (match (_58_2885) with
| (a, wp_a_src) -> begin
(
# 2137 "FStar.TypeChecker.Tc.fst"
let _58_2888 = (let _137_1160 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _137_1160))
in (match (_58_2888) with
| (b, wp_b_tgt) -> begin
(
# 2138 "FStar.TypeChecker.Tc.fst"
let wp_a_tgt = (let _137_1164 = (let _137_1163 = (let _137_1162 = (let _137_1161 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _137_1161))
in FStar_Syntax_Syntax.NT (_137_1162))
in (_137_1163)::[])
in (FStar_Syntax_Subst.subst _137_1164 wp_b_tgt))
in (
# 2139 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _137_1169 = (let _137_1167 = (FStar_Syntax_Syntax.mk_binder a)
in (let _137_1166 = (let _137_1165 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_137_1165)::[])
in (_137_1167)::_137_1166))
in (let _137_1168 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _137_1169 _137_1168)))
in (
# 2140 "FStar.TypeChecker.Tc.fst"
let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (
# 2141 "FStar.TypeChecker.Tc.fst"
let sub = (
# 2141 "FStar.TypeChecker.Tc.fst"
let _58_2892 = sub
in {FStar_Syntax_Syntax.source = _58_2892.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _58_2892.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
in (
# 2142 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect ((sub, r))
in (
# 2143 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(
# 2147 "FStar.TypeChecker.Tc.fst"
let _58_2905 = ()
in (
# 2148 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2149 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2150 "FStar.TypeChecker.Tc.fst"
let _58_2911 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_58_2911) with
| (tps, c) -> begin
(
# 2151 "FStar.TypeChecker.Tc.fst"
let _58_2915 = (tc_tparams env tps)
in (match (_58_2915) with
| (tps, env, us) -> begin
(
# 2152 "FStar.TypeChecker.Tc.fst"
let _58_2919 = (tc_comp env c)
in (match (_58_2919) with
| (c, u, g) -> begin
(
# 2153 "FStar.TypeChecker.Tc.fst"
let _58_2920 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2154 "FStar.TypeChecker.Tc.fst"
let tags = (FStar_All.pipe_right tags (FStar_List.map (fun _58_11 -> (match (_58_11) with
| FStar_Syntax_Syntax.DefaultEffect (None) -> begin
(
# 2156 "FStar.TypeChecker.Tc.fst"
let c' = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let _137_1172 = (FStar_All.pipe_right c'.FStar_Syntax_Syntax.effect_name (fun _137_1171 -> Some (_137_1171)))
in FStar_Syntax_Syntax.DefaultEffect (_137_1172)))
end
| t -> begin
t
end))))
in (
# 2159 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 2160 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.close_comp tps c)
in (
# 2161 "FStar.TypeChecker.Tc.fst"
let _58_2932 = (let _137_1173 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _137_1173))
in (match (_58_2932) with
| (uvs, t) -> begin
(
# 2162 "FStar.TypeChecker.Tc.fst"
let _58_2951 = (match ((let _137_1175 = (let _137_1174 = (FStar_Syntax_Subst.compress t)
in _137_1174.FStar_Syntax_Syntax.n)
in (tps, _137_1175))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_58_2935, c)) -> begin
([], c)
end
| (_58_2941, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _58_2948 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_58_2951) with
| (tps, c) -> begin
(
# 2166 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_effect_abbrev ((lid, uvs, tps, c, tags, r))
in (
# 2167 "FStar.TypeChecker.Tc.fst"
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
# 2171 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2172 "FStar.TypeChecker.Tc.fst"
let _58_2962 = ()
in (
# 2173 "FStar.TypeChecker.Tc.fst"
let k = (let _137_1176 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _137_1176))
in (
# 2174 "FStar.TypeChecker.Tc.fst"
let _58_2967 = (check_and_gen env t k)
in (match (_58_2967) with
| (uvs, t) -> begin
(
# 2175 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (
# 2176 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(
# 2180 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2181 "FStar.TypeChecker.Tc.fst"
let _58_2980 = (FStar_Syntax_Util.type_u ())
in (match (_58_2980) with
| (k, _58_2979) -> begin
(
# 2182 "FStar.TypeChecker.Tc.fst"
let phi = (let _137_1177 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _137_1177 (norm env)))
in (
# 2183 "FStar.TypeChecker.Tc.fst"
let _58_2982 = (FStar_TypeChecker_Util.check_uvars r phi)
in (
# 2184 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))
in (
# 2185 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(
# 2189 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2190 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (
# 2191 "FStar.TypeChecker.Tc.fst"
let _58_2995 = (tc_term env e)
in (match (_58_2995) with
| (e, c, g1) -> begin
(
# 2192 "FStar.TypeChecker.Tc.fst"
let _58_3000 = (let _137_1181 = (let _137_1178 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_137_1178))
in (let _137_1180 = (let _137_1179 = (c.FStar_Syntax_Syntax.comp ())
in (e, _137_1179))
in (check_expected_effect env _137_1181 _137_1180)))
in (match (_58_3000) with
| (e, _58_2998, g) -> begin
(
# 2193 "FStar.TypeChecker.Tc.fst"
let _58_3001 = (let _137_1182 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _137_1182))
in (
# 2194 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, r))
in (
# 2195 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(
# 2199 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2200 "FStar.TypeChecker.Tc.fst"
let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
if (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q')) then begin
Some (q)
end else begin
(let _137_1194 = (let _137_1193 = (let _137_1192 = (let _137_1191 = (FStar_Syntax_Print.lid_to_string l)
in (let _137_1190 = (FStar_Syntax_Print.quals_to_string q)
in (let _137_1189 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _137_1191 _137_1190 _137_1189))))
in (_137_1192, r))
in FStar_Syntax_Syntax.Error (_137_1193))
in (Prims.raise _137_1194))
end
end))
in (
# 2214 "FStar.TypeChecker.Tc.fst"
let _58_3045 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _58_3022 lb -> (match (_58_3022) with
| (gen, lbs, quals_opt) -> begin
(
# 2215 "FStar.TypeChecker.Tc.fst"
let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2216 "FStar.TypeChecker.Tc.fst"
let _58_3041 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(
# 2220 "FStar.TypeChecker.Tc.fst"
let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (
# 2221 "FStar.TypeChecker.Tc.fst"
let _58_3036 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _58_3035 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _137_1197 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _137_1197, quals_opt))))
end)
in (match (_58_3041) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_58_3045) with
| (should_generalize, lbs', quals_opt) -> begin
(
# 2230 "FStar.TypeChecker.Tc.fst"
let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _58_12 -> (match (_58_12) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _58_3054 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (
# 2237 "FStar.TypeChecker.Tc.fst"
let lbs' = (FStar_List.rev lbs')
in (
# 2240 "FStar.TypeChecker.Tc.fst"
let e = (let _137_1201 = (let _137_1200 = (let _137_1199 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _137_1199))
in FStar_Syntax_Syntax.Tm_let (_137_1200))
in (FStar_Syntax_Syntax.mk _137_1201 None r))
in (
# 2243 "FStar.TypeChecker.Tc.fst"
let _58_3088 = (match ((tc_maybe_toplevel_term (
# 2243 "FStar.TypeChecker.Tc.fst"
let _58_3058 = env
in {FStar_TypeChecker_Env.solver = _58_3058.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_3058.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_3058.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_3058.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_3058.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_3058.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_3058.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_3058.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_3058.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_3058.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_3058.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _58_3058.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _58_3058.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_3058.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_3058.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_3058.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_3058.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_3058.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_3058.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_3058.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _58_3065; FStar_Syntax_Syntax.pos = _58_3063; FStar_Syntax_Syntax.vars = _58_3061}, _58_3072, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(
# 2246 "FStar.TypeChecker.Tc.fst"
let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_58_3076, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _58_3082 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _58_3085 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_58_3088) with
| (se, lbs) -> begin
(
# 2253 "FStar.TypeChecker.Tc.fst"
let _58_3094 = if (log env) then begin
(let _137_1209 = (let _137_1208 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 2255 "FStar.TypeChecker.Tc.fst"
let should_log = (match ((let _137_1205 = (let _137_1204 = (let _137_1203 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _137_1203.FStar_Syntax_Syntax.fv_name)
in _137_1204.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _137_1205))) with
| None -> begin
true
end
| _58_3092 -> begin
false
end)
in if should_log then begin
(let _137_1207 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _137_1206 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _137_1207 _137_1206)))
end else begin
""
end))))
in (FStar_All.pipe_right _137_1208 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _137_1209))
end else begin
()
end
in (
# 2262 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end))))
end))

# 2266 "FStar.TypeChecker.Tc.fst"
let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (
# 2290 "FStar.TypeChecker.Tc.fst"
let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _58_13 -> (match (_58_13) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _58_3104 -> begin
false
end)))))
in (
# 2291 "FStar.TypeChecker.Tc.fst"
let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _58_3114 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_58_3116) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _58_3127, _58_3129) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _58_3135 -> (match (_58_3135) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _58_3141, _58_3143, quals, r) -> begin
(
# 2305 "FStar.TypeChecker.Tc.fst"
let dec = (let _137_1225 = (let _137_1224 = (let _137_1223 = (let _137_1222 = (let _137_1221 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _137_1221))
in FStar_Syntax_Syntax.Tm_arrow (_137_1222))
in (FStar_Syntax_Syntax.mk _137_1223 None r))
in (l, us, _137_1224, (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_137_1225))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _58_3153, _58_3155, _58_3157, _58_3159, r) -> begin
(
# 2308 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _58_3165 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_58_3167, _58_3169, quals, _58_3172) -> begin
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
| _58_3191 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_58_3193) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _58_3209, _58_3211, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(
# 2338 "FStar.TypeChecker.Tc.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2339 "FStar.TypeChecker.Tc.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))) then begin
([], hidden)
end else begin
(
# 2342 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::[], (FStar_Ident.range_of_lid lid)))
in ((dec)::[], (lid)::hidden))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (is_abstract quals) then begin
(let _137_1232 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _137_1231 = (let _137_1230 = (let _137_1229 = (let _137_1228 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _137_1228.FStar_Syntax_Syntax.fv_name)
in _137_1229.FStar_Syntax_Syntax.v)
in (_137_1230, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_137_1231)))))
in (_137_1232, hidden))
end else begin
((se)::[], hidden)
end
end))))

# 2351 "FStar.TypeChecker.Tc.fst"
let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (
# 2352 "FStar.TypeChecker.Tc.fst"
let _58_3250 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _58_3231 se -> (match (_58_3231) with
| (ses, exports, env, hidden) -> begin
(
# 2354 "FStar.TypeChecker.Tc.fst"
let _58_3233 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _137_1239 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _137_1239))
end else begin
()
end
in (
# 2357 "FStar.TypeChecker.Tc.fst"
let _58_3237 = (tc_decl env se)
in (match (_58_3237) with
| (se, env) -> begin
(
# 2359 "FStar.TypeChecker.Tc.fst"
let _58_3238 = if ((FStar_ST.read FStar_Options.log_types) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _137_1240 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _137_1240))
end else begin
()
end
in (
# 2362 "FStar.TypeChecker.Tc.fst"
let _58_3240 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (
# 2364 "FStar.TypeChecker.Tc.fst"
let _58_3244 = (for_export hidden se)
in (match (_58_3244) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_58_3250) with
| (ses, exports, env, _58_3249) -> begin
(let _137_1241 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _137_1241, env))
end)))

# 2369 "FStar.TypeChecker.Tc.fst"
let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2370 "FStar.TypeChecker.Tc.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 2371 "FStar.TypeChecker.Tc.fst"
let msg = (Prims.strcat "Internals for " name)
in (
# 2372 "FStar.TypeChecker.Tc.fst"
let env = (
# 2372 "FStar.TypeChecker.Tc.fst"
let _58_3255 = env
in (let _137_1246 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _58_3255.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_3255.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_3255.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_3255.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_3255.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_3255.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_3255.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_3255.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_3255.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_3255.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_3255.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_3255.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_3255.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_3255.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_3255.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_3255.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _137_1246; FStar_TypeChecker_Env.default_effects = _58_3255.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_3255.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_3255.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_3255.FStar_TypeChecker_Env.use_bv_sorts}))
in (
# 2373 "FStar.TypeChecker.Tc.fst"
let _58_3258 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (
# 2374 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (
# 2375 "FStar.TypeChecker.Tc.fst"
let _58_3264 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_58_3264) with
| (ses, exports, env) -> begin
((
# 2376 "FStar.TypeChecker.Tc.fst"
let _58_3265 = modul
in {FStar_Syntax_Syntax.name = _58_3265.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _58_3265.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _58_3265.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))

# 2378 "FStar.TypeChecker.Tc.fst"
let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (
# 2379 "FStar.TypeChecker.Tc.fst"
let _58_3273 = (tc_decls env decls)
in (match (_58_3273) with
| (ses, exports, env) -> begin
(
# 2380 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2380 "FStar.TypeChecker.Tc.fst"
let _58_3274 = modul
in {FStar_Syntax_Syntax.name = _58_3274.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _58_3274.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _58_3274.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))

# 2383 "FStar.TypeChecker.Tc.fst"
let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (
# 2384 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2384 "FStar.TypeChecker.Tc.fst"
let _58_3280 = modul
in {FStar_Syntax_Syntax.name = _58_3280.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _58_3280.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (
# 2385 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.finish_module env modul)
in (
# 2386 "FStar.TypeChecker.Tc.fst"
let _58_3290 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(
# 2388 "FStar.TypeChecker.Tc.fst"
let _58_3284 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (
# 2389 "FStar.TypeChecker.Tc.fst"
let _58_3286 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (
# 2390 "FStar.TypeChecker.Tc.fst"
let _58_3288 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _137_1259 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _137_1259 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))

# 2395 "FStar.TypeChecker.Tc.fst"
let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2396 "FStar.TypeChecker.Tc.fst"
let _58_3297 = (tc_partial_modul env modul)
in (match (_58_3297) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

# 2399 "FStar.TypeChecker.Tc.fst"
let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 2400 "FStar.TypeChecker.Tc.fst"
let _58_3300 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _137_1268 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _137_1268))
end else begin
()
end
in (
# 2402 "FStar.TypeChecker.Tc.fst"
let env = (
# 2402 "FStar.TypeChecker.Tc.fst"
let _58_3302 = env
in {FStar_TypeChecker_Env.solver = _58_3302.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_3302.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_3302.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_3302.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_3302.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_3302.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_3302.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_3302.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_3302.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_3302.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_3302.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_3302.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_3302.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_3302.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_3302.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_3302.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_3302.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _58_3302.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _58_3302.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_3302.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_3302.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 2403 "FStar.TypeChecker.Tc.fst"
let _58_3318 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _58_3310) -> begin
(let _137_1273 = (let _137_1272 = (let _137_1271 = (FStar_TypeChecker_Env.get_range env)
in ((Prims.strcat "Implicit argument: " msg), _137_1271))
in FStar_Syntax_Syntax.Error (_137_1272))
in (Prims.raise _137_1273))
end
in (match (_58_3318) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(let _137_1278 = (let _137_1277 = (let _137_1276 = (let _137_1274 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _137_1274))
in (let _137_1275 = (FStar_TypeChecker_Env.get_range env)
in (_137_1276, _137_1275)))
in FStar_Syntax_Syntax.Error (_137_1277))
in (Prims.raise _137_1278))
end
end)))))

# 2410 "FStar.TypeChecker.Tc.fst"
let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (
# 2411 "FStar.TypeChecker.Tc.fst"
let _58_3321 = if ((let _137_1283 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _137_1283)) <> 0) then begin
(let _137_1284 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _137_1284))
end else begin
()
end
in (
# 2413 "FStar.TypeChecker.Tc.fst"
let _58_3325 = (tc_modul env m)
in (match (_58_3325) with
| (m, env) -> begin
(
# 2414 "FStar.TypeChecker.Tc.fst"
let _58_3326 = if (FStar_Options.should_dump m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _137_1285 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _137_1285))
end else begin
()
end
in (m, env))
end))))




