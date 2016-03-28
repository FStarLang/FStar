
open Prims
# 40 "FStar.TypeChecker.Tc.fst"
let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_ST.read FStar_Options.log_types) && (not ((let _149_3 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _149_3))))))

# 42 "FStar.TypeChecker.Tc.fst"
let rng : FStar_TypeChecker_Env.env  ->  FStar_Range.range = (fun env -> (FStar_TypeChecker_Env.get_range env))

# 43 "FStar.TypeChecker.Tc.fst"
let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (
# 44 "FStar.TypeChecker.Tc.fst"
let _64_18 = env
in {FStar_TypeChecker_Env.solver = _64_18.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_18.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_18.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_18.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_18.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_18.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_18.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_18.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_18.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _64_18.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_18.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _64_18.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _64_18.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _64_18.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _64_18.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _64_18.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_18.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_18.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_18.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_18.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_18.FStar_TypeChecker_Env.use_bv_sorts}))

# 44 "FStar.TypeChecker.Tc.fst"
let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (
# 45 "FStar.TypeChecker.Tc.fst"
let _64_21 = env
in {FStar_TypeChecker_Env.solver = _64_21.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_21.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_21.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_21.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_21.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_21.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_21.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_21.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_21.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _64_21.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_21.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _64_21.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _64_21.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _64_21.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _64_21.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _64_21.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_21.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_21.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_21.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_21.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_21.FStar_TypeChecker_Env.use_bv_sorts}))

# 45 "FStar.TypeChecker.Tc.fst"
let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (
# 48 "FStar.TypeChecker.Tc.fst"
let r = if (tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
v.FStar_Syntax_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos tl.FStar_Syntax_Syntax.pos)
end
in (let _149_17 = (let _149_16 = (FStar_Syntax_Syntax.as_arg v)
in (let _149_15 = (let _149_14 = (FStar_Syntax_Syntax.as_arg tl)
in (_149_14)::[])
in (_149_16)::_149_15))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _149_17 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))

# 50 "FStar.TypeChecker.Tc.fst"
let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _64_1 -> (match (_64_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _64_31 -> begin
false
end))

# 53 "FStar.TypeChecker.Tc.fst"
let steps : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Normalize.step Prims.list = (fun env -> if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::[]
end else begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]
end)

# 57 "FStar.TypeChecker.Tc.fst"
let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Beta)::[]) env t))

# 58 "FStar.TypeChecker.Tc.fst"
let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _149_30 = (steps env)
in (FStar_TypeChecker_Normalize.normalize _149_30 env t)))

# 59 "FStar.TypeChecker.Tc.fst"
let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _149_35 = (steps env)
in (FStar_TypeChecker_Normalize.normalize_comp _149_35 env c)))

# 60 "FStar.TypeChecker.Tc.fst"
let check_no_escape : FStar_Syntax_Syntax.term Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun head_opt env fvs kt -> (
# 62 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
()
end
| _64_48 -> begin
(
# 65 "FStar.TypeChecker.Tc.fst"
let fvs' = (let _149_48 = if try_norm then begin
(norm env t)
end else begin
t
end
in (FStar_Syntax_Free.names _149_48))
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
let fail = (fun _64_55 -> (match (()) with
| () -> begin
(
# 72 "FStar.TypeChecker.Tc.fst"
let msg = (match (head_opt) with
| None -> begin
(let _149_52 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _149_52))
end
| Some (head) -> begin
(let _149_54 = (FStar_Syntax_Print.bv_to_string x)
in (let _149_53 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _149_54 _149_53)))
end)
in (let _149_57 = (let _149_56 = (let _149_55 = (FStar_TypeChecker_Env.get_range env)
in (msg, _149_55))
in FStar_Syntax_Syntax.Error (_149_56))
in (Prims.raise _149_57)))
end))
in (
# 77 "FStar.TypeChecker.Tc.fst"
let s = (let _149_59 = (let _149_58 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _149_58))
in (FStar_TypeChecker_Util.new_uvar env _149_59))
in (match ((FStar_TypeChecker_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g)
end
| _64_64 -> begin
(fail ())
end)))
end
end))
end))
in (aux false kt)))

# 82 "FStar.TypeChecker.Tc.fst"
let maybe_push_binding : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder  ->  FStar_TypeChecker_Env.env = (fun env b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
env
end else begin
(
# 86 "FStar.TypeChecker.Tc.fst"
let _64_67 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_65 = (FStar_Syntax_Print.bv_to_string (Prims.fst b))
in (let _149_64 = (FStar_Syntax_Print.term_to_string (Prims.fst b).FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _149_65 _149_64)))
end else begin
()
end
in (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))
end)

# 88 "FStar.TypeChecker.Tc.fst"
let maybe_make_subst = (fun _64_2 -> (match (_64_2) with
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Syntax_Syntax.NT ((x, e)))::[]
end
| _64_76 -> begin
[]
end))

# 92 "FStar.TypeChecker.Tc.fst"
let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.subst_t = (fun s b v -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
s
end else begin
(FStar_Syntax_Syntax.NT (((Prims.fst b), v)))::s
end)

# 96 "FStar.TypeChecker.Tc.fst"
let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (
# 99 "FStar.TypeChecker.Tc.fst"
let _64_82 = lc
in {FStar_Syntax_Syntax.eff_name = _64_82.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _64_82.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _64_84 -> (match (()) with
| () -> begin
(let _149_78 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _149_78 t))
end))}))

# 99 "FStar.TypeChecker.Tc.fst"
let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (
# 102 "FStar.TypeChecker.Tc.fst"
let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _149_87 = if (not ((FStar_Syntax_Util.is_pure_or_ghost_function t))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _149_87))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (
# 107 "FStar.TypeChecker.Tc.fst"
let t = lc.FStar_Syntax_Syntax.res_typ
in (
# 108 "FStar.TypeChecker.Tc.fst"
let _64_116 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, guard)
end
| Some (t') -> begin
(
# 111 "FStar.TypeChecker.Tc.fst"
let _64_98 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_89 = (FStar_Syntax_Print.term_to_string t)
in (let _149_88 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _149_89 _149_88)))
end else begin
()
end
in (
# 113 "FStar.TypeChecker.Tc.fst"
let _64_102 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_64_102) with
| (e, lc) -> begin
(
# 114 "FStar.TypeChecker.Tc.fst"
let t = lc.FStar_Syntax_Syntax.res_typ
in (
# 115 "FStar.TypeChecker.Tc.fst"
let _64_106 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_64_106) with
| (e, g) -> begin
(
# 116 "FStar.TypeChecker.Tc.fst"
let _64_107 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_91 = (FStar_Syntax_Print.term_to_string t)
in (let _149_90 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _149_91 _149_90)))
end else begin
()
end
in (
# 118 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (
# 119 "FStar.TypeChecker.Tc.fst"
let _64_112 = (let _149_97 = (FStar_All.pipe_left (fun _149_96 -> Some (_149_96)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _149_97 env e lc g))
in (match (_64_112) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))))
end)))
end)))
end)
in (match (_64_116) with
| (e, lc, g) -> begin
(
# 121 "FStar.TypeChecker.Tc.fst"
let _64_117 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_98 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _149_98))
end else begin
()
end
in (e, lc, g))
end)))))

# 123 "FStar.TypeChecker.Tc.fst"
let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (t) -> begin
(
# 129 "FStar.TypeChecker.Tc.fst"
let _64_127 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_64_127) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))

# 130 "FStar.TypeChecker.Tc.fst"
let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _64_132 -> (match (_64_132) with
| (e, c) -> begin
(
# 133 "FStar.TypeChecker.Tc.fst"
let expected_c_opt = (match (copt) with
| Some (_64_134) -> begin
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
(let _149_111 = (norm_c env c)
in (e, _149_111, FStar_TypeChecker_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(
# 156 "FStar.TypeChecker.Tc.fst"
let _64_148 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_114 = (FStar_Syntax_Print.term_to_string e)
in (let _149_113 = (FStar_Syntax_Print.comp_to_string c)
in (let _149_112 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _149_114 _149_113 _149_112))))
end else begin
()
end
in (
# 159 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 160 "FStar.TypeChecker.Tc.fst"
let _64_151 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_117 = (FStar_Syntax_Print.term_to_string e)
in (let _149_116 = (FStar_Syntax_Print.comp_to_string c)
in (let _149_115 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _149_117 _149_116 _149_115))))
end else begin
()
end
in (
# 165 "FStar.TypeChecker.Tc.fst"
let _64_157 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_64_157) with
| (e, _64_155, g) -> begin
(
# 166 "FStar.TypeChecker.Tc.fst"
let g = (let _149_118 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _149_118 "could not prove post-condition" g))
in (
# 167 "FStar.TypeChecker.Tc.fst"
let _64_159 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_120 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _149_119 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _149_120 _149_119)))
end else begin
()
end
in (e, expected_c, g)))
end)))))
end))
end))

# 168 "FStar.TypeChecker.Tc.fst"
let no_logical_guard = (fun env _64_165 -> (match (_64_165) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
(te, kt, f)
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _149_126 = (let _149_125 = (let _149_124 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _149_123 = (FStar_TypeChecker_Env.get_range env)
in (_149_124, _149_123)))
in FStar_Syntax_Syntax.Error (_149_125))
in (Prims.raise _149_126))
end)
end))

# 173 "FStar.TypeChecker.Tc.fst"
let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _149_129 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _149_129))
end))

# 177 "FStar.TypeChecker.Tc.fst"
let with_implicits = (fun imps _64_177 -> (match (_64_177) with
| (e, l, g) -> begin
(e, l, (
# 179 "FStar.TypeChecker.Tc.fst"
let _64_178 = g
in {FStar_TypeChecker_Env.guard_f = _64_178.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _64_178.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _64_178.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (FStar_List.append imps g.FStar_TypeChecker_Env.implicits)}))
end))

# 179 "FStar.TypeChecker.Tc.fst"
let add_implicit : (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun u g -> (
# 180 "FStar.TypeChecker.Tc.fst"
let _64_182 = g
in {FStar_TypeChecker_Env.guard_f = _64_182.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _64_182.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _64_182.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (u)::g.FStar_TypeChecker_Env.implicits}))

# 180 "FStar.TypeChecker.Tc.fst"
let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _64_200; FStar_Syntax_Syntax.result_typ = _64_198; FStar_Syntax_Syntax.effect_args = _pre::_post::(pats, _64_192)::[]; FStar_Syntax_Syntax.flags = _64_189}) -> begin
(
# 189 "FStar.TypeChecker.Tc.fst"
let pat_vars = (FStar_Syntax_Free.names pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _64_207 -> (match (_64_207) with
| (b, _64_206) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _64_211) -> begin
(let _149_142 = (let _149_141 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _149_141))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _149_142))
end))
end
| _64_215 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end)

# 194 "FStar.TypeChecker.Tc.fst"
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
let _64_222 = env
in {FStar_TypeChecker_Env.solver = _64_222.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_222.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_222.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_222.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_222.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_222.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_222.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_222.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_222.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_222.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_222.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_222.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _64_222.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _64_222.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _64_222.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _64_222.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_222.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_222.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_222.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_222.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_222.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 206 "FStar.TypeChecker.Tc.fst"
let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (
# 208 "FStar.TypeChecker.Tc.fst"
let decreases_clause = (fun bs c -> (
# 210 "FStar.TypeChecker.Tc.fst"
let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _64_234 -> (match (_64_234) with
| (b, _64_233) -> begin
(
# 212 "FStar.TypeChecker.Tc.fst"
let t = (let _149_156 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _149_156))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _64_243 -> begin
(let _149_157 = (FStar_Syntax_Syntax.bv_to_name b)
in (_149_157)::[])
end))
end)))))
in (
# 217 "FStar.TypeChecker.Tc.fst"
let as_lex_list = (fun dec -> (
# 218 "FStar.TypeChecker.Tc.fst"
let _64_249 = (FStar_Syntax_Util.head_and_args dec)
in (match (_64_249) with
| (head, _64_248) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _64_253 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (
# 222 "FStar.TypeChecker.Tc.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _64_3 -> (match (_64_3) with
| FStar_Syntax_Syntax.DECREASES (_64_257) -> begin
true
end
| _64_260 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _64_265 -> begin
(
# 226 "FStar.TypeChecker.Tc.fst"
let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| x::[] -> begin
x
end
| _64_270 -> begin
(mk_lex_list xs)
end))
end)))))
in (
# 231 "FStar.TypeChecker.Tc.fst"
let previous_dec = (decreases_clause actuals expected_c)
in (
# 232 "FStar.TypeChecker.Tc.fst"
let guard_one_letrec = (fun _64_275 -> (match (_64_275) with
| (l, t) -> begin
(match ((let _149_163 = (FStar_Syntax_Subst.compress t)
in _149_163.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 236 "FStar.TypeChecker.Tc.fst"
let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _64_282 -> (match (_64_282) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _149_167 = (let _149_166 = (let _149_165 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_149_165))
in (FStar_Syntax_Syntax.new_bv _149_166 x.FStar_Syntax_Syntax.sort))
in (_149_167, imp))
end else begin
(x, imp)
end
end))))
in (
# 237 "FStar.TypeChecker.Tc.fst"
let _64_286 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_64_286) with
| (formals, c) -> begin
(
# 238 "FStar.TypeChecker.Tc.fst"
let dec = (decreases_clause formals c)
in (
# 239 "FStar.TypeChecker.Tc.fst"
let precedes = (let _149_171 = (let _149_170 = (FStar_Syntax_Syntax.as_arg dec)
in (let _149_169 = (let _149_168 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_149_168)::[])
in (_149_170)::_149_169))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _149_171 None r))
in (
# 240 "FStar.TypeChecker.Tc.fst"
let _64_293 = (FStar_Util.prefix formals)
in (match (_64_293) with
| (bs, (last, imp)) -> begin
(
# 241 "FStar.TypeChecker.Tc.fst"
let last = (
# 241 "FStar.TypeChecker.Tc.fst"
let _64_294 = last
in (let _149_172 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _64_294.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_294.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_172}))
in (
# 242 "FStar.TypeChecker.Tc.fst"
let refined_formals = (FStar_List.append bs (((last, imp))::[]))
in (
# 243 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (
# 244 "FStar.TypeChecker.Tc.fst"
let _64_299 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_175 = (FStar_Syntax_Print.lbname_to_string l)
in (let _149_174 = (FStar_Syntax_Print.term_to_string t)
in (let _149_173 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _149_175 _149_174 _149_173))))
end else begin
()
end
in (l, t')))))
end))))
end)))
end
| _64_302 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end))

# 251 "FStar.TypeChecker.Tc.fst"
let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (
# 256 "FStar.TypeChecker.Tc.fst"
let _64_305 = env
in {FStar_TypeChecker_Env.solver = _64_305.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_305.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_305.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_305.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_305.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_305.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_305.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_305.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_305.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_305.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_305.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_305.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _64_305.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _64_305.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _64_305.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _64_305.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_305.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_305.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_305.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_305.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_305.FStar_TypeChecker_Env.use_bv_sorts}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 261 "FStar.TypeChecker.Tc.fst"
let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (
# 262 "FStar.TypeChecker.Tc.fst"
let _64_310 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_244 = (let _149_242 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _149_242))
in (let _149_243 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _149_244 _149_243)))
end else begin
()
end
in (
# 263 "FStar.TypeChecker.Tc.fst"
let top = e
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_64_314) -> begin
(let _149_248 = (FStar_Syntax_Subst.compress e)
in (tc_term env _149_248))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(
# 280 "FStar.TypeChecker.Tc.fst"
let _64_355 = (tc_tot_or_gtot_term env e)
in (match (_64_355) with
| (e, c, g) -> begin
(
# 281 "FStar.TypeChecker.Tc.fst"
let g = (
# 281 "FStar.TypeChecker.Tc.fst"
let _64_356 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _64_356.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _64_356.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _64_356.FStar_TypeChecker_Env.implicits})
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(
# 285 "FStar.TypeChecker.Tc.fst"
let _64_366 = (FStar_Syntax_Util.type_u ())
in (match (_64_366) with
| (t, u) -> begin
(
# 286 "FStar.TypeChecker.Tc.fst"
let _64_370 = (tc_check_tot_or_gtot_term env e t)
in (match (_64_370) with
| (e, c, g) -> begin
(
# 287 "FStar.TypeChecker.Tc.fst"
let _64_377 = (
# 288 "FStar.TypeChecker.Tc.fst"
let _64_374 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_64_374) with
| (env, _64_373) -> begin
(tc_pats env pats)
end))
in (match (_64_377) with
| (pats, g') -> begin
(
# 290 "FStar.TypeChecker.Tc.fst"
let g' = (
# 290 "FStar.TypeChecker.Tc.fst"
let _64_378 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _64_378.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _64_378.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _64_378.FStar_TypeChecker_Env.implicits})
in (let _149_250 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_pattern (pats)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _149_249 = (FStar_TypeChecker_Rel.conj_guard g g')
in (_149_250, c, _149_249))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _149_251 = (FStar_Syntax_Subst.compress e)
in _149_251.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_64_387, {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _64_394; FStar_Syntax_Syntax.lbtyp = _64_392; FStar_Syntax_Syntax.lbeff = _64_390; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 298 "FStar.TypeChecker.Tc.fst"
let _64_405 = (let _149_252 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _149_252 e1))
in (match (_64_405) with
| (e1, c1, g1) -> begin
(
# 299 "FStar.TypeChecker.Tc.fst"
let _64_409 = (tc_term env e2)
in (match (_64_409) with
| (e2, c2, g2) -> begin
(
# 300 "FStar.TypeChecker.Tc.fst"
let c = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (None, c2))
in (
# 301 "FStar.TypeChecker.Tc.fst"
let e = (let _149_257 = (let _149_256 = (let _149_255 = (let _149_254 = (let _149_253 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Common.t_unit, e1))
in (_149_253)::[])
in (false, _149_254))
in (_149_255, e2))
in FStar_Syntax_Syntax.Tm_let (_149_256))
in (FStar_Syntax_Syntax.mk _149_257 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 302 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _149_258 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _149_258)))))
end))
end))
end
| _64_414 -> begin
(
# 305 "FStar.TypeChecker.Tc.fst"
let _64_418 = (tc_term env e)
in (match (_64_418) with
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
let _64_427 = (tc_term env e)
in (match (_64_427) with
| (e, c, g) -> begin
(
# 312 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, m))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _64_432) -> begin
(
# 316 "FStar.TypeChecker.Tc.fst"
let _64_437 = (FStar_Syntax_Util.type_u ())
in (match (_64_437) with
| (k, u) -> begin
(
# 317 "FStar.TypeChecker.Tc.fst"
let _64_442 = (tc_check_tot_or_gtot_term env t k)
in (match (_64_442) with
| (t, _64_440, f) -> begin
(
# 318 "FStar.TypeChecker.Tc.fst"
let _64_446 = (let _149_259 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _149_259 e))
in (match (_64_446) with
| (e, c, g) -> begin
(
# 319 "FStar.TypeChecker.Tc.fst"
let _64_450 = (let _149_263 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _64_447 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _149_263 e c f))
in (match (_64_450) with
| (c, f) -> begin
(
# 320 "FStar.TypeChecker.Tc.fst"
let _64_454 = (let _149_264 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, t, Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _149_264 c))
in (match (_64_454) with
| (e, c, f2) -> begin
(let _149_266 = (let _149_265 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _149_265))
in (e, c, _149_266))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 324 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 325 "FStar.TypeChecker.Tc.fst"
let env = (let _149_268 = (let _149_267 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _149_267 Prims.fst))
in (FStar_All.pipe_right _149_268 instantiate_both))
in (
# 326 "FStar.TypeChecker.Tc.fst"
let _64_461 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_270 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _149_269 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _149_270 _149_269)))
end else begin
()
end
in (
# 330 "FStar.TypeChecker.Tc.fst"
let _64_466 = (tc_term (no_inst env) head)
in (match (_64_466) with
| (head, chead, g_head) -> begin
(
# 331 "FStar.TypeChecker.Tc.fst"
let _64_470 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _149_271 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _149_271))
end else begin
(let _149_272 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _149_272))
end
in (match (_64_470) with
| (e, c, g) -> begin
(
# 334 "FStar.TypeChecker.Tc.fst"
let _64_471 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _149_273 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _149_273))
end else begin
()
end
in (
# 336 "FStar.TypeChecker.Tc.fst"
let c = if (((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) && (not ((FStar_Syntax_Util.is_lcomp_partial_return c)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)) then begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e c)
end else begin
c
end
in (
# 341 "FStar.TypeChecker.Tc.fst"
let _64_478 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_279 = (FStar_Syntax_Print.term_to_string e)
in (let _149_278 = (let _149_274 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _149_274))
in (let _149_277 = (let _149_276 = (FStar_TypeChecker_Env.expected_typ env0)
in (FStar_All.pipe_right _149_276 (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end))))
in (FStar_Util.print3 "(%s) About to check %s against expected typ %s\n" _149_279 _149_278 _149_277))))
end else begin
()
end
in (
# 346 "FStar.TypeChecker.Tc.fst"
let _64_483 = (comp_check_expected_typ env0 e c)
in (match (_64_483) with
| (e, c, g') -> begin
(
# 347 "FStar.TypeChecker.Tc.fst"
let _64_484 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_282 = (FStar_Syntax_Print.term_to_string e)
in (let _149_281 = (let _149_280 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _149_280))
in (FStar_Util.print2 "(%s) checked ... got %s\n" _149_282 _149_281)))
end else begin
()
end
in (
# 351 "FStar.TypeChecker.Tc.fst"
let gimp = (match ((let _149_283 = (FStar_Syntax_Subst.compress head)
in _149_283.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _64_488) -> begin
(
# 354 "FStar.TypeChecker.Tc.fst"
let imp = (env0, u, e, c.FStar_Syntax_Syntax.res_typ, e.FStar_Syntax_Syntax.pos)
in (
# 355 "FStar.TypeChecker.Tc.fst"
let _64_492 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _64_492.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _64_492.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _64_492.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _64_495 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (
# 357 "FStar.TypeChecker.Tc.fst"
let gres = (let _149_284 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _149_284))
in (
# 358 "FStar.TypeChecker.Tc.fst"
let _64_498 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _149_285 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print1 "Guard from application node is %s\n" _149_285))
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
# 363 "FStar.TypeChecker.Tc.fst"
let _64_506 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_64_506) with
| (env1, topt) -> begin
(
# 364 "FStar.TypeChecker.Tc.fst"
let env1 = (instantiate_both env1)
in (
# 365 "FStar.TypeChecker.Tc.fst"
let _64_511 = (tc_term env1 e1)
in (match (_64_511) with
| (e1, c1, g1) -> begin
(
# 366 "FStar.TypeChecker.Tc.fst"
let _64_522 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(
# 369 "FStar.TypeChecker.Tc.fst"
let _64_518 = (FStar_Syntax_Util.type_u ())
in (match (_64_518) with
| (k, _64_517) -> begin
(
# 370 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _149_286 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_149_286, res_t)))
end))
end)
in (match (_64_522) with
| (env_branches, res_t) -> begin
(
# 373 "FStar.TypeChecker.Tc.fst"
let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (
# 374 "FStar.TypeChecker.Tc.fst"
let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (
# 375 "FStar.TypeChecker.Tc.fst"
let _64_539 = (
# 376 "FStar.TypeChecker.Tc.fst"
let _64_536 = (FStar_List.fold_right (fun _64_530 _64_533 -> (match ((_64_530, _64_533)) with
| ((_64_526, f, c, g), (caccum, gaccum)) -> begin
(let _149_289 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _149_289))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_64_536) with
| (cases, g) -> begin
(let _149_290 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_149_290, g))
end))
in (match (_64_539) with
| (c_branches, g_branches) -> begin
(
# 380 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (guard_x), c_branches))
in (
# 381 "FStar.TypeChecker.Tc.fst"
let e = (let _149_294 = (let _149_293 = (let _149_292 = (FStar_List.map (fun _64_548 -> (match (_64_548) with
| (f, _64_543, _64_545, _64_547) -> begin
f
end)) t_eqns)
in (e1, _149_292))
in FStar_Syntax_Syntax.Tm_match (_149_293))
in (FStar_Syntax_Syntax.mk _149_294 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (
# 382 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, cres.FStar_Syntax_Syntax.res_typ, Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (
# 383 "FStar.TypeChecker.Tc.fst"
let _64_551 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _149_297 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _149_296 = (let _149_295 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _149_295))
in (FStar_Util.print2 "(%s) comp type = %s\n" _149_297 _149_296)))
end else begin
()
end
in (let _149_298 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _149_298))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_64_563); FStar_Syntax_Syntax.lbunivs = _64_561; FStar_Syntax_Syntax.lbtyp = _64_559; FStar_Syntax_Syntax.lbeff = _64_557; FStar_Syntax_Syntax.lbdef = _64_555}::[]), _64_569) -> begin
(
# 390 "FStar.TypeChecker.Tc.fst"
let _64_572 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_299 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _149_299))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _64_576), _64_579) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_64_594); FStar_Syntax_Syntax.lbunivs = _64_592; FStar_Syntax_Syntax.lbtyp = _64_590; FStar_Syntax_Syntax.lbeff = _64_588; FStar_Syntax_Syntax.lbdef = _64_586}::_64_584), _64_600) -> begin
(
# 397 "FStar.TypeChecker.Tc.fst"
let _64_603 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_300 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _149_300))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _64_607), _64_610) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 410 "FStar.TypeChecker.Tc.fst"
let check_instantiated_fvar = (fun env v dc e t -> (
# 411 "FStar.TypeChecker.Tc.fst"
let _64_624 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_64_624) with
| (e, t, implicits) -> begin
(
# 413 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _149_314 = (let _149_313 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _149_313))
in FStar_Util.Inr (_149_314))
end
in (
# 414 "FStar.TypeChecker.Tc.fst"
let is_data_ctor = (fun _64_4 -> (match (_64_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _64_634 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _149_320 = (let _149_319 = (let _149_318 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _149_317 = (FStar_TypeChecker_Env.get_range env)
in (_149_318, _149_317)))
in FStar_Syntax_Syntax.Error (_149_319))
in (Prims.raise _149_320))
end else begin
(value_check_expected_typ env e tc implicits)
end))
end)))
in (
# 424 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (
# 425 "FStar.TypeChecker.Tc.fst"
let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(FStar_All.failwith "Impossible: Violation of locally nameless convention")
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(
# 431 "FStar.TypeChecker.Tc.fst"
let g = (match ((let _149_321 = (FStar_Syntax_Subst.compress t1)
in _149_321.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_64_645) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _64_648 -> begin
(
# 433 "FStar.TypeChecker.Tc.fst"
let imp = (env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (
# 434 "FStar.TypeChecker.Tc.fst"
let _64_650 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _64_650.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _64_650.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _64_650.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 439 "FStar.TypeChecker.Tc.fst"
let _64_656 = (FStar_Syntax_Util.type_u ())
in (match (_64_656) with
| (t, u) -> begin
(
# 440 "FStar.TypeChecker.Tc.fst"
let e = (FStar_TypeChecker_Util.new_uvar env t)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))
end))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 444 "FStar.TypeChecker.Tc.fst"
let t = if env.FStar_TypeChecker_Env.use_bv_sorts then begin
x.FStar_Syntax_Syntax.sort
end else begin
(FStar_TypeChecker_Env.lookup_bv env x)
end
in (
# 445 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.bv_to_name (
# 445 "FStar.TypeChecker.Tc.fst"
let _64_661 = x
in {FStar_Syntax_Syntax.ppname = _64_661.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_661.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (
# 446 "FStar.TypeChecker.Tc.fst"
let _64_667 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_64_667) with
| (e, t, implicits) -> begin
(
# 447 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _149_323 = (let _149_322 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _149_322))
in FStar_Util.Inr (_149_323))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _64_674; FStar_Syntax_Syntax.pos = _64_672; FStar_Syntax_Syntax.vars = _64_670}, us) -> begin
(
# 451 "FStar.TypeChecker.Tc.fst"
let us = (FStar_List.map (tc_universe env) us)
in (
# 452 "FStar.TypeChecker.Tc.fst"
let _64_684 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_64_684) with
| (us', t) -> begin
(
# 453 "FStar.TypeChecker.Tc.fst"
let _64_691 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _149_326 = (let _149_325 = (let _149_324 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _149_324))
in FStar_Syntax_Syntax.Error (_149_325))
in (Prims.raise _149_326))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _64_690 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (
# 458 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 458 "FStar.TypeChecker.Tc.fst"
let _64_693 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 458 "FStar.TypeChecker.Tc.fst"
let _64_695 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _64_695.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _64_695.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _64_693.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _64_693.FStar_Syntax_Syntax.fv_qual})
in (
# 459 "FStar.TypeChecker.Tc.fst"
let e = (let _149_329 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _149_329 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(
# 463 "FStar.TypeChecker.Tc.fst"
let _64_703 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_64_703) with
| (us, t) -> begin
(
# 464 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 464 "FStar.TypeChecker.Tc.fst"
let _64_704 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 464 "FStar.TypeChecker.Tc.fst"
let _64_706 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _64_706.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _64_706.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _64_704.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _64_704.FStar_Syntax_Syntax.fv_qual})
in (
# 465 "FStar.TypeChecker.Tc.fst"
let e = (let _149_330 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _149_330 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t)))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(
# 469 "FStar.TypeChecker.Tc.fst"
let t = (tc_constant env top.FStar_Syntax_Syntax.pos c)
in (
# 470 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 474 "FStar.TypeChecker.Tc.fst"
let _64_720 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_64_720) with
| (bs, c) -> begin
(
# 475 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 476 "FStar.TypeChecker.Tc.fst"
let _64_725 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_64_725) with
| (env, _64_724) -> begin
(
# 477 "FStar.TypeChecker.Tc.fst"
let _64_730 = (tc_binders env bs)
in (match (_64_730) with
| (bs, env, g, us) -> begin
(
# 478 "FStar.TypeChecker.Tc.fst"
let _64_734 = (tc_comp env c)
in (match (_64_734) with
| (c, uc, f) -> begin
(
# 479 "FStar.TypeChecker.Tc.fst"
let e = (
# 479 "FStar.TypeChecker.Tc.fst"
let _64_735 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _64_735.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _64_735.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _64_735.FStar_Syntax_Syntax.vars})
in (
# 480 "FStar.TypeChecker.Tc.fst"
let _64_738 = (check_smt_pat env e bs c)
in (
# 481 "FStar.TypeChecker.Tc.fst"
let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (
# 482 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 483 "FStar.TypeChecker.Tc.fst"
let g = (let _149_331 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _149_331))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(
# 487 "FStar.TypeChecker.Tc.fst"
let u = (tc_universe env u)
in (
# 488 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) None top.FStar_Syntax_Syntax.pos)
in (
# 489 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 493 "FStar.TypeChecker.Tc.fst"
let _64_754 = (let _149_333 = (let _149_332 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_332)::[])
in (FStar_Syntax_Subst.open_term _149_333 phi))
in (match (_64_754) with
| (x, phi) -> begin
(
# 494 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 495 "FStar.TypeChecker.Tc.fst"
let _64_759 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_64_759) with
| (env, _64_758) -> begin
(
# 496 "FStar.TypeChecker.Tc.fst"
let _64_764 = (let _149_334 = (FStar_List.hd x)
in (tc_binder env _149_334))
in (match (_64_764) with
| (x, env, f1, u) -> begin
(
# 497 "FStar.TypeChecker.Tc.fst"
let _64_765 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_337 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _149_336 = (FStar_Syntax_Print.term_to_string phi)
in (let _149_335 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _149_337 _149_336 _149_335))))
end else begin
()
end
in (
# 500 "FStar.TypeChecker.Tc.fst"
let _64_770 = (FStar_Syntax_Util.type_u ())
in (match (_64_770) with
| (t_phi, _64_769) -> begin
(
# 501 "FStar.TypeChecker.Tc.fst"
let _64_775 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_64_775) with
| (phi, _64_773, f2) -> begin
(
# 502 "FStar.TypeChecker.Tc.fst"
let e = (
# 502 "FStar.TypeChecker.Tc.fst"
let _64_776 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _64_776.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _64_776.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _64_776.FStar_Syntax_Syntax.vars})
in (
# 503 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 504 "FStar.TypeChecker.Tc.fst"
let g = (let _149_338 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _149_338))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _64_784) -> begin
(
# 508 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (
# 509 "FStar.TypeChecker.Tc.fst"
let _64_790 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_339 = (FStar_Syntax_Print.term_to_string (
# 510 "FStar.TypeChecker.Tc.fst"
let _64_788 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _64_788.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _64_788.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _64_788.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _149_339))
end else begin
()
end
in (
# 511 "FStar.TypeChecker.Tc.fst"
let _64_794 = (FStar_Syntax_Subst.open_term bs body)
in (match (_64_794) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _64_796 -> begin
(let _149_341 = (let _149_340 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _149_340))
in (FStar_All.failwith _149_341))
end)))))
and tc_constant : FStar_TypeChecker_Env.env  ->  FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun env r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_64_802) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_64_805) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int32 (_64_808) -> begin
FStar_TypeChecker_Common.t_int32
end
| FStar_Const.Const_int64 (_64_811) -> begin
FStar_TypeChecker_Common.t_int64
end
| FStar_Const.Const_string (_64_814) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_64_817) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_64_820) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_uint8 (_64_823) -> begin
FStar_TypeChecker_Common.t_uint8
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_64_827) -> begin
(
# 530 "FStar.TypeChecker.Tc.fst"
let fail = (fun _64_830 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Range constant cannot be checked in this context; expected an instance of \'range_of\'", r))))
end))
in (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(fail ())
end
| Some (t) -> begin
if (let _149_347 = (FStar_Syntax_Util.destruct t FStar_Syntax_Const.range_of_lid)
in (FStar_Option.isSome _149_347)) then begin
t
end else begin
(fail ())
end
end))
end
| _64_835 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 551 "FStar.TypeChecker.Tc.fst"
let _64_842 = (FStar_Syntax_Util.type_u ())
in (match (_64_842) with
| (k, u) -> begin
(
# 552 "FStar.TypeChecker.Tc.fst"
let _64_847 = (tc_check_tot_or_gtot_term env t k)
in (match (_64_847) with
| (t, _64_845, g) -> begin
(let _149_350 = (FStar_Syntax_Syntax.mk_Total t)
in (_149_350, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 556 "FStar.TypeChecker.Tc.fst"
let _64_852 = (FStar_Syntax_Util.type_u ())
in (match (_64_852) with
| (k, u) -> begin
(
# 557 "FStar.TypeChecker.Tc.fst"
let _64_857 = (tc_check_tot_or_gtot_term env t k)
in (match (_64_857) with
| (t, _64_855, g) -> begin
(let _149_351 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_149_351, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 561 "FStar.TypeChecker.Tc.fst"
let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (
# 562 "FStar.TypeChecker.Tc.fst"
let tc = (let _149_353 = (let _149_352 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_149_352)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _149_353 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 563 "FStar.TypeChecker.Tc.fst"
let _64_866 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_64_866) with
| (tc, _64_864, f) -> begin
(
# 564 "FStar.TypeChecker.Tc.fst"
let _64_870 = (FStar_Syntax_Util.head_and_args tc)
in (match (_64_870) with
| (_64_868, args) -> begin
(
# 565 "FStar.TypeChecker.Tc.fst"
let _64_873 = (let _149_355 = (FStar_List.hd args)
in (let _149_354 = (FStar_List.tl args)
in (_149_355, _149_354)))
in (match (_64_873) with
| (res, args) -> begin
(
# 566 "FStar.TypeChecker.Tc.fst"
let _64_889 = (let _149_357 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _64_5 -> (match (_64_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(
# 568 "FStar.TypeChecker.Tc.fst"
let _64_880 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_64_880) with
| (env, _64_879) -> begin
(
# 569 "FStar.TypeChecker.Tc.fst"
let _64_885 = (tc_tot_or_gtot_term env e)
in (match (_64_885) with
| (e, _64_883, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _149_357 FStar_List.unzip))
in (match (_64_889) with
| (flags, guards) -> begin
(
# 572 "FStar.TypeChecker.Tc.fst"
let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| _64_894 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _149_359 = (FStar_Syntax_Syntax.mk_Comp (
# 575 "FStar.TypeChecker.Tc.fst"
let _64_896 = c
in {FStar_Syntax_Syntax.effect_name = _64_896.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _64_896.FStar_Syntax_Syntax.flags}))
in (let _149_358 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_149_359, u, _149_358))))
end))
end))
end))
end))))
end))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (
# 582 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun u -> (
# 583 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_64_904) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _149_364 = (aux u)
in FStar_Syntax_Syntax.U_succ (_149_364))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _149_365 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_149_365))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _149_369 = (let _149_368 = (let _149_367 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _149_366 = (FStar_TypeChecker_Env.get_range env)
in (_149_367, _149_366)))
in FStar_Syntax_Syntax.Error (_149_368))
in (Prims.raise _149_369))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _149_370 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _149_370 Prims.snd))
end
| _64_919 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (
# 605 "FStar.TypeChecker.Tc.fst"
let fail = (fun msg t -> (let _149_379 = (let _149_378 = (let _149_377 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_149_377, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_149_378))
in (Prims.raise _149_379)))
in (
# 614 "FStar.TypeChecker.Tc.fst"
let check_binders = (fun env bs bs_expected -> (
# 619 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun _64_937 bs bs_expected -> (match (_64_937) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| ((hd, imp)::bs, (hd_expected, imp')::bs_expected) -> begin
(
# 623 "FStar.TypeChecker.Tc.fst"
let _64_968 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _149_396 = (let _149_395 = (let _149_394 = (let _149_392 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _149_392))
in (let _149_393 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_149_394, _149_393)))
in FStar_Syntax_Syntax.Error (_149_395))
in (Prims.raise _149_396))
end
| _64_967 -> begin
()
end)
in (
# 630 "FStar.TypeChecker.Tc.fst"
let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (
# 631 "FStar.TypeChecker.Tc.fst"
let _64_985 = (match ((let _149_397 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _149_397.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _64_973 -> begin
(
# 634 "FStar.TypeChecker.Tc.fst"
let _64_974 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_398 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _149_398))
end else begin
()
end
in (
# 635 "FStar.TypeChecker.Tc.fst"
let _64_980 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_64_980) with
| (t, _64_978, g1) -> begin
(
# 636 "FStar.TypeChecker.Tc.fst"
let g2 = (let _149_400 = (FStar_TypeChecker_Env.get_range env)
in (let _149_399 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _149_400 "Type annotation on parameter incompatible with the expected type" _149_399)))
in (
# 640 "FStar.TypeChecker.Tc.fst"
let g = (let _149_401 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _149_401))
in (t, g)))
end)))
end)
in (match (_64_985) with
| (t, g) -> begin
(
# 642 "FStar.TypeChecker.Tc.fst"
let hd = (
# 642 "FStar.TypeChecker.Tc.fst"
let _64_986 = hd
in {FStar_Syntax_Syntax.ppname = _64_986.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_986.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 643 "FStar.TypeChecker.Tc.fst"
let b = (hd, imp)
in (
# 644 "FStar.TypeChecker.Tc.fst"
let b_expected = (hd_expected, imp')
in (
# 645 "FStar.TypeChecker.Tc.fst"
let env = (maybe_push_binding env b)
in (
# 646 "FStar.TypeChecker.Tc.fst"
let subst = (let _149_402 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _149_402))
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
# 656 "FStar.TypeChecker.Tc.fst"
let rec expected_function_typ = (fun env t0 -> (match (t0) with
| None -> begin
(
# 666 "FStar.TypeChecker.Tc.fst"
let _64_1006 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _64_1005 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (
# 669 "FStar.TypeChecker.Tc.fst"
let _64_1013 = (tc_binders env bs)
in (match (_64_1013) with
| (bs, envbody, g, _64_1012) -> begin
(None, bs, [], None, envbody, g)
end)))
end
| Some (t) -> begin
(
# 673 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 674 "FStar.TypeChecker.Tc.fst"
let rec as_function_typ = (fun norm t -> (match ((let _149_411 = (FStar_Syntax_Subst.compress t)
in _149_411.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 678 "FStar.TypeChecker.Tc.fst"
let _64_1040 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _64_1039 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 679 "FStar.TypeChecker.Tc.fst"
let _64_1047 = (tc_binders env bs)
in (match (_64_1047) with
| (bs, envbody, g, _64_1046) -> begin
(
# 680 "FStar.TypeChecker.Tc.fst"
let _64_1051 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_64_1051) with
| (envbody, _64_1050) -> begin
(Some ((t, true)), bs, [], None, envbody, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _64_1054) -> begin
(
# 686 "FStar.TypeChecker.Tc.fst"
let _64_1064 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_64_1064) with
| (_64_1058, bs, bs', copt, env, g) -> begin
(Some ((t, false)), bs, bs', copt, env, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 690 "FStar.TypeChecker.Tc.fst"
let _64_1071 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_64_1071) with
| (bs_expected, c_expected) -> begin
(
# 697 "FStar.TypeChecker.Tc.fst"
let check_actuals_against_formals = (fun env bs bs_expected -> (
# 698 "FStar.TypeChecker.Tc.fst"
let rec handle_more = (fun _64_1082 c_expected -> (match (_64_1082) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _149_422 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _149_422))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(
# 703 "FStar.TypeChecker.Tc.fst"
let c = (let _149_423 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _149_423))
in (let _149_424 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _149_424)))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(
# 707 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.subst_comp subst c_expected)
in if (FStar_Syntax_Util.is_total_comp c) then begin
(
# 710 "FStar.TypeChecker.Tc.fst"
let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 713 "FStar.TypeChecker.Tc.fst"
let _64_1103 = (check_binders env more_bs bs_expected)
in (match (_64_1103) with
| (env, bs', more, guard', subst) -> begin
(let _149_426 = (let _149_425 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _149_425, subst))
in (handle_more _149_426 c_expected))
end))
end
| _64_1105 -> begin
(let _149_428 = (let _149_427 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _149_427))
in (fail _149_428 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _149_429 = (check_binders env bs bs_expected)
in (handle_more _149_429 c_expected))))
in (
# 720 "FStar.TypeChecker.Tc.fst"
let mk_letrec_env = (fun envbody bs c -> (
# 721 "FStar.TypeChecker.Tc.fst"
let letrecs = (guard_letrecs envbody bs c)
in (
# 722 "FStar.TypeChecker.Tc.fst"
let envbody = (
# 722 "FStar.TypeChecker.Tc.fst"
let _64_1111 = envbody
in {FStar_TypeChecker_Env.solver = _64_1111.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_1111.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_1111.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_1111.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_1111.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_1111.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_1111.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_1111.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_1111.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_1111.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_1111.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_1111.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _64_1111.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _64_1111.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _64_1111.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _64_1111.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_1111.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_1111.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_1111.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_1111.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_1111.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _64_1116 _64_1119 -> (match ((_64_1116, _64_1119)) with
| ((env, letrec_binders), (l, t)) -> begin
(
# 724 "FStar.TypeChecker.Tc.fst"
let _64_1125 = (let _149_439 = (let _149_438 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _149_438 Prims.fst))
in (tc_term _149_439 t))
in (match (_64_1125) with
| (t, _64_1122, _64_1124) -> begin
(
# 725 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (
# 726 "FStar.TypeChecker.Tc.fst"
let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _149_440 = (FStar_Syntax_Syntax.mk_binder (
# 727 "FStar.TypeChecker.Tc.fst"
let _64_1129 = x
in {FStar_Syntax_Syntax.ppname = _64_1129.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_1129.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_149_440)::letrec_binders)
end
| _64_1132 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (
# 732 "FStar.TypeChecker.Tc.fst"
let _64_1138 = (check_actuals_against_formals env bs bs_expected)
in (match (_64_1138) with
| (envbody, bs, g, c) -> begin
(
# 733 "FStar.TypeChecker.Tc.fst"
let _64_1141 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_64_1141) with
| (envbody, letrecs) -> begin
(
# 734 "FStar.TypeChecker.Tc.fst"
let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, g))
end))
end))))
end))
end
| _64_1144 -> begin
if (not (norm)) then begin
(let _149_441 = (unfold_whnf env t)
in (as_function_typ true _149_441))
end else begin
(
# 742 "FStar.TypeChecker.Tc.fst"
let _64_1153 = (expected_function_typ env None)
in (match (_64_1153) with
| (_64_1146, bs, _64_1149, c_opt, envbody, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (
# 746 "FStar.TypeChecker.Tc.fst"
let use_eq = env.FStar_TypeChecker_Env.use_eq
in (
# 747 "FStar.TypeChecker.Tc.fst"
let _64_1157 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_64_1157) with
| (env, topt) -> begin
(
# 748 "FStar.TypeChecker.Tc.fst"
let _64_1161 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_442 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _149_442 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (
# 752 "FStar.TypeChecker.Tc.fst"
let _64_1169 = (expected_function_typ env topt)
in (match (_64_1169) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, g) -> begin
(
# 753 "FStar.TypeChecker.Tc.fst"
let _64_1175 = (tc_term (
# 753 "FStar.TypeChecker.Tc.fst"
let _64_1170 = envbody
in {FStar_TypeChecker_Env.solver = _64_1170.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_1170.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_1170.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_1170.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_1170.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_1170.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_1170.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_1170.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_1170.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_1170.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_1170.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_1170.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _64_1170.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _64_1170.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _64_1170.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_1170.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_1170.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_1170.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_1170.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_1170.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_64_1175) with
| (body, cbody, guard_body) -> begin
(
# 754 "FStar.TypeChecker.Tc.fst"
let _64_1176 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_446 = (FStar_Syntax_Print.term_to_string body)
in (let _149_445 = (let _149_443 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _149_443))
in (let _149_444 = (FStar_TypeChecker_Rel.guard_to_string env guard_body)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _149_446 _149_445 _149_444))))
end else begin
()
end
in (
# 759 "FStar.TypeChecker.Tc.fst"
let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (
# 761 "FStar.TypeChecker.Tc.fst"
let _64_1179 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _149_449 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _149_448 = (let _149_447 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _149_447))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _149_449 _149_448)))
end else begin
()
end
in (
# 765 "FStar.TypeChecker.Tc.fst"
let _64_1186 = (let _149_451 = (let _149_450 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _149_450))
in (check_expected_effect (
# 765 "FStar.TypeChecker.Tc.fst"
let _64_1181 = envbody
in {FStar_TypeChecker_Env.solver = _64_1181.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_1181.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_1181.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_1181.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_1181.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_1181.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_1181.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_1181.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_1181.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_1181.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_1181.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_1181.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _64_1181.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _64_1181.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _64_1181.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _64_1181.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_1181.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_1181.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_1181.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_1181.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_1181.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _149_451))
in (match (_64_1186) with
| (body, cbody, guard) -> begin
(
# 766 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (
# 767 "FStar.TypeChecker.Tc.fst"
let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _149_452 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _149_452))
end else begin
(
# 769 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (
# 772 "FStar.TypeChecker.Tc.fst"
let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (
# 773 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.abs bs body (Some ((FStar_Syntax_Util.lcomp_of_comp cbody))))
in (
# 774 "FStar.TypeChecker.Tc.fst"
let _64_1209 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(
# 776 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_64_1198) -> begin
(e, t, guard)
end
| _64_1201 -> begin
(
# 785 "FStar.TypeChecker.Tc.fst"
let _64_1204 = if use_teq then begin
(let _149_453 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _149_453))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_64_1204) with
| (e, guard') -> begin
(let _149_454 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _149_454))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_64_1209) with
| (e, tfun, guard) -> begin
(
# 795 "FStar.TypeChecker.Tc.fst"
let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (
# 796 "FStar.TypeChecker.Tc.fst"
let _64_1213 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_64_1213) with
| (c, g) -> begin
(e, c, g)
end)))
end))))))
end)))))
end))
end)))
end)))))))
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead ghead args expected_topt -> (
# 804 "FStar.TypeChecker.Tc.fst"
let n_args = (FStar_List.length args)
in (
# 805 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 806 "FStar.TypeChecker.Tc.fst"
let thead = chead.FStar_Syntax_Syntax.res_typ
in (
# 807 "FStar.TypeChecker.Tc.fst"
let _64_1223 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_463 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _149_462 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _149_463 _149_462)))
end else begin
()
end
in (
# 808 "FStar.TypeChecker.Tc.fst"
let rec check_function_app = (fun norm tf -> (match ((let _149_468 = (FStar_Syntax_Util.unrefine tf)
in _149_468.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 812 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| (e, imp)::tl -> begin
(
# 815 "FStar.TypeChecker.Tc.fst"
let _64_1257 = (tc_term env e)
in (match (_64_1257) with
| (e, c, g_e) -> begin
(
# 816 "FStar.TypeChecker.Tc.fst"
let _64_1261 = (tc_args env tl)
in (match (_64_1261) with
| (args, comps, g_rest) -> begin
(let _149_473 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, (c)::comps, _149_473))
end))
end))
end))
in (
# 824 "FStar.TypeChecker.Tc.fst"
let _64_1265 = (tc_args env args)
in (match (_64_1265) with
| (args, comps, g_args) -> begin
(
# 825 "FStar.TypeChecker.Tc.fst"
let bs = (let _149_475 = (FStar_All.pipe_right comps (FStar_List.map (fun c -> (c.FStar_Syntax_Syntax.res_typ, None))))
in (FStar_Syntax_Util.null_binders_of_tks _149_475))
in (
# 826 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _64_1272 -> begin
FStar_Syntax_Util.ml_comp
end)
in (
# 829 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _149_490 = (FStar_Syntax_Subst.compress t)
in _149_490.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_64_1278) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _64_1283 -> begin
ml_or_tot
end)
end)
in (
# 836 "FStar.TypeChecker.Tc.fst"
let cres = (let _149_495 = (let _149_494 = (let _149_493 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _149_493 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _149_494))
in (ml_or_tot _149_495 r))
in (
# 837 "FStar.TypeChecker.Tc.fst"
let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (
# 838 "FStar.TypeChecker.Tc.fst"
let _64_1287 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _149_498 = (FStar_Syntax_Print.term_to_string head)
in (let _149_497 = (FStar_Syntax_Print.term_to_string tf)
in (let _149_496 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _149_498 _149_497 _149_496))))
end else begin
()
end
in (
# 843 "FStar.TypeChecker.Tc.fst"
let _64_1289 = (let _149_499 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _149_499))
in (
# 844 "FStar.TypeChecker.Tc.fst"
let comp = (let _149_502 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_TypeChecker_Util.bind env None c (None, out))) ((chead)::comps) _149_502))
in (let _149_504 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _149_503 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_149_504, comp, _149_503)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 848 "FStar.TypeChecker.Tc.fst"
let _64_1300 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_64_1300) with
| (bs, c) -> begin
(
# 850 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun _64_1308 bs cres args -> (match (_64_1308) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (_64_1315)))::rest, (_64_1323, None)::_64_1321) -> begin
(
# 861 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 862 "FStar.TypeChecker.Tc.fst"
let _64_1329 = (check_no_escape (Some (head)) env fvs t)
in (
# 863 "FStar.TypeChecker.Tc.fst"
let _64_1335 = (FStar_TypeChecker_Util.new_implicit_var env t)
in (match (_64_1335) with
| (varg, _64_1333, implicits) -> begin
(
# 864 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (
# 865 "FStar.TypeChecker.Tc.fst"
let arg = (let _149_513 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _149_513))
in (let _149_515 = (let _149_514 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _149_514, fvs))
in (tc_args _149_515 rest cres args))))
end))))
end
| ((x, aqual)::rest, (e, aq)::rest') -> begin
(
# 869 "FStar.TypeChecker.Tc.fst"
let _64_1367 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _64_1366 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (
# 874 "FStar.TypeChecker.Tc.fst"
let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 875 "FStar.TypeChecker.Tc.fst"
let x = (
# 875 "FStar.TypeChecker.Tc.fst"
let _64_1370 = x
in {FStar_Syntax_Syntax.ppname = _64_1370.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_1370.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (
# 876 "FStar.TypeChecker.Tc.fst"
let _64_1373 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _149_516 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _149_516))
end else begin
()
end
in (
# 877 "FStar.TypeChecker.Tc.fst"
let _64_1375 = (check_no_escape (Some (head)) env fvs targ)
in (
# 878 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (
# 879 "FStar.TypeChecker.Tc.fst"
let env = (
# 879 "FStar.TypeChecker.Tc.fst"
let _64_1378 = env
in {FStar_TypeChecker_Env.solver = _64_1378.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_1378.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_1378.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_1378.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_1378.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_1378.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_1378.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_1378.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_1378.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_1378.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_1378.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_1378.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _64_1378.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _64_1378.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _64_1378.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _64_1378.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_1378.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_1378.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_1378.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_1378.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_1378.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 880 "FStar.TypeChecker.Tc.fst"
let _64_1381 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_519 = (FStar_Syntax_Print.tag_of_term e)
in (let _149_518 = (FStar_Syntax_Print.term_to_string e)
in (let _149_517 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _149_519 _149_518 _149_517))))
end else begin
()
end
in (
# 881 "FStar.TypeChecker.Tc.fst"
let _64_1386 = (tc_term env e)
in (match (_64_1386) with
| (e, c, g_e) -> begin
(
# 882 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (
# 884 "FStar.TypeChecker.Tc.fst"
let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(
# 886 "FStar.TypeChecker.Tc.fst"
let subst = (let _149_520 = (FStar_List.hd bs)
in (maybe_extend_subst subst _149_520 e))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(
# 889 "FStar.TypeChecker.Tc.fst"
let subst = (let _149_521 = (FStar_List.hd bs)
in (maybe_extend_subst subst _149_521 e))
in (
# 890 "FStar.TypeChecker.Tc.fst"
let _64_1393 = (((Some (x), c))::comps, g)
in (match (_64_1393) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _149_522 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _149_522)) then begin
(
# 894 "FStar.TypeChecker.Tc.fst"
let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (
# 895 "FStar.TypeChecker.Tc.fst"
let arg' = (let _149_523 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _149_523))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (newx), c))::comps, g, fvs) rest cres rest')))
end else begin
(let _149_527 = (let _149_526 = (let _149_525 = (let _149_524 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _149_524))
in (_149_525)::arg_rets)
in (subst, (arg)::outargs, _149_526, ((Some (x), c))::comps, g, (x)::fvs))
in (tc_args _149_527 rest cres rest'))
end
end
end))
end))))))))))
end
| (_64_1397, []) -> begin
(
# 904 "FStar.TypeChecker.Tc.fst"
let _64_1400 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (
# 905 "FStar.TypeChecker.Tc.fst"
let _64_1418 = (match (bs) with
| [] -> begin
(
# 908 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (
# 914 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (
# 916 "FStar.TypeChecker.Tc.fst"
let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _64_1408 -> (match (_64_1408) with
| (_64_1406, c) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (
# 923 "FStar.TypeChecker.Tc.fst"
let cres = if refine_with_equality then begin
(let _149_529 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _149_529 cres))
end else begin
(
# 929 "FStar.TypeChecker.Tc.fst"
let _64_1410 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_532 = (FStar_Syntax_Print.term_to_string head)
in (let _149_531 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _149_530 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _149_532 _149_531 _149_530))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _64_1414 -> begin
(
# 938 "FStar.TypeChecker.Tc.fst"
let g = (let _149_533 = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (FStar_All.pipe_right _149_533 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _149_538 = (let _149_537 = (let _149_536 = (let _149_535 = (let _149_534 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _149_534))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _149_535))
in (FStar_Syntax_Syntax.mk_Total _149_536))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _149_537))
in (_149_538, g)))
end)
in (match (_64_1418) with
| (cres, g) -> begin
(
# 941 "FStar.TypeChecker.Tc.fst"
let _64_1419 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_539 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _149_539))
end else begin
()
end
in (
# 942 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_List.fold_left (fun out c -> (FStar_TypeChecker_Util.bind env None (Prims.snd c) ((Prims.fst c), out))) cres comps)
in (
# 943 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.bind env None chead (None, comp))
in (
# 944 "FStar.TypeChecker.Tc.fst"
let app = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev outargs) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (
# 945 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.record_application_site env app comp)
in (
# 946 "FStar.TypeChecker.Tc.fst"
let _64_1429 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp g)
in (match (_64_1429) with
| (comp, g) -> begin
(
# 947 "FStar.TypeChecker.Tc.fst"
let _64_1430 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_545 = (FStar_TypeChecker_Normalize.term_to_string env app)
in (let _149_544 = (let _149_543 = (comp.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Print.comp_to_string _149_543))
in (FStar_Util.print2 "\t Type of app term %s is %s\n" _149_545 _149_544)))
end else begin
()
end
in (app, comp, g))
end)))))))
end)))
end
| ([], arg::_64_1434) -> begin
(
# 953 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun norm tres -> (
# 954 "FStar.TypeChecker.Tc.fst"
let tres = (let _149_550 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _149_550 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(
# 957 "FStar.TypeChecker.Tc.fst"
let _64_1446 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_551 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _149_551))
end else begin
()
end
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs (FStar_Syntax_Util.lcomp_of_comp cres') args))
end
| _64_1449 when (not (norm)) -> begin
(let _149_552 = (unfold_whnf env tres)
in (aux true _149_552))
end
| _64_1451 -> begin
(let _149_558 = (let _149_557 = (let _149_556 = (let _149_554 = (FStar_TypeChecker_Normalize.term_to_string env tf)
in (let _149_553 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _149_554 _149_553)))
in (let _149_555 = (FStar_Syntax_Syntax.argpos arg)
in (_149_556, _149_555)))
in FStar_Syntax_Syntax.Error (_149_557))
in (Prims.raise _149_558))
end)))
in (aux false cres.FStar_Syntax_Syntax.res_typ))
end)
end))
in (tc_args ([], [], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs (FStar_Syntax_Util.lcomp_of_comp c) args))
end))
end
| _64_1453 -> begin
if (not (norm)) then begin
(let _149_559 = (unfold_whnf env tf)
in (check_function_app true _149_559))
end else begin
(let _149_562 = (let _149_561 = (let _149_560 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_149_560, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_149_561))
in (Prims.raise _149_562))
end
end))
in (let _149_564 = (let _149_563 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _149_563))
in (check_function_app false _149_564))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (
# 983 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 984 "FStar.TypeChecker.Tc.fst"
let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(
# 987 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in (
# 988 "FStar.TypeChecker.Tc.fst"
let _64_1489 = (FStar_List.fold_left2 (fun _64_1470 _64_1473 _64_1476 -> (match ((_64_1470, _64_1473, _64_1476)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(
# 989 "FStar.TypeChecker.Tc.fst"
let _64_1477 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 990 "FStar.TypeChecker.Tc.fst"
let _64_1482 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_64_1482) with
| (e, c, g) -> begin
(
# 991 "FStar.TypeChecker.Tc.fst"
let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (
# 992 "FStar.TypeChecker.Tc.fst"
let g = (let _149_574 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _149_574 g))
in (
# 993 "FStar.TypeChecker.Tc.fst"
let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _149_578 = (let _149_576 = (let _149_575 = (FStar_Syntax_Syntax.as_arg e)
in (_149_575)::[])
in (FStar_List.append seen _149_576))
in (let _149_577 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_149_578, _149_577, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_64_1489) with
| (args, guard, ghost) -> begin
(
# 997 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (
# 998 "FStar.TypeChecker.Tc.fst"
let c = if ghost then begin
(let _149_579 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _149_579 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (
# 999 "FStar.TypeChecker.Tc.fst"
let _64_1494 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_64_1494) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _64_1496 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (
# 1019 "FStar.TypeChecker.Tc.fst"
let _64_1503 = (FStar_Syntax_Subst.open_branch branch)
in (match (_64_1503) with
| (pattern, when_clause, branch_exp) -> begin
(
# 1020 "FStar.TypeChecker.Tc.fst"
let _64_1508 = branch
in (match (_64_1508) with
| (cpat, _64_1506, cbr) -> begin
(
# 1023 "FStar.TypeChecker.Tc.fst"
let tc_pat = (fun allow_implicits pat_t p0 -> (
# 1030 "FStar.TypeChecker.Tc.fst"
let _64_1516 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_64_1516) with
| (pat_bvs, exps, p) -> begin
(
# 1031 "FStar.TypeChecker.Tc.fst"
let _64_1517 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_591 = (FStar_Syntax_Print.pat_to_string p0)
in (let _149_590 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _149_591 _149_590)))
end else begin
()
end
in (
# 1033 "FStar.TypeChecker.Tc.fst"
let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (
# 1034 "FStar.TypeChecker.Tc.fst"
let _64_1523 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_64_1523) with
| (env1, _64_1522) -> begin
(
# 1035 "FStar.TypeChecker.Tc.fst"
let env1 = (
# 1035 "FStar.TypeChecker.Tc.fst"
let _64_1524 = env1
in {FStar_TypeChecker_Env.solver = _64_1524.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_1524.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_1524.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_1524.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_1524.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_1524.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_1524.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_1524.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _64_1524.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_1524.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_1524.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _64_1524.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _64_1524.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _64_1524.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _64_1524.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _64_1524.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_1524.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_1524.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_1524.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_1524.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_1524.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1036 "FStar.TypeChecker.Tc.fst"
let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (
# 1037 "FStar.TypeChecker.Tc.fst"
let _64_1563 = (let _149_614 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (
# 1038 "FStar.TypeChecker.Tc.fst"
let _64_1529 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_594 = (FStar_Syntax_Print.term_to_string e)
in (let _149_593 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _149_594 _149_593)))
end else begin
()
end
in (
# 1041 "FStar.TypeChecker.Tc.fst"
let _64_1534 = (tc_term env1 e)
in (match (_64_1534) with
| (e, lc, g) -> begin
(
# 1043 "FStar.TypeChecker.Tc.fst"
let _64_1535 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_596 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _149_595 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _149_596 _149_595)))
end else begin
()
end
in (
# 1046 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (
# 1047 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (
# 1048 "FStar.TypeChecker.Tc.fst"
let _64_1541 = (let _149_597 = (FStar_TypeChecker_Rel.discharge_guard env (
# 1048 "FStar.TypeChecker.Tc.fst"
let _64_1539 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _64_1539.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _64_1539.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _64_1539.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _149_597 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1049 "FStar.TypeChecker.Tc.fst"
let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (
# 1050 "FStar.TypeChecker.Tc.fst"
let uvars_to_string = (fun uvs -> (let _149_602 = (let _149_601 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _149_601 (FStar_List.map (fun _64_1549 -> (match (_64_1549) with
| (u, _64_1548) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _149_602 (FStar_String.concat ", "))))
in (
# 1051 "FStar.TypeChecker.Tc.fst"
let uvs1 = (FStar_Syntax_Free.uvars e')
in (
# 1052 "FStar.TypeChecker.Tc.fst"
let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (
# 1053 "FStar.TypeChecker.Tc.fst"
let _64_1557 = if (let _149_603 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _149_603)) then begin
(
# 1054 "FStar.TypeChecker.Tc.fst"
let unresolved = (let _149_604 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _149_604 FStar_Util.set_elements))
in (let _149_612 = (let _149_611 = (let _149_610 = (let _149_609 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _149_608 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _149_607 = (let _149_606 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _64_1556 -> (match (_64_1556) with
| (u, _64_1555) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _149_606 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _149_609 _149_608 _149_607))))
in (_149_610, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_149_611))
in (Prims.raise _149_612)))
end else begin
()
end
in (
# 1061 "FStar.TypeChecker.Tc.fst"
let _64_1559 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_613 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _149_613))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _149_614 FStar_List.unzip))
in (match (_64_1563) with
| (exps, norm_exps) -> begin
(
# 1066 "FStar.TypeChecker.Tc.fst"
let p = (FStar_TypeChecker_Util.decorate_pattern env p exps)
in (p, pat_bvs, pat_env, exps, norm_exps))
end))))
end))))
end)))
in (
# 1070 "FStar.TypeChecker.Tc.fst"
let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (
# 1071 "FStar.TypeChecker.Tc.fst"
let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (
# 1072 "FStar.TypeChecker.Tc.fst"
let _64_1570 = (let _149_615 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _149_615 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_64_1570) with
| (scrutinee_env, _64_1569) -> begin
(
# 1075 "FStar.TypeChecker.Tc.fst"
let _64_1576 = (tc_pat true pat_t pattern)
in (match (_64_1576) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(
# 1078 "FStar.TypeChecker.Tc.fst"
let _64_1586 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(
# 1085 "FStar.TypeChecker.Tc.fst"
let _64_1583 = (let _149_616 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _149_616 e))
in (match (_64_1583) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_64_1586) with
| (when_clause, g_when) -> begin
(
# 1089 "FStar.TypeChecker.Tc.fst"
let _64_1590 = (tc_term pat_env branch_exp)
in (match (_64_1590) with
| (branch_exp, c, g_branch) -> begin
(
# 1093 "FStar.TypeChecker.Tc.fst"
let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _149_618 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _149_617 -> Some (_149_617)) _149_618))
end)
in (
# 1100 "FStar.TypeChecker.Tc.fst"
let _64_1646 = (
# 1103 "FStar.TypeChecker.Tc.fst"
let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (
# 1104 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _64_1608 -> begin
(
# 1110 "FStar.TypeChecker.Tc.fst"
let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _149_622 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _149_621 -> Some (_149_621)) _149_622))
end))
end))) None))
in (
# 1115 "FStar.TypeChecker.Tc.fst"
let _64_1616 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_64_1616) with
| (c, g_branch) -> begin
(
# 1119 "FStar.TypeChecker.Tc.fst"
let _64_1641 = (match ((eqs, when_condition)) with
| (None, None) -> begin
(c, g_when)
end
| (Some (f), None) -> begin
(
# 1125 "FStar.TypeChecker.Tc.fst"
let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1126 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _149_625 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _149_624 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_149_625, _149_624)))))
end
| (Some (f), Some (w)) -> begin
(
# 1131 "FStar.TypeChecker.Tc.fst"
let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1132 "FStar.TypeChecker.Tc.fst"
let g_fw = (let _149_626 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_149_626))
in (let _149_629 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _149_628 = (let _149_627 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _149_627 g_when))
in (_149_629, _149_628)))))
end
| (None, Some (w)) -> begin
(
# 1137 "FStar.TypeChecker.Tc.fst"
let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (
# 1138 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _149_630 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_149_630, g_when))))
end)
in (match (_64_1641) with
| (c_weak, g_when_weak) -> begin
(
# 1143 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _149_632 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _149_631 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_149_632, _149_631, g_branch))))
end))
end)))
in (match (_64_1646) with
| (c, g_when, g_branch) -> begin
(
# 1161 "FStar.TypeChecker.Tc.fst"
let branch_guard = (
# 1163 "FStar.TypeChecker.Tc.fst"
let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (
# 1164 "FStar.TypeChecker.Tc.fst"
let discriminate = (fun scrutinee_tm f -> if ((let _149_642 = (let _149_641 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _149_641))
in (FStar_List.length _149_642)) > 1) then begin
(
# 1167 "FStar.TypeChecker.Tc.fst"
let disc = (let _149_643 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _149_643 FStar_Syntax_Syntax.Delta_equational None))
in (
# 1168 "FStar.TypeChecker.Tc.fst"
let disc = (let _149_645 = (let _149_644 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_149_644)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _149_645 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _149_646 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_149_646)::[])))
end else begin
[]
end)
in (
# 1172 "FStar.TypeChecker.Tc.fst"
let fail = (fun _64_1656 -> (match (()) with
| () -> begin
(let _149_652 = (let _149_651 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _149_650 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _149_649 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _149_651 _149_650 _149_649))))
in (FStar_All.failwith _149_652))
end))
in (
# 1178 "FStar.TypeChecker.Tc.fst"
let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _64_1663) -> begin
(head_constructor t)
end
| _64_1667 -> begin
(fail ())
end))
in (
# 1183 "FStar.TypeChecker.Tc.fst"
let pat_exp = (let _149_655 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _149_655 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_64_1692) -> begin
(let _149_660 = (let _149_659 = (let _149_658 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _149_657 = (let _149_656 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_149_656)::[])
in (_149_658)::_149_657))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _149_659 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_149_660)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 1192 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _149_661 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _149_661))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 1197 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(
# 1200 "FStar.TypeChecker.Tc.fst"
let sub_term_guards = (let _149_668 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _64_1710 -> (match (_64_1710) with
| (ei, _64_1709) -> begin
(
# 1201 "FStar.TypeChecker.Tc.fst"
let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _64_1714 -> begin
(
# 1205 "FStar.TypeChecker.Tc.fst"
let sub_term = (let _149_667 = (let _149_664 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _149_664 FStar_Syntax_Syntax.Delta_equational None))
in (let _149_666 = (let _149_665 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_149_665)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _149_667 _149_666 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _149_668 FStar_List.flatten))
in (let _149_669 = (discriminate scrutinee_tm f)
in (FStar_List.append _149_669 sub_term_guards)))
end)
end
| _64_1718 -> begin
[]
end))))))
in (
# 1211 "FStar.TypeChecker.Tc.fst"
let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(
# 1214 "FStar.TypeChecker.Tc.fst"
let t = (let _149_674 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _149_674))
in (
# 1215 "FStar.TypeChecker.Tc.fst"
let _64_1726 = (FStar_Syntax_Util.type_u ())
in (match (_64_1726) with
| (k, _64_1725) -> begin
(
# 1216 "FStar.TypeChecker.Tc.fst"
let _64_1732 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_64_1732) with
| (t, _64_1729, _64_1731) -> begin
t
end))
end)))
end)
in (
# 1220 "FStar.TypeChecker.Tc.fst"
let branch_guard = (let _149_675 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _149_675 FStar_Syntax_Util.mk_disj_l))
in (
# 1223 "FStar.TypeChecker.Tc.fst"
let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
in (
# 1229 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (
# 1231 "FStar.TypeChecker.Tc.fst"
let _64_1740 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_676 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _149_676))
end else begin
()
end
in (let _149_677 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_149_677, branch_guard, c, guard)))))
end)))
end))
end))
end))
end)))))
end))
end)))
and check_top_level_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1245 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1248 "FStar.TypeChecker.Tc.fst"
let _64_1757 = (check_let_bound_def true env lb)
in (match (_64_1757) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(
# 1251 "FStar.TypeChecker.Tc.fst"
let _64_1769 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(
# 1254 "FStar.TypeChecker.Tc.fst"
let g1 = (let _149_680 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _149_680 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1255 "FStar.TypeChecker.Tc.fst"
let _64_1764 = (let _149_684 = (let _149_683 = (let _149_682 = (let _149_681 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _149_681))
in (_149_682)::[])
in (FStar_TypeChecker_Util.generalize env _149_683))
in (FStar_List.hd _149_684))
in (match (_64_1764) with
| (_64_1760, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_64_1769) with
| (g1, e1, univ_vars, c1) -> begin
(
# 1259 "FStar.TypeChecker.Tc.fst"
let _64_1779 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(
# 1261 "FStar.TypeChecker.Tc.fst"
let _64_1772 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_64_1772) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(
# 1264 "FStar.TypeChecker.Tc.fst"
let _64_1773 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _149_685 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _149_685 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _149_686 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_149_686, c1)))
end
end))
end else begin
(
# 1268 "FStar.TypeChecker.Tc.fst"
let _64_1775 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _149_687 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _149_687)))
end
in (match (_64_1779) with
| (e2, c1) -> begin
(
# 1273 "FStar.TypeChecker.Tc.fst"
let cres = (let _149_688 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _149_688))
in (
# 1274 "FStar.TypeChecker.Tc.fst"
let _64_1781 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1276 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _149_689 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_149_689, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _64_1785 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1293 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1296 "FStar.TypeChecker.Tc.fst"
let env = (
# 1296 "FStar.TypeChecker.Tc.fst"
let _64_1796 = env
in {FStar_TypeChecker_Env.solver = _64_1796.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_1796.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_1796.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_1796.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_1796.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_1796.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_1796.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_1796.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_1796.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_1796.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_1796.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_1796.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _64_1796.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _64_1796.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _64_1796.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _64_1796.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_1796.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_1796.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_1796.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_1796.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_1796.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1297 "FStar.TypeChecker.Tc.fst"
let _64_1805 = (let _149_693 = (let _149_692 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _149_692 Prims.fst))
in (check_let_bound_def false _149_693 lb))
in (match (_64_1805) with
| (e1, _64_1801, c1, g1, annotated) -> begin
(
# 1298 "FStar.TypeChecker.Tc.fst"
let x = (
# 1298 "FStar.TypeChecker.Tc.fst"
let _64_1806 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _64_1806.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_1806.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (
# 1299 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (
# 1300 "FStar.TypeChecker.Tc.fst"
let _64_1812 = (let _149_695 = (let _149_694 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_694)::[])
in (FStar_Syntax_Subst.open_term _149_695 e2))
in (match (_64_1812) with
| (xb, e2) -> begin
(
# 1301 "FStar.TypeChecker.Tc.fst"
let xbinder = (FStar_List.hd xb)
in (
# 1302 "FStar.TypeChecker.Tc.fst"
let x = (Prims.fst xbinder)
in (
# 1303 "FStar.TypeChecker.Tc.fst"
let _64_1818 = (let _149_696 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _149_696 e2))
in (match (_64_1818) with
| (e2, c2, g2) -> begin
(
# 1304 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (x), c2))
in (
# 1305 "FStar.TypeChecker.Tc.fst"
let e = (let _149_699 = (let _149_698 = (let _149_697 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _149_697))
in FStar_Syntax_Syntax.Tm_let (_149_698))
in (FStar_Syntax_Syntax.mk _149_699 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 1306 "FStar.TypeChecker.Tc.fst"
let x_eq_e1 = (let _149_702 = (let _149_701 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _149_701 e1))
in (FStar_All.pipe_left (fun _149_700 -> FStar_TypeChecker_Common.NonTrivial (_149_700)) _149_702))
in (
# 1307 "FStar.TypeChecker.Tc.fst"
let g2 = (let _149_704 = (let _149_703 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _149_703 g2))
in (FStar_TypeChecker_Rel.close_guard xb _149_704))
in (
# 1309 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if annotated then begin
(e, cres, guard)
end else begin
(
# 1313 "FStar.TypeChecker.Tc.fst"
let _64_1824 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end)))))
end))))
end))))
end)))
end
| _64_1827 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1322 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1325 "FStar.TypeChecker.Tc.fst"
let _64_1839 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_64_1839) with
| (lbs, e2) -> begin
(
# 1327 "FStar.TypeChecker.Tc.fst"
let _64_1842 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_64_1842) with
| (env0, topt) -> begin
(
# 1328 "FStar.TypeChecker.Tc.fst"
let _64_1845 = (build_let_rec_env true env0 lbs)
in (match (_64_1845) with
| (lbs, rec_env) -> begin
(
# 1329 "FStar.TypeChecker.Tc.fst"
let _64_1848 = (check_let_recs rec_env lbs)
in (match (_64_1848) with
| (lbs, g_lbs) -> begin
(
# 1330 "FStar.TypeChecker.Tc.fst"
let g_lbs = (let _149_707 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _149_707 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1332 "FStar.TypeChecker.Tc.fst"
let all_lb_names = (let _149_710 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _149_710 (fun _149_709 -> Some (_149_709))))
in (
# 1334 "FStar.TypeChecker.Tc.fst"
let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(
# 1340 "FStar.TypeChecker.Tc.fst"
let ecs = (let _149_714 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _149_713 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _149_713)))))
in (FStar_TypeChecker_Util.generalize env _149_714))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _64_1859 -> (match (_64_1859) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (
# 1347 "FStar.TypeChecker.Tc.fst"
let cres = (let _149_716 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _149_716))
in (
# 1348 "FStar.TypeChecker.Tc.fst"
let _64_1862 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1350 "FStar.TypeChecker.Tc.fst"
let _64_1866 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_64_1866) with
| (lbs, e2) -> begin
(let _149_718 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _149_717 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_149_718, cres, _149_717)))
end)))))))
end))
end))
end))
end))
end
| _64_1868 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1361 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1364 "FStar.TypeChecker.Tc.fst"
let _64_1880 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_64_1880) with
| (lbs, e2) -> begin
(
# 1366 "FStar.TypeChecker.Tc.fst"
let _64_1883 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_64_1883) with
| (env0, topt) -> begin
(
# 1367 "FStar.TypeChecker.Tc.fst"
let _64_1886 = (build_let_rec_env false env0 lbs)
in (match (_64_1886) with
| (lbs, rec_env) -> begin
(
# 1368 "FStar.TypeChecker.Tc.fst"
let _64_1889 = (check_let_recs rec_env lbs)
in (match (_64_1889) with
| (lbs, g_lbs) -> begin
(
# 1370 "FStar.TypeChecker.Tc.fst"
let _64_1901 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (
# 1371 "FStar.TypeChecker.Tc.fst"
let x = (
# 1371 "FStar.TypeChecker.Tc.fst"
let _64_1892 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _64_1892.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_1892.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (
# 1372 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1372 "FStar.TypeChecker.Tc.fst"
let _64_1895 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _64_1895.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _64_1895.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _64_1895.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _64_1895.FStar_Syntax_Syntax.lbdef})
in (
# 1373 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], lb.FStar_Syntax_Syntax.lbtyp))
in (env, lb))))) env))
in (match (_64_1901) with
| (env, lbs) -> begin
(
# 1376 "FStar.TypeChecker.Tc.fst"
let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (
# 1378 "FStar.TypeChecker.Tc.fst"
let _64_1907 = (tc_term env e2)
in (match (_64_1907) with
| (e2, cres, g2) -> begin
(
# 1379 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (
# 1380 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (
# 1381 "FStar.TypeChecker.Tc.fst"
let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (
# 1382 "FStar.TypeChecker.Tc.fst"
let cres = (
# 1382 "FStar.TypeChecker.Tc.fst"
let _64_1911 = cres
in {FStar_Syntax_Syntax.eff_name = _64_1911.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _64_1911.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _64_1911.FStar_Syntax_Syntax.comp})
in (
# 1384 "FStar.TypeChecker.Tc.fst"
let _64_1916 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_64_1916) with
| (lbs, e2) -> begin
(
# 1385 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_64_1919) -> begin
(e, cres, guard)
end
| None -> begin
(
# 1389 "FStar.TypeChecker.Tc.fst"
let _64_1922 = (check_no_escape None env bvs tres)
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
| _64_1925 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (
# 1400 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1401 "FStar.TypeChecker.Tc.fst"
let _64_1958 = (FStar_List.fold_left (fun _64_1932 lb -> (match (_64_1932) with
| (lbs, env) -> begin
(
# 1402 "FStar.TypeChecker.Tc.fst"
let _64_1937 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_64_1937) with
| (univ_vars, t, check_t) -> begin
(
# 1403 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (
# 1404 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (
# 1405 "FStar.TypeChecker.Tc.fst"
let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(
# 1410 "FStar.TypeChecker.Tc.fst"
let _64_1946 = (let _149_730 = (let _149_729 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _149_729))
in (tc_check_tot_or_gtot_term (
# 1410 "FStar.TypeChecker.Tc.fst"
let _64_1940 = env0
in {FStar_TypeChecker_Env.solver = _64_1940.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_1940.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_1940.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_1940.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_1940.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_1940.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_1940.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_1940.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_1940.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_1940.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_1940.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_1940.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _64_1940.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _64_1940.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _64_1940.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _64_1940.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_1940.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_1940.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_1940.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_1940.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_1940.FStar_TypeChecker_Env.use_bv_sorts}) t _149_730))
in (match (_64_1946) with
| (t, _64_1944, g) -> begin
(
# 1411 "FStar.TypeChecker.Tc.fst"
let _64_1947 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (
# 1413 "FStar.TypeChecker.Tc.fst"
let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(
# 1415 "FStar.TypeChecker.Tc.fst"
let _64_1950 = env
in {FStar_TypeChecker_Env.solver = _64_1950.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_1950.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_1950.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_1950.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_1950.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_1950.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_1950.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_1950.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_1950.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_1950.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_1950.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_1950.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _64_1950.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _64_1950.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _64_1950.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _64_1950.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_1950.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_1950.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_1950.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_1950.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_1950.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (
# 1417 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1417 "FStar.TypeChecker.Tc.fst"
let _64_1953 = lb
in {FStar_Syntax_Syntax.lbname = _64_1953.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _64_1953.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_64_1958) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (
# 1424 "FStar.TypeChecker.Tc.fst"
let _64_1971 = (let _149_735 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 1425 "FStar.TypeChecker.Tc.fst"
let _64_1965 = (let _149_734 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _149_734 lb.FStar_Syntax_Syntax.lbdef))
in (match (_64_1965) with
| (e, c, g) -> begin
(
# 1426 "FStar.TypeChecker.Tc.fst"
let _64_1966 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1428 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _149_735 FStar_List.unzip))
in (match (_64_1971) with
| (lbs, gs) -> begin
(
# 1430 "FStar.TypeChecker.Tc.fst"
let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (
# 1444 "FStar.TypeChecker.Tc.fst"
let _64_1979 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_64_1979) with
| (env1, _64_1978) -> begin
(
# 1445 "FStar.TypeChecker.Tc.fst"
let e1 = lb.FStar_Syntax_Syntax.lbdef
in (
# 1448 "FStar.TypeChecker.Tc.fst"
let _64_1985 = (check_lbtyp top_level env lb)
in (match (_64_1985) with
| (topt, wf_annot, univ_vars, env1) -> begin
(
# 1450 "FStar.TypeChecker.Tc.fst"
let _64_1986 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1454 "FStar.TypeChecker.Tc.fst"
let _64_1993 = (tc_maybe_toplevel_term (
# 1454 "FStar.TypeChecker.Tc.fst"
let _64_1988 = env1
in {FStar_TypeChecker_Env.solver = _64_1988.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_1988.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_1988.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_1988.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_1988.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_1988.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_1988.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_1988.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_1988.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_1988.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_1988.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_1988.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _64_1988.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _64_1988.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _64_1988.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _64_1988.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_1988.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_1988.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_1988.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_1988.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_1988.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_64_1993) with
| (e1, c1, g1) -> begin
(
# 1457 "FStar.TypeChecker.Tc.fst"
let _64_1997 = (let _149_742 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _64_1994 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _149_742 e1 c1 wf_annot))
in (match (_64_1997) with
| (c1, guard_f) -> begin
(
# 1460 "FStar.TypeChecker.Tc.fst"
let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (
# 1462 "FStar.TypeChecker.Tc.fst"
let _64_1999 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _149_743 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _149_743))
end else begin
()
end
in (let _149_744 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _149_744))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (
# 1474 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 1477 "FStar.TypeChecker.Tc.fst"
let _64_2006 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _64_2009 -> begin
(
# 1481 "FStar.TypeChecker.Tc.fst"
let _64_2012 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_64_2012) with
| (univ_vars, t) -> begin
(
# 1482 "FStar.TypeChecker.Tc.fst"
let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _149_748 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _149_748))
end else begin
(
# 1489 "FStar.TypeChecker.Tc.fst"
let _64_2017 = (FStar_Syntax_Util.type_u ())
in (match (_64_2017) with
| (k, _64_2016) -> begin
(
# 1490 "FStar.TypeChecker.Tc.fst"
let _64_2022 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_64_2022) with
| (t, _64_2020, g) -> begin
(
# 1491 "FStar.TypeChecker.Tc.fst"
let _64_2023 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _149_751 = (let _149_749 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _149_749))
in (let _149_750 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _149_751 _149_750)))
end else begin
()
end
in (
# 1495 "FStar.TypeChecker.Tc.fst"
let t = (norm env1 t)
in (let _149_752 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _149_752))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _64_2029 -> (match (_64_2029) with
| (x, imp) -> begin
(
# 1500 "FStar.TypeChecker.Tc.fst"
let _64_2032 = (FStar_Syntax_Util.type_u ())
in (match (_64_2032) with
| (tu, u) -> begin
(
# 1501 "FStar.TypeChecker.Tc.fst"
let _64_2037 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_64_2037) with
| (t, _64_2035, g) -> begin
(
# 1502 "FStar.TypeChecker.Tc.fst"
let x = ((
# 1502 "FStar.TypeChecker.Tc.fst"
let _64_2038 = x
in {FStar_Syntax_Syntax.ppname = _64_2038.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_2038.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (
# 1503 "FStar.TypeChecker.Tc.fst"
let _64_2041 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_756 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _149_755 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _149_756 _149_755)))
end else begin
()
end
in (let _149_757 = (maybe_push_binding env x)
in (x, _149_757, g, u))))
end))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe Prims.list) = (fun env bs -> (
# 1508 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_TypeChecker_Rel.trivial_guard, [])
end
| b::bs -> begin
(
# 1511 "FStar.TypeChecker.Tc.fst"
let _64_2056 = (tc_binder env b)
in (match (_64_2056) with
| (b, env', g, u) -> begin
(
# 1512 "FStar.TypeChecker.Tc.fst"
let _64_2061 = (aux env' bs)
in (match (_64_2061) with
| (bs, env', g', us) -> begin
(let _149_765 = (let _149_764 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _149_764))
in ((b)::bs, env', _149_765, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (
# 1517 "FStar.TypeChecker.Tc.fst"
let tc_args = (fun env args -> (FStar_List.fold_right (fun _64_2069 _64_2072 -> (match ((_64_2069, _64_2072)) with
| ((t, imp), (args, g)) -> begin
(
# 1521 "FStar.TypeChecker.Tc.fst"
let _64_2077 = (tc_term env t)
in (match (_64_2077) with
| (t, _64_2075, g') -> begin
(let _149_774 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _149_774))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _64_2081 -> (match (_64_2081) with
| (pats, g) -> begin
(
# 1524 "FStar.TypeChecker.Tc.fst"
let _64_2084 = (tc_args env p)
in (match (_64_2084) with
| (args, g') -> begin
(let _149_777 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _149_777))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1529 "FStar.TypeChecker.Tc.fst"
let _64_2090 = (tc_maybe_toplevel_term env e)
in (match (_64_2090) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(
# 1532 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (
# 1533 "FStar.TypeChecker.Tc.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 1534 "FStar.TypeChecker.Tc.fst"
let _64_2093 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_780 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _149_780))
end else begin
()
end
in (
# 1535 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 1536 "FStar.TypeChecker.Tc.fst"
let _64_2098 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _149_781 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_149_781, false))
end else begin
(let _149_782 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_149_782, true))
end
in (match (_64_2098) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _149_783 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _149_783))
end
| _64_2102 -> begin
if allow_ghost then begin
(let _149_786 = (let _149_785 = (let _149_784 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_149_784, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_149_785))
in (Prims.raise _149_786))
end else begin
(let _149_789 = (let _149_788 = (let _149_787 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_149_787, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_149_788))
in (Prims.raise _149_789))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 1550 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))

# 1551 "FStar.TypeChecker.Tc.fst"
let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (
# 1555 "FStar.TypeChecker.Tc.fst"
let _64_2112 = (tc_tot_or_gtot_term env t)
in (match (_64_2112) with
| (t, c, g) -> begin
(
# 1556 "FStar.TypeChecker.Tc.fst"
let _64_2113 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))

# 1557 "FStar.TypeChecker.Tc.fst"
let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (
# 1560 "FStar.TypeChecker.Tc.fst"
let _64_2121 = (tc_check_tot_or_gtot_term env t k)
in (match (_64_2121) with
| (t, c, g) -> begin
(
# 1561 "FStar.TypeChecker.Tc.fst"
let _64_2122 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))

# 1562 "FStar.TypeChecker.Tc.fst"
let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _149_809 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _149_809)))

# 1565 "FStar.TypeChecker.Tc.fst"
let check_nogen = (fun env t k -> (
# 1568 "FStar.TypeChecker.Tc.fst"
let t = (tc_check_trivial_guard env t k)
in (let _149_813 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _149_813))))

# 1569 "FStar.TypeChecker.Tc.fst"
let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (
# 1572 "FStar.TypeChecker.Tc.fst"
let _64_2137 = (tc_binders env tps)
in (match (_64_2137) with
| (tps, env, g, us) -> begin
(
# 1573 "FStar.TypeChecker.Tc.fst"
let _64_2138 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))

# 1574 "FStar.TypeChecker.Tc.fst"
let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (
# 1577 "FStar.TypeChecker.Tc.fst"
let fail = (fun _64_2144 -> (match (()) with
| () -> begin
(let _149_828 = (let _149_827 = (let _149_826 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_149_826, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_149_827))
in (Prims.raise _149_828))
end))
in (
# 1578 "FStar.TypeChecker.Tc.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1581 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _64_2161)::(wp, _64_2157)::(_wlp, _64_2153)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _64_2165 -> begin
(fail ())
end))
end
| _64_2167 -> begin
(fail ())
end))))

# 1586 "FStar.TypeChecker.Tc.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 1591 "FStar.TypeChecker.Tc.fst"
let _64_2174 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_64_2174) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _64_2176 -> begin
(
# 1594 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow binders c)
in (
# 1595 "FStar.TypeChecker.Tc.fst"
let _64_2180 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_64_2180) with
| (uvs, t') -> begin
(match ((let _149_835 = (FStar_Syntax_Subst.compress t')
in _149_835.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _64_2186 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 1598 "FStar.TypeChecker.Tc.fst"
let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (
# 1601 "FStar.TypeChecker.Tc.fst"
let fail = (fun t -> (let _149_846 = (let _149_845 = (let _149_844 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_149_844, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_149_845))
in (Prims.raise _149_846)))
in (match ((let _149_847 = (FStar_Syntax_Subst.compress signature)
in _149_847.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1604 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _64_2207)::(wp, _64_2203)::(_wlp, _64_2199)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _64_2211 -> begin
(fail signature)
end))
end
| _64_2213 -> begin
(fail signature)
end)))

# 1609 "FStar.TypeChecker.Tc.fst"
let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (
# 1612 "FStar.TypeChecker.Tc.fst"
let _64_2218 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_64_2218) with
| (a, wp) -> begin
(
# 1613 "FStar.TypeChecker.Tc.fst"
let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _64_2221 -> begin
(
# 1617 "FStar.TypeChecker.Tc.fst"
let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (
# 1618 "FStar.TypeChecker.Tc.fst"
let op = (fun ts -> (
# 1619 "FStar.TypeChecker.Tc.fst"
let _64_2225 = ()
in (
# 1620 "FStar.TypeChecker.Tc.fst"
let t0 = (Prims.snd ts)
in (
# 1621 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (
# 1623 "FStar.TypeChecker.Tc.fst"
let _64_2229 = ed
in (let _149_866 = (op ed.FStar_Syntax_Syntax.ret)
in (let _149_865 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _149_864 = (op ed.FStar_Syntax_Syntax.bind_wlp)
in (let _149_863 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _149_862 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _149_861 = (op ed.FStar_Syntax_Syntax.ite_wlp)
in (let _149_860 = (op ed.FStar_Syntax_Syntax.wp_binop)
in (let _149_859 = (op ed.FStar_Syntax_Syntax.wp_as_type)
in (let _149_858 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _149_857 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _149_856 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _149_855 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _149_854 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _64_2229.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _64_2229.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _64_2229.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _64_2229.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _64_2229.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _149_866; FStar_Syntax_Syntax.bind_wp = _149_865; FStar_Syntax_Syntax.bind_wlp = _149_864; FStar_Syntax_Syntax.if_then_else = _149_863; FStar_Syntax_Syntax.ite_wp = _149_862; FStar_Syntax_Syntax.ite_wlp = _149_861; FStar_Syntax_Syntax.wp_binop = _149_860; FStar_Syntax_Syntax.wp_as_type = _149_859; FStar_Syntax_Syntax.close_wp = _149_858; FStar_Syntax_Syntax.assert_p = _149_857; FStar_Syntax_Syntax.assume_p = _149_856; FStar_Syntax_Syntax.null_wp = _149_855; FStar_Syntax_Syntax.trivial = _149_854}))))))))))))))))
end)
in (ed, a, wp))
end)))

# 1637 "FStar.TypeChecker.Tc.fst"
let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (
# 1640 "FStar.TypeChecker.Tc.fst"
let _64_2234 = ()
in (
# 1641 "FStar.TypeChecker.Tc.fst"
let _64_2238 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_64_2238) with
| (binders_un, signature_un) -> begin
(
# 1642 "FStar.TypeChecker.Tc.fst"
let _64_2243 = (tc_tparams env0 binders_un)
in (match (_64_2243) with
| (binders, env, _64_2242) -> begin
(
# 1643 "FStar.TypeChecker.Tc.fst"
let _64_2247 = (tc_trivial_guard env signature_un)
in (match (_64_2247) with
| (signature, _64_2246) -> begin
(
# 1644 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1644 "FStar.TypeChecker.Tc.fst"
let _64_2248 = ed
in {FStar_Syntax_Syntax.qualifiers = _64_2248.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _64_2248.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _64_2248.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _64_2248.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _64_2248.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _64_2248.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = _64_2248.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _64_2248.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _64_2248.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = _64_2248.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _64_2248.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _64_2248.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _64_2248.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _64_2248.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _64_2248.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _64_2248.FStar_Syntax_Syntax.trivial})
in (
# 1647 "FStar.TypeChecker.Tc.fst"
let _64_2254 = (open_effect_decl env ed)
in (match (_64_2254) with
| (ed, a, wp_a) -> begin
(
# 1648 "FStar.TypeChecker.Tc.fst"
let get_effect_signature = (fun _64_2256 -> (match (()) with
| () -> begin
(
# 1649 "FStar.TypeChecker.Tc.fst"
let _64_2260 = (tc_trivial_guard env signature_un)
in (match (_64_2260) with
| (signature, _64_2259) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (
# 1653 "FStar.TypeChecker.Tc.fst"
let env = (let _149_873 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _149_873))
in (
# 1655 "FStar.TypeChecker.Tc.fst"
let _64_2262 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _149_876 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _149_875 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _149_874 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checked effect signature: %s %s : %s\n" _149_876 _149_875 _149_874))))
end else begin
()
end
in (
# 1661 "FStar.TypeChecker.Tc.fst"
let check_and_gen' = (fun env _64_2269 k -> (match (_64_2269) with
| (_64_2267, t) -> begin
(check_and_gen env t k)
end))
in (
# 1664 "FStar.TypeChecker.Tc.fst"
let ret = (
# 1665 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_888 = (let _149_886 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_885 = (let _149_884 = (let _149_883 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _149_883))
in (_149_884)::[])
in (_149_886)::_149_885))
in (let _149_887 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _149_888 _149_887)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (
# 1668 "FStar.TypeChecker.Tc.fst"
let bind_wp = (
# 1669 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1670 "FStar.TypeChecker.Tc.fst"
let _64_2276 = (get_effect_signature ())
in (match (_64_2276) with
| (b, wp_b) -> begin
(
# 1671 "FStar.TypeChecker.Tc.fst"
let a_wp_b = (let _149_892 = (let _149_890 = (let _149_889 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _149_889))
in (_149_890)::[])
in (let _149_891 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _149_892 _149_891)))
in (
# 1672 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = a_wp_b
in (
# 1673 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_905 = (let _149_903 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_902 = (let _149_901 = (FStar_Syntax_Syntax.mk_binder b)
in (let _149_900 = (let _149_899 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _149_898 = (let _149_897 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _149_896 = (let _149_895 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (let _149_894 = (let _149_893 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_149_893)::[])
in (_149_895)::_149_894))
in (_149_897)::_149_896))
in (_149_899)::_149_898))
in (_149_901)::_149_900))
in (_149_903)::_149_902))
in (let _149_904 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _149_905 _149_904)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k))))
end)))
in (
# 1679 "FStar.TypeChecker.Tc.fst"
let bind_wlp = (
# 1680 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1681 "FStar.TypeChecker.Tc.fst"
let _64_2284 = (get_effect_signature ())
in (match (_64_2284) with
| (b, wlp_b) -> begin
(
# 1682 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = (let _149_909 = (let _149_907 = (let _149_906 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _149_906))
in (_149_907)::[])
in (let _149_908 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _149_909 _149_908)))
in (
# 1683 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_918 = (let _149_916 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_915 = (let _149_914 = (FStar_Syntax_Syntax.mk_binder b)
in (let _149_913 = (let _149_912 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _149_911 = (let _149_910 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_149_910)::[])
in (_149_912)::_149_911))
in (_149_914)::_149_913))
in (_149_916)::_149_915))
in (let _149_917 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _149_918 _149_917)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wlp expected_k)))
end)))
in (
# 1689 "FStar.TypeChecker.Tc.fst"
let if_then_else = (
# 1690 "FStar.TypeChecker.Tc.fst"
let p = (let _149_920 = (let _149_919 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _149_919 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _149_920))
in (
# 1691 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_929 = (let _149_927 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_926 = (let _149_925 = (FStar_Syntax_Syntax.mk_binder p)
in (let _149_924 = (let _149_923 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _149_922 = (let _149_921 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_149_921)::[])
in (_149_923)::_149_922))
in (_149_925)::_149_924))
in (_149_927)::_149_926))
in (let _149_928 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_929 _149_928)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (
# 1697 "FStar.TypeChecker.Tc.fst"
let ite_wp = (
# 1698 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1699 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_936 = (let _149_934 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_933 = (let _149_932 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _149_931 = (let _149_930 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_149_930)::[])
in (_149_932)::_149_931))
in (_149_934)::_149_933))
in (let _149_935 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_936 _149_935)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k)))
in (
# 1705 "FStar.TypeChecker.Tc.fst"
let ite_wlp = (
# 1706 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1707 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_941 = (let _149_939 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_938 = (let _149_937 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (_149_937)::[])
in (_149_939)::_149_938))
in (let _149_940 = (FStar_Syntax_Syntax.mk_Total wlp_a)
in (FStar_Syntax_Util.arrow _149_941 _149_940)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wlp expected_k)))
in (
# 1712 "FStar.TypeChecker.Tc.fst"
let wp_binop = (
# 1713 "FStar.TypeChecker.Tc.fst"
let bin_op = (
# 1714 "FStar.TypeChecker.Tc.fst"
let _64_2299 = (FStar_Syntax_Util.type_u ())
in (match (_64_2299) with
| (t1, u1) -> begin
(
# 1715 "FStar.TypeChecker.Tc.fst"
let _64_2302 = (FStar_Syntax_Util.type_u ())
in (match (_64_2302) with
| (t2, u2) -> begin
(
# 1716 "FStar.TypeChecker.Tc.fst"
let t = (let _149_942 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_max ((u1)::(u2)::[]))) None _149_942))
in (let _149_947 = (let _149_945 = (FStar_Syntax_Syntax.null_binder t1)
in (let _149_944 = (let _149_943 = (FStar_Syntax_Syntax.null_binder t2)
in (_149_943)::[])
in (_149_945)::_149_944))
in (let _149_946 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _149_947 _149_946))))
end))
end))
in (
# 1718 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_956 = (let _149_954 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_953 = (let _149_952 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _149_951 = (let _149_950 = (FStar_Syntax_Syntax.null_binder bin_op)
in (let _149_949 = (let _149_948 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_149_948)::[])
in (_149_950)::_149_949))
in (_149_952)::_149_951))
in (_149_954)::_149_953))
in (let _149_955 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_956 _149_955)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_binop expected_k)))
in (
# 1725 "FStar.TypeChecker.Tc.fst"
let wp_as_type = (
# 1726 "FStar.TypeChecker.Tc.fst"
let _64_2310 = (FStar_Syntax_Util.type_u ())
in (match (_64_2310) with
| (t, _64_2309) -> begin
(
# 1727 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_961 = (let _149_959 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_958 = (let _149_957 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_149_957)::[])
in (_149_959)::_149_958))
in (let _149_960 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _149_961 _149_960)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (
# 1732 "FStar.TypeChecker.Tc.fst"
let close_wp = (
# 1733 "FStar.TypeChecker.Tc.fst"
let b = (let _149_963 = (let _149_962 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _149_962 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _149_963))
in (
# 1734 "FStar.TypeChecker.Tc.fst"
let b_wp_a = (let _149_967 = (let _149_965 = (let _149_964 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _149_964))
in (_149_965)::[])
in (let _149_966 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_967 _149_966)))
in (
# 1735 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_974 = (let _149_972 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_971 = (let _149_970 = (FStar_Syntax_Syntax.mk_binder b)
in (let _149_969 = (let _149_968 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_149_968)::[])
in (_149_970)::_149_969))
in (_149_972)::_149_971))
in (let _149_973 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_974 _149_973)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (
# 1739 "FStar.TypeChecker.Tc.fst"
let assert_p = (
# 1740 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_983 = (let _149_981 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_980 = (let _149_979 = (let _149_976 = (let _149_975 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _149_975 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _149_976))
in (let _149_978 = (let _149_977 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_149_977)::[])
in (_149_979)::_149_978))
in (_149_981)::_149_980))
in (let _149_982 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_983 _149_982)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (
# 1746 "FStar.TypeChecker.Tc.fst"
let assume_p = (
# 1747 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_992 = (let _149_990 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_989 = (let _149_988 = (let _149_985 = (let _149_984 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _149_984 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _149_985))
in (let _149_987 = (let _149_986 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_149_986)::[])
in (_149_988)::_149_987))
in (_149_990)::_149_989))
in (let _149_991 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_992 _149_991)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (
# 1753 "FStar.TypeChecker.Tc.fst"
let null_wp = (
# 1754 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_995 = (let _149_993 = (FStar_Syntax_Syntax.mk_binder a)
in (_149_993)::[])
in (let _149_994 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_995 _149_994)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (
# 1758 "FStar.TypeChecker.Tc.fst"
let trivial_wp = (
# 1759 "FStar.TypeChecker.Tc.fst"
let _64_2326 = (FStar_Syntax_Util.type_u ())
in (match (_64_2326) with
| (t, _64_2325) -> begin
(
# 1760 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_1000 = (let _149_998 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_997 = (let _149_996 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_149_996)::[])
in (_149_998)::_149_997))
in (let _149_999 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _149_1000 _149_999)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (
# 1766 "FStar.TypeChecker.Tc.fst"
let t = (let _149_1001 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _149_1001))
in (
# 1767 "FStar.TypeChecker.Tc.fst"
let _64_2332 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_64_2332) with
| (univs, t) -> begin
(
# 1768 "FStar.TypeChecker.Tc.fst"
let _64_2348 = (match ((let _149_1003 = (let _149_1002 = (FStar_Syntax_Subst.compress t)
in _149_1002.FStar_Syntax_Syntax.n)
in (binders, _149_1003))) with
| ([], _64_2335) -> begin
([], t)
end
| (_64_2338, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _64_2345 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_64_2348) with
| (binders, signature) -> begin
(
# 1772 "FStar.TypeChecker.Tc.fst"
let close = (fun ts -> (let _149_1006 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _149_1006)))
in (
# 1773 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1773 "FStar.TypeChecker.Tc.fst"
let _64_2351 = ed
in (let _149_1019 = (close ret)
in (let _149_1018 = (close bind_wp)
in (let _149_1017 = (close bind_wlp)
in (let _149_1016 = (close if_then_else)
in (let _149_1015 = (close ite_wp)
in (let _149_1014 = (close ite_wlp)
in (let _149_1013 = (close wp_binop)
in (let _149_1012 = (close wp_as_type)
in (let _149_1011 = (close close_wp)
in (let _149_1010 = (close assert_p)
in (let _149_1009 = (close assume_p)
in (let _149_1008 = (close null_wp)
in (let _149_1007 = (close trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _64_2351.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _64_2351.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _149_1019; FStar_Syntax_Syntax.bind_wp = _149_1018; FStar_Syntax_Syntax.bind_wlp = _149_1017; FStar_Syntax_Syntax.if_then_else = _149_1016; FStar_Syntax_Syntax.ite_wp = _149_1015; FStar_Syntax_Syntax.ite_wlp = _149_1014; FStar_Syntax_Syntax.wp_binop = _149_1013; FStar_Syntax_Syntax.wp_as_type = _149_1012; FStar_Syntax_Syntax.close_wp = _149_1011; FStar_Syntax_Syntax.assert_p = _149_1010; FStar_Syntax_Syntax.assume_p = _149_1009; FStar_Syntax_Syntax.null_wp = _149_1008; FStar_Syntax_Syntax.trivial = _149_1007}))))))))))))))
in (
# 1791 "FStar.TypeChecker.Tc.fst"
let _64_2354 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_1020 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _149_1020))
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

# 1793 "FStar.TypeChecker.Tc.fst"
let tc_lex_t = (fun env ses quals lids -> (
# 1802 "FStar.TypeChecker.Tc.fst"
let _64_2360 = ()
in (
# 1803 "FStar.TypeChecker.Tc.fst"
let _64_2368 = ()
in (match (ses) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _64_2397, _64_2399, [], r)::FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _64_2388, r1)::FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _64_2377, r2)::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(
# 1818 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (
# 1819 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (
# 1820 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (
# 1821 "FStar.TypeChecker.Tc.fst"
let tc = FStar_Syntax_Syntax.Sig_inductive_typ ((lex_t, (u)::[], [], t, [], (FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[], [], r))
in (
# 1823 "FStar.TypeChecker.Tc.fst"
let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (
# 1824 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (let _149_1028 = (let _149_1027 = (let _149_1026 = (let _149_1025 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _149_1025 FStar_Syntax_Syntax.Delta_constant None))
in (_149_1026, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_149_1027))
in (FStar_Syntax_Syntax.mk _149_1028 None r1))
in (
# 1825 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (
# 1826 "FStar.TypeChecker.Tc.fst"
let dc_lextop = FStar_Syntax_Syntax.Sig_datacon ((lex_top, (utop)::[], lex_top_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r1))
in (
# 1828 "FStar.TypeChecker.Tc.fst"
let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1829 "FStar.TypeChecker.Tc.fst"
let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1830 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (
# 1831 "FStar.TypeChecker.Tc.fst"
let a = (let _149_1029 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _149_1029))
in (
# 1832 "FStar.TypeChecker.Tc.fst"
let hd = (let _149_1030 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _149_1030))
in (
# 1833 "FStar.TypeChecker.Tc.fst"
let tl = (let _149_1035 = (let _149_1034 = (let _149_1033 = (let _149_1032 = (let _149_1031 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _149_1031 FStar_Syntax_Syntax.Delta_constant None))
in (_149_1032, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_149_1033))
in (FStar_Syntax_Syntax.mk _149_1034 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _149_1035))
in (
# 1834 "FStar.TypeChecker.Tc.fst"
let res = (let _149_1039 = (let _149_1038 = (let _149_1037 = (let _149_1036 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _149_1036 FStar_Syntax_Syntax.Delta_constant None))
in (_149_1037, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_149_1038))
in (FStar_Syntax_Syntax.mk _149_1039 None r2))
in (let _149_1040 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _149_1040))))))
in (
# 1836 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (
# 1837 "FStar.TypeChecker.Tc.fst"
let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _149_1042 = (let _149_1041 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _149_1041))
in FStar_Syntax_Syntax.Sig_bundle (_149_1042)))))))))))))))
end
| _64_2423 -> begin
(let _149_1044 = (let _149_1043 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _149_1043))
in (FStar_All.failwith _149_1044))
end))))

# 1841 "FStar.TypeChecker.Tc.fst"
let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (
# 1906 "FStar.TypeChecker.Tc.fst"
let warn_positivity = (fun l r -> (let _149_1058 = (let _149_1057 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _149_1057))
in (FStar_TypeChecker_Errors.diag r _149_1058)))
in (
# 1908 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1911 "FStar.TypeChecker.Tc.fst"
let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(
# 1916 "FStar.TypeChecker.Tc.fst"
let _64_2445 = ()
in (
# 1917 "FStar.TypeChecker.Tc.fst"
let _64_2447 = (warn_positivity tc r)
in (
# 1918 "FStar.TypeChecker.Tc.fst"
let _64_2451 = (FStar_Syntax_Subst.open_term tps k)
in (match (_64_2451) with
| (tps, k) -> begin
(
# 1919 "FStar.TypeChecker.Tc.fst"
let _64_2455 = (tc_tparams env tps)
in (match (_64_2455) with
| (tps, env_tps, us) -> begin
(
# 1920 "FStar.TypeChecker.Tc.fst"
let _64_2458 = (FStar_Syntax_Util.arrow_formals k)
in (match (_64_2458) with
| (indices, t) -> begin
(
# 1921 "FStar.TypeChecker.Tc.fst"
let _64_2462 = (tc_tparams env_tps indices)
in (match (_64_2462) with
| (indices, env', us') -> begin
(
# 1922 "FStar.TypeChecker.Tc.fst"
let _64_2466 = (tc_trivial_guard env' t)
in (match (_64_2466) with
| (t, _64_2465) -> begin
(
# 1923 "FStar.TypeChecker.Tc.fst"
let k = (let _149_1063 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _149_1063))
in (
# 1924 "FStar.TypeChecker.Tc.fst"
let _64_2470 = (FStar_Syntax_Util.type_u ())
in (match (_64_2470) with
| (t_type, u) -> begin
(
# 1925 "FStar.TypeChecker.Tc.fst"
let _64_2471 = (let _149_1064 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _149_1064))
in (
# 1927 "FStar.TypeChecker.Tc.fst"
let t_tc = (let _149_1065 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _149_1065))
in (
# 1928 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 1929 "FStar.TypeChecker.Tc.fst"
let k = (FStar_Syntax_Subst.close tps k)
in (
# 1930 "FStar.TypeChecker.Tc.fst"
let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _149_1066 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) ([], t_tc))
in (_149_1066, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u)))))))
end)))
end))
end))
end))
end))
end))))
end
| _64_2478 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1937 "FStar.TypeChecker.Tc.fst"
let positive_if_pure = (fun _64_2480 l -> ())
in (
# 1940 "FStar.TypeChecker.Tc.fst"
let tc_data = (fun env tcs _64_6 -> (match (_64_6) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(
# 1942 "FStar.TypeChecker.Tc.fst"
let _64_2497 = ()
in (
# 1944 "FStar.TypeChecker.Tc.fst"
let _64_2532 = (
# 1945 "FStar.TypeChecker.Tc.fst"
let tps_u_opt = (FStar_Util.find_map tcs (fun _64_2501 -> (match (_64_2501) with
| (se, u_tc) -> begin
if (let _149_1079 = (let _149_1078 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _149_1078))
in (FStar_Ident.lid_equals tc_lid _149_1079)) then begin
(
# 1947 "FStar.TypeChecker.Tc.fst"
let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_64_2503, _64_2505, tps, _64_2508, _64_2510, _64_2512, _64_2514, _64_2516) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _64_2522 -> (match (_64_2522) with
| (x, _64_2521) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _64_2524 -> begin
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
in (match (_64_2532) with
| (tps, u_tc) -> begin
(
# 1960 "FStar.TypeChecker.Tc.fst"
let _64_2552 = (match ((let _149_1081 = (FStar_Syntax_Subst.compress t)
in _149_1081.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(
# 1965 "FStar.TypeChecker.Tc.fst"
let _64_2540 = (FStar_Util.first_N ntps bs)
in (match (_64_2540) with
| (_64_2538, bs') -> begin
(
# 1966 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (
# 1967 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _64_2546 -> (match (_64_2546) with
| (x, _64_2545) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _149_1084 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _149_1084))))
end))
end
| _64_2549 -> begin
([], t)
end)
in (match (_64_2552) with
| (arguments, result) -> begin
(
# 1971 "FStar.TypeChecker.Tc.fst"
let _64_2553 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_1087 = (FStar_Syntax_Print.lid_to_string c)
in (let _149_1086 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _149_1085 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _149_1087 _149_1086 _149_1085))))
end else begin
()
end
in (
# 1977 "FStar.TypeChecker.Tc.fst"
let _64_2558 = (tc_tparams env arguments)
in (match (_64_2558) with
| (arguments, env', us) -> begin
(
# 1978 "FStar.TypeChecker.Tc.fst"
let _64_2562 = (tc_trivial_guard env' result)
in (match (_64_2562) with
| (result, _64_2561) -> begin
(
# 1979 "FStar.TypeChecker.Tc.fst"
let _64_2566 = (FStar_Syntax_Util.head_and_args result)
in (match (_64_2566) with
| (head, _64_2565) -> begin
(
# 1980 "FStar.TypeChecker.Tc.fst"
let _64_2571 = (match ((let _149_1088 = (FStar_Syntax_Subst.compress head)
in _149_1088.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _64_2570 -> begin
(let _149_1092 = (let _149_1091 = (let _149_1090 = (let _149_1089 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _149_1089))
in (_149_1090, r))
in FStar_Syntax_Syntax.Error (_149_1091))
in (Prims.raise _149_1092))
end)
in (
# 1983 "FStar.TypeChecker.Tc.fst"
let g = (FStar_List.fold_left2 (fun g _64_2577 u_x -> (match (_64_2577) with
| (x, _64_2576) -> begin
(
# 1984 "FStar.TypeChecker.Tc.fst"
let _64_2579 = ()
in (let _149_1096 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _149_1096)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (
# 1990 "FStar.TypeChecker.Tc.fst"
let t = (let _149_1100 = (let _149_1098 = (FStar_All.pipe_right tps (FStar_List.map (fun _64_2585 -> (match (_64_2585) with
| (x, _64_2584) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _149_1098 arguments))
in (let _149_1099 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _149_1100 _149_1099)))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _64_2588 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1998 "FStar.TypeChecker.Tc.fst"
let generalize_and_inst_within = (fun env g tcs datas -> (
# 1999 "FStar.TypeChecker.Tc.fst"
let _64_2594 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2000 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _64_7 -> (match (_64_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_64_2598, _64_2600, tps, k, _64_2604, _64_2606, _64_2608, _64_2610) -> begin
(let _149_1111 = (let _149_1110 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _149_1110))
in (FStar_Syntax_Syntax.null_binder _149_1111))
end
| _64_2614 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2003 "FStar.TypeChecker.Tc.fst"
let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _64_8 -> (match (_64_8) with
| FStar_Syntax_Syntax.Sig_datacon (_64_2618, _64_2620, t, _64_2623, _64_2625, _64_2627, _64_2629, _64_2631) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _64_2635 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2006 "FStar.TypeChecker.Tc.fst"
let t = (let _149_1113 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _149_1113))
in (
# 2007 "FStar.TypeChecker.Tc.fst"
let _64_2638 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_1114 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _149_1114))
end else begin
()
end
in (
# 2008 "FStar.TypeChecker.Tc.fst"
let _64_2642 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_64_2642) with
| (uvs, t) -> begin
(
# 2009 "FStar.TypeChecker.Tc.fst"
let _64_2644 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_1118 = (let _149_1116 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _149_1116 (FStar_String.concat ", ")))
in (let _149_1117 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _149_1118 _149_1117)))
end else begin
()
end
in (
# 2012 "FStar.TypeChecker.Tc.fst"
let _64_2648 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_64_2648) with
| (uvs, t) -> begin
(
# 2013 "FStar.TypeChecker.Tc.fst"
let _64_2652 = (FStar_Syntax_Util.arrow_formals t)
in (match (_64_2652) with
| (args, _64_2651) -> begin
(
# 2014 "FStar.TypeChecker.Tc.fst"
let _64_2655 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_64_2655) with
| (tc_types, data_types) -> begin
(
# 2015 "FStar.TypeChecker.Tc.fst"
let tcs = (FStar_List.map2 (fun _64_2659 se -> (match (_64_2659) with
| (x, _64_2658) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _64_2663, tps, _64_2666, mutuals, datas, quals, r) -> begin
(
# 2017 "FStar.TypeChecker.Tc.fst"
let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (
# 2018 "FStar.TypeChecker.Tc.fst"
let _64_2689 = (match ((let _149_1121 = (FStar_Syntax_Subst.compress ty)
in _149_1121.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 2020 "FStar.TypeChecker.Tc.fst"
let _64_2680 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_64_2680) with
| (tps, rest) -> begin
(
# 2021 "FStar.TypeChecker.Tc.fst"
let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _64_2683 -> begin
(let _149_1122 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _149_1122 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _64_2686 -> begin
([], ty)
end)
in (match (_64_2689) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _64_2691 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (
# 2031 "FStar.TypeChecker.Tc.fst"
let datas = (match (uvs) with
| [] -> begin
datas
end
| _64_2695 -> begin
(
# 2034 "FStar.TypeChecker.Tc.fst"
let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _149_1123 -> FStar_Syntax_Syntax.U_name (_149_1123))))
in (
# 2035 "FStar.TypeChecker.Tc.fst"
let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _64_9 -> (match (_64_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _64_2700, _64_2702, _64_2704, _64_2706, _64_2708, _64_2710, _64_2712) -> begin
(tc, uvs_universes)
end
| _64_2716 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _64_2721 d -> (match (_64_2721) with
| (t, _64_2720) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _64_2725, _64_2727, tc, ntps, quals, mutuals, r) -> begin
(
# 2039 "FStar.TypeChecker.Tc.fst"
let ty = (let _149_1127 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _149_1127 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _64_2737 -> begin
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
# 2045 "FStar.TypeChecker.Tc.fst"
let _64_2747 = (FStar_All.pipe_right ses (FStar_List.partition (fun _64_10 -> (match (_64_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_64_2741) -> begin
true
end
| _64_2744 -> begin
false
end))))
in (match (_64_2747) with
| (tys, datas) -> begin
(
# 2047 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2050 "FStar.TypeChecker.Tc.fst"
let _64_2764 = (FStar_List.fold_right (fun tc _64_2753 -> (match (_64_2753) with
| (env, all_tcs, g) -> begin
(
# 2051 "FStar.TypeChecker.Tc.fst"
let _64_2757 = (tc_tycon env tc)
in (match (_64_2757) with
| (env, tc, tc_u) -> begin
(
# 2052 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (
# 2053 "FStar.TypeChecker.Tc.fst"
let _64_2759 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_1131 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _149_1131))
end else begin
()
end
in (let _149_1132 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _149_1132))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_64_2764) with
| (env, tcs, g) -> begin
(
# 2060 "FStar.TypeChecker.Tc.fst"
let _64_2774 = (FStar_List.fold_right (fun se _64_2768 -> (match (_64_2768) with
| (datas, g) -> begin
(
# 2061 "FStar.TypeChecker.Tc.fst"
let _64_2771 = (tc_data env tcs se)
in (match (_64_2771) with
| (data, g') -> begin
(let _149_1135 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _149_1135))
end))
end)) datas ([], g))
in (match (_64_2774) with
| (datas, g) -> begin
(
# 2066 "FStar.TypeChecker.Tc.fst"
let _64_2777 = (let _149_1136 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _149_1136 datas))
in (match (_64_2777) with
| (tcs, datas) -> begin
(let _149_1138 = (let _149_1137 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _149_1137))
in FStar_Syntax_Syntax.Sig_bundle (_149_1138))
end))
end))
end)))
end)))))))))

# 2067 "FStar.TypeChecker.Tc.fst"
let rec tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.env) = (fun env se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(
# 2082 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2083 "FStar.TypeChecker.Tc.fst"
let se = (tc_lex_t env ses quals lids)
in (let _149_1143 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _149_1143))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(
# 2087 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2088 "FStar.TypeChecker.Tc.fst"
let se = (tc_inductive env ses quals lids)
in (let _149_1144 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _149_1144))))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(
# 2092 "FStar.TypeChecker.Tc.fst"
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
# 2098 "FStar.TypeChecker.Tc.fst"
let _64_2815 = (set_options FStar_Options.Set o)
in (se, env))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(
# 2101 "FStar.TypeChecker.Tc.fst"
let _64_2819 = (let _149_1149 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _149_1149 Prims.ignore))
in (
# 2102 "FStar.TypeChecker.Tc.fst"
let _64_2824 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (
# 2105 "FStar.TypeChecker.Tc.fst"
let _64_2826 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (se, env))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(
# 2110 "FStar.TypeChecker.Tc.fst"
let ne = (tc_eff_decl env ne)
in (
# 2111 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (
# 2112 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(
# 2116 "FStar.TypeChecker.Tc.fst"
let _64_2841 = (let _149_1150 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _149_1150))
in (match (_64_2841) with
| (a, wp_a_src) -> begin
(
# 2117 "FStar.TypeChecker.Tc.fst"
let _64_2844 = (let _149_1151 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _149_1151))
in (match (_64_2844) with
| (b, wp_b_tgt) -> begin
(
# 2118 "FStar.TypeChecker.Tc.fst"
let wp_a_tgt = (let _149_1155 = (let _149_1154 = (let _149_1153 = (let _149_1152 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _149_1152))
in FStar_Syntax_Syntax.NT (_149_1153))
in (_149_1154)::[])
in (FStar_Syntax_Subst.subst _149_1155 wp_b_tgt))
in (
# 2119 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_1160 = (let _149_1158 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_1157 = (let _149_1156 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_149_1156)::[])
in (_149_1158)::_149_1157))
in (let _149_1159 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _149_1160 _149_1159)))
in (
# 2120 "FStar.TypeChecker.Tc.fst"
let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (
# 2121 "FStar.TypeChecker.Tc.fst"
let sub = (
# 2121 "FStar.TypeChecker.Tc.fst"
let _64_2848 = sub
in {FStar_Syntax_Syntax.source = _64_2848.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _64_2848.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
in (
# 2122 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect ((sub, r))
in (
# 2123 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(
# 2127 "FStar.TypeChecker.Tc.fst"
let _64_2861 = ()
in (
# 2128 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2129 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2130 "FStar.TypeChecker.Tc.fst"
let _64_2867 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_64_2867) with
| (tps, c) -> begin
(
# 2131 "FStar.TypeChecker.Tc.fst"
let _64_2871 = (tc_tparams env tps)
in (match (_64_2871) with
| (tps, env, us) -> begin
(
# 2132 "FStar.TypeChecker.Tc.fst"
let _64_2875 = (tc_comp env c)
in (match (_64_2875) with
| (c, u, g) -> begin
(
# 2133 "FStar.TypeChecker.Tc.fst"
let _64_2876 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2134 "FStar.TypeChecker.Tc.fst"
let tags = (FStar_All.pipe_right tags (FStar_List.map (fun _64_11 -> (match (_64_11) with
| FStar_Syntax_Syntax.DefaultEffect (None) -> begin
(
# 2136 "FStar.TypeChecker.Tc.fst"
let c' = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let _149_1163 = (FStar_All.pipe_right c'.FStar_Syntax_Syntax.effect_name (fun _149_1162 -> Some (_149_1162)))
in FStar_Syntax_Syntax.DefaultEffect (_149_1163)))
end
| t -> begin
t
end))))
in (
# 2139 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 2140 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.close_comp tps c)
in (
# 2141 "FStar.TypeChecker.Tc.fst"
let _64_2888 = (let _149_1164 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _149_1164))
in (match (_64_2888) with
| (uvs, t) -> begin
(
# 2142 "FStar.TypeChecker.Tc.fst"
let _64_2907 = (match ((let _149_1166 = (let _149_1165 = (FStar_Syntax_Subst.compress t)
in _149_1165.FStar_Syntax_Syntax.n)
in (tps, _149_1166))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_64_2891, c)) -> begin
([], c)
end
| (_64_2897, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _64_2904 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_64_2907) with
| (tps, c) -> begin
(
# 2146 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_effect_abbrev ((lid, uvs, tps, c, tags, r))
in (
# 2147 "FStar.TypeChecker.Tc.fst"
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
# 2151 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2152 "FStar.TypeChecker.Tc.fst"
let _64_2918 = ()
in (
# 2153 "FStar.TypeChecker.Tc.fst"
let k = (let _149_1167 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _149_1167))
in (
# 2154 "FStar.TypeChecker.Tc.fst"
let _64_2923 = (check_and_gen env t k)
in (match (_64_2923) with
| (uvs, t) -> begin
(
# 2155 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (
# 2156 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(
# 2160 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2161 "FStar.TypeChecker.Tc.fst"
let _64_2936 = (FStar_Syntax_Util.type_u ())
in (match (_64_2936) with
| (k, _64_2935) -> begin
(
# 2162 "FStar.TypeChecker.Tc.fst"
let phi = (let _149_1168 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _149_1168 (norm env)))
in (
# 2163 "FStar.TypeChecker.Tc.fst"
let _64_2938 = (FStar_TypeChecker_Util.check_uvars r phi)
in (
# 2164 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))
in (
# 2165 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(
# 2169 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2170 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (
# 2171 "FStar.TypeChecker.Tc.fst"
let _64_2951 = (tc_term env e)
in (match (_64_2951) with
| (e, c, g1) -> begin
(
# 2172 "FStar.TypeChecker.Tc.fst"
let _64_2956 = (let _149_1172 = (let _149_1169 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_149_1169))
in (let _149_1171 = (let _149_1170 = (c.FStar_Syntax_Syntax.comp ())
in (e, _149_1170))
in (check_expected_effect env _149_1172 _149_1171)))
in (match (_64_2956) with
| (e, _64_2954, g) -> begin
(
# 2173 "FStar.TypeChecker.Tc.fst"
let _64_2957 = (let _149_1173 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _149_1173))
in (
# 2174 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, r))
in (
# 2175 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(
# 2179 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2180 "FStar.TypeChecker.Tc.fst"
let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
if (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q')) then begin
Some (q)
end else begin
(let _149_1185 = (let _149_1184 = (let _149_1183 = (let _149_1182 = (FStar_Syntax_Print.lid_to_string l)
in (let _149_1181 = (FStar_Syntax_Print.quals_to_string q)
in (let _149_1180 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _149_1182 _149_1181 _149_1180))))
in (_149_1183, r))
in FStar_Syntax_Syntax.Error (_149_1184))
in (Prims.raise _149_1185))
end
end))
in (
# 2194 "FStar.TypeChecker.Tc.fst"
let _64_3001 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _64_2978 lb -> (match (_64_2978) with
| (gen, lbs, quals_opt) -> begin
(
# 2195 "FStar.TypeChecker.Tc.fst"
let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2196 "FStar.TypeChecker.Tc.fst"
let _64_2997 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(
# 2200 "FStar.TypeChecker.Tc.fst"
let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (
# 2201 "FStar.TypeChecker.Tc.fst"
let _64_2992 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _64_2991 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _149_1188 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _149_1188, quals_opt))))
end)
in (match (_64_2997) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_64_3001) with
| (should_generalize, lbs', quals_opt) -> begin
(
# 2210 "FStar.TypeChecker.Tc.fst"
let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _64_12 -> (match (_64_12) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _64_3010 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (
# 2217 "FStar.TypeChecker.Tc.fst"
let lbs' = (FStar_List.rev lbs')
in (
# 2220 "FStar.TypeChecker.Tc.fst"
let e = (let _149_1192 = (let _149_1191 = (let _149_1190 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _149_1190))
in FStar_Syntax_Syntax.Tm_let (_149_1191))
in (FStar_Syntax_Syntax.mk _149_1192 None r))
in (
# 2223 "FStar.TypeChecker.Tc.fst"
let _64_3044 = (match ((tc_maybe_toplevel_term (
# 2223 "FStar.TypeChecker.Tc.fst"
let _64_3014 = env
in {FStar_TypeChecker_Env.solver = _64_3014.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_3014.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_3014.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_3014.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_3014.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_3014.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_3014.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_3014.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_3014.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_3014.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_3014.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _64_3014.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _64_3014.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _64_3014.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _64_3014.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_3014.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_3014.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_3014.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_3014.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_3014.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _64_3021; FStar_Syntax_Syntax.pos = _64_3019; FStar_Syntax_Syntax.vars = _64_3017}, _64_3028, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(
# 2226 "FStar.TypeChecker.Tc.fst"
let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_64_3032, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _64_3038 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _64_3041 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_64_3044) with
| (se, lbs) -> begin
(
# 2233 "FStar.TypeChecker.Tc.fst"
let _64_3050 = if (log env) then begin
(let _149_1200 = (let _149_1199 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 2235 "FStar.TypeChecker.Tc.fst"
let should_log = (match ((let _149_1196 = (let _149_1195 = (let _149_1194 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _149_1194.FStar_Syntax_Syntax.fv_name)
in _149_1195.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _149_1196))) with
| None -> begin
true
end
| _64_3048 -> begin
false
end)
in if should_log then begin
(let _149_1198 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _149_1197 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _149_1198 _149_1197)))
end else begin
""
end))))
in (FStar_All.pipe_right _149_1199 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _149_1200))
end else begin
()
end
in (
# 2242 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end))))
end))

# 2243 "FStar.TypeChecker.Tc.fst"
let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (
# 2270 "FStar.TypeChecker.Tc.fst"
let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _64_13 -> (match (_64_13) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _64_3060 -> begin
false
end)))))
in (
# 2271 "FStar.TypeChecker.Tc.fst"
let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _64_3070 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_64_3072) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _64_3083, _64_3085) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _64_3091 -> (match (_64_3091) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _64_3097, _64_3099, quals, r) -> begin
(
# 2285 "FStar.TypeChecker.Tc.fst"
let dec = (let _149_1216 = (let _149_1215 = (let _149_1214 = (let _149_1213 = (let _149_1212 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _149_1212))
in FStar_Syntax_Syntax.Tm_arrow (_149_1213))
in (FStar_Syntax_Syntax.mk _149_1214 None r))
in (l, us, _149_1215, (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_149_1216))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _64_3109, _64_3111, _64_3113, _64_3115, r) -> begin
(
# 2288 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _64_3121 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_64_3123, _64_3125, quals, _64_3128) -> begin
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
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _64_14 -> (match (_64_14) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _64_3147 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_64_3149) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _64_3165, _64_3167, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(
# 2318 "FStar.TypeChecker.Tc.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2319 "FStar.TypeChecker.Tc.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))) then begin
([], hidden)
end else begin
(
# 2322 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::[], (FStar_Ident.range_of_lid lid)))
in ((dec)::[], (lid)::hidden))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (is_abstract quals) then begin
(let _149_1223 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _149_1222 = (let _149_1221 = (let _149_1220 = (let _149_1219 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _149_1219.FStar_Syntax_Syntax.fv_name)
in _149_1220.FStar_Syntax_Syntax.v)
in (_149_1221, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_149_1222)))))
in (_149_1223, hidden))
end else begin
((se)::[], hidden)
end
end))))

# 2329 "FStar.TypeChecker.Tc.fst"
let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (
# 2332 "FStar.TypeChecker.Tc.fst"
let _64_3206 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _64_3187 se -> (match (_64_3187) with
| (ses, exports, env, hidden) -> begin
(
# 2334 "FStar.TypeChecker.Tc.fst"
let _64_3189 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_1230 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _149_1230))
end else begin
()
end
in (
# 2337 "FStar.TypeChecker.Tc.fst"
let _64_3193 = (tc_decl env se)
in (match (_64_3193) with
| (se, env) -> begin
(
# 2339 "FStar.TypeChecker.Tc.fst"
let _64_3194 = if ((FStar_ST.read FStar_Options.log_types) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _149_1231 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _149_1231))
end else begin
()
end
in (
# 2342 "FStar.TypeChecker.Tc.fst"
let _64_3196 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (
# 2344 "FStar.TypeChecker.Tc.fst"
let _64_3200 = (for_export hidden se)
in (match (_64_3200) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_64_3206) with
| (ses, exports, env, _64_3205) -> begin
(let _149_1232 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _149_1232, env))
end)))

# 2347 "FStar.TypeChecker.Tc.fst"
let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2350 "FStar.TypeChecker.Tc.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 2351 "FStar.TypeChecker.Tc.fst"
let msg = (Prims.strcat "Internals for " name)
in (
# 2352 "FStar.TypeChecker.Tc.fst"
let env = (
# 2352 "FStar.TypeChecker.Tc.fst"
let _64_3211 = env
in (let _149_1237 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _64_3211.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_3211.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_3211.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_3211.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_3211.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_3211.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_3211.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_3211.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_3211.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_3211.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_3211.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_3211.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _64_3211.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _64_3211.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _64_3211.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _64_3211.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _149_1237; FStar_TypeChecker_Env.default_effects = _64_3211.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_3211.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_3211.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_3211.FStar_TypeChecker_Env.use_bv_sorts}))
in (
# 2353 "FStar.TypeChecker.Tc.fst"
let _64_3214 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (
# 2354 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (
# 2355 "FStar.TypeChecker.Tc.fst"
let _64_3220 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_64_3220) with
| (ses, exports, env) -> begin
((
# 2356 "FStar.TypeChecker.Tc.fst"
let _64_3221 = modul
in {FStar_Syntax_Syntax.name = _64_3221.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _64_3221.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _64_3221.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))

# 2356 "FStar.TypeChecker.Tc.fst"
let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (
# 2359 "FStar.TypeChecker.Tc.fst"
let _64_3229 = (tc_decls env decls)
in (match (_64_3229) with
| (ses, exports, env) -> begin
(
# 2360 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2360 "FStar.TypeChecker.Tc.fst"
let _64_3230 = modul
in {FStar_Syntax_Syntax.name = _64_3230.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _64_3230.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _64_3230.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))

# 2361 "FStar.TypeChecker.Tc.fst"
let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (
# 2364 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2364 "FStar.TypeChecker.Tc.fst"
let _64_3236 = modul
in {FStar_Syntax_Syntax.name = _64_3236.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _64_3236.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (
# 2365 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.finish_module env modul)
in (
# 2366 "FStar.TypeChecker.Tc.fst"
let _64_3246 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(
# 2368 "FStar.TypeChecker.Tc.fst"
let _64_3240 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (
# 2369 "FStar.TypeChecker.Tc.fst"
let _64_3242 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (
# 2370 "FStar.TypeChecker.Tc.fst"
let _64_3244 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _149_1250 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _149_1250 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))

# 2373 "FStar.TypeChecker.Tc.fst"
let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2376 "FStar.TypeChecker.Tc.fst"
let _64_3253 = (tc_partial_modul env modul)
in (match (_64_3253) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

# 2377 "FStar.TypeChecker.Tc.fst"
let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 2380 "FStar.TypeChecker.Tc.fst"
let _64_3256 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _149_1259 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _149_1259))
end else begin
()
end
in (
# 2382 "FStar.TypeChecker.Tc.fst"
let env = (
# 2382 "FStar.TypeChecker.Tc.fst"
let _64_3258 = env
in {FStar_TypeChecker_Env.solver = _64_3258.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_3258.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_3258.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_3258.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_3258.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_3258.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_3258.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_3258.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_3258.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_3258.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_3258.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_3258.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _64_3258.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _64_3258.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _64_3258.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _64_3258.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_3258.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_3258.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_3258.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_3258.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_3258.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 2383 "FStar.TypeChecker.Tc.fst"
let _64_3274 = (FStar_All.try_with (fun _64_3262 -> (match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)) (fun _64_3261 -> (match (_64_3261) with
| FStar_Syntax_Syntax.Error (msg, _64_3266) -> begin
(let _149_1264 = (let _149_1263 = (let _149_1262 = (FStar_TypeChecker_Env.get_range env)
in ((Prims.strcat "Implicit argument: " msg), _149_1262))
in FStar_Syntax_Syntax.Error (_149_1263))
in (Prims.raise _149_1264))
end)))
in (match (_64_3274) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(let _149_1269 = (let _149_1268 = (let _149_1267 = (let _149_1265 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _149_1265))
in (let _149_1266 = (FStar_TypeChecker_Env.get_range env)
in (_149_1267, _149_1266)))
in FStar_Syntax_Syntax.Error (_149_1268))
in (Prims.raise _149_1269))
end
end)))))

# 2388 "FStar.TypeChecker.Tc.fst"
let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (
# 2391 "FStar.TypeChecker.Tc.fst"
let _64_3277 = if ((let _149_1274 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _149_1274)) <> 0) then begin
(let _149_1275 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _149_1275))
end else begin
()
end
in (
# 2393 "FStar.TypeChecker.Tc.fst"
let _64_3281 = (tc_modul env m)
in (match (_64_3281) with
| (m, env) -> begin
(
# 2394 "FStar.TypeChecker.Tc.fst"
let _64_3282 = if (FStar_Options.should_dump m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _149_1276 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _149_1276))
end else begin
()
end
in (m, env))
end))))




