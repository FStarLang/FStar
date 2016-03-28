
open Prims
# 42 "FStar.TypeChecker.Tc.fst"
let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_ST.read FStar_Options.log_types) && (not ((let _149_3 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _149_3))))))

# 43 "FStar.TypeChecker.Tc.fst"
let rng : FStar_TypeChecker_Env.env  ->  FStar_Range.range = (fun env -> (FStar_TypeChecker_Env.get_range env))

# 44 "FStar.TypeChecker.Tc.fst"
let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (
# 44 "FStar.TypeChecker.Tc.fst"
let _64_18 = env
in {FStar_TypeChecker_Env.solver = _64_18.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_18.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_18.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_18.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_18.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_18.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_18.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_18.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_18.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _64_18.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_18.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _64_18.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _64_18.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _64_18.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _64_18.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _64_18.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_18.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_18.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_18.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_18.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_18.FStar_TypeChecker_Env.use_bv_sorts}))

# 45 "FStar.TypeChecker.Tc.fst"
let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (
# 45 "FStar.TypeChecker.Tc.fst"
let _64_21 = env
in {FStar_TypeChecker_Env.solver = _64_21.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_21.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_21.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_21.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_21.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_21.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_21.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_21.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_21.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _64_21.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_21.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _64_21.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _64_21.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _64_21.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _64_21.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _64_21.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_21.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_21.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_21.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_21.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_21.FStar_TypeChecker_Env.use_bv_sorts}))

# 46 "FStar.TypeChecker.Tc.fst"
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

# 51 "FStar.TypeChecker.Tc.fst"
let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _64_1 -> (match (_64_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _64_31 -> begin
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
let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _149_30 = (steps env)
in (FStar_TypeChecker_Normalize.normalize _149_30 env t)))

# 60 "FStar.TypeChecker.Tc.fst"
let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _149_35 = (steps env)
in (FStar_TypeChecker_Normalize.normalize_comp _149_35 env c)))

# 61 "FStar.TypeChecker.Tc.fst"
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

# 84 "FStar.TypeChecker.Tc.fst"
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

# 90 "FStar.TypeChecker.Tc.fst"
let maybe_make_subst = (fun _64_2 -> (match (_64_2) with
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Syntax_Syntax.NT ((x, e)))::[]
end
| _64_76 -> begin
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
let _64_82 = lc
in {FStar_Syntax_Syntax.eff_name = _64_82.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _64_82.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _64_84 -> (match (()) with
| () -> begin
(let _149_78 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _149_78 t))
end))}))

# 101 "FStar.TypeChecker.Tc.fst"
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

# 125 "FStar.TypeChecker.Tc.fst"
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

# 132 "FStar.TypeChecker.Tc.fst"
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

# 170 "FStar.TypeChecker.Tc.fst"
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

# 175 "FStar.TypeChecker.Tc.fst"
let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _149_129 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _149_129))
end))

# 179 "FStar.TypeChecker.Tc.fst"
let with_implicits = (fun imps _64_177 -> (match (_64_177) with
| (e, l, g) -> begin
(e, l, (
# 179 "FStar.TypeChecker.Tc.fst"
let _64_178 = g
in {FStar_TypeChecker_Env.guard_f = _64_178.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _64_178.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _64_178.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (FStar_List.append imps g.FStar_TypeChecker_Env.implicits)}))
end))

# 180 "FStar.TypeChecker.Tc.fst"
let add_implicit : (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun u g -> (
# 180 "FStar.TypeChecker.Tc.fst"
let _64_182 = g
in {FStar_TypeChecker_Env.guard_f = _64_182.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _64_182.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _64_182.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (u)::g.FStar_TypeChecker_Env.implicits}))

# 185 "FStar.TypeChecker.Tc.fst"
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

# 256 "FStar.TypeChecker.Tc.fst"
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
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _64_433) -> begin
(
# 316 "FStar.TypeChecker.Tc.fst"
let _64_440 = (tc_comp env expected_c)
in (match (_64_440) with
| (expected_c, _64_438, g) -> begin
(
# 317 "FStar.TypeChecker.Tc.fst"
let _64_444 = (tc_term env e)
in (match (_64_444) with
| (e, c', g') -> begin
(
# 318 "FStar.TypeChecker.Tc.fst"
let _64_448 = (let _149_260 = (let _149_259 = (c'.FStar_Syntax_Syntax.comp ())
in (e, _149_259))
in (check_expected_effect env (Some (expected_c)) _149_260))
in (match (_64_448) with
| (e, expected_c, g'') -> begin
(
# 319 "FStar.TypeChecker.Tc.fst"
let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (let _149_263 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t_res), Some ((FStar_Syntax_Util.comp_effect_name expected_c))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _149_262 = (let _149_261 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _149_261))
in (_149_263, (FStar_Syntax_Util.lcomp_of_comp expected_c), _149_262))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _64_454) -> begin
(
# 325 "FStar.TypeChecker.Tc.fst"
let _64_459 = (FStar_Syntax_Util.type_u ())
in (match (_64_459) with
| (k, u) -> begin
(
# 326 "FStar.TypeChecker.Tc.fst"
let _64_464 = (tc_check_tot_or_gtot_term env t k)
in (match (_64_464) with
| (t, _64_462, f) -> begin
(
# 327 "FStar.TypeChecker.Tc.fst"
let _64_468 = (let _149_264 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _149_264 e))
in (match (_64_468) with
| (e, c, g) -> begin
(
# 328 "FStar.TypeChecker.Tc.fst"
let _64_472 = (let _149_268 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _64_469 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _149_268 e c f))
in (match (_64_472) with
| (c, f) -> begin
(
# 329 "FStar.TypeChecker.Tc.fst"
let _64_476 = (let _149_269 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t), Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _149_269 c))
in (match (_64_476) with
| (e, c, f2) -> begin
(let _149_271 = (let _149_270 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _149_270))
in (e, c, _149_271))
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
let env = (let _149_273 = (let _149_272 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _149_272 Prims.fst))
in (FStar_All.pipe_right _149_273 instantiate_both))
in (
# 335 "FStar.TypeChecker.Tc.fst"
let _64_483 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_275 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _149_274 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _149_275 _149_274)))
end else begin
()
end
in (
# 339 "FStar.TypeChecker.Tc.fst"
let _64_488 = (tc_term (no_inst env) head)
in (match (_64_488) with
| (head, chead, g_head) -> begin
(
# 340 "FStar.TypeChecker.Tc.fst"
let _64_492 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _149_276 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _149_276))
end else begin
(let _149_277 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _149_277))
end
in (match (_64_492) with
| (e, c, g) -> begin
(
# 343 "FStar.TypeChecker.Tc.fst"
let _64_493 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _149_278 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _149_278))
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
let _64_500 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_284 = (FStar_Syntax_Print.term_to_string e)
in (let _149_283 = (let _149_279 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _149_279))
in (let _149_282 = (let _149_281 = (FStar_TypeChecker_Env.expected_typ env0)
in (FStar_All.pipe_right _149_281 (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end))))
in (FStar_Util.print3 "(%s) About to check %s against expected typ %s\n" _149_284 _149_283 _149_282))))
end else begin
()
end
in (
# 355 "FStar.TypeChecker.Tc.fst"
let _64_505 = (comp_check_expected_typ env0 e c)
in (match (_64_505) with
| (e, c, g') -> begin
(
# 356 "FStar.TypeChecker.Tc.fst"
let _64_506 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_287 = (FStar_Syntax_Print.term_to_string e)
in (let _149_286 = (let _149_285 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _149_285))
in (FStar_Util.print2 "(%s) checked ... got %s\n" _149_287 _149_286)))
end else begin
()
end
in (
# 360 "FStar.TypeChecker.Tc.fst"
let gimp = (match ((let _149_288 = (FStar_Syntax_Subst.compress head)
in _149_288.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _64_510) -> begin
(
# 363 "FStar.TypeChecker.Tc.fst"
let imp = (env0, u, e, c.FStar_Syntax_Syntax.res_typ, e.FStar_Syntax_Syntax.pos)
in (
# 364 "FStar.TypeChecker.Tc.fst"
let _64_514 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _64_514.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _64_514.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _64_514.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _64_517 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (
# 366 "FStar.TypeChecker.Tc.fst"
let gres = (let _149_289 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _149_289))
in (
# 367 "FStar.TypeChecker.Tc.fst"
let _64_520 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _149_290 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print1 "Guard from application node is %s\n" _149_290))
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
let _64_528 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_64_528) with
| (env1, topt) -> begin
(
# 373 "FStar.TypeChecker.Tc.fst"
let env1 = (instantiate_both env1)
in (
# 374 "FStar.TypeChecker.Tc.fst"
let _64_533 = (tc_term env1 e1)
in (match (_64_533) with
| (e1, c1, g1) -> begin
(
# 375 "FStar.TypeChecker.Tc.fst"
let _64_544 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(
# 378 "FStar.TypeChecker.Tc.fst"
let _64_540 = (FStar_Syntax_Util.type_u ())
in (match (_64_540) with
| (k, _64_539) -> begin
(
# 379 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _149_291 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_149_291, res_t)))
end))
end)
in (match (_64_544) with
| (env_branches, res_t) -> begin
(
# 382 "FStar.TypeChecker.Tc.fst"
let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (
# 383 "FStar.TypeChecker.Tc.fst"
let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (
# 384 "FStar.TypeChecker.Tc.fst"
let _64_561 = (
# 385 "FStar.TypeChecker.Tc.fst"
let _64_558 = (FStar_List.fold_right (fun _64_552 _64_555 -> (match ((_64_552, _64_555)) with
| ((_64_548, f, c, g), (caccum, gaccum)) -> begin
(let _149_294 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _149_294))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_64_558) with
| (cases, g) -> begin
(let _149_295 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_149_295, g))
end))
in (match (_64_561) with
| (c_branches, g_branches) -> begin
(
# 389 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (guard_x), c_branches))
in (
# 390 "FStar.TypeChecker.Tc.fst"
let e = (let _149_299 = (let _149_298 = (let _149_297 = (FStar_List.map (fun _64_570 -> (match (_64_570) with
| (f, _64_565, _64_567, _64_569) -> begin
f
end)) t_eqns)
in (e1, _149_297))
in FStar_Syntax_Syntax.Tm_match (_149_298))
in (FStar_Syntax_Syntax.mk _149_299 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (
# 392 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ), Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (
# 393 "FStar.TypeChecker.Tc.fst"
let _64_573 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _149_302 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _149_301 = (let _149_300 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _149_300))
in (FStar_Util.print2 "(%s) comp type = %s\n" _149_302 _149_301)))
end else begin
()
end
in (let _149_303 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _149_303))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_64_585); FStar_Syntax_Syntax.lbunivs = _64_583; FStar_Syntax_Syntax.lbtyp = _64_581; FStar_Syntax_Syntax.lbeff = _64_579; FStar_Syntax_Syntax.lbdef = _64_577}::[]), _64_591) -> begin
(
# 400 "FStar.TypeChecker.Tc.fst"
let _64_594 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_304 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _149_304))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _64_598), _64_601) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_64_616); FStar_Syntax_Syntax.lbunivs = _64_614; FStar_Syntax_Syntax.lbtyp = _64_612; FStar_Syntax_Syntax.lbeff = _64_610; FStar_Syntax_Syntax.lbdef = _64_608}::_64_606), _64_622) -> begin
(
# 407 "FStar.TypeChecker.Tc.fst"
let _64_625 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_305 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _149_305))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _64_629), _64_632) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 420 "FStar.TypeChecker.Tc.fst"
let check_instantiated_fvar = (fun env v dc e t -> (
# 421 "FStar.TypeChecker.Tc.fst"
let _64_646 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_64_646) with
| (e, t, implicits) -> begin
(
# 423 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _149_319 = (let _149_318 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _149_318))
in FStar_Util.Inr (_149_319))
end
in (
# 424 "FStar.TypeChecker.Tc.fst"
let is_data_ctor = (fun _64_4 -> (match (_64_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _64_656 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _149_325 = (let _149_324 = (let _149_323 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _149_322 = (FStar_TypeChecker_Env.get_range env)
in (_149_323, _149_322)))
in FStar_Syntax_Syntax.Error (_149_324))
in (Prims.raise _149_325))
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
let g = (match ((let _149_326 = (FStar_Syntax_Subst.compress t1)
in _149_326.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_64_667) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _64_670 -> begin
(
# 443 "FStar.TypeChecker.Tc.fst"
let imp = (env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (
# 444 "FStar.TypeChecker.Tc.fst"
let _64_672 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _64_672.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _64_672.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _64_672.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 449 "FStar.TypeChecker.Tc.fst"
let _64_678 = (FStar_Syntax_Util.type_u ())
in (match (_64_678) with
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
let _64_683 = x
in {FStar_Syntax_Syntax.ppname = _64_683.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_683.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (
# 456 "FStar.TypeChecker.Tc.fst"
let _64_689 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_64_689) with
| (e, t, implicits) -> begin
(
# 457 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _149_328 = (let _149_327 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _149_327))
in FStar_Util.Inr (_149_328))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _64_696; FStar_Syntax_Syntax.pos = _64_694; FStar_Syntax_Syntax.vars = _64_692}, us) -> begin
(
# 461 "FStar.TypeChecker.Tc.fst"
let us = (FStar_List.map (tc_universe env) us)
in (
# 462 "FStar.TypeChecker.Tc.fst"
let _64_706 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_64_706) with
| (us', t) -> begin
(
# 463 "FStar.TypeChecker.Tc.fst"
let _64_713 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _149_331 = (let _149_330 = (let _149_329 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _149_329))
in FStar_Syntax_Syntax.Error (_149_330))
in (Prims.raise _149_331))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _64_712 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (
# 468 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 468 "FStar.TypeChecker.Tc.fst"
let _64_715 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 468 "FStar.TypeChecker.Tc.fst"
let _64_717 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _64_717.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _64_717.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _64_715.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _64_715.FStar_Syntax_Syntax.fv_qual})
in (
# 469 "FStar.TypeChecker.Tc.fst"
let e = (let _149_334 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _149_334 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(
# 473 "FStar.TypeChecker.Tc.fst"
let _64_725 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_64_725) with
| (us, t) -> begin
(
# 474 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 474 "FStar.TypeChecker.Tc.fst"
let _64_726 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 474 "FStar.TypeChecker.Tc.fst"
let _64_728 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _64_728.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _64_728.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _64_726.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _64_726.FStar_Syntax_Syntax.fv_qual})
in (
# 475 "FStar.TypeChecker.Tc.fst"
let e = (let _149_335 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _149_335 us))
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
let _64_742 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_64_742) with
| (bs, c) -> begin
(
# 485 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 486 "FStar.TypeChecker.Tc.fst"
let _64_747 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_64_747) with
| (env, _64_746) -> begin
(
# 487 "FStar.TypeChecker.Tc.fst"
let _64_752 = (tc_binders env bs)
in (match (_64_752) with
| (bs, env, g, us) -> begin
(
# 488 "FStar.TypeChecker.Tc.fst"
let _64_756 = (tc_comp env c)
in (match (_64_756) with
| (c, uc, f) -> begin
(
# 489 "FStar.TypeChecker.Tc.fst"
let e = (
# 489 "FStar.TypeChecker.Tc.fst"
let _64_757 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _64_757.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _64_757.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _64_757.FStar_Syntax_Syntax.vars})
in (
# 490 "FStar.TypeChecker.Tc.fst"
let _64_760 = (check_smt_pat env e bs c)
in (
# 491 "FStar.TypeChecker.Tc.fst"
let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (
# 492 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 493 "FStar.TypeChecker.Tc.fst"
let g = (let _149_336 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _149_336))
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
let _64_776 = (let _149_338 = (let _149_337 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_337)::[])
in (FStar_Syntax_Subst.open_term _149_338 phi))
in (match (_64_776) with
| (x, phi) -> begin
(
# 504 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 505 "FStar.TypeChecker.Tc.fst"
let _64_781 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_64_781) with
| (env, _64_780) -> begin
(
# 506 "FStar.TypeChecker.Tc.fst"
let _64_786 = (let _149_339 = (FStar_List.hd x)
in (tc_binder env _149_339))
in (match (_64_786) with
| (x, env, f1, u) -> begin
(
# 507 "FStar.TypeChecker.Tc.fst"
let _64_787 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_342 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _149_341 = (FStar_Syntax_Print.term_to_string phi)
in (let _149_340 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _149_342 _149_341 _149_340))))
end else begin
()
end
in (
# 510 "FStar.TypeChecker.Tc.fst"
let _64_792 = (FStar_Syntax_Util.type_u ())
in (match (_64_792) with
| (t_phi, _64_791) -> begin
(
# 511 "FStar.TypeChecker.Tc.fst"
let _64_797 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_64_797) with
| (phi, _64_795, f2) -> begin
(
# 512 "FStar.TypeChecker.Tc.fst"
let e = (
# 512 "FStar.TypeChecker.Tc.fst"
let _64_798 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _64_798.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _64_798.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _64_798.FStar_Syntax_Syntax.vars})
in (
# 513 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 514 "FStar.TypeChecker.Tc.fst"
let g = (let _149_343 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _149_343))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _64_806) -> begin
(
# 518 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (
# 519 "FStar.TypeChecker.Tc.fst"
let _64_812 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_344 = (FStar_Syntax_Print.term_to_string (
# 520 "FStar.TypeChecker.Tc.fst"
let _64_810 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _64_810.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _64_810.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _64_810.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _149_344))
end else begin
()
end
in (
# 521 "FStar.TypeChecker.Tc.fst"
let _64_816 = (FStar_Syntax_Subst.open_term bs body)
in (match (_64_816) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _64_818 -> begin
(let _149_346 = (let _149_345 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _149_345))
in (FStar_All.failwith _149_346))
end)))))
and tc_constant : FStar_TypeChecker_Env.env  ->  FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun env r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_64_824) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_64_827) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int32 (_64_830) -> begin
FStar_TypeChecker_Common.t_int32
end
| FStar_Const.Const_int64 (_64_833) -> begin
FStar_TypeChecker_Common.t_int64
end
| FStar_Const.Const_string (_64_836) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_64_839) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_64_842) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_uint8 (_64_845) -> begin
FStar_TypeChecker_Common.t_uint8
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_64_849) -> begin
(
# 540 "FStar.TypeChecker.Tc.fst"
let fail = (fun _64_852 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Range constant cannot be checked in this context; expected an instance of \'range_of\'", r))))
end))
in (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(fail ())
end
| Some (t) -> begin
if (let _149_352 = (FStar_Syntax_Util.destruct t FStar_Syntax_Const.range_of_lid)
in (FStar_Option.isSome _149_352)) then begin
t
end else begin
(fail ())
end
end))
end
| _64_857 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 561 "FStar.TypeChecker.Tc.fst"
let _64_864 = (FStar_Syntax_Util.type_u ())
in (match (_64_864) with
| (k, u) -> begin
(
# 562 "FStar.TypeChecker.Tc.fst"
let _64_869 = (tc_check_tot_or_gtot_term env t k)
in (match (_64_869) with
| (t, _64_867, g) -> begin
(let _149_355 = (FStar_Syntax_Syntax.mk_Total t)
in (_149_355, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 566 "FStar.TypeChecker.Tc.fst"
let _64_874 = (FStar_Syntax_Util.type_u ())
in (match (_64_874) with
| (k, u) -> begin
(
# 567 "FStar.TypeChecker.Tc.fst"
let _64_879 = (tc_check_tot_or_gtot_term env t k)
in (match (_64_879) with
| (t, _64_877, g) -> begin
(let _149_356 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_149_356, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 571 "FStar.TypeChecker.Tc.fst"
let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (
# 572 "FStar.TypeChecker.Tc.fst"
let tc = (let _149_358 = (let _149_357 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_149_357)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _149_358 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 573 "FStar.TypeChecker.Tc.fst"
let _64_888 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_64_888) with
| (tc, _64_886, f) -> begin
(
# 574 "FStar.TypeChecker.Tc.fst"
let _64_892 = (FStar_Syntax_Util.head_and_args tc)
in (match (_64_892) with
| (_64_890, args) -> begin
(
# 575 "FStar.TypeChecker.Tc.fst"
let _64_895 = (let _149_360 = (FStar_List.hd args)
in (let _149_359 = (FStar_List.tl args)
in (_149_360, _149_359)))
in (match (_64_895) with
| (res, args) -> begin
(
# 576 "FStar.TypeChecker.Tc.fst"
let _64_911 = (let _149_362 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _64_5 -> (match (_64_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(
# 578 "FStar.TypeChecker.Tc.fst"
let _64_902 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_64_902) with
| (env, _64_901) -> begin
(
# 579 "FStar.TypeChecker.Tc.fst"
let _64_907 = (tc_tot_or_gtot_term env e)
in (match (_64_907) with
| (e, _64_905, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _149_362 FStar_List.unzip))
in (match (_64_911) with
| (flags, guards) -> begin
(
# 582 "FStar.TypeChecker.Tc.fst"
let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| _64_916 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _149_364 = (FStar_Syntax_Syntax.mk_Comp (
# 585 "FStar.TypeChecker.Tc.fst"
let _64_918 = c
in {FStar_Syntax_Syntax.effect_name = _64_918.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _64_918.FStar_Syntax_Syntax.flags}))
in (let _149_363 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_149_364, u, _149_363))))
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
| FStar_Syntax_Syntax.U_bvar (_64_926) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _149_369 = (aux u)
in FStar_Syntax_Syntax.U_succ (_149_369))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _149_370 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_149_370))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _149_374 = (let _149_373 = (let _149_372 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _149_371 = (FStar_TypeChecker_Env.get_range env)
in (_149_372, _149_371)))
in FStar_Syntax_Syntax.Error (_149_373))
in (Prims.raise _149_374))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _149_375 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _149_375 Prims.snd))
end
| _64_941 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (
# 615 "FStar.TypeChecker.Tc.fst"
let fail = (fun msg t -> (let _149_384 = (let _149_383 = (let _149_382 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_149_382, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_149_383))
in (Prims.raise _149_384)))
in (
# 624 "FStar.TypeChecker.Tc.fst"
let check_binders = (fun env bs bs_expected -> (
# 629 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun _64_959 bs bs_expected -> (match (_64_959) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| ((hd, imp)::bs, (hd_expected, imp')::bs_expected) -> begin
(
# 633 "FStar.TypeChecker.Tc.fst"
let _64_990 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _149_401 = (let _149_400 = (let _149_399 = (let _149_397 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _149_397))
in (let _149_398 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_149_399, _149_398)))
in FStar_Syntax_Syntax.Error (_149_400))
in (Prims.raise _149_401))
end
| _64_989 -> begin
()
end)
in (
# 640 "FStar.TypeChecker.Tc.fst"
let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (
# 641 "FStar.TypeChecker.Tc.fst"
let _64_1007 = (match ((let _149_402 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _149_402.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _64_995 -> begin
(
# 644 "FStar.TypeChecker.Tc.fst"
let _64_996 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_403 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _149_403))
end else begin
()
end
in (
# 645 "FStar.TypeChecker.Tc.fst"
let _64_1002 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_64_1002) with
| (t, _64_1000, g1) -> begin
(
# 646 "FStar.TypeChecker.Tc.fst"
let g2 = (let _149_405 = (FStar_TypeChecker_Env.get_range env)
in (let _149_404 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _149_405 "Type annotation on parameter incompatible with the expected type" _149_404)))
in (
# 650 "FStar.TypeChecker.Tc.fst"
let g = (let _149_406 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _149_406))
in (t, g)))
end)))
end)
in (match (_64_1007) with
| (t, g) -> begin
(
# 652 "FStar.TypeChecker.Tc.fst"
let hd = (
# 652 "FStar.TypeChecker.Tc.fst"
let _64_1008 = hd
in {FStar_Syntax_Syntax.ppname = _64_1008.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_1008.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
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
let subst = (let _149_407 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _149_407))
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
let rec expected_function_typ = (fun env t0 -> (match (t0) with
| None -> begin
(
# 676 "FStar.TypeChecker.Tc.fst"
let _64_1028 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _64_1027 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (
# 679 "FStar.TypeChecker.Tc.fst"
let _64_1035 = (tc_binders env bs)
in (match (_64_1035) with
| (bs, envbody, g, _64_1034) -> begin
(None, bs, [], None, envbody, g)
end)))
end
| Some (t) -> begin
(
# 683 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 684 "FStar.TypeChecker.Tc.fst"
let rec as_function_typ = (fun norm t -> (match ((let _149_416 = (FStar_Syntax_Subst.compress t)
in _149_416.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 688 "FStar.TypeChecker.Tc.fst"
let _64_1062 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _64_1061 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 689 "FStar.TypeChecker.Tc.fst"
let _64_1069 = (tc_binders env bs)
in (match (_64_1069) with
| (bs, envbody, g, _64_1068) -> begin
(
# 690 "FStar.TypeChecker.Tc.fst"
let _64_1073 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_64_1073) with
| (envbody, _64_1072) -> begin
(Some ((t, true)), bs, [], None, envbody, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _64_1076) -> begin
(
# 696 "FStar.TypeChecker.Tc.fst"
let _64_1086 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_64_1086) with
| (_64_1080, bs, bs', copt, env, g) -> begin
(Some ((t, false)), bs, bs', copt, env, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 700 "FStar.TypeChecker.Tc.fst"
let _64_1093 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_64_1093) with
| (bs_expected, c_expected) -> begin
(
# 707 "FStar.TypeChecker.Tc.fst"
let check_actuals_against_formals = (fun env bs bs_expected -> (
# 708 "FStar.TypeChecker.Tc.fst"
let rec handle_more = (fun _64_1104 c_expected -> (match (_64_1104) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _149_427 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _149_427))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(
# 713 "FStar.TypeChecker.Tc.fst"
let c = (let _149_428 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _149_428))
in (let _149_429 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _149_429)))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(
# 717 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.subst_comp subst c_expected)
in if (FStar_Syntax_Util.is_total_comp c) then begin
(
# 720 "FStar.TypeChecker.Tc.fst"
let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 723 "FStar.TypeChecker.Tc.fst"
let _64_1125 = (check_binders env more_bs bs_expected)
in (match (_64_1125) with
| (env, bs', more, guard', subst) -> begin
(let _149_431 = (let _149_430 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _149_430, subst))
in (handle_more _149_431 c_expected))
end))
end
| _64_1127 -> begin
(let _149_433 = (let _149_432 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _149_432))
in (fail _149_433 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _149_434 = (check_binders env bs bs_expected)
in (handle_more _149_434 c_expected))))
in (
# 730 "FStar.TypeChecker.Tc.fst"
let mk_letrec_env = (fun envbody bs c -> (
# 731 "FStar.TypeChecker.Tc.fst"
let letrecs = (guard_letrecs envbody bs c)
in (
# 732 "FStar.TypeChecker.Tc.fst"
let envbody = (
# 732 "FStar.TypeChecker.Tc.fst"
let _64_1133 = envbody
in {FStar_TypeChecker_Env.solver = _64_1133.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_1133.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_1133.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_1133.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_1133.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_1133.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_1133.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_1133.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_1133.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_1133.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_1133.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_1133.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _64_1133.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _64_1133.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _64_1133.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _64_1133.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_1133.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_1133.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_1133.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_1133.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_1133.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _64_1138 _64_1141 -> (match ((_64_1138, _64_1141)) with
| ((env, letrec_binders), (l, t)) -> begin
(
# 736 "FStar.TypeChecker.Tc.fst"
let _64_1147 = (let _149_444 = (let _149_443 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _149_443 Prims.fst))
in (tc_term _149_444 t))
in (match (_64_1147) with
| (t, _64_1144, _64_1146) -> begin
(
# 737 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (
# 738 "FStar.TypeChecker.Tc.fst"
let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _149_445 = (FStar_Syntax_Syntax.mk_binder (
# 739 "FStar.TypeChecker.Tc.fst"
let _64_1151 = x
in {FStar_Syntax_Syntax.ppname = _64_1151.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_1151.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_149_445)::letrec_binders)
end
| _64_1154 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (
# 744 "FStar.TypeChecker.Tc.fst"
let _64_1160 = (check_actuals_against_formals env bs bs_expected)
in (match (_64_1160) with
| (envbody, bs, g, c) -> begin
(
# 745 "FStar.TypeChecker.Tc.fst"
let _64_1163 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_64_1163) with
| (envbody, letrecs) -> begin
(
# 746 "FStar.TypeChecker.Tc.fst"
let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, g))
end))
end))))
end))
end
| _64_1166 -> begin
if (not (norm)) then begin
(let _149_446 = (unfold_whnf env t)
in (as_function_typ true _149_446))
end else begin
(
# 754 "FStar.TypeChecker.Tc.fst"
let _64_1175 = (expected_function_typ env None)
in (match (_64_1175) with
| (_64_1168, bs, _64_1171, c_opt, envbody, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (
# 758 "FStar.TypeChecker.Tc.fst"
let use_eq = env.FStar_TypeChecker_Env.use_eq
in (
# 759 "FStar.TypeChecker.Tc.fst"
let _64_1179 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_64_1179) with
| (env, topt) -> begin
(
# 760 "FStar.TypeChecker.Tc.fst"
let _64_1183 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_447 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _149_447 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (
# 764 "FStar.TypeChecker.Tc.fst"
let _64_1191 = (expected_function_typ env topt)
in (match (_64_1191) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, g) -> begin
(
# 765 "FStar.TypeChecker.Tc.fst"
let _64_1197 = (tc_term (
# 765 "FStar.TypeChecker.Tc.fst"
let _64_1192 = envbody
in {FStar_TypeChecker_Env.solver = _64_1192.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_1192.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_1192.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_1192.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_1192.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_1192.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_1192.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_1192.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_1192.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_1192.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_1192.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_1192.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _64_1192.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _64_1192.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _64_1192.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_1192.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_1192.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_1192.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_1192.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_1192.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_64_1197) with
| (body, cbody, guard_body) -> begin
(
# 766 "FStar.TypeChecker.Tc.fst"
let _64_1198 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_451 = (FStar_Syntax_Print.term_to_string body)
in (let _149_450 = (let _149_448 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _149_448))
in (let _149_449 = (FStar_TypeChecker_Rel.guard_to_string env guard_body)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _149_451 _149_450 _149_449))))
end else begin
()
end
in (
# 771 "FStar.TypeChecker.Tc.fst"
let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (
# 773 "FStar.TypeChecker.Tc.fst"
let _64_1201 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _149_454 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _149_453 = (let _149_452 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _149_452))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _149_454 _149_453)))
end else begin
()
end
in (
# 777 "FStar.TypeChecker.Tc.fst"
let _64_1208 = (let _149_456 = (let _149_455 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _149_455))
in (check_expected_effect (
# 777 "FStar.TypeChecker.Tc.fst"
let _64_1203 = envbody
in {FStar_TypeChecker_Env.solver = _64_1203.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_1203.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_1203.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_1203.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_1203.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_1203.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_1203.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_1203.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_1203.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_1203.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_1203.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_1203.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _64_1203.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _64_1203.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _64_1203.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _64_1203.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_1203.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_1203.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_1203.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_1203.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_1203.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _149_456))
in (match (_64_1208) with
| (body, cbody, guard) -> begin
(
# 778 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (
# 779 "FStar.TypeChecker.Tc.fst"
let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _149_457 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _149_457))
end else begin
(
# 781 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (
# 784 "FStar.TypeChecker.Tc.fst"
let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (
# 785 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.abs bs body (Some ((FStar_Syntax_Util.lcomp_of_comp cbody))))
in (
# 786 "FStar.TypeChecker.Tc.fst"
let _64_1231 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(
# 788 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_64_1220) -> begin
(e, t, guard)
end
| _64_1223 -> begin
(
# 797 "FStar.TypeChecker.Tc.fst"
let _64_1226 = if use_teq then begin
(let _149_458 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _149_458))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_64_1226) with
| (e, guard') -> begin
(let _149_459 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _149_459))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_64_1231) with
| (e, tfun, guard) -> begin
(
# 807 "FStar.TypeChecker.Tc.fst"
let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (
# 808 "FStar.TypeChecker.Tc.fst"
let _64_1235 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_64_1235) with
| (c, g) -> begin
(e, c, g)
end)))
end))))))
end)))))
end))
end)))
end)))))))
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead ghead args expected_topt -> (
# 816 "FStar.TypeChecker.Tc.fst"
let n_args = (FStar_List.length args)
in (
# 817 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 818 "FStar.TypeChecker.Tc.fst"
let thead = chead.FStar_Syntax_Syntax.res_typ
in (
# 819 "FStar.TypeChecker.Tc.fst"
let _64_1245 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_468 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _149_467 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _149_468 _149_467)))
end else begin
()
end
in (
# 820 "FStar.TypeChecker.Tc.fst"
let rec check_function_app = (fun norm tf -> (match ((let _149_473 = (FStar_Syntax_Util.unrefine tf)
in _149_473.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 824 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| (e, imp)::tl -> begin
(
# 827 "FStar.TypeChecker.Tc.fst"
let _64_1279 = (tc_term env e)
in (match (_64_1279) with
| (e, c, g_e) -> begin
(
# 828 "FStar.TypeChecker.Tc.fst"
let _64_1283 = (tc_args env tl)
in (match (_64_1283) with
| (args, comps, g_rest) -> begin
(let _149_478 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, (c)::comps, _149_478))
end))
end))
end))
in (
# 836 "FStar.TypeChecker.Tc.fst"
let _64_1287 = (tc_args env args)
in (match (_64_1287) with
| (args, comps, g_args) -> begin
(
# 837 "FStar.TypeChecker.Tc.fst"
let bs = (let _149_480 = (FStar_All.pipe_right comps (FStar_List.map (fun c -> (c.FStar_Syntax_Syntax.res_typ, None))))
in (FStar_Syntax_Util.null_binders_of_tks _149_480))
in (
# 838 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _64_1294 -> begin
FStar_Syntax_Util.ml_comp
end)
in (
# 841 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _149_495 = (FStar_Syntax_Subst.compress t)
in _149_495.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_64_1300) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _64_1305 -> begin
ml_or_tot
end)
end)
in (
# 848 "FStar.TypeChecker.Tc.fst"
let cres = (let _149_500 = (let _149_499 = (let _149_498 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _149_498 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _149_499))
in (ml_or_tot _149_500 r))
in (
# 849 "FStar.TypeChecker.Tc.fst"
let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (
# 850 "FStar.TypeChecker.Tc.fst"
let _64_1309 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _149_503 = (FStar_Syntax_Print.term_to_string head)
in (let _149_502 = (FStar_Syntax_Print.term_to_string tf)
in (let _149_501 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _149_503 _149_502 _149_501))))
end else begin
()
end
in (
# 855 "FStar.TypeChecker.Tc.fst"
let _64_1311 = (let _149_504 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _149_504))
in (
# 856 "FStar.TypeChecker.Tc.fst"
let comp = (let _149_507 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_TypeChecker_Util.bind env None c (None, out))) ((chead)::comps) _149_507))
in (let _149_509 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _149_508 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_149_509, comp, _149_508)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 860 "FStar.TypeChecker.Tc.fst"
let _64_1322 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_64_1322) with
| (bs, c) -> begin
(
# 862 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun _64_1330 bs cres args -> (match (_64_1330) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (_64_1337)))::rest, (_64_1345, None)::_64_1343) -> begin
(
# 873 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 874 "FStar.TypeChecker.Tc.fst"
let _64_1351 = (check_no_escape (Some (head)) env fvs t)
in (
# 875 "FStar.TypeChecker.Tc.fst"
let _64_1357 = (FStar_TypeChecker_Util.new_implicit_var env t)
in (match (_64_1357) with
| (varg, _64_1355, implicits) -> begin
(
# 876 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (
# 877 "FStar.TypeChecker.Tc.fst"
let arg = (let _149_518 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _149_518))
in (let _149_520 = (let _149_519 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _149_519, fvs))
in (tc_args _149_520 rest cres args))))
end))))
end
| ((x, aqual)::rest, (e, aq)::rest') -> begin
(
# 881 "FStar.TypeChecker.Tc.fst"
let _64_1389 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _64_1388 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (
# 886 "FStar.TypeChecker.Tc.fst"
let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 887 "FStar.TypeChecker.Tc.fst"
let x = (
# 887 "FStar.TypeChecker.Tc.fst"
let _64_1392 = x
in {FStar_Syntax_Syntax.ppname = _64_1392.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_1392.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (
# 888 "FStar.TypeChecker.Tc.fst"
let _64_1395 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _149_521 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _149_521))
end else begin
()
end
in (
# 889 "FStar.TypeChecker.Tc.fst"
let _64_1397 = (check_no_escape (Some (head)) env fvs targ)
in (
# 890 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (
# 891 "FStar.TypeChecker.Tc.fst"
let env = (
# 891 "FStar.TypeChecker.Tc.fst"
let _64_1400 = env
in {FStar_TypeChecker_Env.solver = _64_1400.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_1400.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_1400.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_1400.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_1400.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_1400.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_1400.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_1400.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_1400.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_1400.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_1400.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_1400.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _64_1400.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _64_1400.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _64_1400.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _64_1400.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_1400.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_1400.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_1400.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_1400.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_1400.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 892 "FStar.TypeChecker.Tc.fst"
let _64_1403 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_524 = (FStar_Syntax_Print.tag_of_term e)
in (let _149_523 = (FStar_Syntax_Print.term_to_string e)
in (let _149_522 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _149_524 _149_523 _149_522))))
end else begin
()
end
in (
# 893 "FStar.TypeChecker.Tc.fst"
let _64_1408 = (tc_term env e)
in (match (_64_1408) with
| (e, c, g_e) -> begin
(
# 894 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (
# 896 "FStar.TypeChecker.Tc.fst"
let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(
# 898 "FStar.TypeChecker.Tc.fst"
let subst = (let _149_525 = (FStar_List.hd bs)
in (maybe_extend_subst subst _149_525 e))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(
# 901 "FStar.TypeChecker.Tc.fst"
let subst = (let _149_526 = (FStar_List.hd bs)
in (maybe_extend_subst subst _149_526 e))
in (
# 902 "FStar.TypeChecker.Tc.fst"
let _64_1415 = (((Some (x), c))::comps, g)
in (match (_64_1415) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _149_527 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _149_527)) then begin
(
# 906 "FStar.TypeChecker.Tc.fst"
let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (
# 907 "FStar.TypeChecker.Tc.fst"
let arg' = (let _149_528 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _149_528))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (newx), c))::comps, g, fvs) rest cres rest')))
end else begin
(let _149_532 = (let _149_531 = (let _149_530 = (let _149_529 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _149_529))
in (_149_530)::arg_rets)
in (subst, (arg)::outargs, _149_531, ((Some (x), c))::comps, g, (x)::fvs))
in (tc_args _149_532 rest cres rest'))
end
end
end))
end))))))))))
end
| (_64_1419, []) -> begin
(
# 916 "FStar.TypeChecker.Tc.fst"
let _64_1422 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (
# 917 "FStar.TypeChecker.Tc.fst"
let _64_1440 = (match (bs) with
| [] -> begin
(
# 920 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (
# 926 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (
# 928 "FStar.TypeChecker.Tc.fst"
let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _64_1430 -> (match (_64_1430) with
| (_64_1428, c) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (
# 935 "FStar.TypeChecker.Tc.fst"
let cres = if refine_with_equality then begin
(let _149_534 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _149_534 cres))
end else begin
(
# 941 "FStar.TypeChecker.Tc.fst"
let _64_1432 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_537 = (FStar_Syntax_Print.term_to_string head)
in (let _149_536 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _149_535 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _149_537 _149_536 _149_535))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _64_1436 -> begin
(
# 950 "FStar.TypeChecker.Tc.fst"
let g = (let _149_538 = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (FStar_All.pipe_right _149_538 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _149_543 = (let _149_542 = (let _149_541 = (let _149_540 = (let _149_539 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _149_539))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _149_540))
in (FStar_Syntax_Syntax.mk_Total _149_541))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _149_542))
in (_149_543, g)))
end)
in (match (_64_1440) with
| (cres, g) -> begin
(
# 953 "FStar.TypeChecker.Tc.fst"
let _64_1441 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_544 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _149_544))
end else begin
()
end
in (
# 954 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_List.fold_left (fun out c -> (FStar_TypeChecker_Util.bind env None (Prims.snd c) ((Prims.fst c), out))) cres comps)
in (
# 955 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.bind env None chead (None, comp))
in (
# 956 "FStar.TypeChecker.Tc.fst"
let app = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev outargs) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (
# 957 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.record_application_site env app comp)
in (
# 958 "FStar.TypeChecker.Tc.fst"
let _64_1451 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp g)
in (match (_64_1451) with
| (comp, g) -> begin
(
# 959 "FStar.TypeChecker.Tc.fst"
let _64_1452 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_550 = (FStar_TypeChecker_Normalize.term_to_string env app)
in (let _149_549 = (let _149_548 = (comp.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Print.comp_to_string _149_548))
in (FStar_Util.print2 "\t Type of app term %s is %s\n" _149_550 _149_549)))
end else begin
()
end
in (app, comp, g))
end)))))))
end)))
end
| ([], arg::_64_1456) -> begin
(
# 965 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun norm tres -> (
# 966 "FStar.TypeChecker.Tc.fst"
let tres = (let _149_555 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _149_555 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(
# 969 "FStar.TypeChecker.Tc.fst"
let _64_1468 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_556 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _149_556))
end else begin
()
end
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs (FStar_Syntax_Util.lcomp_of_comp cres') args))
end
| _64_1471 when (not (norm)) -> begin
(let _149_557 = (unfold_whnf env tres)
in (aux true _149_557))
end
| _64_1473 -> begin
(let _149_563 = (let _149_562 = (let _149_561 = (let _149_559 = (FStar_TypeChecker_Normalize.term_to_string env tf)
in (let _149_558 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _149_559 _149_558)))
in (let _149_560 = (FStar_Syntax_Syntax.argpos arg)
in (_149_561, _149_560)))
in FStar_Syntax_Syntax.Error (_149_562))
in (Prims.raise _149_563))
end)))
in (aux false cres.FStar_Syntax_Syntax.res_typ))
end)
end))
in (tc_args ([], [], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs (FStar_Syntax_Util.lcomp_of_comp c) args))
end))
end
| _64_1475 -> begin
if (not (norm)) then begin
(let _149_564 = (unfold_whnf env tf)
in (check_function_app true _149_564))
end else begin
(let _149_567 = (let _149_566 = (let _149_565 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_149_565, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_149_566))
in (Prims.raise _149_567))
end
end))
in (let _149_569 = (let _149_568 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _149_568))
in (check_function_app false _149_569))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (
# 995 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 996 "FStar.TypeChecker.Tc.fst"
let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(
# 999 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in (
# 1000 "FStar.TypeChecker.Tc.fst"
let _64_1511 = (FStar_List.fold_left2 (fun _64_1492 _64_1495 _64_1498 -> (match ((_64_1492, _64_1495, _64_1498)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(
# 1001 "FStar.TypeChecker.Tc.fst"
let _64_1499 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1002 "FStar.TypeChecker.Tc.fst"
let _64_1504 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_64_1504) with
| (e, c, g) -> begin
(
# 1003 "FStar.TypeChecker.Tc.fst"
let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (
# 1004 "FStar.TypeChecker.Tc.fst"
let g = (let _149_579 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _149_579 g))
in (
# 1005 "FStar.TypeChecker.Tc.fst"
let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _149_583 = (let _149_581 = (let _149_580 = (FStar_Syntax_Syntax.as_arg e)
in (_149_580)::[])
in (FStar_List.append seen _149_581))
in (let _149_582 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_149_583, _149_582, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_64_1511) with
| (args, guard, ghost) -> begin
(
# 1009 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (
# 1010 "FStar.TypeChecker.Tc.fst"
let c = if ghost then begin
(let _149_584 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _149_584 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (
# 1011 "FStar.TypeChecker.Tc.fst"
let _64_1516 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_64_1516) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _64_1518 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (
# 1031 "FStar.TypeChecker.Tc.fst"
let _64_1525 = (FStar_Syntax_Subst.open_branch branch)
in (match (_64_1525) with
| (pattern, when_clause, branch_exp) -> begin
(
# 1032 "FStar.TypeChecker.Tc.fst"
let _64_1530 = branch
in (match (_64_1530) with
| (cpat, _64_1528, cbr) -> begin
(
# 1035 "FStar.TypeChecker.Tc.fst"
let tc_pat = (fun allow_implicits pat_t p0 -> (
# 1042 "FStar.TypeChecker.Tc.fst"
let _64_1538 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_64_1538) with
| (pat_bvs, exps, p) -> begin
(
# 1043 "FStar.TypeChecker.Tc.fst"
let _64_1539 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_596 = (FStar_Syntax_Print.pat_to_string p0)
in (let _149_595 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _149_596 _149_595)))
end else begin
()
end
in (
# 1045 "FStar.TypeChecker.Tc.fst"
let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (
# 1046 "FStar.TypeChecker.Tc.fst"
let _64_1545 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_64_1545) with
| (env1, _64_1544) -> begin
(
# 1047 "FStar.TypeChecker.Tc.fst"
let env1 = (
# 1047 "FStar.TypeChecker.Tc.fst"
let _64_1546 = env1
in {FStar_TypeChecker_Env.solver = _64_1546.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_1546.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_1546.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_1546.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_1546.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_1546.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_1546.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_1546.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _64_1546.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_1546.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_1546.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _64_1546.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _64_1546.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _64_1546.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _64_1546.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _64_1546.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_1546.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_1546.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_1546.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_1546.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_1546.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1048 "FStar.TypeChecker.Tc.fst"
let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (
# 1049 "FStar.TypeChecker.Tc.fst"
let _64_1585 = (let _149_619 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (
# 1050 "FStar.TypeChecker.Tc.fst"
let _64_1551 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_599 = (FStar_Syntax_Print.term_to_string e)
in (let _149_598 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _149_599 _149_598)))
end else begin
()
end
in (
# 1053 "FStar.TypeChecker.Tc.fst"
let _64_1556 = (tc_term env1 e)
in (match (_64_1556) with
| (e, lc, g) -> begin
(
# 1055 "FStar.TypeChecker.Tc.fst"
let _64_1557 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_601 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _149_600 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _149_601 _149_600)))
end else begin
()
end
in (
# 1058 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (
# 1059 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (
# 1060 "FStar.TypeChecker.Tc.fst"
let _64_1563 = (let _149_602 = (FStar_TypeChecker_Rel.discharge_guard env (
# 1060 "FStar.TypeChecker.Tc.fst"
let _64_1561 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _64_1561.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _64_1561.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _64_1561.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _149_602 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1061 "FStar.TypeChecker.Tc.fst"
let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (
# 1062 "FStar.TypeChecker.Tc.fst"
let uvars_to_string = (fun uvs -> (let _149_607 = (let _149_606 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _149_606 (FStar_List.map (fun _64_1571 -> (match (_64_1571) with
| (u, _64_1570) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _149_607 (FStar_String.concat ", "))))
in (
# 1063 "FStar.TypeChecker.Tc.fst"
let uvs1 = (FStar_Syntax_Free.uvars e')
in (
# 1064 "FStar.TypeChecker.Tc.fst"
let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (
# 1065 "FStar.TypeChecker.Tc.fst"
let _64_1579 = if (let _149_608 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _149_608)) then begin
(
# 1066 "FStar.TypeChecker.Tc.fst"
let unresolved = (let _149_609 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _149_609 FStar_Util.set_elements))
in (let _149_617 = (let _149_616 = (let _149_615 = (let _149_614 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _149_613 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _149_612 = (let _149_611 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _64_1578 -> (match (_64_1578) with
| (u, _64_1577) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _149_611 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _149_614 _149_613 _149_612))))
in (_149_615, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_149_616))
in (Prims.raise _149_617)))
end else begin
()
end
in (
# 1073 "FStar.TypeChecker.Tc.fst"
let _64_1581 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_618 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _149_618))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _149_619 FStar_List.unzip))
in (match (_64_1585) with
| (exps, norm_exps) -> begin
(
# 1078 "FStar.TypeChecker.Tc.fst"
let p = (FStar_TypeChecker_Util.decorate_pattern env p exps)
in (p, pat_bvs, pat_env, exps, norm_exps))
end))))
end))))
end)))
in (
# 1082 "FStar.TypeChecker.Tc.fst"
let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (
# 1083 "FStar.TypeChecker.Tc.fst"
let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (
# 1084 "FStar.TypeChecker.Tc.fst"
let _64_1592 = (let _149_620 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _149_620 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_64_1592) with
| (scrutinee_env, _64_1591) -> begin
(
# 1087 "FStar.TypeChecker.Tc.fst"
let _64_1598 = (tc_pat true pat_t pattern)
in (match (_64_1598) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(
# 1090 "FStar.TypeChecker.Tc.fst"
let _64_1608 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(
# 1097 "FStar.TypeChecker.Tc.fst"
let _64_1605 = (let _149_621 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _149_621 e))
in (match (_64_1605) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_64_1608) with
| (when_clause, g_when) -> begin
(
# 1101 "FStar.TypeChecker.Tc.fst"
let _64_1612 = (tc_term pat_env branch_exp)
in (match (_64_1612) with
| (branch_exp, c, g_branch) -> begin
(
# 1105 "FStar.TypeChecker.Tc.fst"
let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _149_623 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _149_622 -> Some (_149_622)) _149_623))
end)
in (
# 1112 "FStar.TypeChecker.Tc.fst"
let _64_1668 = (
# 1115 "FStar.TypeChecker.Tc.fst"
let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (
# 1116 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _64_1630 -> begin
(
# 1122 "FStar.TypeChecker.Tc.fst"
let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _149_627 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _149_626 -> Some (_149_626)) _149_627))
end))
end))) None))
in (
# 1127 "FStar.TypeChecker.Tc.fst"
let _64_1638 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_64_1638) with
| (c, g_branch) -> begin
(
# 1131 "FStar.TypeChecker.Tc.fst"
let _64_1663 = (match ((eqs, when_condition)) with
| (None, None) -> begin
(c, g_when)
end
| (Some (f), None) -> begin
(
# 1137 "FStar.TypeChecker.Tc.fst"
let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1138 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _149_630 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _149_629 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_149_630, _149_629)))))
end
| (Some (f), Some (w)) -> begin
(
# 1143 "FStar.TypeChecker.Tc.fst"
let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1144 "FStar.TypeChecker.Tc.fst"
let g_fw = (let _149_631 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_149_631))
in (let _149_634 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _149_633 = (let _149_632 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _149_632 g_when))
in (_149_634, _149_633)))))
end
| (None, Some (w)) -> begin
(
# 1149 "FStar.TypeChecker.Tc.fst"
let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (
# 1150 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _149_635 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_149_635, g_when))))
end)
in (match (_64_1663) with
| (c_weak, g_when_weak) -> begin
(
# 1155 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _149_637 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _149_636 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_149_637, _149_636, g_branch))))
end))
end)))
in (match (_64_1668) with
| (c, g_when, g_branch) -> begin
(
# 1173 "FStar.TypeChecker.Tc.fst"
let branch_guard = (
# 1175 "FStar.TypeChecker.Tc.fst"
let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (
# 1176 "FStar.TypeChecker.Tc.fst"
let discriminate = (fun scrutinee_tm f -> if ((let _149_647 = (let _149_646 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _149_646))
in (FStar_List.length _149_647)) > 1) then begin
(
# 1179 "FStar.TypeChecker.Tc.fst"
let disc = (let _149_648 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _149_648 FStar_Syntax_Syntax.Delta_equational None))
in (
# 1180 "FStar.TypeChecker.Tc.fst"
let disc = (let _149_650 = (let _149_649 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_149_649)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _149_650 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _149_651 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_149_651)::[])))
end else begin
[]
end)
in (
# 1184 "FStar.TypeChecker.Tc.fst"
let fail = (fun _64_1678 -> (match (()) with
| () -> begin
(let _149_657 = (let _149_656 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _149_655 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _149_654 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _149_656 _149_655 _149_654))))
in (FStar_All.failwith _149_657))
end))
in (
# 1190 "FStar.TypeChecker.Tc.fst"
let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _64_1685) -> begin
(head_constructor t)
end
| _64_1689 -> begin
(fail ())
end))
in (
# 1195 "FStar.TypeChecker.Tc.fst"
let pat_exp = (let _149_660 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _149_660 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_64_1714) -> begin
(let _149_665 = (let _149_664 = (let _149_663 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _149_662 = (let _149_661 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_149_661)::[])
in (_149_663)::_149_662))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _149_664 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_149_665)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 1204 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _149_666 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _149_666))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 1209 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(
# 1212 "FStar.TypeChecker.Tc.fst"
let sub_term_guards = (let _149_673 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _64_1732 -> (match (_64_1732) with
| (ei, _64_1731) -> begin
(
# 1213 "FStar.TypeChecker.Tc.fst"
let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _64_1736 -> begin
(
# 1217 "FStar.TypeChecker.Tc.fst"
let sub_term = (let _149_672 = (let _149_669 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _149_669 FStar_Syntax_Syntax.Delta_equational None))
in (let _149_671 = (let _149_670 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_149_670)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _149_672 _149_671 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _149_673 FStar_List.flatten))
in (let _149_674 = (discriminate scrutinee_tm f)
in (FStar_List.append _149_674 sub_term_guards)))
end)
end
| _64_1740 -> begin
[]
end))))))
in (
# 1223 "FStar.TypeChecker.Tc.fst"
let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(
# 1226 "FStar.TypeChecker.Tc.fst"
let t = (let _149_679 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _149_679))
in (
# 1227 "FStar.TypeChecker.Tc.fst"
let _64_1748 = (FStar_Syntax_Util.type_u ())
in (match (_64_1748) with
| (k, _64_1747) -> begin
(
# 1228 "FStar.TypeChecker.Tc.fst"
let _64_1754 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_64_1754) with
| (t, _64_1751, _64_1753) -> begin
t
end))
end)))
end)
in (
# 1232 "FStar.TypeChecker.Tc.fst"
let branch_guard = (let _149_680 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _149_680 FStar_Syntax_Util.mk_disj_l))
in (
# 1235 "FStar.TypeChecker.Tc.fst"
let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
in (
# 1241 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (
# 1243 "FStar.TypeChecker.Tc.fst"
let _64_1762 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_681 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _149_681))
end else begin
()
end
in (let _149_682 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_149_682, branch_guard, c, guard)))))
end)))
end))
end))
end))
end)))))
end))
end)))
and check_top_level_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1257 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1260 "FStar.TypeChecker.Tc.fst"
let _64_1779 = (check_let_bound_def true env lb)
in (match (_64_1779) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(
# 1263 "FStar.TypeChecker.Tc.fst"
let _64_1791 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(
# 1266 "FStar.TypeChecker.Tc.fst"
let g1 = (let _149_685 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _149_685 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1267 "FStar.TypeChecker.Tc.fst"
let _64_1786 = (let _149_689 = (let _149_688 = (let _149_687 = (let _149_686 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _149_686))
in (_149_687)::[])
in (FStar_TypeChecker_Util.generalize env _149_688))
in (FStar_List.hd _149_689))
in (match (_64_1786) with
| (_64_1782, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_64_1791) with
| (g1, e1, univ_vars, c1) -> begin
(
# 1271 "FStar.TypeChecker.Tc.fst"
let _64_1801 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(
# 1273 "FStar.TypeChecker.Tc.fst"
let _64_1794 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_64_1794) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(
# 1276 "FStar.TypeChecker.Tc.fst"
let _64_1795 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _149_690 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _149_690 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _149_691 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_149_691, c1)))
end
end))
end else begin
(
# 1280 "FStar.TypeChecker.Tc.fst"
let _64_1797 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _149_692 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _149_692)))
end
in (match (_64_1801) with
| (e2, c1) -> begin
(
# 1285 "FStar.TypeChecker.Tc.fst"
let cres = (let _149_693 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _149_693))
in (
# 1286 "FStar.TypeChecker.Tc.fst"
let _64_1803 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1288 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _149_694 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_149_694, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _64_1807 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1305 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1308 "FStar.TypeChecker.Tc.fst"
let env = (
# 1308 "FStar.TypeChecker.Tc.fst"
let _64_1818 = env
in {FStar_TypeChecker_Env.solver = _64_1818.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_1818.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_1818.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_1818.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_1818.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_1818.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_1818.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_1818.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_1818.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_1818.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_1818.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_1818.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _64_1818.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _64_1818.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _64_1818.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _64_1818.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_1818.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_1818.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_1818.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_1818.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_1818.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1309 "FStar.TypeChecker.Tc.fst"
let _64_1827 = (let _149_698 = (let _149_697 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _149_697 Prims.fst))
in (check_let_bound_def false _149_698 lb))
in (match (_64_1827) with
| (e1, _64_1823, c1, g1, annotated) -> begin
(
# 1310 "FStar.TypeChecker.Tc.fst"
let x = (
# 1310 "FStar.TypeChecker.Tc.fst"
let _64_1828 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _64_1828.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_1828.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (
# 1311 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (
# 1312 "FStar.TypeChecker.Tc.fst"
let _64_1834 = (let _149_700 = (let _149_699 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_699)::[])
in (FStar_Syntax_Subst.open_term _149_700 e2))
in (match (_64_1834) with
| (xb, e2) -> begin
(
# 1313 "FStar.TypeChecker.Tc.fst"
let xbinder = (FStar_List.hd xb)
in (
# 1314 "FStar.TypeChecker.Tc.fst"
let x = (Prims.fst xbinder)
in (
# 1315 "FStar.TypeChecker.Tc.fst"
let _64_1840 = (let _149_701 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _149_701 e2))
in (match (_64_1840) with
| (e2, c2, g2) -> begin
(
# 1316 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (x), c2))
in (
# 1317 "FStar.TypeChecker.Tc.fst"
let e = (let _149_704 = (let _149_703 = (let _149_702 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _149_702))
in FStar_Syntax_Syntax.Tm_let (_149_703))
in (FStar_Syntax_Syntax.mk _149_704 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 1318 "FStar.TypeChecker.Tc.fst"
let x_eq_e1 = (let _149_707 = (let _149_706 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _149_706 e1))
in (FStar_All.pipe_left (fun _149_705 -> FStar_TypeChecker_Common.NonTrivial (_149_705)) _149_707))
in (
# 1319 "FStar.TypeChecker.Tc.fst"
let g2 = (let _149_709 = (let _149_708 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _149_708 g2))
in (FStar_TypeChecker_Rel.close_guard xb _149_709))
in (
# 1321 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if annotated then begin
(e, cres, guard)
end else begin
(
# 1325 "FStar.TypeChecker.Tc.fst"
let _64_1846 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end)))))
end))))
end))))
end)))
end
| _64_1849 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1334 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1337 "FStar.TypeChecker.Tc.fst"
let _64_1861 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_64_1861) with
| (lbs, e2) -> begin
(
# 1339 "FStar.TypeChecker.Tc.fst"
let _64_1864 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_64_1864) with
| (env0, topt) -> begin
(
# 1340 "FStar.TypeChecker.Tc.fst"
let _64_1867 = (build_let_rec_env true env0 lbs)
in (match (_64_1867) with
| (lbs, rec_env) -> begin
(
# 1341 "FStar.TypeChecker.Tc.fst"
let _64_1870 = (check_let_recs rec_env lbs)
in (match (_64_1870) with
| (lbs, g_lbs) -> begin
(
# 1342 "FStar.TypeChecker.Tc.fst"
let g_lbs = (let _149_712 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _149_712 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1344 "FStar.TypeChecker.Tc.fst"
let all_lb_names = (let _149_715 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _149_715 (fun _149_714 -> Some (_149_714))))
in (
# 1346 "FStar.TypeChecker.Tc.fst"
let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(
# 1352 "FStar.TypeChecker.Tc.fst"
let ecs = (let _149_719 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _149_718 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _149_718)))))
in (FStar_TypeChecker_Util.generalize env _149_719))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _64_1881 -> (match (_64_1881) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (
# 1359 "FStar.TypeChecker.Tc.fst"
let cres = (let _149_721 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _149_721))
in (
# 1360 "FStar.TypeChecker.Tc.fst"
let _64_1884 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1362 "FStar.TypeChecker.Tc.fst"
let _64_1888 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_64_1888) with
| (lbs, e2) -> begin
(let _149_723 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _149_722 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_149_723, cres, _149_722)))
end)))))))
end))
end))
end))
end))
end
| _64_1890 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1373 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1376 "FStar.TypeChecker.Tc.fst"
let _64_1902 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_64_1902) with
| (lbs, e2) -> begin
(
# 1378 "FStar.TypeChecker.Tc.fst"
let _64_1905 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_64_1905) with
| (env0, topt) -> begin
(
# 1379 "FStar.TypeChecker.Tc.fst"
let _64_1908 = (build_let_rec_env false env0 lbs)
in (match (_64_1908) with
| (lbs, rec_env) -> begin
(
# 1380 "FStar.TypeChecker.Tc.fst"
let _64_1911 = (check_let_recs rec_env lbs)
in (match (_64_1911) with
| (lbs, g_lbs) -> begin
(
# 1382 "FStar.TypeChecker.Tc.fst"
let _64_1923 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (
# 1383 "FStar.TypeChecker.Tc.fst"
let x = (
# 1383 "FStar.TypeChecker.Tc.fst"
let _64_1914 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _64_1914.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_1914.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (
# 1384 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1384 "FStar.TypeChecker.Tc.fst"
let _64_1917 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _64_1917.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _64_1917.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _64_1917.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _64_1917.FStar_Syntax_Syntax.lbdef})
in (
# 1385 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], lb.FStar_Syntax_Syntax.lbtyp))
in (env, lb))))) env))
in (match (_64_1923) with
| (env, lbs) -> begin
(
# 1388 "FStar.TypeChecker.Tc.fst"
let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (
# 1390 "FStar.TypeChecker.Tc.fst"
let _64_1929 = (tc_term env e2)
in (match (_64_1929) with
| (e2, cres, g2) -> begin
(
# 1391 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (
# 1392 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (
# 1393 "FStar.TypeChecker.Tc.fst"
let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (
# 1394 "FStar.TypeChecker.Tc.fst"
let cres = (
# 1394 "FStar.TypeChecker.Tc.fst"
let _64_1933 = cres
in {FStar_Syntax_Syntax.eff_name = _64_1933.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _64_1933.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _64_1933.FStar_Syntax_Syntax.comp})
in (
# 1396 "FStar.TypeChecker.Tc.fst"
let _64_1938 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_64_1938) with
| (lbs, e2) -> begin
(
# 1397 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_64_1941) -> begin
(e, cres, guard)
end
| None -> begin
(
# 1401 "FStar.TypeChecker.Tc.fst"
let _64_1944 = (check_no_escape None env bvs tres)
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
| _64_1947 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (
# 1412 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1413 "FStar.TypeChecker.Tc.fst"
let _64_1980 = (FStar_List.fold_left (fun _64_1954 lb -> (match (_64_1954) with
| (lbs, env) -> begin
(
# 1414 "FStar.TypeChecker.Tc.fst"
let _64_1959 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_64_1959) with
| (univ_vars, t, check_t) -> begin
(
# 1415 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (
# 1416 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (
# 1417 "FStar.TypeChecker.Tc.fst"
let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(
# 1422 "FStar.TypeChecker.Tc.fst"
let _64_1968 = (let _149_735 = (let _149_734 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _149_734))
in (tc_check_tot_or_gtot_term (
# 1422 "FStar.TypeChecker.Tc.fst"
let _64_1962 = env0
in {FStar_TypeChecker_Env.solver = _64_1962.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_1962.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_1962.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_1962.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_1962.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_1962.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_1962.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_1962.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_1962.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_1962.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_1962.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_1962.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _64_1962.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _64_1962.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _64_1962.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _64_1962.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_1962.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_1962.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_1962.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_1962.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_1962.FStar_TypeChecker_Env.use_bv_sorts}) t _149_735))
in (match (_64_1968) with
| (t, _64_1966, g) -> begin
(
# 1423 "FStar.TypeChecker.Tc.fst"
let _64_1969 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (
# 1425 "FStar.TypeChecker.Tc.fst"
let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(
# 1427 "FStar.TypeChecker.Tc.fst"
let _64_1972 = env
in {FStar_TypeChecker_Env.solver = _64_1972.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_1972.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_1972.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_1972.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_1972.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_1972.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_1972.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_1972.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_1972.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_1972.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_1972.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_1972.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _64_1972.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _64_1972.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _64_1972.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _64_1972.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_1972.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_1972.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_1972.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_1972.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_1972.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (
# 1429 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1429 "FStar.TypeChecker.Tc.fst"
let _64_1975 = lb
in {FStar_Syntax_Syntax.lbname = _64_1975.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _64_1975.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_64_1980) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (
# 1436 "FStar.TypeChecker.Tc.fst"
let _64_1993 = (let _149_740 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 1437 "FStar.TypeChecker.Tc.fst"
let _64_1987 = (let _149_739 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _149_739 lb.FStar_Syntax_Syntax.lbdef))
in (match (_64_1987) with
| (e, c, g) -> begin
(
# 1438 "FStar.TypeChecker.Tc.fst"
let _64_1988 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1440 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _149_740 FStar_List.unzip))
in (match (_64_1993) with
| (lbs, gs) -> begin
(
# 1442 "FStar.TypeChecker.Tc.fst"
let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (
# 1456 "FStar.TypeChecker.Tc.fst"
let _64_2001 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_64_2001) with
| (env1, _64_2000) -> begin
(
# 1457 "FStar.TypeChecker.Tc.fst"
let e1 = lb.FStar_Syntax_Syntax.lbdef
in (
# 1460 "FStar.TypeChecker.Tc.fst"
let _64_2007 = (check_lbtyp top_level env lb)
in (match (_64_2007) with
| (topt, wf_annot, univ_vars, env1) -> begin
(
# 1462 "FStar.TypeChecker.Tc.fst"
let _64_2008 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1466 "FStar.TypeChecker.Tc.fst"
let _64_2015 = (tc_maybe_toplevel_term (
# 1466 "FStar.TypeChecker.Tc.fst"
let _64_2010 = env1
in {FStar_TypeChecker_Env.solver = _64_2010.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_2010.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_2010.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_2010.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_2010.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_2010.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_2010.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_2010.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_2010.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_2010.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_2010.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_2010.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _64_2010.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _64_2010.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _64_2010.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _64_2010.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_2010.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_2010.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_2010.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_2010.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_2010.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_64_2015) with
| (e1, c1, g1) -> begin
(
# 1469 "FStar.TypeChecker.Tc.fst"
let _64_2019 = (let _149_747 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _64_2016 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _149_747 e1 c1 wf_annot))
in (match (_64_2019) with
| (c1, guard_f) -> begin
(
# 1472 "FStar.TypeChecker.Tc.fst"
let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (
# 1474 "FStar.TypeChecker.Tc.fst"
let _64_2021 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _149_748 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _149_748))
end else begin
()
end
in (let _149_749 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _149_749))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (
# 1486 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 1489 "FStar.TypeChecker.Tc.fst"
let _64_2028 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _64_2031 -> begin
(
# 1493 "FStar.TypeChecker.Tc.fst"
let _64_2034 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_64_2034) with
| (univ_vars, t) -> begin
(
# 1494 "FStar.TypeChecker.Tc.fst"
let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _149_753 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _149_753))
end else begin
(
# 1501 "FStar.TypeChecker.Tc.fst"
let _64_2039 = (FStar_Syntax_Util.type_u ())
in (match (_64_2039) with
| (k, _64_2038) -> begin
(
# 1502 "FStar.TypeChecker.Tc.fst"
let _64_2044 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_64_2044) with
| (t, _64_2042, g) -> begin
(
# 1503 "FStar.TypeChecker.Tc.fst"
let _64_2045 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _149_756 = (let _149_754 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _149_754))
in (let _149_755 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _149_756 _149_755)))
end else begin
()
end
in (
# 1507 "FStar.TypeChecker.Tc.fst"
let t = (norm env1 t)
in (let _149_757 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _149_757))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _64_2051 -> (match (_64_2051) with
| (x, imp) -> begin
(
# 1512 "FStar.TypeChecker.Tc.fst"
let _64_2054 = (FStar_Syntax_Util.type_u ())
in (match (_64_2054) with
| (tu, u) -> begin
(
# 1513 "FStar.TypeChecker.Tc.fst"
let _64_2059 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_64_2059) with
| (t, _64_2057, g) -> begin
(
# 1514 "FStar.TypeChecker.Tc.fst"
let x = ((
# 1514 "FStar.TypeChecker.Tc.fst"
let _64_2060 = x
in {FStar_Syntax_Syntax.ppname = _64_2060.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_2060.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (
# 1515 "FStar.TypeChecker.Tc.fst"
let _64_2063 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_761 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _149_760 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _149_761 _149_760)))
end else begin
()
end
in (let _149_762 = (maybe_push_binding env x)
in (x, _149_762, g, u))))
end))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe Prims.list) = (fun env bs -> (
# 1520 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_TypeChecker_Rel.trivial_guard, [])
end
| b::bs -> begin
(
# 1523 "FStar.TypeChecker.Tc.fst"
let _64_2078 = (tc_binder env b)
in (match (_64_2078) with
| (b, env', g, u) -> begin
(
# 1524 "FStar.TypeChecker.Tc.fst"
let _64_2083 = (aux env' bs)
in (match (_64_2083) with
| (bs, env', g', us) -> begin
(let _149_770 = (let _149_769 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _149_769))
in ((b)::bs, env', _149_770, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (
# 1529 "FStar.TypeChecker.Tc.fst"
let tc_args = (fun env args -> (FStar_List.fold_right (fun _64_2091 _64_2094 -> (match ((_64_2091, _64_2094)) with
| ((t, imp), (args, g)) -> begin
(
# 1533 "FStar.TypeChecker.Tc.fst"
let _64_2099 = (tc_term env t)
in (match (_64_2099) with
| (t, _64_2097, g') -> begin
(let _149_779 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _149_779))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _64_2103 -> (match (_64_2103) with
| (pats, g) -> begin
(
# 1536 "FStar.TypeChecker.Tc.fst"
let _64_2106 = (tc_args env p)
in (match (_64_2106) with
| (args, g') -> begin
(let _149_782 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _149_782))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1541 "FStar.TypeChecker.Tc.fst"
let _64_2112 = (tc_maybe_toplevel_term env e)
in (match (_64_2112) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(
# 1544 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (
# 1545 "FStar.TypeChecker.Tc.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 1546 "FStar.TypeChecker.Tc.fst"
let _64_2115 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_785 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _149_785))
end else begin
()
end
in (
# 1547 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 1548 "FStar.TypeChecker.Tc.fst"
let _64_2120 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _149_786 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_149_786, false))
end else begin
(let _149_787 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_149_787, true))
end
in (match (_64_2120) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _149_788 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _149_788))
end
| _64_2124 -> begin
if allow_ghost then begin
(let _149_791 = (let _149_790 = (let _149_789 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_149_789, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_149_790))
in (Prims.raise _149_791))
end else begin
(let _149_794 = (let _149_793 = (let _149_792 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_149_792, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_149_793))
in (Prims.raise _149_794))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 1562 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))

# 1566 "FStar.TypeChecker.Tc.fst"
let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (
# 1567 "FStar.TypeChecker.Tc.fst"
let _64_2134 = (tc_tot_or_gtot_term env t)
in (match (_64_2134) with
| (t, c, g) -> begin
(
# 1568 "FStar.TypeChecker.Tc.fst"
let _64_2135 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))

# 1571 "FStar.TypeChecker.Tc.fst"
let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (
# 1572 "FStar.TypeChecker.Tc.fst"
let _64_2143 = (tc_check_tot_or_gtot_term env t k)
in (match (_64_2143) with
| (t, c, g) -> begin
(
# 1573 "FStar.TypeChecker.Tc.fst"
let _64_2144 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))

# 1576 "FStar.TypeChecker.Tc.fst"
let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _149_814 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _149_814)))

# 1579 "FStar.TypeChecker.Tc.fst"
let check_nogen = (fun env t k -> (
# 1580 "FStar.TypeChecker.Tc.fst"
let t = (tc_check_trivial_guard env t k)
in (let _149_818 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _149_818))))

# 1583 "FStar.TypeChecker.Tc.fst"
let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (
# 1584 "FStar.TypeChecker.Tc.fst"
let _64_2159 = (tc_binders env tps)
in (match (_64_2159) with
| (tps, env, g, us) -> begin
(
# 1585 "FStar.TypeChecker.Tc.fst"
let _64_2160 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))

# 1588 "FStar.TypeChecker.Tc.fst"
let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (
# 1589 "FStar.TypeChecker.Tc.fst"
let fail = (fun _64_2166 -> (match (()) with
| () -> begin
(let _149_833 = (let _149_832 = (let _149_831 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_149_831, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_149_832))
in (Prims.raise _149_833))
end))
in (
# 1590 "FStar.TypeChecker.Tc.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1593 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _64_2183)::(wp, _64_2179)::(_wlp, _64_2175)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _64_2187 -> begin
(fail ())
end))
end
| _64_2189 -> begin
(fail ())
end))))

# 1600 "FStar.TypeChecker.Tc.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 1603 "FStar.TypeChecker.Tc.fst"
let _64_2196 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_64_2196) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _64_2198 -> begin
(
# 1606 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow binders c)
in (
# 1607 "FStar.TypeChecker.Tc.fst"
let _64_2202 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_64_2202) with
| (uvs, t') -> begin
(match ((let _149_840 = (FStar_Syntax_Subst.compress t')
in _149_840.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _64_2208 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 1612 "FStar.TypeChecker.Tc.fst"
let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (
# 1613 "FStar.TypeChecker.Tc.fst"
let fail = (fun t -> (let _149_851 = (let _149_850 = (let _149_849 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_149_849, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_149_850))
in (Prims.raise _149_851)))
in (match ((let _149_852 = (FStar_Syntax_Subst.compress signature)
in _149_852.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1616 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _64_2229)::(wp, _64_2225)::(_wlp, _64_2221)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _64_2233 -> begin
(fail signature)
end))
end
| _64_2235 -> begin
(fail signature)
end)))

# 1623 "FStar.TypeChecker.Tc.fst"
let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (
# 1624 "FStar.TypeChecker.Tc.fst"
let _64_2240 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_64_2240) with
| (a, wp) -> begin
(
# 1625 "FStar.TypeChecker.Tc.fst"
let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _64_2243 -> begin
(
# 1629 "FStar.TypeChecker.Tc.fst"
let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (
# 1630 "FStar.TypeChecker.Tc.fst"
let op = (fun ts -> (
# 1631 "FStar.TypeChecker.Tc.fst"
let _64_2247 = ()
in (
# 1632 "FStar.TypeChecker.Tc.fst"
let t0 = (Prims.snd ts)
in (
# 1633 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (
# 1635 "FStar.TypeChecker.Tc.fst"
let _64_2251 = ed
in (let _149_871 = (op ed.FStar_Syntax_Syntax.ret)
in (let _149_870 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _149_869 = (op ed.FStar_Syntax_Syntax.bind_wlp)
in (let _149_868 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _149_867 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _149_866 = (op ed.FStar_Syntax_Syntax.ite_wlp)
in (let _149_865 = (op ed.FStar_Syntax_Syntax.wp_binop)
in (let _149_864 = (op ed.FStar_Syntax_Syntax.wp_as_type)
in (let _149_863 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _149_862 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _149_861 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _149_860 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _149_859 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _64_2251.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _64_2251.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _64_2251.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _64_2251.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _64_2251.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _149_871; FStar_Syntax_Syntax.bind_wp = _149_870; FStar_Syntax_Syntax.bind_wlp = _149_869; FStar_Syntax_Syntax.if_then_else = _149_868; FStar_Syntax_Syntax.ite_wp = _149_867; FStar_Syntax_Syntax.ite_wlp = _149_866; FStar_Syntax_Syntax.wp_binop = _149_865; FStar_Syntax_Syntax.wp_as_type = _149_864; FStar_Syntax_Syntax.close_wp = _149_863; FStar_Syntax_Syntax.assert_p = _149_862; FStar_Syntax_Syntax.assume_p = _149_861; FStar_Syntax_Syntax.null_wp = _149_860; FStar_Syntax_Syntax.trivial = _149_859}))))))))))))))))
end)
in (ed, a, wp))
end)))

# 1651 "FStar.TypeChecker.Tc.fst"
let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (
# 1652 "FStar.TypeChecker.Tc.fst"
let _64_2256 = ()
in (
# 1653 "FStar.TypeChecker.Tc.fst"
let _64_2260 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_64_2260) with
| (binders_un, signature_un) -> begin
(
# 1654 "FStar.TypeChecker.Tc.fst"
let _64_2265 = (tc_tparams env0 binders_un)
in (match (_64_2265) with
| (binders, env, _64_2264) -> begin
(
# 1655 "FStar.TypeChecker.Tc.fst"
let _64_2269 = (tc_trivial_guard env signature_un)
in (match (_64_2269) with
| (signature, _64_2268) -> begin
(
# 1656 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1656 "FStar.TypeChecker.Tc.fst"
let _64_2270 = ed
in {FStar_Syntax_Syntax.qualifiers = _64_2270.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _64_2270.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _64_2270.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _64_2270.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _64_2270.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _64_2270.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = _64_2270.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _64_2270.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _64_2270.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = _64_2270.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _64_2270.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _64_2270.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _64_2270.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _64_2270.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _64_2270.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _64_2270.FStar_Syntax_Syntax.trivial})
in (
# 1659 "FStar.TypeChecker.Tc.fst"
let _64_2276 = (open_effect_decl env ed)
in (match (_64_2276) with
| (ed, a, wp_a) -> begin
(
# 1660 "FStar.TypeChecker.Tc.fst"
let get_effect_signature = (fun _64_2278 -> (match (()) with
| () -> begin
(
# 1661 "FStar.TypeChecker.Tc.fst"
let _64_2282 = (tc_trivial_guard env signature_un)
in (match (_64_2282) with
| (signature, _64_2281) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (
# 1665 "FStar.TypeChecker.Tc.fst"
let env = (let _149_878 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _149_878))
in (
# 1667 "FStar.TypeChecker.Tc.fst"
let _64_2284 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _149_881 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _149_880 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _149_879 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checked effect signature: %s %s : %s\n" _149_881 _149_880 _149_879))))
end else begin
()
end
in (
# 1673 "FStar.TypeChecker.Tc.fst"
let check_and_gen' = (fun env _64_2291 k -> (match (_64_2291) with
| (_64_2289, t) -> begin
(check_and_gen env t k)
end))
in (
# 1676 "FStar.TypeChecker.Tc.fst"
let ret = (
# 1677 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_893 = (let _149_891 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_890 = (let _149_889 = (let _149_888 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _149_888))
in (_149_889)::[])
in (_149_891)::_149_890))
in (let _149_892 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _149_893 _149_892)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (
# 1680 "FStar.TypeChecker.Tc.fst"
let bind_wp = (
# 1681 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1682 "FStar.TypeChecker.Tc.fst"
let _64_2298 = (get_effect_signature ())
in (match (_64_2298) with
| (b, wp_b) -> begin
(
# 1683 "FStar.TypeChecker.Tc.fst"
let a_wp_b = (let _149_897 = (let _149_895 = (let _149_894 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _149_894))
in (_149_895)::[])
in (let _149_896 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _149_897 _149_896)))
in (
# 1684 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = a_wp_b
in (
# 1685 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_910 = (let _149_908 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_907 = (let _149_906 = (FStar_Syntax_Syntax.mk_binder b)
in (let _149_905 = (let _149_904 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _149_903 = (let _149_902 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _149_901 = (let _149_900 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (let _149_899 = (let _149_898 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_149_898)::[])
in (_149_900)::_149_899))
in (_149_902)::_149_901))
in (_149_904)::_149_903))
in (_149_906)::_149_905))
in (_149_908)::_149_907))
in (let _149_909 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _149_910 _149_909)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k))))
end)))
in (
# 1691 "FStar.TypeChecker.Tc.fst"
let bind_wlp = (
# 1692 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1693 "FStar.TypeChecker.Tc.fst"
let _64_2306 = (get_effect_signature ())
in (match (_64_2306) with
| (b, wlp_b) -> begin
(
# 1694 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = (let _149_914 = (let _149_912 = (let _149_911 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _149_911))
in (_149_912)::[])
in (let _149_913 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _149_914 _149_913)))
in (
# 1695 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_923 = (let _149_921 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_920 = (let _149_919 = (FStar_Syntax_Syntax.mk_binder b)
in (let _149_918 = (let _149_917 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _149_916 = (let _149_915 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_149_915)::[])
in (_149_917)::_149_916))
in (_149_919)::_149_918))
in (_149_921)::_149_920))
in (let _149_922 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _149_923 _149_922)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wlp expected_k)))
end)))
in (
# 1701 "FStar.TypeChecker.Tc.fst"
let if_then_else = (
# 1702 "FStar.TypeChecker.Tc.fst"
let p = (let _149_925 = (let _149_924 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _149_924 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _149_925))
in (
# 1703 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_934 = (let _149_932 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_931 = (let _149_930 = (FStar_Syntax_Syntax.mk_binder p)
in (let _149_929 = (let _149_928 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _149_927 = (let _149_926 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_149_926)::[])
in (_149_928)::_149_927))
in (_149_930)::_149_929))
in (_149_932)::_149_931))
in (let _149_933 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_934 _149_933)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (
# 1709 "FStar.TypeChecker.Tc.fst"
let ite_wp = (
# 1710 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1711 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_941 = (let _149_939 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_938 = (let _149_937 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _149_936 = (let _149_935 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_149_935)::[])
in (_149_937)::_149_936))
in (_149_939)::_149_938))
in (let _149_940 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_941 _149_940)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k)))
in (
# 1717 "FStar.TypeChecker.Tc.fst"
let ite_wlp = (
# 1718 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1719 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_946 = (let _149_944 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_943 = (let _149_942 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (_149_942)::[])
in (_149_944)::_149_943))
in (let _149_945 = (FStar_Syntax_Syntax.mk_Total wlp_a)
in (FStar_Syntax_Util.arrow _149_946 _149_945)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wlp expected_k)))
in (
# 1724 "FStar.TypeChecker.Tc.fst"
let wp_binop = (
# 1725 "FStar.TypeChecker.Tc.fst"
let bin_op = (
# 1726 "FStar.TypeChecker.Tc.fst"
let _64_2321 = (FStar_Syntax_Util.type_u ())
in (match (_64_2321) with
| (t1, u1) -> begin
(
# 1727 "FStar.TypeChecker.Tc.fst"
let _64_2324 = (FStar_Syntax_Util.type_u ())
in (match (_64_2324) with
| (t2, u2) -> begin
(
# 1728 "FStar.TypeChecker.Tc.fst"
let t = (let _149_947 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_max ((u1)::(u2)::[]))) None _149_947))
in (let _149_952 = (let _149_950 = (FStar_Syntax_Syntax.null_binder t1)
in (let _149_949 = (let _149_948 = (FStar_Syntax_Syntax.null_binder t2)
in (_149_948)::[])
in (_149_950)::_149_949))
in (let _149_951 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _149_952 _149_951))))
end))
end))
in (
# 1730 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_961 = (let _149_959 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_958 = (let _149_957 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _149_956 = (let _149_955 = (FStar_Syntax_Syntax.null_binder bin_op)
in (let _149_954 = (let _149_953 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_149_953)::[])
in (_149_955)::_149_954))
in (_149_957)::_149_956))
in (_149_959)::_149_958))
in (let _149_960 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_961 _149_960)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_binop expected_k)))
in (
# 1737 "FStar.TypeChecker.Tc.fst"
let wp_as_type = (
# 1738 "FStar.TypeChecker.Tc.fst"
let _64_2332 = (FStar_Syntax_Util.type_u ())
in (match (_64_2332) with
| (t, _64_2331) -> begin
(
# 1739 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_966 = (let _149_964 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_963 = (let _149_962 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_149_962)::[])
in (_149_964)::_149_963))
in (let _149_965 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _149_966 _149_965)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (
# 1744 "FStar.TypeChecker.Tc.fst"
let close_wp = (
# 1745 "FStar.TypeChecker.Tc.fst"
let b = (let _149_968 = (let _149_967 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _149_967 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _149_968))
in (
# 1746 "FStar.TypeChecker.Tc.fst"
let b_wp_a = (let _149_972 = (let _149_970 = (let _149_969 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _149_969))
in (_149_970)::[])
in (let _149_971 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_972 _149_971)))
in (
# 1747 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_979 = (let _149_977 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_976 = (let _149_975 = (FStar_Syntax_Syntax.mk_binder b)
in (let _149_974 = (let _149_973 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_149_973)::[])
in (_149_975)::_149_974))
in (_149_977)::_149_976))
in (let _149_978 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_979 _149_978)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (
# 1751 "FStar.TypeChecker.Tc.fst"
let assert_p = (
# 1752 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_988 = (let _149_986 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_985 = (let _149_984 = (let _149_981 = (let _149_980 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _149_980 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _149_981))
in (let _149_983 = (let _149_982 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_149_982)::[])
in (_149_984)::_149_983))
in (_149_986)::_149_985))
in (let _149_987 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_988 _149_987)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (
# 1758 "FStar.TypeChecker.Tc.fst"
let assume_p = (
# 1759 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_997 = (let _149_995 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_994 = (let _149_993 = (let _149_990 = (let _149_989 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _149_989 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _149_990))
in (let _149_992 = (let _149_991 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_149_991)::[])
in (_149_993)::_149_992))
in (_149_995)::_149_994))
in (let _149_996 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_997 _149_996)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (
# 1765 "FStar.TypeChecker.Tc.fst"
let null_wp = (
# 1766 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_1000 = (let _149_998 = (FStar_Syntax_Syntax.mk_binder a)
in (_149_998)::[])
in (let _149_999 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_1000 _149_999)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (
# 1770 "FStar.TypeChecker.Tc.fst"
let trivial_wp = (
# 1771 "FStar.TypeChecker.Tc.fst"
let _64_2348 = (FStar_Syntax_Util.type_u ())
in (match (_64_2348) with
| (t, _64_2347) -> begin
(
# 1772 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_1005 = (let _149_1003 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_1002 = (let _149_1001 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_149_1001)::[])
in (_149_1003)::_149_1002))
in (let _149_1004 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _149_1005 _149_1004)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (
# 1778 "FStar.TypeChecker.Tc.fst"
let t = (let _149_1006 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _149_1006))
in (
# 1779 "FStar.TypeChecker.Tc.fst"
let _64_2354 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_64_2354) with
| (univs, t) -> begin
(
# 1780 "FStar.TypeChecker.Tc.fst"
let _64_2370 = (match ((let _149_1008 = (let _149_1007 = (FStar_Syntax_Subst.compress t)
in _149_1007.FStar_Syntax_Syntax.n)
in (binders, _149_1008))) with
| ([], _64_2357) -> begin
([], t)
end
| (_64_2360, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _64_2367 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_64_2370) with
| (binders, signature) -> begin
(
# 1784 "FStar.TypeChecker.Tc.fst"
let close = (fun ts -> (let _149_1011 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _149_1011)))
in (
# 1785 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1785 "FStar.TypeChecker.Tc.fst"
let _64_2373 = ed
in (let _149_1024 = (close ret)
in (let _149_1023 = (close bind_wp)
in (let _149_1022 = (close bind_wlp)
in (let _149_1021 = (close if_then_else)
in (let _149_1020 = (close ite_wp)
in (let _149_1019 = (close ite_wlp)
in (let _149_1018 = (close wp_binop)
in (let _149_1017 = (close wp_as_type)
in (let _149_1016 = (close close_wp)
in (let _149_1015 = (close assert_p)
in (let _149_1014 = (close assume_p)
in (let _149_1013 = (close null_wp)
in (let _149_1012 = (close trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _64_2373.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _64_2373.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _149_1024; FStar_Syntax_Syntax.bind_wp = _149_1023; FStar_Syntax_Syntax.bind_wlp = _149_1022; FStar_Syntax_Syntax.if_then_else = _149_1021; FStar_Syntax_Syntax.ite_wp = _149_1020; FStar_Syntax_Syntax.ite_wlp = _149_1019; FStar_Syntax_Syntax.wp_binop = _149_1018; FStar_Syntax_Syntax.wp_as_type = _149_1017; FStar_Syntax_Syntax.close_wp = _149_1016; FStar_Syntax_Syntax.assert_p = _149_1015; FStar_Syntax_Syntax.assume_p = _149_1014; FStar_Syntax_Syntax.null_wp = _149_1013; FStar_Syntax_Syntax.trivial = _149_1012}))))))))))))))
in (
# 1803 "FStar.TypeChecker.Tc.fst"
let _64_2376 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_1025 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _149_1025))
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

# 1807 "FStar.TypeChecker.Tc.fst"
let tc_lex_t = (fun env ses quals lids -> (
# 1814 "FStar.TypeChecker.Tc.fst"
let _64_2382 = ()
in (
# 1815 "FStar.TypeChecker.Tc.fst"
let _64_2390 = ()
in (match (ses) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _64_2419, _64_2421, [], r)::FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _64_2410, r1)::FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _64_2399, r2)::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(
# 1830 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (
# 1831 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (
# 1832 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (
# 1833 "FStar.TypeChecker.Tc.fst"
let tc = FStar_Syntax_Syntax.Sig_inductive_typ ((lex_t, (u)::[], [], t, [], (FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[], [], r))
in (
# 1835 "FStar.TypeChecker.Tc.fst"
let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (
# 1836 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (let _149_1033 = (let _149_1032 = (let _149_1031 = (let _149_1030 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _149_1030 FStar_Syntax_Syntax.Delta_constant None))
in (_149_1031, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_149_1032))
in (FStar_Syntax_Syntax.mk _149_1033 None r1))
in (
# 1837 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (
# 1838 "FStar.TypeChecker.Tc.fst"
let dc_lextop = FStar_Syntax_Syntax.Sig_datacon ((lex_top, (utop)::[], lex_top_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r1))
in (
# 1840 "FStar.TypeChecker.Tc.fst"
let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1841 "FStar.TypeChecker.Tc.fst"
let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1842 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (
# 1843 "FStar.TypeChecker.Tc.fst"
let a = (let _149_1034 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _149_1034))
in (
# 1844 "FStar.TypeChecker.Tc.fst"
let hd = (let _149_1035 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _149_1035))
in (
# 1845 "FStar.TypeChecker.Tc.fst"
let tl = (let _149_1040 = (let _149_1039 = (let _149_1038 = (let _149_1037 = (let _149_1036 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _149_1036 FStar_Syntax_Syntax.Delta_constant None))
in (_149_1037, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_149_1038))
in (FStar_Syntax_Syntax.mk _149_1039 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _149_1040))
in (
# 1846 "FStar.TypeChecker.Tc.fst"
let res = (let _149_1044 = (let _149_1043 = (let _149_1042 = (let _149_1041 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _149_1041 FStar_Syntax_Syntax.Delta_constant None))
in (_149_1042, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_149_1043))
in (FStar_Syntax_Syntax.mk _149_1044 None r2))
in (let _149_1045 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _149_1045))))))
in (
# 1848 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (
# 1849 "FStar.TypeChecker.Tc.fst"
let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _149_1047 = (let _149_1046 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _149_1046))
in FStar_Syntax_Syntax.Sig_bundle (_149_1047)))))))))))))))
end
| _64_2445 -> begin
(let _149_1049 = (let _149_1048 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _149_1048))
in (FStar_All.failwith _149_1049))
end))))

# 1855 "FStar.TypeChecker.Tc.fst"
let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (
# 1918 "FStar.TypeChecker.Tc.fst"
let warn_positivity = (fun l r -> (let _149_1063 = (let _149_1062 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _149_1062))
in (FStar_TypeChecker_Errors.diag r _149_1063)))
in (
# 1920 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1923 "FStar.TypeChecker.Tc.fst"
let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(
# 1928 "FStar.TypeChecker.Tc.fst"
let _64_2467 = ()
in (
# 1929 "FStar.TypeChecker.Tc.fst"
let _64_2469 = (warn_positivity tc r)
in (
# 1930 "FStar.TypeChecker.Tc.fst"
let _64_2473 = (FStar_Syntax_Subst.open_term tps k)
in (match (_64_2473) with
| (tps, k) -> begin
(
# 1931 "FStar.TypeChecker.Tc.fst"
let _64_2477 = (tc_tparams env tps)
in (match (_64_2477) with
| (tps, env_tps, us) -> begin
(
# 1932 "FStar.TypeChecker.Tc.fst"
let _64_2480 = (FStar_Syntax_Util.arrow_formals k)
in (match (_64_2480) with
| (indices, t) -> begin
(
# 1933 "FStar.TypeChecker.Tc.fst"
let _64_2484 = (tc_tparams env_tps indices)
in (match (_64_2484) with
| (indices, env', us') -> begin
(
# 1934 "FStar.TypeChecker.Tc.fst"
let _64_2488 = (tc_trivial_guard env' t)
in (match (_64_2488) with
| (t, _64_2487) -> begin
(
# 1935 "FStar.TypeChecker.Tc.fst"
let k = (let _149_1068 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _149_1068))
in (
# 1936 "FStar.TypeChecker.Tc.fst"
let _64_2492 = (FStar_Syntax_Util.type_u ())
in (match (_64_2492) with
| (t_type, u) -> begin
(
# 1937 "FStar.TypeChecker.Tc.fst"
let _64_2493 = (let _149_1069 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _149_1069))
in (
# 1939 "FStar.TypeChecker.Tc.fst"
let t_tc = (let _149_1070 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _149_1070))
in (
# 1940 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 1941 "FStar.TypeChecker.Tc.fst"
let k = (FStar_Syntax_Subst.close tps k)
in (
# 1942 "FStar.TypeChecker.Tc.fst"
let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _149_1071 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) ([], t_tc))
in (_149_1071, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u)))))))
end)))
end))
end))
end))
end))
end))))
end
| _64_2500 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1949 "FStar.TypeChecker.Tc.fst"
let positive_if_pure = (fun _64_2502 l -> ())
in (
# 1952 "FStar.TypeChecker.Tc.fst"
let tc_data = (fun env tcs _64_6 -> (match (_64_6) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(
# 1954 "FStar.TypeChecker.Tc.fst"
let _64_2519 = ()
in (
# 1956 "FStar.TypeChecker.Tc.fst"
let _64_2554 = (
# 1957 "FStar.TypeChecker.Tc.fst"
let tps_u_opt = (FStar_Util.find_map tcs (fun _64_2523 -> (match (_64_2523) with
| (se, u_tc) -> begin
if (let _149_1084 = (let _149_1083 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _149_1083))
in (FStar_Ident.lid_equals tc_lid _149_1084)) then begin
(
# 1959 "FStar.TypeChecker.Tc.fst"
let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_64_2525, _64_2527, tps, _64_2530, _64_2532, _64_2534, _64_2536, _64_2538) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _64_2544 -> (match (_64_2544) with
| (x, _64_2543) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _64_2546 -> begin
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
in (match (_64_2554) with
| (tps, u_tc) -> begin
(
# 1972 "FStar.TypeChecker.Tc.fst"
let _64_2574 = (match ((let _149_1086 = (FStar_Syntax_Subst.compress t)
in _149_1086.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(
# 1977 "FStar.TypeChecker.Tc.fst"
let _64_2562 = (FStar_Util.first_N ntps bs)
in (match (_64_2562) with
| (_64_2560, bs') -> begin
(
# 1978 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (
# 1979 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _64_2568 -> (match (_64_2568) with
| (x, _64_2567) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _149_1089 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _149_1089))))
end))
end
| _64_2571 -> begin
([], t)
end)
in (match (_64_2574) with
| (arguments, result) -> begin
(
# 1983 "FStar.TypeChecker.Tc.fst"
let _64_2575 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_1092 = (FStar_Syntax_Print.lid_to_string c)
in (let _149_1091 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _149_1090 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _149_1092 _149_1091 _149_1090))))
end else begin
()
end
in (
# 1989 "FStar.TypeChecker.Tc.fst"
let _64_2580 = (tc_tparams env arguments)
in (match (_64_2580) with
| (arguments, env', us) -> begin
(
# 1990 "FStar.TypeChecker.Tc.fst"
let _64_2584 = (tc_trivial_guard env' result)
in (match (_64_2584) with
| (result, _64_2583) -> begin
(
# 1991 "FStar.TypeChecker.Tc.fst"
let _64_2588 = (FStar_Syntax_Util.head_and_args result)
in (match (_64_2588) with
| (head, _64_2587) -> begin
(
# 1992 "FStar.TypeChecker.Tc.fst"
let _64_2593 = (match ((let _149_1093 = (FStar_Syntax_Subst.compress head)
in _149_1093.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _64_2592 -> begin
(let _149_1097 = (let _149_1096 = (let _149_1095 = (let _149_1094 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _149_1094))
in (_149_1095, r))
in FStar_Syntax_Syntax.Error (_149_1096))
in (Prims.raise _149_1097))
end)
in (
# 1995 "FStar.TypeChecker.Tc.fst"
let g = (FStar_List.fold_left2 (fun g _64_2599 u_x -> (match (_64_2599) with
| (x, _64_2598) -> begin
(
# 1996 "FStar.TypeChecker.Tc.fst"
let _64_2601 = ()
in (let _149_1101 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _149_1101)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (
# 2002 "FStar.TypeChecker.Tc.fst"
let t = (let _149_1105 = (let _149_1103 = (FStar_All.pipe_right tps (FStar_List.map (fun _64_2607 -> (match (_64_2607) with
| (x, _64_2606) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _149_1103 arguments))
in (let _149_1104 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _149_1105 _149_1104)))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _64_2610 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 2010 "FStar.TypeChecker.Tc.fst"
let generalize_and_inst_within = (fun env g tcs datas -> (
# 2011 "FStar.TypeChecker.Tc.fst"
let _64_2616 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2012 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _64_7 -> (match (_64_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_64_2620, _64_2622, tps, k, _64_2626, _64_2628, _64_2630, _64_2632) -> begin
(let _149_1116 = (let _149_1115 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _149_1115))
in (FStar_Syntax_Syntax.null_binder _149_1116))
end
| _64_2636 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2015 "FStar.TypeChecker.Tc.fst"
let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _64_8 -> (match (_64_8) with
| FStar_Syntax_Syntax.Sig_datacon (_64_2640, _64_2642, t, _64_2645, _64_2647, _64_2649, _64_2651, _64_2653) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _64_2657 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2018 "FStar.TypeChecker.Tc.fst"
let t = (let _149_1118 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _149_1118))
in (
# 2019 "FStar.TypeChecker.Tc.fst"
let _64_2660 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_1119 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _149_1119))
end else begin
()
end
in (
# 2020 "FStar.TypeChecker.Tc.fst"
let _64_2664 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_64_2664) with
| (uvs, t) -> begin
(
# 2021 "FStar.TypeChecker.Tc.fst"
let _64_2666 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_1123 = (let _149_1121 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _149_1121 (FStar_String.concat ", ")))
in (let _149_1122 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _149_1123 _149_1122)))
end else begin
()
end
in (
# 2024 "FStar.TypeChecker.Tc.fst"
let _64_2670 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_64_2670) with
| (uvs, t) -> begin
(
# 2025 "FStar.TypeChecker.Tc.fst"
let _64_2674 = (FStar_Syntax_Util.arrow_formals t)
in (match (_64_2674) with
| (args, _64_2673) -> begin
(
# 2026 "FStar.TypeChecker.Tc.fst"
let _64_2677 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_64_2677) with
| (tc_types, data_types) -> begin
(
# 2027 "FStar.TypeChecker.Tc.fst"
let tcs = (FStar_List.map2 (fun _64_2681 se -> (match (_64_2681) with
| (x, _64_2680) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _64_2685, tps, _64_2688, mutuals, datas, quals, r) -> begin
(
# 2029 "FStar.TypeChecker.Tc.fst"
let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (
# 2030 "FStar.TypeChecker.Tc.fst"
let _64_2711 = (match ((let _149_1126 = (FStar_Syntax_Subst.compress ty)
in _149_1126.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 2032 "FStar.TypeChecker.Tc.fst"
let _64_2702 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_64_2702) with
| (tps, rest) -> begin
(
# 2033 "FStar.TypeChecker.Tc.fst"
let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _64_2705 -> begin
(let _149_1127 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _149_1127 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _64_2708 -> begin
([], ty)
end)
in (match (_64_2711) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _64_2713 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (
# 2043 "FStar.TypeChecker.Tc.fst"
let datas = (match (uvs) with
| [] -> begin
datas
end
| _64_2717 -> begin
(
# 2046 "FStar.TypeChecker.Tc.fst"
let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _149_1128 -> FStar_Syntax_Syntax.U_name (_149_1128))))
in (
# 2047 "FStar.TypeChecker.Tc.fst"
let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _64_9 -> (match (_64_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _64_2722, _64_2724, _64_2726, _64_2728, _64_2730, _64_2732, _64_2734) -> begin
(tc, uvs_universes)
end
| _64_2738 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _64_2743 d -> (match (_64_2743) with
| (t, _64_2742) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _64_2747, _64_2749, tc, ntps, quals, mutuals, r) -> begin
(
# 2051 "FStar.TypeChecker.Tc.fst"
let ty = (let _149_1132 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _149_1132 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _64_2759 -> begin
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
# 2057 "FStar.TypeChecker.Tc.fst"
let _64_2769 = (FStar_All.pipe_right ses (FStar_List.partition (fun _64_10 -> (match (_64_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_64_2763) -> begin
true
end
| _64_2766 -> begin
false
end))))
in (match (_64_2769) with
| (tys, datas) -> begin
(
# 2059 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2062 "FStar.TypeChecker.Tc.fst"
let _64_2786 = (FStar_List.fold_right (fun tc _64_2775 -> (match (_64_2775) with
| (env, all_tcs, g) -> begin
(
# 2063 "FStar.TypeChecker.Tc.fst"
let _64_2779 = (tc_tycon env tc)
in (match (_64_2779) with
| (env, tc, tc_u) -> begin
(
# 2064 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (
# 2065 "FStar.TypeChecker.Tc.fst"
let _64_2781 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_1136 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _149_1136))
end else begin
()
end
in (let _149_1137 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _149_1137))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_64_2786) with
| (env, tcs, g) -> begin
(
# 2072 "FStar.TypeChecker.Tc.fst"
let _64_2796 = (FStar_List.fold_right (fun se _64_2790 -> (match (_64_2790) with
| (datas, g) -> begin
(
# 2073 "FStar.TypeChecker.Tc.fst"
let _64_2793 = (tc_data env tcs se)
in (match (_64_2793) with
| (data, g') -> begin
(let _149_1140 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _149_1140))
end))
end)) datas ([], g))
in (match (_64_2796) with
| (datas, g) -> begin
(
# 2078 "FStar.TypeChecker.Tc.fst"
let _64_2799 = (let _149_1141 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _149_1141 datas))
in (match (_64_2799) with
| (tcs, datas) -> begin
(let _149_1143 = (let _149_1142 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _149_1142))
in FStar_Syntax_Syntax.Sig_bundle (_149_1143))
end))
end))
end)))
end)))))))))

# 2081 "FStar.TypeChecker.Tc.fst"
let rec tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.env) = (fun env se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(
# 2094 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2095 "FStar.TypeChecker.Tc.fst"
let se = (tc_lex_t env ses quals lids)
in (let _149_1148 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _149_1148))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(
# 2099 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2100 "FStar.TypeChecker.Tc.fst"
let se = (tc_inductive env ses quals lids)
in (let _149_1149 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _149_1149))))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(
# 2104 "FStar.TypeChecker.Tc.fst"
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
# 2110 "FStar.TypeChecker.Tc.fst"
let _64_2837 = (set_options FStar_Options.Set o)
in (se, env))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(
# 2113 "FStar.TypeChecker.Tc.fst"
let _64_2841 = (let _149_1154 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _149_1154 Prims.ignore))
in (
# 2114 "FStar.TypeChecker.Tc.fst"
let _64_2846 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (
# 2117 "FStar.TypeChecker.Tc.fst"
let _64_2848 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (se, env))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(
# 2122 "FStar.TypeChecker.Tc.fst"
let ne = (tc_eff_decl env ne)
in (
# 2123 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (
# 2124 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(
# 2128 "FStar.TypeChecker.Tc.fst"
let _64_2863 = (let _149_1155 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _149_1155))
in (match (_64_2863) with
| (a, wp_a_src) -> begin
(
# 2129 "FStar.TypeChecker.Tc.fst"
let _64_2866 = (let _149_1156 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _149_1156))
in (match (_64_2866) with
| (b, wp_b_tgt) -> begin
(
# 2130 "FStar.TypeChecker.Tc.fst"
let wp_a_tgt = (let _149_1160 = (let _149_1159 = (let _149_1158 = (let _149_1157 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _149_1157))
in FStar_Syntax_Syntax.NT (_149_1158))
in (_149_1159)::[])
in (FStar_Syntax_Subst.subst _149_1160 wp_b_tgt))
in (
# 2131 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _149_1165 = (let _149_1163 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_1162 = (let _149_1161 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_149_1161)::[])
in (_149_1163)::_149_1162))
in (let _149_1164 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _149_1165 _149_1164)))
in (
# 2132 "FStar.TypeChecker.Tc.fst"
let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (
# 2133 "FStar.TypeChecker.Tc.fst"
let sub = (
# 2133 "FStar.TypeChecker.Tc.fst"
let _64_2870 = sub
in {FStar_Syntax_Syntax.source = _64_2870.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _64_2870.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
in (
# 2134 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect ((sub, r))
in (
# 2135 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(
# 2139 "FStar.TypeChecker.Tc.fst"
let _64_2883 = ()
in (
# 2140 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2141 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2142 "FStar.TypeChecker.Tc.fst"
let _64_2889 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_64_2889) with
| (tps, c) -> begin
(
# 2143 "FStar.TypeChecker.Tc.fst"
let _64_2893 = (tc_tparams env tps)
in (match (_64_2893) with
| (tps, env, us) -> begin
(
# 2144 "FStar.TypeChecker.Tc.fst"
let _64_2897 = (tc_comp env c)
in (match (_64_2897) with
| (c, u, g) -> begin
(
# 2145 "FStar.TypeChecker.Tc.fst"
let _64_2898 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2146 "FStar.TypeChecker.Tc.fst"
let tags = (FStar_All.pipe_right tags (FStar_List.map (fun _64_11 -> (match (_64_11) with
| FStar_Syntax_Syntax.DefaultEffect (None) -> begin
(
# 2148 "FStar.TypeChecker.Tc.fst"
let c' = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let _149_1168 = (FStar_All.pipe_right c'.FStar_Syntax_Syntax.effect_name (fun _149_1167 -> Some (_149_1167)))
in FStar_Syntax_Syntax.DefaultEffect (_149_1168)))
end
| t -> begin
t
end))))
in (
# 2151 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 2152 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.close_comp tps c)
in (
# 2153 "FStar.TypeChecker.Tc.fst"
let _64_2910 = (let _149_1169 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _149_1169))
in (match (_64_2910) with
| (uvs, t) -> begin
(
# 2154 "FStar.TypeChecker.Tc.fst"
let _64_2929 = (match ((let _149_1171 = (let _149_1170 = (FStar_Syntax_Subst.compress t)
in _149_1170.FStar_Syntax_Syntax.n)
in (tps, _149_1171))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_64_2913, c)) -> begin
([], c)
end
| (_64_2919, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _64_2926 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_64_2929) with
| (tps, c) -> begin
(
# 2158 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_effect_abbrev ((lid, uvs, tps, c, tags, r))
in (
# 2159 "FStar.TypeChecker.Tc.fst"
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
# 2163 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2164 "FStar.TypeChecker.Tc.fst"
let _64_2940 = ()
in (
# 2165 "FStar.TypeChecker.Tc.fst"
let k = (let _149_1172 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _149_1172))
in (
# 2166 "FStar.TypeChecker.Tc.fst"
let _64_2945 = (check_and_gen env t k)
in (match (_64_2945) with
| (uvs, t) -> begin
(
# 2167 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (
# 2168 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(
# 2172 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2173 "FStar.TypeChecker.Tc.fst"
let _64_2958 = (FStar_Syntax_Util.type_u ())
in (match (_64_2958) with
| (k, _64_2957) -> begin
(
# 2174 "FStar.TypeChecker.Tc.fst"
let phi = (let _149_1173 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _149_1173 (norm env)))
in (
# 2175 "FStar.TypeChecker.Tc.fst"
let _64_2960 = (FStar_TypeChecker_Util.check_uvars r phi)
in (
# 2176 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))
in (
# 2177 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(
# 2181 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2182 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (
# 2183 "FStar.TypeChecker.Tc.fst"
let _64_2973 = (tc_term env e)
in (match (_64_2973) with
| (e, c, g1) -> begin
(
# 2184 "FStar.TypeChecker.Tc.fst"
let _64_2978 = (let _149_1177 = (let _149_1174 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_149_1174))
in (let _149_1176 = (let _149_1175 = (c.FStar_Syntax_Syntax.comp ())
in (e, _149_1175))
in (check_expected_effect env _149_1177 _149_1176)))
in (match (_64_2978) with
| (e, _64_2976, g) -> begin
(
# 2185 "FStar.TypeChecker.Tc.fst"
let _64_2979 = (let _149_1178 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _149_1178))
in (
# 2186 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, r))
in (
# 2187 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(
# 2191 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2192 "FStar.TypeChecker.Tc.fst"
let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
if (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q')) then begin
Some (q)
end else begin
(let _149_1190 = (let _149_1189 = (let _149_1188 = (let _149_1187 = (FStar_Syntax_Print.lid_to_string l)
in (let _149_1186 = (FStar_Syntax_Print.quals_to_string q)
in (let _149_1185 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _149_1187 _149_1186 _149_1185))))
in (_149_1188, r))
in FStar_Syntax_Syntax.Error (_149_1189))
in (Prims.raise _149_1190))
end
end))
in (
# 2206 "FStar.TypeChecker.Tc.fst"
let _64_3023 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _64_3000 lb -> (match (_64_3000) with
| (gen, lbs, quals_opt) -> begin
(
# 2207 "FStar.TypeChecker.Tc.fst"
let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2208 "FStar.TypeChecker.Tc.fst"
let _64_3019 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(
# 2212 "FStar.TypeChecker.Tc.fst"
let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (
# 2213 "FStar.TypeChecker.Tc.fst"
let _64_3014 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _64_3013 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _149_1193 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _149_1193, quals_opt))))
end)
in (match (_64_3019) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_64_3023) with
| (should_generalize, lbs', quals_opt) -> begin
(
# 2222 "FStar.TypeChecker.Tc.fst"
let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _64_12 -> (match (_64_12) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _64_3032 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (
# 2229 "FStar.TypeChecker.Tc.fst"
let lbs' = (FStar_List.rev lbs')
in (
# 2232 "FStar.TypeChecker.Tc.fst"
let e = (let _149_1197 = (let _149_1196 = (let _149_1195 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _149_1195))
in FStar_Syntax_Syntax.Tm_let (_149_1196))
in (FStar_Syntax_Syntax.mk _149_1197 None r))
in (
# 2235 "FStar.TypeChecker.Tc.fst"
let _64_3066 = (match ((tc_maybe_toplevel_term (
# 2235 "FStar.TypeChecker.Tc.fst"
let _64_3036 = env
in {FStar_TypeChecker_Env.solver = _64_3036.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_3036.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_3036.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_3036.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_3036.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_3036.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_3036.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_3036.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_3036.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_3036.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_3036.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _64_3036.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _64_3036.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _64_3036.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _64_3036.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_3036.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_3036.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_3036.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_3036.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_3036.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _64_3043; FStar_Syntax_Syntax.pos = _64_3041; FStar_Syntax_Syntax.vars = _64_3039}, _64_3050, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(
# 2238 "FStar.TypeChecker.Tc.fst"
let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_64_3054, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _64_3060 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _64_3063 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_64_3066) with
| (se, lbs) -> begin
(
# 2245 "FStar.TypeChecker.Tc.fst"
let _64_3072 = if (log env) then begin
(let _149_1205 = (let _149_1204 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 2247 "FStar.TypeChecker.Tc.fst"
let should_log = (match ((let _149_1201 = (let _149_1200 = (let _149_1199 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _149_1199.FStar_Syntax_Syntax.fv_name)
in _149_1200.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _149_1201))) with
| None -> begin
true
end
| _64_3070 -> begin
false
end)
in if should_log then begin
(let _149_1203 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _149_1202 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _149_1203 _149_1202)))
end else begin
""
end))))
in (FStar_All.pipe_right _149_1204 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _149_1205))
end else begin
()
end
in (
# 2254 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end))))
end))

# 2258 "FStar.TypeChecker.Tc.fst"
let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (
# 2282 "FStar.TypeChecker.Tc.fst"
let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _64_13 -> (match (_64_13) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _64_3082 -> begin
false
end)))))
in (
# 2283 "FStar.TypeChecker.Tc.fst"
let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _64_3092 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_64_3094) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _64_3105, _64_3107) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _64_3113 -> (match (_64_3113) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _64_3119, _64_3121, quals, r) -> begin
(
# 2297 "FStar.TypeChecker.Tc.fst"
let dec = (let _149_1221 = (let _149_1220 = (let _149_1219 = (let _149_1218 = (let _149_1217 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _149_1217))
in FStar_Syntax_Syntax.Tm_arrow (_149_1218))
in (FStar_Syntax_Syntax.mk _149_1219 None r))
in (l, us, _149_1220, (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_149_1221))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _64_3131, _64_3133, _64_3135, _64_3137, r) -> begin
(
# 2300 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _64_3143 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_64_3145, _64_3147, quals, _64_3150) -> begin
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
| _64_3169 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_64_3171) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _64_3187, _64_3189, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(
# 2330 "FStar.TypeChecker.Tc.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2331 "FStar.TypeChecker.Tc.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))) then begin
([], hidden)
end else begin
(
# 2334 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::[], (FStar_Ident.range_of_lid lid)))
in ((dec)::[], (lid)::hidden))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (is_abstract quals) then begin
(let _149_1228 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _149_1227 = (let _149_1226 = (let _149_1225 = (let _149_1224 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _149_1224.FStar_Syntax_Syntax.fv_name)
in _149_1225.FStar_Syntax_Syntax.v)
in (_149_1226, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_149_1227)))))
in (_149_1228, hidden))
end else begin
((se)::[], hidden)
end
end))))

# 2343 "FStar.TypeChecker.Tc.fst"
let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (
# 2344 "FStar.TypeChecker.Tc.fst"
let _64_3228 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _64_3209 se -> (match (_64_3209) with
| (ses, exports, env, hidden) -> begin
(
# 2346 "FStar.TypeChecker.Tc.fst"
let _64_3211 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_1235 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _149_1235))
end else begin
()
end
in (
# 2349 "FStar.TypeChecker.Tc.fst"
let _64_3215 = (tc_decl env se)
in (match (_64_3215) with
| (se, env) -> begin
(
# 2351 "FStar.TypeChecker.Tc.fst"
let _64_3216 = if ((FStar_ST.read FStar_Options.log_types) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _149_1236 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _149_1236))
end else begin
()
end
in (
# 2354 "FStar.TypeChecker.Tc.fst"
let _64_3218 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (
# 2356 "FStar.TypeChecker.Tc.fst"
let _64_3222 = (for_export hidden se)
in (match (_64_3222) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_64_3228) with
| (ses, exports, env, _64_3227) -> begin
(let _149_1237 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _149_1237, env))
end)))

# 2361 "FStar.TypeChecker.Tc.fst"
let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2362 "FStar.TypeChecker.Tc.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 2363 "FStar.TypeChecker.Tc.fst"
let msg = (Prims.strcat "Internals for " name)
in (
# 2364 "FStar.TypeChecker.Tc.fst"
let env = (
# 2364 "FStar.TypeChecker.Tc.fst"
let _64_3233 = env
in (let _149_1242 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _64_3233.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_3233.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_3233.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_3233.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_3233.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_3233.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_3233.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_3233.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_3233.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_3233.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_3233.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_3233.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _64_3233.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _64_3233.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _64_3233.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _64_3233.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _149_1242; FStar_TypeChecker_Env.default_effects = _64_3233.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_3233.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_3233.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_3233.FStar_TypeChecker_Env.use_bv_sorts}))
in (
# 2365 "FStar.TypeChecker.Tc.fst"
let _64_3236 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (
# 2366 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (
# 2367 "FStar.TypeChecker.Tc.fst"
let _64_3242 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_64_3242) with
| (ses, exports, env) -> begin
((
# 2368 "FStar.TypeChecker.Tc.fst"
let _64_3243 = modul
in {FStar_Syntax_Syntax.name = _64_3243.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _64_3243.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _64_3243.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))

# 2370 "FStar.TypeChecker.Tc.fst"
let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (
# 2371 "FStar.TypeChecker.Tc.fst"
let _64_3251 = (tc_decls env decls)
in (match (_64_3251) with
| (ses, exports, env) -> begin
(
# 2372 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2372 "FStar.TypeChecker.Tc.fst"
let _64_3252 = modul
in {FStar_Syntax_Syntax.name = _64_3252.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _64_3252.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _64_3252.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))

# 2375 "FStar.TypeChecker.Tc.fst"
let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (
# 2376 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2376 "FStar.TypeChecker.Tc.fst"
let _64_3258 = modul
in {FStar_Syntax_Syntax.name = _64_3258.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _64_3258.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (
# 2377 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.finish_module env modul)
in (
# 2378 "FStar.TypeChecker.Tc.fst"
let _64_3268 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(
# 2380 "FStar.TypeChecker.Tc.fst"
let _64_3262 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (
# 2381 "FStar.TypeChecker.Tc.fst"
let _64_3264 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (
# 2382 "FStar.TypeChecker.Tc.fst"
let _64_3266 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _149_1255 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _149_1255 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))

# 2387 "FStar.TypeChecker.Tc.fst"
let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2388 "FStar.TypeChecker.Tc.fst"
let _64_3275 = (tc_partial_modul env modul)
in (match (_64_3275) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

# 2391 "FStar.TypeChecker.Tc.fst"
let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 2392 "FStar.TypeChecker.Tc.fst"
let _64_3278 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _149_1264 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _149_1264))
end else begin
()
end
in (
# 2394 "FStar.TypeChecker.Tc.fst"
let env = (
# 2394 "FStar.TypeChecker.Tc.fst"
let _64_3280 = env
in {FStar_TypeChecker_Env.solver = _64_3280.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _64_3280.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _64_3280.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _64_3280.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _64_3280.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _64_3280.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _64_3280.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _64_3280.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _64_3280.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _64_3280.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _64_3280.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _64_3280.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _64_3280.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _64_3280.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _64_3280.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _64_3280.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _64_3280.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _64_3280.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _64_3280.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _64_3280.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _64_3280.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 2395 "FStar.TypeChecker.Tc.fst"
let _64_3296 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _64_3288) -> begin
(let _149_1269 = (let _149_1268 = (let _149_1267 = (FStar_TypeChecker_Env.get_range env)
in ((Prims.strcat "Implicit argument: " msg), _149_1267))
in FStar_Syntax_Syntax.Error (_149_1268))
in (Prims.raise _149_1269))
end
in (match (_64_3296) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(let _149_1274 = (let _149_1273 = (let _149_1272 = (let _149_1270 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _149_1270))
in (let _149_1271 = (FStar_TypeChecker_Env.get_range env)
in (_149_1272, _149_1271)))
in FStar_Syntax_Syntax.Error (_149_1273))
in (Prims.raise _149_1274))
end
end)))))

# 2402 "FStar.TypeChecker.Tc.fst"
let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (
# 2403 "FStar.TypeChecker.Tc.fst"
let _64_3299 = if ((let _149_1279 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _149_1279)) <> 0) then begin
(let _149_1280 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _149_1280))
end else begin
()
end
in (
# 2405 "FStar.TypeChecker.Tc.fst"
let _64_3303 = (tc_modul env m)
in (match (_64_3303) with
| (m, env) -> begin
(
# 2406 "FStar.TypeChecker.Tc.fst"
let _64_3304 = if (FStar_Options.should_dump m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _149_1281 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _149_1281))
end else begin
()
end
in (m, env))
end))))




