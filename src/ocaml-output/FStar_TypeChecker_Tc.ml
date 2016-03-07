
open Prims
# 42 "FStar.TypeChecker.Tc.fst"
let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_ST.read FStar_Options.log_types) && (not ((let _151_3 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _151_3))))))

# 43 "FStar.TypeChecker.Tc.fst"
let rng : FStar_TypeChecker_Env.env  ->  FStar_Range.range = (fun env -> (FStar_TypeChecker_Env.get_range env))

# 44 "FStar.TypeChecker.Tc.fst"
let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (
# 44 "FStar.TypeChecker.Tc.fst"
let _70_18 = env
in {FStar_TypeChecker_Env.solver = _70_18.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_18.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_18.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_18.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_18.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_18.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_18.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_18.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_18.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _70_18.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_18.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_18.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _70_18.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _70_18.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_18.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_18.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_18.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_18.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_18.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_18.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_18.FStar_TypeChecker_Env.use_bv_sorts}))

# 45 "FStar.TypeChecker.Tc.fst"
let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (
# 45 "FStar.TypeChecker.Tc.fst"
let _70_21 = env
in {FStar_TypeChecker_Env.solver = _70_21.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_21.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_21.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_21.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_21.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_21.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_21.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_21.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_21.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _70_21.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_21.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_21.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _70_21.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _70_21.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_21.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_21.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_21.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_21.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_21.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_21.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_21.FStar_TypeChecker_Env.use_bv_sorts}))

# 46 "FStar.TypeChecker.Tc.fst"
let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (
# 48 "FStar.TypeChecker.Tc.fst"
let r = if (tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
v.FStar_Syntax_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos tl.FStar_Syntax_Syntax.pos)
end
in (let _151_17 = (let _151_16 = (FStar_Syntax_Syntax.as_arg v)
in (let _151_15 = (let _151_14 = (FStar_Syntax_Syntax.as_arg tl)
in (_151_14)::[])
in (_151_16)::_151_15))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _151_17 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))

# 51 "FStar.TypeChecker.Tc.fst"
let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _70_1 -> (match (_70_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _70_31 -> begin
false
end))

# 54 "FStar.TypeChecker.Tc.fst"
let steps : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Normalize.step Prims.list = (fun env -> if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::[]
end else begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]
end)

# 58 "FStar.TypeChecker.Tc.fst"
let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Unfold)::(FStar_TypeChecker_Normalize.Beta)::[]) env t))

# 59 "FStar.TypeChecker.Tc.fst"
let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _151_30 = (steps env)
in (FStar_TypeChecker_Normalize.normalize _151_30 env t)))

# 60 "FStar.TypeChecker.Tc.fst"
let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _151_35 = (steps env)
in (FStar_TypeChecker_Normalize.normalize_comp _151_35 env c)))

# 61 "FStar.TypeChecker.Tc.fst"
let check_no_escape : FStar_Syntax_Syntax.term Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun head_opt env fvs kt -> (
# 62 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
()
end
| _70_48 -> begin
(
# 65 "FStar.TypeChecker.Tc.fst"
let fvs' = (let _151_48 = if try_norm then begin
(norm env t)
end else begin
t
end
in (FStar_Syntax_Free.names _151_48))
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
let fail = (fun _70_55 -> (match (()) with
| () -> begin
(
# 72 "FStar.TypeChecker.Tc.fst"
let msg = (match (head_opt) with
| None -> begin
(let _151_52 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _151_52))
end
| Some (head) -> begin
(let _151_54 = (FStar_Syntax_Print.bv_to_string x)
in (let _151_53 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _151_54 _151_53)))
end)
in (let _151_57 = (let _151_56 = (let _151_55 = (FStar_TypeChecker_Env.get_range env)
in (msg, _151_55))
in FStar_Syntax_Syntax.Error (_151_56))
in (Prims.raise _151_57)))
end))
in (
# 77 "FStar.TypeChecker.Tc.fst"
let s = (let _151_59 = (let _151_58 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _151_58))
in (FStar_TypeChecker_Util.new_uvar env _151_59))
in (match ((FStar_TypeChecker_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g)
end
| _70_64 -> begin
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
let _70_67 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_65 = (FStar_Syntax_Print.bv_to_string (Prims.fst b))
in (let _151_64 = (FStar_Syntax_Print.term_to_string (Prims.fst b).FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _151_65 _151_64)))
end else begin
()
end
in (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))
end)

# 90 "FStar.TypeChecker.Tc.fst"
let maybe_make_subst = (fun _70_2 -> (match (_70_2) with
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Syntax_Syntax.NT ((x, e)))::[]
end
| _70_76 -> begin
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
let _70_82 = lc
in {FStar_Syntax_Syntax.eff_name = _70_82.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _70_82.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _70_84 -> (match (()) with
| () -> begin
(let _151_78 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _151_78 t))
end))}))

# 101 "FStar.TypeChecker.Tc.fst"
let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (
# 102 "FStar.TypeChecker.Tc.fst"
let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _151_87 = if (not ((FStar_Syntax_Util.is_pure_or_ghost_function t))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _151_87))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (
# 107 "FStar.TypeChecker.Tc.fst"
let t = lc.FStar_Syntax_Syntax.res_typ
in (
# 108 "FStar.TypeChecker.Tc.fst"
let _70_116 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, guard)
end
| Some (t') -> begin
(
# 111 "FStar.TypeChecker.Tc.fst"
let _70_98 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_89 = (FStar_Syntax_Print.term_to_string t)
in (let _151_88 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _151_89 _151_88)))
end else begin
()
end
in (
# 113 "FStar.TypeChecker.Tc.fst"
let _70_102 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_70_102) with
| (e, lc) -> begin
(
# 114 "FStar.TypeChecker.Tc.fst"
let t = lc.FStar_Syntax_Syntax.res_typ
in (
# 115 "FStar.TypeChecker.Tc.fst"
let _70_106 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_70_106) with
| (e, g) -> begin
(
# 116 "FStar.TypeChecker.Tc.fst"
let _70_107 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_91 = (FStar_Syntax_Print.term_to_string t)
in (let _151_90 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _151_91 _151_90)))
end else begin
()
end
in (
# 118 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (
# 119 "FStar.TypeChecker.Tc.fst"
let _70_112 = (let _151_97 = (FStar_All.pipe_left (fun _151_96 -> Some (_151_96)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _151_97 env e lc g))
in (match (_70_112) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))))
end)))
end)))
end)
in (match (_70_116) with
| (e, lc, g) -> begin
(
# 121 "FStar.TypeChecker.Tc.fst"
let _70_117 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_98 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _151_98))
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
let _70_127 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_70_127) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))

# 132 "FStar.TypeChecker.Tc.fst"
let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _70_132 -> (match (_70_132) with
| (e, c) -> begin
(
# 133 "FStar.TypeChecker.Tc.fst"
let expected_c_opt = (match (copt) with
| Some (_70_134) -> begin
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
(let _151_111 = (norm_c env c)
in (e, _151_111, FStar_TypeChecker_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(
# 156 "FStar.TypeChecker.Tc.fst"
let _70_148 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_114 = (FStar_Syntax_Print.term_to_string e)
in (let _151_113 = (FStar_Syntax_Print.comp_to_string c)
in (let _151_112 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _151_114 _151_113 _151_112))))
end else begin
()
end
in (
# 159 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 160 "FStar.TypeChecker.Tc.fst"
let _70_151 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_117 = (FStar_Syntax_Print.term_to_string e)
in (let _151_116 = (FStar_Syntax_Print.comp_to_string c)
in (let _151_115 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _151_117 _151_116 _151_115))))
end else begin
()
end
in (
# 165 "FStar.TypeChecker.Tc.fst"
let _70_157 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_70_157) with
| (e, _70_155, g) -> begin
(
# 166 "FStar.TypeChecker.Tc.fst"
let g = (let _151_118 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _151_118 "could not prove post-condition" g))
in (
# 167 "FStar.TypeChecker.Tc.fst"
let _70_159 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_120 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _151_119 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _151_120 _151_119)))
end else begin
()
end
in (e, expected_c, g)))
end)))))
end))
end))

# 170 "FStar.TypeChecker.Tc.fst"
let no_logical_guard = (fun env _70_165 -> (match (_70_165) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
(te, kt, f)
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _151_126 = (let _151_125 = (let _151_124 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _151_123 = (FStar_TypeChecker_Env.get_range env)
in (_151_124, _151_123)))
in FStar_Syntax_Syntax.Error (_151_125))
in (Prims.raise _151_126))
end)
end))

# 175 "FStar.TypeChecker.Tc.fst"
let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _151_129 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _151_129))
end))

# 179 "FStar.TypeChecker.Tc.fst"
let with_implicits = (fun imps _70_177 -> (match (_70_177) with
| (e, l, g) -> begin
(e, l, (
# 179 "FStar.TypeChecker.Tc.fst"
let _70_178 = g
in {FStar_TypeChecker_Env.guard_f = _70_178.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _70_178.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _70_178.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (FStar_List.append imps g.FStar_TypeChecker_Env.implicits)}))
end))

# 180 "FStar.TypeChecker.Tc.fst"
let add_implicit : (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun u g -> (
# 180 "FStar.TypeChecker.Tc.fst"
let _70_182 = g
in {FStar_TypeChecker_Env.guard_f = _70_182.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _70_182.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _70_182.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (u)::g.FStar_TypeChecker_Env.implicits}))

# 185 "FStar.TypeChecker.Tc.fst"
let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _70_200; FStar_Syntax_Syntax.result_typ = _70_198; FStar_Syntax_Syntax.effect_args = _pre::_post::(pats, _70_192)::[]; FStar_Syntax_Syntax.flags = _70_189}) -> begin
(
# 189 "FStar.TypeChecker.Tc.fst"
let pat_vars = (FStar_Syntax_Free.names pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _70_207 -> (match (_70_207) with
| (b, _70_206) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _70_211) -> begin
(let _151_142 = (let _151_141 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _151_141))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _151_142))
end))
end
| _70_215 -> begin
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
let _70_222 = env
in {FStar_TypeChecker_Env.solver = _70_222.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_222.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_222.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_222.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_222.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_222.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_222.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_222.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_222.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_222.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_222.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_222.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _70_222.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _70_222.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_222.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_222.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_222.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_222.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_222.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_222.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_222.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 206 "FStar.TypeChecker.Tc.fst"
let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (
# 208 "FStar.TypeChecker.Tc.fst"
let decreases_clause = (fun bs c -> (
# 210 "FStar.TypeChecker.Tc.fst"
let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _70_234 -> (match (_70_234) with
| (b, _70_233) -> begin
(
# 212 "FStar.TypeChecker.Tc.fst"
let t = (let _151_156 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _151_156))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _70_243 -> begin
(let _151_157 = (FStar_Syntax_Syntax.bv_to_name b)
in (_151_157)::[])
end))
end)))))
in (
# 217 "FStar.TypeChecker.Tc.fst"
let as_lex_list = (fun dec -> (
# 218 "FStar.TypeChecker.Tc.fst"
let _70_249 = (FStar_Syntax_Util.head_and_args dec)
in (match (_70_249) with
| (head, _70_248) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _70_253 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (
# 222 "FStar.TypeChecker.Tc.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _70_3 -> (match (_70_3) with
| FStar_Syntax_Syntax.DECREASES (_70_257) -> begin
true
end
| _70_260 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _70_265 -> begin
(
# 226 "FStar.TypeChecker.Tc.fst"
let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| x::[] -> begin
x
end
| _70_270 -> begin
(mk_lex_list xs)
end))
end)))))
in (
# 231 "FStar.TypeChecker.Tc.fst"
let previous_dec = (decreases_clause actuals expected_c)
in (
# 232 "FStar.TypeChecker.Tc.fst"
let guard_one_letrec = (fun _70_275 -> (match (_70_275) with
| (l, t) -> begin
(match ((let _151_163 = (FStar_Syntax_Subst.compress t)
in _151_163.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 236 "FStar.TypeChecker.Tc.fst"
let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _70_282 -> (match (_70_282) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _151_167 = (let _151_166 = (let _151_165 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_151_165))
in (FStar_Syntax_Syntax.new_bv _151_166 x.FStar_Syntax_Syntax.sort))
in (_151_167, imp))
end else begin
(x, imp)
end
end))))
in (
# 237 "FStar.TypeChecker.Tc.fst"
let _70_286 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_70_286) with
| (formals, c) -> begin
(
# 238 "FStar.TypeChecker.Tc.fst"
let dec = (decreases_clause formals c)
in (
# 239 "FStar.TypeChecker.Tc.fst"
let precedes = (let _151_171 = (let _151_170 = (FStar_Syntax_Syntax.as_arg dec)
in (let _151_169 = (let _151_168 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_151_168)::[])
in (_151_170)::_151_169))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _151_171 None r))
in (
# 240 "FStar.TypeChecker.Tc.fst"
let _70_293 = (FStar_Util.prefix formals)
in (match (_70_293) with
| (bs, (last, imp)) -> begin
(
# 241 "FStar.TypeChecker.Tc.fst"
let last = (
# 241 "FStar.TypeChecker.Tc.fst"
let _70_294 = last
in (let _151_172 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _70_294.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_294.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _151_172}))
in (
# 242 "FStar.TypeChecker.Tc.fst"
let refined_formals = (FStar_List.append bs (((last, imp))::[]))
in (
# 243 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (
# 244 "FStar.TypeChecker.Tc.fst"
let _70_299 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_175 = (FStar_Syntax_Print.lbname_to_string l)
in (let _151_174 = (FStar_Syntax_Print.term_to_string t)
in (let _151_173 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _151_175 _151_174 _151_173))))
end else begin
()
end
in (l, t')))))
end))))
end)))
end
| _70_302 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end))

# 256 "FStar.TypeChecker.Tc.fst"
let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (
# 256 "FStar.TypeChecker.Tc.fst"
let _70_305 = env
in {FStar_TypeChecker_Env.solver = _70_305.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_305.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_305.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_305.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_305.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_305.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_305.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_305.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_305.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_305.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_305.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_305.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_305.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _70_305.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_305.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_305.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_305.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_305.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_305.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_305.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_305.FStar_TypeChecker_Env.use_bv_sorts}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 261 "FStar.TypeChecker.Tc.fst"
let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (
# 262 "FStar.TypeChecker.Tc.fst"
let _70_310 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_244 = (let _151_242 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _151_242))
in (let _151_243 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _151_244 _151_243)))
end else begin
()
end
in (
# 263 "FStar.TypeChecker.Tc.fst"
let top = e
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_70_314) -> begin
(let _151_248 = (FStar_Syntax_Subst.compress e)
in (tc_term env _151_248))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(
# 280 "FStar.TypeChecker.Tc.fst"
let _70_355 = (tc_tot_or_gtot_term env e)
in (match (_70_355) with
| (e, c, g) -> begin
(
# 281 "FStar.TypeChecker.Tc.fst"
let g = (
# 281 "FStar.TypeChecker.Tc.fst"
let _70_356 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _70_356.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _70_356.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _70_356.FStar_TypeChecker_Env.implicits})
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(
# 285 "FStar.TypeChecker.Tc.fst"
let _70_366 = (FStar_Syntax_Util.type_u ())
in (match (_70_366) with
| (t, u) -> begin
(
# 286 "FStar.TypeChecker.Tc.fst"
let _70_370 = (tc_check_tot_or_gtot_term env e t)
in (match (_70_370) with
| (e, c, g) -> begin
(
# 287 "FStar.TypeChecker.Tc.fst"
let _70_377 = (
# 288 "FStar.TypeChecker.Tc.fst"
let _70_374 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_374) with
| (env, _70_373) -> begin
(tc_pats env pats)
end))
in (match (_70_377) with
| (pats, g') -> begin
(
# 290 "FStar.TypeChecker.Tc.fst"
let g' = (
# 290 "FStar.TypeChecker.Tc.fst"
let _70_378 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _70_378.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _70_378.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _70_378.FStar_TypeChecker_Env.implicits})
in (let _151_250 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_pattern (pats)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _151_249 = (FStar_TypeChecker_Rel.conj_guard g g')
in (_151_250, c, _151_249))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _151_251 = (FStar_Syntax_Subst.compress e)
in _151_251.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_70_387, {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _70_394; FStar_Syntax_Syntax.lbtyp = _70_392; FStar_Syntax_Syntax.lbeff = _70_390; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 298 "FStar.TypeChecker.Tc.fst"
let _70_405 = (let _151_252 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _151_252 e1))
in (match (_70_405) with
| (e1, c1, g1) -> begin
(
# 299 "FStar.TypeChecker.Tc.fst"
let _70_409 = (tc_term env e2)
in (match (_70_409) with
| (e2, c2, g2) -> begin
(
# 300 "FStar.TypeChecker.Tc.fst"
let c = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (None, c2))
in (
# 301 "FStar.TypeChecker.Tc.fst"
let e = (let _151_257 = (let _151_256 = (let _151_255 = (let _151_254 = (let _151_253 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Common.t_unit, e1))
in (_151_253)::[])
in (false, _151_254))
in (_151_255, e2))
in FStar_Syntax_Syntax.Tm_let (_151_256))
in (FStar_Syntax_Syntax.mk _151_257 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 302 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _151_258 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _151_258)))))
end))
end))
end
| _70_414 -> begin
(
# 305 "FStar.TypeChecker.Tc.fst"
let _70_418 = (tc_term env e)
in (match (_70_418) with
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
let _70_427 = (tc_term env e)
in (match (_70_427) with
| (e, c, g) -> begin
(
# 312 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, m))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _70_432) -> begin
(
# 316 "FStar.TypeChecker.Tc.fst"
let _70_437 = (FStar_Syntax_Util.type_u ())
in (match (_70_437) with
| (k, u) -> begin
(
# 317 "FStar.TypeChecker.Tc.fst"
let _70_442 = (tc_check_tot_or_gtot_term env t k)
in (match (_70_442) with
| (t, _70_440, f) -> begin
(
# 318 "FStar.TypeChecker.Tc.fst"
let _70_446 = (let _151_259 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _151_259 e))
in (match (_70_446) with
| (e, c, g) -> begin
(
# 319 "FStar.TypeChecker.Tc.fst"
let _70_450 = (let _151_263 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _70_447 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _151_263 e c f))
in (match (_70_450) with
| (c, f) -> begin
(
# 320 "FStar.TypeChecker.Tc.fst"
let _70_454 = (let _151_264 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, t, Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _151_264 c))
in (match (_70_454) with
| (e, c, f2) -> begin
(let _151_266 = (let _151_265 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _151_265))
in (e, c, _151_266))
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
let env = (let _151_268 = (let _151_267 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _151_267 Prims.fst))
in (FStar_All.pipe_right _151_268 instantiate_both))
in (
# 326 "FStar.TypeChecker.Tc.fst"
let _70_461 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_270 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _151_269 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _151_270 _151_269)))
end else begin
()
end
in (
# 330 "FStar.TypeChecker.Tc.fst"
let _70_466 = (tc_term (no_inst env) head)
in (match (_70_466) with
| (head, chead, g_head) -> begin
(
# 331 "FStar.TypeChecker.Tc.fst"
let _70_470 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _151_271 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _151_271))
end else begin
(let _151_272 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _151_272))
end
in (match (_70_470) with
| (e, c, g) -> begin
(
# 334 "FStar.TypeChecker.Tc.fst"
let _70_471 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _151_273 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _151_273))
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
let _70_478 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_279 = (FStar_Syntax_Print.term_to_string e)
in (let _151_278 = (let _151_274 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _151_274))
in (let _151_277 = (let _151_276 = (FStar_TypeChecker_Env.expected_typ env0)
in (FStar_All.pipe_right _151_276 (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end))))
in (FStar_Util.print3 "(%s) About to check %s against expected typ %s\n" _151_279 _151_278 _151_277))))
end else begin
()
end
in (
# 346 "FStar.TypeChecker.Tc.fst"
let _70_483 = (comp_check_expected_typ env0 e c)
in (match (_70_483) with
| (e, c, g') -> begin
(
# 347 "FStar.TypeChecker.Tc.fst"
let _70_484 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_282 = (FStar_Syntax_Print.term_to_string e)
in (let _151_281 = (let _151_280 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _151_280))
in (FStar_Util.print2 "(%s) checked ... got %s\n" _151_282 _151_281)))
end else begin
()
end
in (
# 351 "FStar.TypeChecker.Tc.fst"
let gimp = (match ((let _151_283 = (FStar_Syntax_Subst.compress head)
in _151_283.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _70_488) -> begin
(
# 354 "FStar.TypeChecker.Tc.fst"
let imp = (env0, u, e, c.FStar_Syntax_Syntax.res_typ, e.FStar_Syntax_Syntax.pos)
in (
# 355 "FStar.TypeChecker.Tc.fst"
let _70_492 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _70_492.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _70_492.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _70_492.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _70_495 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (
# 357 "FStar.TypeChecker.Tc.fst"
let gres = (let _151_284 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _151_284))
in (
# 358 "FStar.TypeChecker.Tc.fst"
let _70_498 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _151_285 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print1 "Guard from application node is %s\n" _151_285))
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
let _70_506 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_506) with
| (env1, topt) -> begin
(
# 364 "FStar.TypeChecker.Tc.fst"
let env1 = (instantiate_both env1)
in (
# 365 "FStar.TypeChecker.Tc.fst"
let _70_511 = (tc_term env1 e1)
in (match (_70_511) with
| (e1, c1, g1) -> begin
(
# 366 "FStar.TypeChecker.Tc.fst"
let _70_522 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(
# 369 "FStar.TypeChecker.Tc.fst"
let _70_518 = (FStar_Syntax_Util.type_u ())
in (match (_70_518) with
| (k, _70_517) -> begin
(
# 370 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _151_286 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_151_286, res_t)))
end))
end)
in (match (_70_522) with
| (env_branches, res_t) -> begin
(
# 373 "FStar.TypeChecker.Tc.fst"
let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (
# 374 "FStar.TypeChecker.Tc.fst"
let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (
# 375 "FStar.TypeChecker.Tc.fst"
let _70_539 = (
# 376 "FStar.TypeChecker.Tc.fst"
let _70_536 = (FStar_List.fold_right (fun _70_530 _70_533 -> (match ((_70_530, _70_533)) with
| ((_70_526, f, c, g), (caccum, gaccum)) -> begin
(let _151_289 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _151_289))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_70_536) with
| (cases, g) -> begin
(let _151_290 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_151_290, g))
end))
in (match (_70_539) with
| (c_branches, g_branches) -> begin
(
# 380 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (guard_x), c_branches))
in (
# 381 "FStar.TypeChecker.Tc.fst"
let e = (let _151_294 = (let _151_293 = (let _151_292 = (FStar_List.map (fun _70_548 -> (match (_70_548) with
| (f, _70_543, _70_545, _70_547) -> begin
f
end)) t_eqns)
in (e1, _151_292))
in FStar_Syntax_Syntax.Tm_match (_151_293))
in (FStar_Syntax_Syntax.mk _151_294 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (
# 382 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, cres.FStar_Syntax_Syntax.res_typ, Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (
# 383 "FStar.TypeChecker.Tc.fst"
let _70_551 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _151_297 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _151_296 = (let _151_295 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _151_295))
in (FStar_Util.print2 "(%s) comp type = %s\n" _151_297 _151_296)))
end else begin
()
end
in (let _151_298 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _151_298))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_70_563); FStar_Syntax_Syntax.lbunivs = _70_561; FStar_Syntax_Syntax.lbtyp = _70_559; FStar_Syntax_Syntax.lbeff = _70_557; FStar_Syntax_Syntax.lbdef = _70_555}::[]), _70_569) -> begin
(
# 390 "FStar.TypeChecker.Tc.fst"
let _70_572 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_299 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _151_299))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _70_576), _70_579) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_70_594); FStar_Syntax_Syntax.lbunivs = _70_592; FStar_Syntax_Syntax.lbtyp = _70_590; FStar_Syntax_Syntax.lbeff = _70_588; FStar_Syntax_Syntax.lbdef = _70_586}::_70_584), _70_600) -> begin
(
# 397 "FStar.TypeChecker.Tc.fst"
let _70_603 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_300 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _151_300))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _70_607), _70_610) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 410 "FStar.TypeChecker.Tc.fst"
let check_instantiated_fvar = (fun env v dc e t -> (
# 411 "FStar.TypeChecker.Tc.fst"
let _70_624 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_70_624) with
| (e, t, implicits) -> begin
(
# 413 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _151_314 = (let _151_313 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_313))
in FStar_Util.Inr (_151_314))
end
in (
# 414 "FStar.TypeChecker.Tc.fst"
let is_data_ctor = (fun _70_4 -> (match (_70_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _70_634 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _151_320 = (let _151_319 = (let _151_318 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _151_317 = (FStar_TypeChecker_Env.get_range env)
in (_151_318, _151_317)))
in FStar_Syntax_Syntax.Error (_151_319))
in (Prims.raise _151_320))
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
let g = (match ((let _151_321 = (FStar_Syntax_Subst.compress t1)
in _151_321.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_70_645) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _70_648 -> begin
(
# 433 "FStar.TypeChecker.Tc.fst"
let imp = (env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (
# 434 "FStar.TypeChecker.Tc.fst"
let _70_650 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _70_650.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _70_650.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _70_650.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 439 "FStar.TypeChecker.Tc.fst"
let _70_656 = (FStar_Syntax_Util.type_u ())
in (match (_70_656) with
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
let _70_661 = x
in {FStar_Syntax_Syntax.ppname = _70_661.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_661.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (
# 446 "FStar.TypeChecker.Tc.fst"
let _70_667 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_70_667) with
| (e, t, implicits) -> begin
(
# 447 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _151_323 = (let _151_322 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_322))
in FStar_Util.Inr (_151_323))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _70_674; FStar_Syntax_Syntax.pos = _70_672; FStar_Syntax_Syntax.vars = _70_670}, us) -> begin
(
# 451 "FStar.TypeChecker.Tc.fst"
let us = (FStar_List.map (tc_universe env) us)
in (
# 452 "FStar.TypeChecker.Tc.fst"
let _70_684 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_70_684) with
| (us', t) -> begin
(
# 453 "FStar.TypeChecker.Tc.fst"
let _70_691 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _151_326 = (let _151_325 = (let _151_324 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _151_324))
in FStar_Syntax_Syntax.Error (_151_325))
in (Prims.raise _151_326))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _70_690 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (
# 458 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 458 "FStar.TypeChecker.Tc.fst"
let _70_693 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 458 "FStar.TypeChecker.Tc.fst"
let _70_695 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _70_695.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _70_695.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _70_693.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _70_693.FStar_Syntax_Syntax.fv_qual})
in (
# 459 "FStar.TypeChecker.Tc.fst"
let e = (let _151_329 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _151_329 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(
# 463 "FStar.TypeChecker.Tc.fst"
let _70_703 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_70_703) with
| (us, t) -> begin
(
# 464 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 464 "FStar.TypeChecker.Tc.fst"
let _70_704 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 464 "FStar.TypeChecker.Tc.fst"
let _70_706 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _70_706.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _70_706.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _70_704.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _70_704.FStar_Syntax_Syntax.fv_qual})
in (
# 465 "FStar.TypeChecker.Tc.fst"
let e = (let _151_330 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _151_330 us))
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
let _70_720 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_70_720) with
| (bs, c) -> begin
(
# 475 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 476 "FStar.TypeChecker.Tc.fst"
let _70_725 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_725) with
| (env, _70_724) -> begin
(
# 477 "FStar.TypeChecker.Tc.fst"
let _70_730 = (tc_binders env bs)
in (match (_70_730) with
| (bs, env, g, us) -> begin
(
# 478 "FStar.TypeChecker.Tc.fst"
let _70_734 = (tc_comp env c)
in (match (_70_734) with
| (c, uc, f) -> begin
(
# 479 "FStar.TypeChecker.Tc.fst"
let e = (
# 479 "FStar.TypeChecker.Tc.fst"
let _70_735 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _70_735.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _70_735.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _70_735.FStar_Syntax_Syntax.vars})
in (
# 480 "FStar.TypeChecker.Tc.fst"
let _70_738 = (check_smt_pat env e bs c)
in (
# 481 "FStar.TypeChecker.Tc.fst"
let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (
# 482 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 483 "FStar.TypeChecker.Tc.fst"
let g = (let _151_331 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _151_331))
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
let _70_754 = (let _151_333 = (let _151_332 = (FStar_Syntax_Syntax.mk_binder x)
in (_151_332)::[])
in (FStar_Syntax_Subst.open_term _151_333 phi))
in (match (_70_754) with
| (x, phi) -> begin
(
# 494 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 495 "FStar.TypeChecker.Tc.fst"
let _70_759 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_759) with
| (env, _70_758) -> begin
(
# 496 "FStar.TypeChecker.Tc.fst"
let _70_764 = (let _151_334 = (FStar_List.hd x)
in (tc_binder env _151_334))
in (match (_70_764) with
| (x, env, f1, u) -> begin
(
# 497 "FStar.TypeChecker.Tc.fst"
let _70_765 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_337 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _151_336 = (FStar_Syntax_Print.term_to_string phi)
in (let _151_335 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _151_337 _151_336 _151_335))))
end else begin
()
end
in (
# 500 "FStar.TypeChecker.Tc.fst"
let _70_770 = (FStar_Syntax_Util.type_u ())
in (match (_70_770) with
| (t_phi, _70_769) -> begin
(
# 501 "FStar.TypeChecker.Tc.fst"
let _70_775 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_70_775) with
| (phi, _70_773, f2) -> begin
(
# 502 "FStar.TypeChecker.Tc.fst"
let e = (
# 502 "FStar.TypeChecker.Tc.fst"
let _70_776 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _70_776.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _70_776.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _70_776.FStar_Syntax_Syntax.vars})
in (
# 503 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 504 "FStar.TypeChecker.Tc.fst"
let g = (let _151_338 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _151_338))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _70_784) -> begin
(
# 508 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (
# 509 "FStar.TypeChecker.Tc.fst"
let _70_790 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_339 = (FStar_Syntax_Print.term_to_string (
# 510 "FStar.TypeChecker.Tc.fst"
let _70_788 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _70_788.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _70_788.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _70_788.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _151_339))
end else begin
()
end
in (
# 511 "FStar.TypeChecker.Tc.fst"
let _70_794 = (FStar_Syntax_Subst.open_term bs body)
in (match (_70_794) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _70_796 -> begin
(let _151_341 = (let _151_340 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _151_340))
in (FStar_All.failwith _151_341))
end)))))
and tc_constant : FStar_TypeChecker_Env.env  ->  FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun env r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_70_802) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_70_805) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int32 (_70_808) -> begin
FStar_TypeChecker_Common.t_int32
end
| FStar_Const.Const_int64 (_70_811) -> begin
FStar_TypeChecker_Common.t_int64
end
| FStar_Const.Const_string (_70_814) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_70_817) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_70_820) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_uint8 (_70_823) -> begin
FStar_TypeChecker_Common.t_uint8
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_70_827) -> begin
(
# 530 "FStar.TypeChecker.Tc.fst"
let fail = (fun _70_830 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Range constant cannot be checked in this context; expected an instance of \'range_of\'", r))))
end))
in (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(fail ())
end
| Some (t) -> begin
if (let _151_347 = (FStar_Syntax_Util.destruct t FStar_Syntax_Const.range_of_lid)
in (FStar_Option.isSome _151_347)) then begin
t
end else begin
(fail ())
end
end))
end
| _70_835 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 551 "FStar.TypeChecker.Tc.fst"
let _70_842 = (FStar_Syntax_Util.type_u ())
in (match (_70_842) with
| (k, u) -> begin
(
# 552 "FStar.TypeChecker.Tc.fst"
let _70_847 = (tc_check_tot_or_gtot_term env t k)
in (match (_70_847) with
| (t, _70_845, g) -> begin
(let _151_350 = (FStar_Syntax_Syntax.mk_Total t)
in (_151_350, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 556 "FStar.TypeChecker.Tc.fst"
let _70_852 = (FStar_Syntax_Util.type_u ())
in (match (_70_852) with
| (k, u) -> begin
(
# 557 "FStar.TypeChecker.Tc.fst"
let _70_857 = (tc_check_tot_or_gtot_term env t k)
in (match (_70_857) with
| (t, _70_855, g) -> begin
(let _151_351 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_151_351, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 561 "FStar.TypeChecker.Tc.fst"
let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (
# 562 "FStar.TypeChecker.Tc.fst"
let tc = (let _151_353 = (let _151_352 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_151_352)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _151_353 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 563 "FStar.TypeChecker.Tc.fst"
let _70_866 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_70_866) with
| (tc, _70_864, f) -> begin
(
# 564 "FStar.TypeChecker.Tc.fst"
let _70_870 = (FStar_Syntax_Util.head_and_args tc)
in (match (_70_870) with
| (_70_868, args) -> begin
(
# 565 "FStar.TypeChecker.Tc.fst"
let _70_873 = (let _151_355 = (FStar_List.hd args)
in (let _151_354 = (FStar_List.tl args)
in (_151_355, _151_354)))
in (match (_70_873) with
| (res, args) -> begin
(
# 566 "FStar.TypeChecker.Tc.fst"
let _70_889 = (let _151_357 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _70_5 -> (match (_70_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(
# 568 "FStar.TypeChecker.Tc.fst"
let _70_880 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_880) with
| (env, _70_879) -> begin
(
# 569 "FStar.TypeChecker.Tc.fst"
let _70_885 = (tc_tot_or_gtot_term env e)
in (match (_70_885) with
| (e, _70_883, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _151_357 FStar_List.unzip))
in (match (_70_889) with
| (flags, guards) -> begin
(
# 572 "FStar.TypeChecker.Tc.fst"
let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| _70_894 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _151_359 = (FStar_Syntax_Syntax.mk_Comp (
# 575 "FStar.TypeChecker.Tc.fst"
let _70_896 = c
in {FStar_Syntax_Syntax.effect_name = _70_896.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _70_896.FStar_Syntax_Syntax.flags}))
in (let _151_358 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_151_359, u, _151_358))))
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
| FStar_Syntax_Syntax.U_bvar (_70_904) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _151_364 = (aux u)
in FStar_Syntax_Syntax.U_succ (_151_364))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _151_365 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_151_365))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _151_369 = (let _151_368 = (let _151_367 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _151_366 = (FStar_TypeChecker_Env.get_range env)
in (_151_367, _151_366)))
in FStar_Syntax_Syntax.Error (_151_368))
in (Prims.raise _151_369))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _151_370 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_370 Prims.snd))
end
| _70_919 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (
# 605 "FStar.TypeChecker.Tc.fst"
let fail = (fun msg t -> (let _151_379 = (let _151_378 = (let _151_377 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_151_377, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_151_378))
in (Prims.raise _151_379)))
in (
# 614 "FStar.TypeChecker.Tc.fst"
let check_binders = (fun env bs bs_expected -> (
# 619 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun _70_937 bs bs_expected -> (match (_70_937) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| ((hd, imp)::bs, (hd_expected, imp')::bs_expected) -> begin
(
# 623 "FStar.TypeChecker.Tc.fst"
let _70_968 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _151_396 = (let _151_395 = (let _151_394 = (let _151_392 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _151_392))
in (let _151_393 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_151_394, _151_393)))
in FStar_Syntax_Syntax.Error (_151_395))
in (Prims.raise _151_396))
end
| _70_967 -> begin
()
end)
in (
# 630 "FStar.TypeChecker.Tc.fst"
let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (
# 631 "FStar.TypeChecker.Tc.fst"
let _70_985 = (match ((let _151_397 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _151_397.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _70_973 -> begin
(
# 634 "FStar.TypeChecker.Tc.fst"
let _70_974 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_398 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _151_398))
end else begin
()
end
in (
# 635 "FStar.TypeChecker.Tc.fst"
let _70_980 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_70_980) with
| (t, _70_978, g1) -> begin
(
# 636 "FStar.TypeChecker.Tc.fst"
let g2 = (let _151_400 = (FStar_TypeChecker_Env.get_range env)
in (let _151_399 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _151_400 "Type annotation on parameter incompatible with the expected type" _151_399)))
in (
# 640 "FStar.TypeChecker.Tc.fst"
let g = (let _151_401 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _151_401))
in (t, g)))
end)))
end)
in (match (_70_985) with
| (t, g) -> begin
(
# 642 "FStar.TypeChecker.Tc.fst"
let hd = (
# 642 "FStar.TypeChecker.Tc.fst"
let _70_986 = hd
in {FStar_Syntax_Syntax.ppname = _70_986.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_986.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
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
let subst = (let _151_402 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _151_402))
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
let _70_1006 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _70_1005 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (
# 669 "FStar.TypeChecker.Tc.fst"
let _70_1013 = (tc_binders env bs)
in (match (_70_1013) with
| (bs, envbody, g, _70_1012) -> begin
(None, bs, [], None, envbody, g)
end)))
end
| Some (t) -> begin
(
# 673 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 674 "FStar.TypeChecker.Tc.fst"
let rec as_function_typ = (fun norm t -> (match ((let _151_411 = (FStar_Syntax_Subst.compress t)
in _151_411.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 678 "FStar.TypeChecker.Tc.fst"
let _70_1040 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _70_1039 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 679 "FStar.TypeChecker.Tc.fst"
let _70_1047 = (tc_binders env bs)
in (match (_70_1047) with
| (bs, envbody, g, _70_1046) -> begin
(
# 680 "FStar.TypeChecker.Tc.fst"
let _70_1051 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_70_1051) with
| (envbody, _70_1050) -> begin
(Some ((t, true)), bs, [], None, envbody, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _70_1054) -> begin
(
# 686 "FStar.TypeChecker.Tc.fst"
let _70_1064 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_70_1064) with
| (_70_1058, bs, bs', copt, env, g) -> begin
(Some ((t, false)), bs, bs', copt, env, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 690 "FStar.TypeChecker.Tc.fst"
let _70_1071 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_70_1071) with
| (bs_expected, c_expected) -> begin
(
# 697 "FStar.TypeChecker.Tc.fst"
let check_actuals_against_formals = (fun env bs bs_expected -> (
# 698 "FStar.TypeChecker.Tc.fst"
let rec handle_more = (fun _70_1082 c_expected -> (match (_70_1082) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _151_422 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _151_422))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(
# 703 "FStar.TypeChecker.Tc.fst"
let c = (let _151_423 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _151_423))
in (let _151_424 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _151_424)))
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
let _70_1103 = (check_binders env more_bs bs_expected)
in (match (_70_1103) with
| (env, bs', more, guard', subst) -> begin
(let _151_426 = (let _151_425 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _151_425, subst))
in (handle_more _151_426 c_expected))
end))
end
| _70_1105 -> begin
(let _151_428 = (let _151_427 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _151_427))
in (fail _151_428 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _151_429 = (check_binders env bs bs_expected)
in (handle_more _151_429 c_expected))))
in (
# 720 "FStar.TypeChecker.Tc.fst"
let mk_letrec_env = (fun envbody bs c -> (
# 721 "FStar.TypeChecker.Tc.fst"
let letrecs = (guard_letrecs envbody bs c)
in (
# 722 "FStar.TypeChecker.Tc.fst"
let envbody = (
# 722 "FStar.TypeChecker.Tc.fst"
let _70_1111 = envbody
in {FStar_TypeChecker_Env.solver = _70_1111.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1111.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1111.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1111.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1111.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1111.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1111.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1111.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1111.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1111.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1111.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1111.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _70_1111.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _70_1111.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_1111.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_1111.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1111.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1111.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1111.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1111.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1111.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _70_1116 _70_1119 -> (match ((_70_1116, _70_1119)) with
| ((env, letrec_binders), (l, t)) -> begin
(
# 724 "FStar.TypeChecker.Tc.fst"
let _70_1125 = (let _151_439 = (let _151_438 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _151_438 Prims.fst))
in (tc_term _151_439 t))
in (match (_70_1125) with
| (t, _70_1122, _70_1124) -> begin
(
# 725 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (
# 726 "FStar.TypeChecker.Tc.fst"
let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _151_440 = (FStar_Syntax_Syntax.mk_binder (
# 727 "FStar.TypeChecker.Tc.fst"
let _70_1129 = x
in {FStar_Syntax_Syntax.ppname = _70_1129.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_1129.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_151_440)::letrec_binders)
end
| _70_1132 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (
# 732 "FStar.TypeChecker.Tc.fst"
let _70_1138 = (check_actuals_against_formals env bs bs_expected)
in (match (_70_1138) with
| (envbody, bs, g, c) -> begin
(
# 733 "FStar.TypeChecker.Tc.fst"
let _70_1141 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_70_1141) with
| (envbody, letrecs) -> begin
(
# 734 "FStar.TypeChecker.Tc.fst"
let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, g))
end))
end))))
end))
end
| _70_1144 -> begin
if (not (norm)) then begin
(let _151_441 = (unfold_whnf env t)
in (as_function_typ true _151_441))
end else begin
(
# 742 "FStar.TypeChecker.Tc.fst"
let _70_1153 = (expected_function_typ env None)
in (match (_70_1153) with
| (_70_1146, bs, _70_1149, c_opt, envbody, g) -> begin
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
let _70_1157 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_1157) with
| (env, topt) -> begin
(
# 748 "FStar.TypeChecker.Tc.fst"
let _70_1161 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_442 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _151_442 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (
# 752 "FStar.TypeChecker.Tc.fst"
let _70_1169 = (expected_function_typ env topt)
in (match (_70_1169) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, g) -> begin
(
# 753 "FStar.TypeChecker.Tc.fst"
let _70_1175 = (tc_term (
# 753 "FStar.TypeChecker.Tc.fst"
let _70_1170 = envbody
in {FStar_TypeChecker_Env.solver = _70_1170.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1170.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1170.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1170.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1170.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1170.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1170.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1170.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1170.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1170.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1170.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1170.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_1170.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _70_1170.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _70_1170.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1170.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1170.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1170.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1170.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1170.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_70_1175) with
| (body, cbody, guard_body) -> begin
(
# 754 "FStar.TypeChecker.Tc.fst"
let _70_1176 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_446 = (FStar_Syntax_Print.term_to_string body)
in (let _151_445 = (let _151_443 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _151_443))
in (let _151_444 = (FStar_TypeChecker_Rel.guard_to_string env guard_body)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _151_446 _151_445 _151_444))))
end else begin
()
end
in (
# 759 "FStar.TypeChecker.Tc.fst"
let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (
# 761 "FStar.TypeChecker.Tc.fst"
let _70_1179 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _151_449 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _151_448 = (let _151_447 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _151_447))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _151_449 _151_448)))
end else begin
()
end
in (
# 765 "FStar.TypeChecker.Tc.fst"
let _70_1186 = (let _151_451 = (let _151_450 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _151_450))
in (check_expected_effect (
# 765 "FStar.TypeChecker.Tc.fst"
let _70_1181 = envbody
in {FStar_TypeChecker_Env.solver = _70_1181.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1181.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1181.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1181.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1181.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1181.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1181.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1181.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1181.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1181.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1181.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1181.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_1181.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _70_1181.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _70_1181.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _70_1181.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1181.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1181.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1181.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1181.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1181.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _151_451))
in (match (_70_1186) with
| (body, cbody, guard) -> begin
(
# 766 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (
# 767 "FStar.TypeChecker.Tc.fst"
let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _151_452 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _151_452))
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
let _70_1209 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(
# 776 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_70_1198) -> begin
(e, t, guard)
end
| _70_1201 -> begin
(
# 785 "FStar.TypeChecker.Tc.fst"
let _70_1204 = if use_teq then begin
(let _151_453 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _151_453))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_70_1204) with
| (e, guard') -> begin
(let _151_454 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _151_454))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_70_1209) with
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
let _70_1213 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_70_1213) with
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
let _70_1223 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_463 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _151_462 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _151_463 _151_462)))
end else begin
()
end
in (
# 808 "FStar.TypeChecker.Tc.fst"
let rec check_function_app = (fun norm tf -> (match ((let _151_468 = (FStar_Syntax_Util.unrefine tf)
in _151_468.FStar_Syntax_Syntax.n)) with
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
let _70_1257 = (tc_term env e)
in (match (_70_1257) with
| (e, c, g_e) -> begin
(
# 816 "FStar.TypeChecker.Tc.fst"
let _70_1261 = (tc_args env tl)
in (match (_70_1261) with
| (args, comps, g_rest) -> begin
(let _151_473 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, (c)::comps, _151_473))
end))
end))
end))
in (
# 824 "FStar.TypeChecker.Tc.fst"
let _70_1265 = (tc_args env args)
in (match (_70_1265) with
| (args, comps, g_args) -> begin
(
# 825 "FStar.TypeChecker.Tc.fst"
let bs = (let _151_475 = (FStar_All.pipe_right comps (FStar_List.map (fun c -> (c.FStar_Syntax_Syntax.res_typ, None))))
in (FStar_Syntax_Util.null_binders_of_tks _151_475))
in (
# 826 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _70_1272 -> begin
FStar_Syntax_Util.ml_comp
end)
in (
# 829 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _151_490 = (FStar_Syntax_Subst.compress t)
in _151_490.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_70_1278) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _70_1283 -> begin
ml_or_tot
end)
end)
in (
# 836 "FStar.TypeChecker.Tc.fst"
let cres = (let _151_495 = (let _151_494 = (let _151_493 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_493 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _151_494))
in (ml_or_tot _151_495 r))
in (
# 837 "FStar.TypeChecker.Tc.fst"
let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (
# 838 "FStar.TypeChecker.Tc.fst"
let _70_1287 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _151_498 = (FStar_Syntax_Print.term_to_string head)
in (let _151_497 = (FStar_Syntax_Print.term_to_string tf)
in (let _151_496 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _151_498 _151_497 _151_496))))
end else begin
()
end
in (
# 843 "FStar.TypeChecker.Tc.fst"
let _70_1289 = (let _151_499 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _151_499))
in (
# 844 "FStar.TypeChecker.Tc.fst"
let comp = (let _151_502 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_TypeChecker_Util.bind env None c (None, out))) ((chead)::comps) _151_502))
in (let _151_504 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _151_503 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_151_504, comp, _151_503)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 848 "FStar.TypeChecker.Tc.fst"
let _70_1300 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_70_1300) with
| (bs, c) -> begin
(
# 850 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun _70_1308 bs cres args -> (match (_70_1308) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (_70_1315)))::rest, (_70_1323, None)::_70_1321) -> begin
(
# 861 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 862 "FStar.TypeChecker.Tc.fst"
let _70_1329 = (check_no_escape (Some (head)) env fvs t)
in (
# 863 "FStar.TypeChecker.Tc.fst"
let _70_1335 = (FStar_TypeChecker_Util.new_implicit_var env t)
in (match (_70_1335) with
| (varg, _70_1333, implicits) -> begin
(
# 864 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (
# 865 "FStar.TypeChecker.Tc.fst"
let arg = (let _151_513 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _151_513))
in (let _151_515 = (let _151_514 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _151_514, fvs))
in (tc_args _151_515 rest cres args))))
end))))
end
| ((x, aqual)::rest, (e, aq)::rest') -> begin
(
# 869 "FStar.TypeChecker.Tc.fst"
let _70_1367 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _70_1366 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (
# 874 "FStar.TypeChecker.Tc.fst"
let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 875 "FStar.TypeChecker.Tc.fst"
let x = (
# 875 "FStar.TypeChecker.Tc.fst"
let _70_1370 = x
in {FStar_Syntax_Syntax.ppname = _70_1370.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_1370.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (
# 876 "FStar.TypeChecker.Tc.fst"
let _70_1373 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _151_516 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _151_516))
end else begin
()
end
in (
# 877 "FStar.TypeChecker.Tc.fst"
let _70_1375 = (check_no_escape (Some (head)) env fvs targ)
in (
# 878 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (
# 879 "FStar.TypeChecker.Tc.fst"
let env = (
# 879 "FStar.TypeChecker.Tc.fst"
let _70_1378 = env
in {FStar_TypeChecker_Env.solver = _70_1378.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1378.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1378.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1378.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1378.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1378.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1378.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1378.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1378.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1378.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1378.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1378.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_1378.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _70_1378.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _70_1378.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _70_1378.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1378.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1378.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1378.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1378.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1378.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 880 "FStar.TypeChecker.Tc.fst"
let _70_1381 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_519 = (FStar_Syntax_Print.tag_of_term e)
in (let _151_518 = (FStar_Syntax_Print.term_to_string e)
in (let _151_517 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _151_519 _151_518 _151_517))))
end else begin
()
end
in (
# 881 "FStar.TypeChecker.Tc.fst"
let _70_1386 = (tc_term env e)
in (match (_70_1386) with
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
let subst = (let _151_520 = (FStar_List.hd bs)
in (maybe_extend_subst subst _151_520 e))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(
# 889 "FStar.TypeChecker.Tc.fst"
let subst = (let _151_521 = (FStar_List.hd bs)
in (maybe_extend_subst subst _151_521 e))
in (
# 890 "FStar.TypeChecker.Tc.fst"
let _70_1393 = (((Some (x), c))::comps, g)
in (match (_70_1393) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _151_522 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _151_522)) then begin
(
# 894 "FStar.TypeChecker.Tc.fst"
let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (
# 895 "FStar.TypeChecker.Tc.fst"
let arg' = (let _151_523 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _151_523))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (newx), c))::comps, g, fvs) rest cres rest')))
end else begin
(let _151_527 = (let _151_526 = (let _151_525 = (let _151_524 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _151_524))
in (_151_525)::arg_rets)
in (subst, (arg)::outargs, _151_526, ((Some (x), c))::comps, g, (x)::fvs))
in (tc_args _151_527 rest cres rest'))
end
end
end))
end))))))))))
end
| (_70_1397, []) -> begin
(
# 904 "FStar.TypeChecker.Tc.fst"
let _70_1400 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (
# 905 "FStar.TypeChecker.Tc.fst"
let _70_1418 = (match (bs) with
| [] -> begin
(
# 908 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (
# 914 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (
# 916 "FStar.TypeChecker.Tc.fst"
let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _70_1408 -> (match (_70_1408) with
| (_70_1406, c) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (
# 923 "FStar.TypeChecker.Tc.fst"
let cres = if refine_with_equality then begin
(let _151_529 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _151_529 cres))
end else begin
(
# 929 "FStar.TypeChecker.Tc.fst"
let _70_1410 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_532 = (FStar_Syntax_Print.term_to_string head)
in (let _151_531 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _151_530 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _151_532 _151_531 _151_530))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _70_1414 -> begin
(
# 938 "FStar.TypeChecker.Tc.fst"
let g = (let _151_533 = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (FStar_All.pipe_right _151_533 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _151_538 = (let _151_537 = (let _151_536 = (let _151_535 = (let _151_534 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _151_534))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _151_535))
in (FStar_Syntax_Syntax.mk_Total _151_536))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_537))
in (_151_538, g)))
end)
in (match (_70_1418) with
| (cres, g) -> begin
(
# 941 "FStar.TypeChecker.Tc.fst"
let _70_1419 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_539 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _151_539))
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
let _70_1429 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp g)
in (match (_70_1429) with
| (comp, g) -> begin
(
# 947 "FStar.TypeChecker.Tc.fst"
let _70_1430 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_545 = (FStar_TypeChecker_Normalize.term_to_string env app)
in (let _151_544 = (let _151_543 = (comp.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Print.comp_to_string _151_543))
in (FStar_Util.print2 "\t Type of app term %s is %s\n" _151_545 _151_544)))
end else begin
()
end
in (app, comp, g))
end)))))))
end)))
end
| ([], arg::_70_1434) -> begin
(
# 953 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun norm tres -> (
# 954 "FStar.TypeChecker.Tc.fst"
let tres = (let _151_550 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _151_550 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(
# 957 "FStar.TypeChecker.Tc.fst"
let _70_1446 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_551 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _151_551))
end else begin
()
end
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs (FStar_Syntax_Util.lcomp_of_comp cres') args))
end
| _70_1449 when (not (norm)) -> begin
(let _151_552 = (unfold_whnf env tres)
in (aux true _151_552))
end
| _70_1451 -> begin
(let _151_558 = (let _151_557 = (let _151_556 = (let _151_554 = (FStar_TypeChecker_Normalize.term_to_string env tf)
in (let _151_553 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _151_554 _151_553)))
in (let _151_555 = (FStar_Syntax_Syntax.argpos arg)
in (_151_556, _151_555)))
in FStar_Syntax_Syntax.Error (_151_557))
in (Prims.raise _151_558))
end)))
in (aux false cres.FStar_Syntax_Syntax.res_typ))
end)
end))
in (tc_args ([], [], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs (FStar_Syntax_Util.lcomp_of_comp c) args))
end))
end
| _70_1453 -> begin
if (not (norm)) then begin
(let _151_559 = (unfold_whnf env tf)
in (check_function_app true _151_559))
end else begin
(let _151_562 = (let _151_561 = (let _151_560 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_151_560, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_151_561))
in (Prims.raise _151_562))
end
end))
in (let _151_564 = (let _151_563 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _151_563))
in (check_function_app false _151_564))))))))
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
let _70_1489 = (FStar_List.fold_left2 (fun _70_1470 _70_1473 _70_1476 -> (match ((_70_1470, _70_1473, _70_1476)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(
# 989 "FStar.TypeChecker.Tc.fst"
let _70_1477 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 990 "FStar.TypeChecker.Tc.fst"
let _70_1482 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_70_1482) with
| (e, c, g) -> begin
(
# 991 "FStar.TypeChecker.Tc.fst"
let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (
# 992 "FStar.TypeChecker.Tc.fst"
let g = (let _151_574 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _151_574 g))
in (
# 993 "FStar.TypeChecker.Tc.fst"
let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _151_578 = (let _151_576 = (let _151_575 = (FStar_Syntax_Syntax.as_arg e)
in (_151_575)::[])
in (FStar_List.append seen _151_576))
in (let _151_577 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_151_578, _151_577, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_70_1489) with
| (args, guard, ghost) -> begin
(
# 997 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (
# 998 "FStar.TypeChecker.Tc.fst"
let c = if ghost then begin
(let _151_579 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _151_579 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (
# 999 "FStar.TypeChecker.Tc.fst"
let _70_1494 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_70_1494) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _70_1496 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (
# 1019 "FStar.TypeChecker.Tc.fst"
let _70_1503 = (FStar_Syntax_Subst.open_branch branch)
in (match (_70_1503) with
| (pattern, when_clause, branch_exp) -> begin
(
# 1020 "FStar.TypeChecker.Tc.fst"
let _70_1508 = branch
in (match (_70_1508) with
| (cpat, _70_1506, cbr) -> begin
(
# 1023 "FStar.TypeChecker.Tc.fst"
let tc_pat = (fun allow_implicits pat_t p0 -> (
# 1030 "FStar.TypeChecker.Tc.fst"
let _70_1516 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_70_1516) with
| (pat_bvs, exps, p) -> begin
(
# 1031 "FStar.TypeChecker.Tc.fst"
let _70_1517 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_591 = (FStar_Syntax_Print.pat_to_string p0)
in (let _151_590 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _151_591 _151_590)))
end else begin
()
end
in (
# 1033 "FStar.TypeChecker.Tc.fst"
let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (
# 1034 "FStar.TypeChecker.Tc.fst"
let _70_1523 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_70_1523) with
| (env1, _70_1522) -> begin
(
# 1035 "FStar.TypeChecker.Tc.fst"
let env1 = (
# 1035 "FStar.TypeChecker.Tc.fst"
let _70_1524 = env1
in {FStar_TypeChecker_Env.solver = _70_1524.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1524.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1524.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1524.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1524.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1524.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1524.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1524.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _70_1524.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1524.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1524.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_1524.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _70_1524.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _70_1524.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_1524.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_1524.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1524.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1524.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1524.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1524.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1524.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1036 "FStar.TypeChecker.Tc.fst"
let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (
# 1037 "FStar.TypeChecker.Tc.fst"
let _70_1563 = (let _151_614 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (
# 1038 "FStar.TypeChecker.Tc.fst"
let _70_1529 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_594 = (FStar_Syntax_Print.term_to_string e)
in (let _151_593 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _151_594 _151_593)))
end else begin
()
end
in (
# 1041 "FStar.TypeChecker.Tc.fst"
let _70_1534 = (tc_term env1 e)
in (match (_70_1534) with
| (e, lc, g) -> begin
(
# 1043 "FStar.TypeChecker.Tc.fst"
let _70_1535 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_596 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _151_595 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _151_596 _151_595)))
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
let _70_1541 = (let _151_597 = (FStar_TypeChecker_Rel.discharge_guard env (
# 1048 "FStar.TypeChecker.Tc.fst"
let _70_1539 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _70_1539.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _70_1539.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _70_1539.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _151_597 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1049 "FStar.TypeChecker.Tc.fst"
let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (
# 1050 "FStar.TypeChecker.Tc.fst"
let uvars_to_string = (fun uvs -> (let _151_602 = (let _151_601 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _151_601 (FStar_List.map (fun _70_1549 -> (match (_70_1549) with
| (u, _70_1548) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _151_602 (FStar_String.concat ", "))))
in (
# 1051 "FStar.TypeChecker.Tc.fst"
let uvs1 = (FStar_Syntax_Free.uvars e')
in (
# 1052 "FStar.TypeChecker.Tc.fst"
let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (
# 1053 "FStar.TypeChecker.Tc.fst"
let _70_1557 = if (let _151_603 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _151_603)) then begin
(
# 1054 "FStar.TypeChecker.Tc.fst"
let unresolved = (let _151_604 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _151_604 FStar_Util.set_elements))
in (let _151_612 = (let _151_611 = (let _151_610 = (let _151_609 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _151_608 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _151_607 = (let _151_606 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _70_1556 -> (match (_70_1556) with
| (u, _70_1555) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _151_606 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _151_609 _151_608 _151_607))))
in (_151_610, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_151_611))
in (Prims.raise _151_612)))
end else begin
()
end
in (
# 1061 "FStar.TypeChecker.Tc.fst"
let _70_1559 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_613 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _151_613))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _151_614 FStar_List.unzip))
in (match (_70_1563) with
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
let _70_1570 = (let _151_615 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _151_615 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_70_1570) with
| (scrutinee_env, _70_1569) -> begin
(
# 1075 "FStar.TypeChecker.Tc.fst"
let _70_1576 = (tc_pat true pat_t pattern)
in (match (_70_1576) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(
# 1078 "FStar.TypeChecker.Tc.fst"
let _70_1586 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(
# 1085 "FStar.TypeChecker.Tc.fst"
let _70_1583 = (let _151_616 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _151_616 e))
in (match (_70_1583) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_70_1586) with
| (when_clause, g_when) -> begin
(
# 1089 "FStar.TypeChecker.Tc.fst"
let _70_1590 = (tc_term pat_env branch_exp)
in (match (_70_1590) with
| (branch_exp, c, g_branch) -> begin
(
# 1093 "FStar.TypeChecker.Tc.fst"
let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _151_618 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _151_617 -> Some (_151_617)) _151_618))
end)
in (
# 1100 "FStar.TypeChecker.Tc.fst"
let _70_1646 = (
# 1103 "FStar.TypeChecker.Tc.fst"
let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (
# 1104 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _70_1608 -> begin
(
# 1110 "FStar.TypeChecker.Tc.fst"
let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _151_622 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _151_621 -> Some (_151_621)) _151_622))
end))
end))) None))
in (
# 1115 "FStar.TypeChecker.Tc.fst"
let _70_1616 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_70_1616) with
| (c, g_branch) -> begin
(
# 1119 "FStar.TypeChecker.Tc.fst"
let _70_1641 = (match ((eqs, when_condition)) with
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
in (let _151_625 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _151_624 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_151_625, _151_624)))))
end
| (Some (f), Some (w)) -> begin
(
# 1131 "FStar.TypeChecker.Tc.fst"
let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1132 "FStar.TypeChecker.Tc.fst"
let g_fw = (let _151_626 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_151_626))
in (let _151_629 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _151_628 = (let _151_627 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _151_627 g_when))
in (_151_629, _151_628)))))
end
| (None, Some (w)) -> begin
(
# 1137 "FStar.TypeChecker.Tc.fst"
let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (
# 1138 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _151_630 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_151_630, g_when))))
end)
in (match (_70_1641) with
| (c_weak, g_when_weak) -> begin
(
# 1143 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _151_632 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _151_631 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_151_632, _151_631, g_branch))))
end))
end)))
in (match (_70_1646) with
| (c, g_when, g_branch) -> begin
(
# 1161 "FStar.TypeChecker.Tc.fst"
let branch_guard = (
# 1163 "FStar.TypeChecker.Tc.fst"
let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (
# 1164 "FStar.TypeChecker.Tc.fst"
let discriminate = (fun scrutinee_tm f -> if ((let _151_642 = (let _151_641 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _151_641))
in (FStar_List.length _151_642)) > 1) then begin
(
# 1167 "FStar.TypeChecker.Tc.fst"
let disc = (let _151_643 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _151_643 FStar_Syntax_Syntax.Delta_equational None))
in (
# 1168 "FStar.TypeChecker.Tc.fst"
let disc = (let _151_645 = (let _151_644 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_151_644)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _151_645 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _151_646 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_151_646)::[])))
end else begin
[]
end)
in (
# 1172 "FStar.TypeChecker.Tc.fst"
let fail = (fun _70_1656 -> (match (()) with
| () -> begin
(let _151_652 = (let _151_651 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _151_650 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _151_649 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _151_651 _151_650 _151_649))))
in (FStar_All.failwith _151_652))
end))
in (
# 1178 "FStar.TypeChecker.Tc.fst"
let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _70_1663) -> begin
(head_constructor t)
end
| _70_1667 -> begin
(fail ())
end))
in (
# 1183 "FStar.TypeChecker.Tc.fst"
let pat_exp = (let _151_655 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _151_655 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_70_1692) -> begin
(let _151_660 = (let _151_659 = (let _151_658 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _151_657 = (let _151_656 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_151_656)::[])
in (_151_658)::_151_657))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _151_659 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_151_660)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 1192 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _151_661 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _151_661))
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
let sub_term_guards = (let _151_668 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _70_1710 -> (match (_70_1710) with
| (ei, _70_1709) -> begin
(
# 1201 "FStar.TypeChecker.Tc.fst"
let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (
# 1202 "FStar.TypeChecker.Tc.fst"
let sub_term = (let _151_667 = (let _151_664 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _151_664 FStar_Syntax_Syntax.Delta_equational None))
in (let _151_666 = (let _151_665 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_151_665)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _151_667 _151_666 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei)))
end))))
in (FStar_All.pipe_right _151_668 FStar_List.flatten))
in (let _151_669 = (discriminate scrutinee_tm f)
in (FStar_List.append _151_669 sub_term_guards)))
end)
end
| _70_1715 -> begin
[]
end))))))
in (
# 1208 "FStar.TypeChecker.Tc.fst"
let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(
# 1211 "FStar.TypeChecker.Tc.fst"
let t = (let _151_674 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _151_674))
in (
# 1212 "FStar.TypeChecker.Tc.fst"
let _70_1723 = (FStar_Syntax_Util.type_u ())
in (match (_70_1723) with
| (k, _70_1722) -> begin
(
# 1213 "FStar.TypeChecker.Tc.fst"
let _70_1729 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_70_1729) with
| (t, _70_1726, _70_1728) -> begin
t
end))
end)))
end)
in (
# 1217 "FStar.TypeChecker.Tc.fst"
let branch_guard = (let _151_675 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _151_675 FStar_Syntax_Util.mk_disj_l))
in (
# 1220 "FStar.TypeChecker.Tc.fst"
let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
in (
# 1226 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (
# 1228 "FStar.TypeChecker.Tc.fst"
let _70_1737 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_676 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _151_676))
end else begin
()
end
in (let _151_677 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_151_677, branch_guard, c, guard)))))
end)))
end))
end))
end))
end)))))
end))
end)))
and check_top_level_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1242 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1245 "FStar.TypeChecker.Tc.fst"
let _70_1754 = (check_let_bound_def true env lb)
in (match (_70_1754) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(
# 1248 "FStar.TypeChecker.Tc.fst"
let _70_1766 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(
# 1251 "FStar.TypeChecker.Tc.fst"
let g1 = (let _151_680 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _151_680 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1252 "FStar.TypeChecker.Tc.fst"
let _70_1761 = (let _151_684 = (let _151_683 = (let _151_682 = (let _151_681 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _151_681))
in (_151_682)::[])
in (FStar_TypeChecker_Util.generalize env _151_683))
in (FStar_List.hd _151_684))
in (match (_70_1761) with
| (_70_1757, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_70_1766) with
| (g1, e1, univ_vars, c1) -> begin
(
# 1256 "FStar.TypeChecker.Tc.fst"
let _70_1776 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(
# 1258 "FStar.TypeChecker.Tc.fst"
let _70_1769 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_70_1769) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(
# 1261 "FStar.TypeChecker.Tc.fst"
let _70_1770 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _151_685 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _151_685 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _151_686 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_151_686, c1)))
end
end))
end else begin
(
# 1265 "FStar.TypeChecker.Tc.fst"
let _70_1772 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _151_687 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _151_687)))
end
in (match (_70_1776) with
| (e2, c1) -> begin
(
# 1270 "FStar.TypeChecker.Tc.fst"
let cres = (let _151_688 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_688))
in (
# 1271 "FStar.TypeChecker.Tc.fst"
let _70_1778 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1273 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _151_689 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_151_689, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _70_1782 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1290 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1293 "FStar.TypeChecker.Tc.fst"
let env = (
# 1293 "FStar.TypeChecker.Tc.fst"
let _70_1793 = env
in {FStar_TypeChecker_Env.solver = _70_1793.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1793.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1793.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1793.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1793.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1793.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1793.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1793.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1793.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1793.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1793.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1793.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_1793.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _70_1793.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_1793.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_1793.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1793.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1793.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1793.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1793.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1793.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1294 "FStar.TypeChecker.Tc.fst"
let _70_1802 = (let _151_693 = (let _151_692 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _151_692 Prims.fst))
in (check_let_bound_def false _151_693 lb))
in (match (_70_1802) with
| (e1, _70_1798, c1, g1, annotated) -> begin
(
# 1295 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (
# 1296 "FStar.TypeChecker.Tc.fst"
let x = (
# 1296 "FStar.TypeChecker.Tc.fst"
let _70_1804 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _70_1804.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_1804.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (
# 1297 "FStar.TypeChecker.Tc.fst"
let _70_1809 = (let _151_695 = (let _151_694 = (FStar_Syntax_Syntax.mk_binder x)
in (_151_694)::[])
in (FStar_Syntax_Subst.open_term _151_695 e2))
in (match (_70_1809) with
| (xb, e2) -> begin
(
# 1298 "FStar.TypeChecker.Tc.fst"
let xbinder = (FStar_List.hd xb)
in (
# 1299 "FStar.TypeChecker.Tc.fst"
let x = (Prims.fst xbinder)
in (
# 1300 "FStar.TypeChecker.Tc.fst"
let _70_1815 = (let _151_696 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _151_696 e2))
in (match (_70_1815) with
| (e2, c2, g2) -> begin
(
# 1301 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (x), c2))
in (
# 1302 "FStar.TypeChecker.Tc.fst"
let e = (let _151_699 = (let _151_698 = (let _151_697 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _151_697))
in FStar_Syntax_Syntax.Tm_let (_151_698))
in (FStar_Syntax_Syntax.mk _151_699 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 1303 "FStar.TypeChecker.Tc.fst"
let x_eq_e1 = (let _151_702 = (let _151_701 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _151_701 e1))
in (FStar_All.pipe_left (fun _151_700 -> FStar_TypeChecker_Common.NonTrivial (_151_700)) _151_702))
in (
# 1304 "FStar.TypeChecker.Tc.fst"
let g2 = (let _151_704 = (let _151_703 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _151_703 g2))
in (FStar_TypeChecker_Rel.close_guard xb _151_704))
in (
# 1306 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if annotated then begin
(e, cres, guard)
end else begin
(
# 1310 "FStar.TypeChecker.Tc.fst"
let _70_1821 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end)))))
end))))
end))))
end)))
end
| _70_1824 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1319 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1322 "FStar.TypeChecker.Tc.fst"
let _70_1836 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_70_1836) with
| (lbs, e2) -> begin
(
# 1324 "FStar.TypeChecker.Tc.fst"
let _70_1839 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_1839) with
| (env0, topt) -> begin
(
# 1325 "FStar.TypeChecker.Tc.fst"
let _70_1842 = (build_let_rec_env true env0 lbs)
in (match (_70_1842) with
| (lbs, rec_env) -> begin
(
# 1326 "FStar.TypeChecker.Tc.fst"
let _70_1845 = (check_let_recs rec_env lbs)
in (match (_70_1845) with
| (lbs, g_lbs) -> begin
(
# 1327 "FStar.TypeChecker.Tc.fst"
let g_lbs = (let _151_707 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _151_707 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1329 "FStar.TypeChecker.Tc.fst"
let all_lb_names = (let _151_710 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _151_710 (fun _151_709 -> Some (_151_709))))
in (
# 1331 "FStar.TypeChecker.Tc.fst"
let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(
# 1337 "FStar.TypeChecker.Tc.fst"
let ecs = (let _151_714 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _151_713 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _151_713)))))
in (FStar_TypeChecker_Util.generalize env _151_714))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _70_1856 -> (match (_70_1856) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (
# 1344 "FStar.TypeChecker.Tc.fst"
let cres = (let _151_716 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_716))
in (
# 1345 "FStar.TypeChecker.Tc.fst"
let _70_1859 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1347 "FStar.TypeChecker.Tc.fst"
let _70_1863 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_70_1863) with
| (lbs, e2) -> begin
(let _151_718 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _151_717 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_151_718, cres, _151_717)))
end)))))))
end))
end))
end))
end))
end
| _70_1865 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1358 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1361 "FStar.TypeChecker.Tc.fst"
let _70_1877 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_70_1877) with
| (lbs, e2) -> begin
(
# 1363 "FStar.TypeChecker.Tc.fst"
let _70_1880 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_1880) with
| (env0, topt) -> begin
(
# 1364 "FStar.TypeChecker.Tc.fst"
let _70_1883 = (build_let_rec_env false env0 lbs)
in (match (_70_1883) with
| (lbs, rec_env) -> begin
(
# 1365 "FStar.TypeChecker.Tc.fst"
let _70_1886 = (check_let_recs rec_env lbs)
in (match (_70_1886) with
| (lbs, g_lbs) -> begin
(
# 1367 "FStar.TypeChecker.Tc.fst"
let _70_1904 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _70_1889 _70_1898 -> (match ((_70_1889, _70_1898)) with
| ((bvs, env), {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _70_1896; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _70_1893; FStar_Syntax_Syntax.lbdef = _70_1891}) -> begin
(
# 1368 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env x ([], t))
in (let _151_724 = (let _151_723 = (
# 1369 "FStar.TypeChecker.Tc.fst"
let _70_1900 = (FStar_Util.left x)
in {FStar_Syntax_Syntax.ppname = _70_1900.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_1900.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (_151_723)::bvs)
in (_151_724, env)))
end)) ([], env)))
in (match (_70_1904) with
| (bvs, env) -> begin
(
# 1370 "FStar.TypeChecker.Tc.fst"
let bvs = (FStar_List.rev bvs)
in (
# 1372 "FStar.TypeChecker.Tc.fst"
let _70_1909 = (tc_term env e2)
in (match (_70_1909) with
| (e2, cres, g2) -> begin
(
# 1373 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (
# 1374 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (
# 1375 "FStar.TypeChecker.Tc.fst"
let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (
# 1376 "FStar.TypeChecker.Tc.fst"
let cres = (
# 1376 "FStar.TypeChecker.Tc.fst"
let _70_1913 = cres
in {FStar_Syntax_Syntax.eff_name = _70_1913.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _70_1913.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _70_1913.FStar_Syntax_Syntax.comp})
in (
# 1378 "FStar.TypeChecker.Tc.fst"
let _70_1918 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_70_1918) with
| (lbs, e2) -> begin
(
# 1379 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_70_1921) -> begin
(e, cres, guard)
end
| None -> begin
(
# 1383 "FStar.TypeChecker.Tc.fst"
let _70_1924 = (check_no_escape None env bvs tres)
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
| _70_1927 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (
# 1394 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1395 "FStar.TypeChecker.Tc.fst"
let _70_1960 = (FStar_List.fold_left (fun _70_1934 lb -> (match (_70_1934) with
| (lbs, env) -> begin
(
# 1396 "FStar.TypeChecker.Tc.fst"
let _70_1939 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_70_1939) with
| (univ_vars, t, check_t) -> begin
(
# 1397 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (
# 1398 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (
# 1399 "FStar.TypeChecker.Tc.fst"
let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(
# 1404 "FStar.TypeChecker.Tc.fst"
let _70_1948 = (let _151_731 = (let _151_730 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _151_730))
in (tc_check_tot_or_gtot_term (
# 1404 "FStar.TypeChecker.Tc.fst"
let _70_1942 = env0
in {FStar_TypeChecker_Env.solver = _70_1942.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1942.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1942.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1942.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1942.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1942.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1942.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1942.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1942.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1942.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1942.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1942.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_1942.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _70_1942.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _70_1942.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_1942.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1942.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1942.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1942.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1942.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1942.FStar_TypeChecker_Env.use_bv_sorts}) t _151_731))
in (match (_70_1948) with
| (t, _70_1946, g) -> begin
(
# 1405 "FStar.TypeChecker.Tc.fst"
let _70_1949 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (
# 1407 "FStar.TypeChecker.Tc.fst"
let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(
# 1409 "FStar.TypeChecker.Tc.fst"
let _70_1952 = env
in {FStar_TypeChecker_Env.solver = _70_1952.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1952.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1952.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1952.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1952.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1952.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1952.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1952.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1952.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1952.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1952.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1952.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _70_1952.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _70_1952.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_1952.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_1952.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1952.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1952.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1952.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1952.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1952.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (
# 1411 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1411 "FStar.TypeChecker.Tc.fst"
let _70_1955 = lb
in {FStar_Syntax_Syntax.lbname = _70_1955.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _70_1955.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_70_1960) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (
# 1418 "FStar.TypeChecker.Tc.fst"
let _70_1973 = (let _151_736 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 1419 "FStar.TypeChecker.Tc.fst"
let _70_1967 = (let _151_735 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _151_735 lb.FStar_Syntax_Syntax.lbdef))
in (match (_70_1967) with
| (e, c, g) -> begin
(
# 1420 "FStar.TypeChecker.Tc.fst"
let _70_1968 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1422 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _151_736 FStar_List.unzip))
in (match (_70_1973) with
| (lbs, gs) -> begin
(
# 1424 "FStar.TypeChecker.Tc.fst"
let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (
# 1438 "FStar.TypeChecker.Tc.fst"
let _70_1981 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_1981) with
| (env1, _70_1980) -> begin
(
# 1439 "FStar.TypeChecker.Tc.fst"
let e1 = lb.FStar_Syntax_Syntax.lbdef
in (
# 1442 "FStar.TypeChecker.Tc.fst"
let _70_1987 = (check_lbtyp top_level env lb)
in (match (_70_1987) with
| (topt, wf_annot, univ_vars, env1) -> begin
(
# 1444 "FStar.TypeChecker.Tc.fst"
let _70_1988 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1448 "FStar.TypeChecker.Tc.fst"
let _70_1995 = (tc_maybe_toplevel_term (
# 1448 "FStar.TypeChecker.Tc.fst"
let _70_1990 = env1
in {FStar_TypeChecker_Env.solver = _70_1990.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1990.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1990.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1990.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1990.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1990.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1990.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1990.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1990.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1990.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1990.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1990.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_1990.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _70_1990.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_1990.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_1990.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1990.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1990.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1990.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1990.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1990.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_70_1995) with
| (e1, c1, g1) -> begin
(
# 1451 "FStar.TypeChecker.Tc.fst"
let _70_1999 = (let _151_743 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _70_1996 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _151_743 e1 c1 wf_annot))
in (match (_70_1999) with
| (c1, guard_f) -> begin
(
# 1454 "FStar.TypeChecker.Tc.fst"
let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (
# 1456 "FStar.TypeChecker.Tc.fst"
let _70_2001 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _151_744 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _151_744))
end else begin
()
end
in (let _151_745 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _151_745))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (
# 1468 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 1471 "FStar.TypeChecker.Tc.fst"
let _70_2008 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _70_2011 -> begin
(
# 1475 "FStar.TypeChecker.Tc.fst"
let _70_2014 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_70_2014) with
| (univ_vars, t) -> begin
(
# 1476 "FStar.TypeChecker.Tc.fst"
let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _151_749 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _151_749))
end else begin
(
# 1483 "FStar.TypeChecker.Tc.fst"
let _70_2019 = (FStar_Syntax_Util.type_u ())
in (match (_70_2019) with
| (k, _70_2018) -> begin
(
# 1484 "FStar.TypeChecker.Tc.fst"
let _70_2024 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_70_2024) with
| (t, _70_2022, g) -> begin
(
# 1485 "FStar.TypeChecker.Tc.fst"
let _70_2025 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _151_752 = (let _151_750 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _151_750))
in (let _151_751 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _151_752 _151_751)))
end else begin
()
end
in (
# 1489 "FStar.TypeChecker.Tc.fst"
let t = (norm env1 t)
in (let _151_753 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _151_753))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _70_2031 -> (match (_70_2031) with
| (x, imp) -> begin
(
# 1494 "FStar.TypeChecker.Tc.fst"
let _70_2034 = (FStar_Syntax_Util.type_u ())
in (match (_70_2034) with
| (tu, u) -> begin
(
# 1495 "FStar.TypeChecker.Tc.fst"
let _70_2039 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_70_2039) with
| (t, _70_2037, g) -> begin
(
# 1496 "FStar.TypeChecker.Tc.fst"
let x = ((
# 1496 "FStar.TypeChecker.Tc.fst"
let _70_2040 = x
in {FStar_Syntax_Syntax.ppname = _70_2040.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_2040.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (
# 1497 "FStar.TypeChecker.Tc.fst"
let _70_2043 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_757 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _151_756 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _151_757 _151_756)))
end else begin
()
end
in (let _151_758 = (maybe_push_binding env x)
in (x, _151_758, g, u))))
end))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe Prims.list) = (fun env bs -> (
# 1502 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_TypeChecker_Rel.trivial_guard, [])
end
| b::bs -> begin
(
# 1505 "FStar.TypeChecker.Tc.fst"
let _70_2058 = (tc_binder env b)
in (match (_70_2058) with
| (b, env', g, u) -> begin
(
# 1506 "FStar.TypeChecker.Tc.fst"
let _70_2063 = (aux env' bs)
in (match (_70_2063) with
| (bs, env', g', us) -> begin
(let _151_766 = (let _151_765 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _151_765))
in ((b)::bs, env', _151_766, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (
# 1511 "FStar.TypeChecker.Tc.fst"
let tc_args = (fun env args -> (FStar_List.fold_right (fun _70_2071 _70_2074 -> (match ((_70_2071, _70_2074)) with
| ((t, imp), (args, g)) -> begin
(
# 1515 "FStar.TypeChecker.Tc.fst"
let _70_2079 = (tc_term env t)
in (match (_70_2079) with
| (t, _70_2077, g') -> begin
(let _151_775 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _151_775))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _70_2083 -> (match (_70_2083) with
| (pats, g) -> begin
(
# 1518 "FStar.TypeChecker.Tc.fst"
let _70_2086 = (tc_args env p)
in (match (_70_2086) with
| (args, g') -> begin
(let _151_778 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _151_778))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1523 "FStar.TypeChecker.Tc.fst"
let _70_2092 = (tc_maybe_toplevel_term env e)
in (match (_70_2092) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(
# 1526 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (
# 1527 "FStar.TypeChecker.Tc.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 1528 "FStar.TypeChecker.Tc.fst"
let _70_2095 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_781 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _151_781))
end else begin
()
end
in (
# 1529 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 1530 "FStar.TypeChecker.Tc.fst"
let _70_2100 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _151_782 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_151_782, false))
end else begin
(let _151_783 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_151_783, true))
end
in (match (_70_2100) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _151_784 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _151_784))
end
| _70_2104 -> begin
if allow_ghost then begin
(let _151_787 = (let _151_786 = (let _151_785 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_151_785, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_151_786))
in (Prims.raise _151_787))
end else begin
(let _151_790 = (let _151_789 = (let _151_788 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_151_788, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_151_789))
in (Prims.raise _151_790))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 1544 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))

# 1548 "FStar.TypeChecker.Tc.fst"
let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (
# 1549 "FStar.TypeChecker.Tc.fst"
let _70_2114 = (tc_tot_or_gtot_term env t)
in (match (_70_2114) with
| (t, c, g) -> begin
(
# 1550 "FStar.TypeChecker.Tc.fst"
let _70_2115 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))

# 1553 "FStar.TypeChecker.Tc.fst"
let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (
# 1554 "FStar.TypeChecker.Tc.fst"
let _70_2123 = (tc_check_tot_or_gtot_term env t k)
in (match (_70_2123) with
| (t, c, g) -> begin
(
# 1555 "FStar.TypeChecker.Tc.fst"
let _70_2124 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))

# 1558 "FStar.TypeChecker.Tc.fst"
let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _151_810 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _151_810)))

# 1561 "FStar.TypeChecker.Tc.fst"
let check_nogen = (fun env t k -> (
# 1562 "FStar.TypeChecker.Tc.fst"
let t = (tc_check_trivial_guard env t k)
in (let _151_814 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _151_814))))

# 1565 "FStar.TypeChecker.Tc.fst"
let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (
# 1566 "FStar.TypeChecker.Tc.fst"
let _70_2139 = (tc_binders env tps)
in (match (_70_2139) with
| (tps, env, g, us) -> begin
(
# 1567 "FStar.TypeChecker.Tc.fst"
let _70_2140 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))

# 1570 "FStar.TypeChecker.Tc.fst"
let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (
# 1571 "FStar.TypeChecker.Tc.fst"
let fail = (fun _70_2146 -> (match (()) with
| () -> begin
(let _151_829 = (let _151_828 = (let _151_827 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_151_827, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_151_828))
in (Prims.raise _151_829))
end))
in (
# 1572 "FStar.TypeChecker.Tc.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1575 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _70_2163)::(wp, _70_2159)::(_wlp, _70_2155)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _70_2167 -> begin
(fail ())
end))
end
| _70_2169 -> begin
(fail ())
end))))

# 1582 "FStar.TypeChecker.Tc.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 1585 "FStar.TypeChecker.Tc.fst"
let _70_2176 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_70_2176) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _70_2178 -> begin
(
# 1588 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow binders c)
in (
# 1589 "FStar.TypeChecker.Tc.fst"
let _70_2182 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_70_2182) with
| (uvs, t') -> begin
(match ((let _151_836 = (FStar_Syntax_Subst.compress t')
in _151_836.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _70_2188 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 1594 "FStar.TypeChecker.Tc.fst"
let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (
# 1595 "FStar.TypeChecker.Tc.fst"
let fail = (fun t -> (let _151_847 = (let _151_846 = (let _151_845 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_151_845, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_151_846))
in (Prims.raise _151_847)))
in (match ((let _151_848 = (FStar_Syntax_Subst.compress signature)
in _151_848.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1598 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _70_2209)::(wp, _70_2205)::(_wlp, _70_2201)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _70_2213 -> begin
(fail signature)
end))
end
| _70_2215 -> begin
(fail signature)
end)))

# 1605 "FStar.TypeChecker.Tc.fst"
let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (
# 1606 "FStar.TypeChecker.Tc.fst"
let _70_2220 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_70_2220) with
| (a, wp) -> begin
(
# 1607 "FStar.TypeChecker.Tc.fst"
let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _70_2223 -> begin
(
# 1611 "FStar.TypeChecker.Tc.fst"
let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (
# 1612 "FStar.TypeChecker.Tc.fst"
let op = (fun ts -> (
# 1613 "FStar.TypeChecker.Tc.fst"
let _70_2227 = ()
in (
# 1614 "FStar.TypeChecker.Tc.fst"
let t0 = (Prims.snd ts)
in (
# 1615 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (
# 1617 "FStar.TypeChecker.Tc.fst"
let _70_2231 = ed
in (let _151_867 = (op ed.FStar_Syntax_Syntax.ret)
in (let _151_866 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _151_865 = (op ed.FStar_Syntax_Syntax.bind_wlp)
in (let _151_864 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _151_863 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _151_862 = (op ed.FStar_Syntax_Syntax.ite_wlp)
in (let _151_861 = (op ed.FStar_Syntax_Syntax.wp_binop)
in (let _151_860 = (op ed.FStar_Syntax_Syntax.wp_as_type)
in (let _151_859 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _151_858 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _151_857 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _151_856 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _151_855 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _70_2231.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _70_2231.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _70_2231.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _70_2231.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _70_2231.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _151_867; FStar_Syntax_Syntax.bind_wp = _151_866; FStar_Syntax_Syntax.bind_wlp = _151_865; FStar_Syntax_Syntax.if_then_else = _151_864; FStar_Syntax_Syntax.ite_wp = _151_863; FStar_Syntax_Syntax.ite_wlp = _151_862; FStar_Syntax_Syntax.wp_binop = _151_861; FStar_Syntax_Syntax.wp_as_type = _151_860; FStar_Syntax_Syntax.close_wp = _151_859; FStar_Syntax_Syntax.assert_p = _151_858; FStar_Syntax_Syntax.assume_p = _151_857; FStar_Syntax_Syntax.null_wp = _151_856; FStar_Syntax_Syntax.trivial = _151_855}))))))))))))))))
end)
in (ed, a, wp))
end)))

# 1633 "FStar.TypeChecker.Tc.fst"
let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (
# 1634 "FStar.TypeChecker.Tc.fst"
let _70_2236 = ()
in (
# 1635 "FStar.TypeChecker.Tc.fst"
let _70_2240 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_70_2240) with
| (binders_un, signature_un) -> begin
(
# 1636 "FStar.TypeChecker.Tc.fst"
let _70_2245 = (tc_tparams env0 binders_un)
in (match (_70_2245) with
| (binders, env, _70_2244) -> begin
(
# 1637 "FStar.TypeChecker.Tc.fst"
let _70_2249 = (tc_trivial_guard env signature_un)
in (match (_70_2249) with
| (signature, _70_2248) -> begin
(
# 1638 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1638 "FStar.TypeChecker.Tc.fst"
let _70_2250 = ed
in {FStar_Syntax_Syntax.qualifiers = _70_2250.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _70_2250.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _70_2250.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _70_2250.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _70_2250.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _70_2250.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = _70_2250.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _70_2250.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _70_2250.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = _70_2250.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _70_2250.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _70_2250.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _70_2250.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _70_2250.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _70_2250.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _70_2250.FStar_Syntax_Syntax.trivial})
in (
# 1641 "FStar.TypeChecker.Tc.fst"
let _70_2256 = (open_effect_decl env ed)
in (match (_70_2256) with
| (ed, a, wp_a) -> begin
(
# 1642 "FStar.TypeChecker.Tc.fst"
let get_effect_signature = (fun _70_2258 -> (match (()) with
| () -> begin
(
# 1643 "FStar.TypeChecker.Tc.fst"
let _70_2262 = (tc_trivial_guard env signature_un)
in (match (_70_2262) with
| (signature, _70_2261) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (
# 1647 "FStar.TypeChecker.Tc.fst"
let env = (let _151_874 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _151_874))
in (
# 1649 "FStar.TypeChecker.Tc.fst"
let _70_2264 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _151_877 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _151_876 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _151_875 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checked effect signature: %s %s : %s\n" _151_877 _151_876 _151_875))))
end else begin
()
end
in (
# 1655 "FStar.TypeChecker.Tc.fst"
let check_and_gen' = (fun env _70_2271 k -> (match (_70_2271) with
| (_70_2269, t) -> begin
(check_and_gen env t k)
end))
in (
# 1658 "FStar.TypeChecker.Tc.fst"
let ret = (
# 1659 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_889 = (let _151_887 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_886 = (let _151_885 = (let _151_884 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _151_884))
in (_151_885)::[])
in (_151_887)::_151_886))
in (let _151_888 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _151_889 _151_888)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (
# 1662 "FStar.TypeChecker.Tc.fst"
let bind_wp = (
# 1663 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1664 "FStar.TypeChecker.Tc.fst"
let _70_2278 = (get_effect_signature ())
in (match (_70_2278) with
| (b, wp_b) -> begin
(
# 1665 "FStar.TypeChecker.Tc.fst"
let a_wp_b = (let _151_893 = (let _151_891 = (let _151_890 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _151_890))
in (_151_891)::[])
in (let _151_892 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _151_893 _151_892)))
in (
# 1666 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = a_wp_b
in (
# 1667 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_906 = (let _151_904 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_903 = (let _151_902 = (FStar_Syntax_Syntax.mk_binder b)
in (let _151_901 = (let _151_900 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _151_899 = (let _151_898 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _151_897 = (let _151_896 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (let _151_895 = (let _151_894 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_151_894)::[])
in (_151_896)::_151_895))
in (_151_898)::_151_897))
in (_151_900)::_151_899))
in (_151_902)::_151_901))
in (_151_904)::_151_903))
in (let _151_905 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _151_906 _151_905)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k))))
end)))
in (
# 1673 "FStar.TypeChecker.Tc.fst"
let bind_wlp = (
# 1674 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1675 "FStar.TypeChecker.Tc.fst"
let _70_2286 = (get_effect_signature ())
in (match (_70_2286) with
| (b, wlp_b) -> begin
(
# 1676 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = (let _151_910 = (let _151_908 = (let _151_907 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _151_907))
in (_151_908)::[])
in (let _151_909 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _151_910 _151_909)))
in (
# 1677 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_919 = (let _151_917 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_916 = (let _151_915 = (FStar_Syntax_Syntax.mk_binder b)
in (let _151_914 = (let _151_913 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _151_912 = (let _151_911 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_151_911)::[])
in (_151_913)::_151_912))
in (_151_915)::_151_914))
in (_151_917)::_151_916))
in (let _151_918 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _151_919 _151_918)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wlp expected_k)))
end)))
in (
# 1683 "FStar.TypeChecker.Tc.fst"
let if_then_else = (
# 1684 "FStar.TypeChecker.Tc.fst"
let p = (let _151_921 = (let _151_920 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_920 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _151_921))
in (
# 1685 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_930 = (let _151_928 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_927 = (let _151_926 = (FStar_Syntax_Syntax.mk_binder p)
in (let _151_925 = (let _151_924 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _151_923 = (let _151_922 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_922)::[])
in (_151_924)::_151_923))
in (_151_926)::_151_925))
in (_151_928)::_151_927))
in (let _151_929 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_930 _151_929)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (
# 1691 "FStar.TypeChecker.Tc.fst"
let ite_wp = (
# 1692 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1693 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_937 = (let _151_935 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_934 = (let _151_933 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _151_932 = (let _151_931 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_931)::[])
in (_151_933)::_151_932))
in (_151_935)::_151_934))
in (let _151_936 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_937 _151_936)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k)))
in (
# 1699 "FStar.TypeChecker.Tc.fst"
let ite_wlp = (
# 1700 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1701 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_942 = (let _151_940 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_939 = (let _151_938 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (_151_938)::[])
in (_151_940)::_151_939))
in (let _151_941 = (FStar_Syntax_Syntax.mk_Total wlp_a)
in (FStar_Syntax_Util.arrow _151_942 _151_941)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wlp expected_k)))
in (
# 1706 "FStar.TypeChecker.Tc.fst"
let wp_binop = (
# 1707 "FStar.TypeChecker.Tc.fst"
let bin_op = (
# 1708 "FStar.TypeChecker.Tc.fst"
let _70_2301 = (FStar_Syntax_Util.type_u ())
in (match (_70_2301) with
| (t1, u1) -> begin
(
# 1709 "FStar.TypeChecker.Tc.fst"
let _70_2304 = (FStar_Syntax_Util.type_u ())
in (match (_70_2304) with
| (t2, u2) -> begin
(
# 1710 "FStar.TypeChecker.Tc.fst"
let t = (let _151_943 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_max ((u1)::(u2)::[]))) None _151_943))
in (let _151_948 = (let _151_946 = (FStar_Syntax_Syntax.null_binder t1)
in (let _151_945 = (let _151_944 = (FStar_Syntax_Syntax.null_binder t2)
in (_151_944)::[])
in (_151_946)::_151_945))
in (let _151_947 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _151_948 _151_947))))
end))
end))
in (
# 1712 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_957 = (let _151_955 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_954 = (let _151_953 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _151_952 = (let _151_951 = (FStar_Syntax_Syntax.null_binder bin_op)
in (let _151_950 = (let _151_949 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_949)::[])
in (_151_951)::_151_950))
in (_151_953)::_151_952))
in (_151_955)::_151_954))
in (let _151_956 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_957 _151_956)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_binop expected_k)))
in (
# 1719 "FStar.TypeChecker.Tc.fst"
let wp_as_type = (
# 1720 "FStar.TypeChecker.Tc.fst"
let _70_2312 = (FStar_Syntax_Util.type_u ())
in (match (_70_2312) with
| (t, _70_2311) -> begin
(
# 1721 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_962 = (let _151_960 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_959 = (let _151_958 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_958)::[])
in (_151_960)::_151_959))
in (let _151_961 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _151_962 _151_961)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (
# 1726 "FStar.TypeChecker.Tc.fst"
let close_wp = (
# 1727 "FStar.TypeChecker.Tc.fst"
let b = (let _151_964 = (let _151_963 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_963 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _151_964))
in (
# 1728 "FStar.TypeChecker.Tc.fst"
let b_wp_a = (let _151_968 = (let _151_966 = (let _151_965 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _151_965))
in (_151_966)::[])
in (let _151_967 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_968 _151_967)))
in (
# 1729 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_975 = (let _151_973 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_972 = (let _151_971 = (FStar_Syntax_Syntax.mk_binder b)
in (let _151_970 = (let _151_969 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_151_969)::[])
in (_151_971)::_151_970))
in (_151_973)::_151_972))
in (let _151_974 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_975 _151_974)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (
# 1733 "FStar.TypeChecker.Tc.fst"
let assert_p = (
# 1734 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_984 = (let _151_982 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_981 = (let _151_980 = (let _151_977 = (let _151_976 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_976 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _151_977))
in (let _151_979 = (let _151_978 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_978)::[])
in (_151_980)::_151_979))
in (_151_982)::_151_981))
in (let _151_983 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_984 _151_983)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (
# 1740 "FStar.TypeChecker.Tc.fst"
let assume_p = (
# 1741 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_993 = (let _151_991 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_990 = (let _151_989 = (let _151_986 = (let _151_985 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_985 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _151_986))
in (let _151_988 = (let _151_987 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_987)::[])
in (_151_989)::_151_988))
in (_151_991)::_151_990))
in (let _151_992 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_993 _151_992)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (
# 1747 "FStar.TypeChecker.Tc.fst"
let null_wp = (
# 1748 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_996 = (let _151_994 = (FStar_Syntax_Syntax.mk_binder a)
in (_151_994)::[])
in (let _151_995 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_996 _151_995)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (
# 1752 "FStar.TypeChecker.Tc.fst"
let trivial_wp = (
# 1753 "FStar.TypeChecker.Tc.fst"
let _70_2328 = (FStar_Syntax_Util.type_u ())
in (match (_70_2328) with
| (t, _70_2327) -> begin
(
# 1754 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1001 = (let _151_999 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_998 = (let _151_997 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_997)::[])
in (_151_999)::_151_998))
in (let _151_1000 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _151_1001 _151_1000)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (
# 1760 "FStar.TypeChecker.Tc.fst"
let t = (let _151_1002 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _151_1002))
in (
# 1761 "FStar.TypeChecker.Tc.fst"
let _70_2334 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_70_2334) with
| (univs, t) -> begin
(
# 1762 "FStar.TypeChecker.Tc.fst"
let _70_2350 = (match ((let _151_1004 = (let _151_1003 = (FStar_Syntax_Subst.compress t)
in _151_1003.FStar_Syntax_Syntax.n)
in (binders, _151_1004))) with
| ([], _70_2337) -> begin
([], t)
end
| (_70_2340, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _70_2347 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_70_2350) with
| (binders, signature) -> begin
(
# 1766 "FStar.TypeChecker.Tc.fst"
let close = (fun ts -> (let _151_1007 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _151_1007)))
in (
# 1767 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1767 "FStar.TypeChecker.Tc.fst"
let _70_2353 = ed
in (let _151_1020 = (close ret)
in (let _151_1019 = (close bind_wp)
in (let _151_1018 = (close bind_wlp)
in (let _151_1017 = (close if_then_else)
in (let _151_1016 = (close ite_wp)
in (let _151_1015 = (close ite_wlp)
in (let _151_1014 = (close wp_binop)
in (let _151_1013 = (close wp_as_type)
in (let _151_1012 = (close close_wp)
in (let _151_1011 = (close assert_p)
in (let _151_1010 = (close assume_p)
in (let _151_1009 = (close null_wp)
in (let _151_1008 = (close trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _70_2353.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _70_2353.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _151_1020; FStar_Syntax_Syntax.bind_wp = _151_1019; FStar_Syntax_Syntax.bind_wlp = _151_1018; FStar_Syntax_Syntax.if_then_else = _151_1017; FStar_Syntax_Syntax.ite_wp = _151_1016; FStar_Syntax_Syntax.ite_wlp = _151_1015; FStar_Syntax_Syntax.wp_binop = _151_1014; FStar_Syntax_Syntax.wp_as_type = _151_1013; FStar_Syntax_Syntax.close_wp = _151_1012; FStar_Syntax_Syntax.assert_p = _151_1011; FStar_Syntax_Syntax.assume_p = _151_1010; FStar_Syntax_Syntax.null_wp = _151_1009; FStar_Syntax_Syntax.trivial = _151_1008}))))))))))))))
in (
# 1785 "FStar.TypeChecker.Tc.fst"
let _70_2356 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1021 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _151_1021))
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

# 1789 "FStar.TypeChecker.Tc.fst"
let tc_lex_t = (fun env ses quals lids -> (
# 1796 "FStar.TypeChecker.Tc.fst"
let _70_2362 = ()
in (
# 1797 "FStar.TypeChecker.Tc.fst"
let _70_2370 = ()
in (match (ses) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _70_2399, _70_2401, [], r)::FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _70_2390, r1)::FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _70_2379, r2)::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(
# 1812 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (
# 1813 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (
# 1814 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (
# 1815 "FStar.TypeChecker.Tc.fst"
let tc = FStar_Syntax_Syntax.Sig_inductive_typ ((lex_t, (u)::[], [], t, [], (FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[], [], r))
in (
# 1817 "FStar.TypeChecker.Tc.fst"
let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (
# 1818 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (let _151_1029 = (let _151_1028 = (let _151_1027 = (let _151_1026 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _151_1026 FStar_Syntax_Syntax.Delta_constant None))
in (_151_1027, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_151_1028))
in (FStar_Syntax_Syntax.mk _151_1029 None r1))
in (
# 1819 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (
# 1820 "FStar.TypeChecker.Tc.fst"
let dc_lextop = FStar_Syntax_Syntax.Sig_datacon ((lex_top, (utop)::[], lex_top_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r1))
in (
# 1822 "FStar.TypeChecker.Tc.fst"
let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1823 "FStar.TypeChecker.Tc.fst"
let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1824 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (
# 1825 "FStar.TypeChecker.Tc.fst"
let a = (let _151_1030 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _151_1030))
in (
# 1826 "FStar.TypeChecker.Tc.fst"
let hd = (let _151_1031 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _151_1031))
in (
# 1827 "FStar.TypeChecker.Tc.fst"
let tl = (let _151_1036 = (let _151_1035 = (let _151_1034 = (let _151_1033 = (let _151_1032 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _151_1032 FStar_Syntax_Syntax.Delta_constant None))
in (_151_1033, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_151_1034))
in (FStar_Syntax_Syntax.mk _151_1035 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _151_1036))
in (
# 1828 "FStar.TypeChecker.Tc.fst"
let res = (let _151_1040 = (let _151_1039 = (let _151_1038 = (let _151_1037 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _151_1037 FStar_Syntax_Syntax.Delta_constant None))
in (_151_1038, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_151_1039))
in (FStar_Syntax_Syntax.mk _151_1040 None r2))
in (let _151_1041 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _151_1041))))))
in (
# 1830 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (
# 1831 "FStar.TypeChecker.Tc.fst"
let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _151_1043 = (let _151_1042 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _151_1042))
in FStar_Syntax_Syntax.Sig_bundle (_151_1043)))))))))))))))
end
| _70_2425 -> begin
(let _151_1045 = (let _151_1044 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _151_1044))
in (FStar_All.failwith _151_1045))
end))))

# 1837 "FStar.TypeChecker.Tc.fst"
let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (
# 1900 "FStar.TypeChecker.Tc.fst"
let warn_positivity = (fun l r -> (let _151_1059 = (let _151_1058 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _151_1058))
in (FStar_TypeChecker_Errors.warn r _151_1059)))
in (
# 1902 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1905 "FStar.TypeChecker.Tc.fst"
let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(
# 1910 "FStar.TypeChecker.Tc.fst"
let _70_2447 = ()
in (
# 1911 "FStar.TypeChecker.Tc.fst"
let _70_2449 = (warn_positivity tc r)
in (
# 1912 "FStar.TypeChecker.Tc.fst"
let _70_2453 = (FStar_Syntax_Subst.open_term tps k)
in (match (_70_2453) with
| (tps, k) -> begin
(
# 1913 "FStar.TypeChecker.Tc.fst"
let _70_2457 = (tc_tparams env tps)
in (match (_70_2457) with
| (tps, env_tps, us) -> begin
(
# 1914 "FStar.TypeChecker.Tc.fst"
let _70_2460 = (FStar_Syntax_Util.arrow_formals k)
in (match (_70_2460) with
| (indices, t) -> begin
(
# 1915 "FStar.TypeChecker.Tc.fst"
let _70_2464 = (tc_tparams env_tps indices)
in (match (_70_2464) with
| (indices, env', us') -> begin
(
# 1916 "FStar.TypeChecker.Tc.fst"
let _70_2468 = (tc_trivial_guard env' t)
in (match (_70_2468) with
| (t, _70_2467) -> begin
(
# 1917 "FStar.TypeChecker.Tc.fst"
let k = (let _151_1064 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _151_1064))
in (
# 1918 "FStar.TypeChecker.Tc.fst"
let _70_2472 = (FStar_Syntax_Util.type_u ())
in (match (_70_2472) with
| (t_type, u) -> begin
(
# 1919 "FStar.TypeChecker.Tc.fst"
let _70_2473 = (let _151_1065 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _151_1065))
in (
# 1921 "FStar.TypeChecker.Tc.fst"
let t_tc = (let _151_1066 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _151_1066))
in (
# 1922 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 1923 "FStar.TypeChecker.Tc.fst"
let k = (FStar_Syntax_Subst.close tps k)
in (
# 1924 "FStar.TypeChecker.Tc.fst"
let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _151_1067 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) ([], t_tc))
in (_151_1067, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u)))))))
end)))
end))
end))
end))
end))
end))))
end
| _70_2480 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1931 "FStar.TypeChecker.Tc.fst"
let positive_if_pure = (fun _70_2482 l -> ())
in (
# 1934 "FStar.TypeChecker.Tc.fst"
let tc_data = (fun env tcs _70_6 -> (match (_70_6) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(
# 1936 "FStar.TypeChecker.Tc.fst"
let _70_2499 = ()
in (
# 1938 "FStar.TypeChecker.Tc.fst"
let _70_2534 = (
# 1939 "FStar.TypeChecker.Tc.fst"
let tps_u_opt = (FStar_Util.find_map tcs (fun _70_2503 -> (match (_70_2503) with
| (se, u_tc) -> begin
if (let _151_1080 = (let _151_1079 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _151_1079))
in (FStar_Ident.lid_equals tc_lid _151_1080)) then begin
(
# 1941 "FStar.TypeChecker.Tc.fst"
let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_70_2505, _70_2507, tps, _70_2510, _70_2512, _70_2514, _70_2516, _70_2518) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _70_2524 -> (match (_70_2524) with
| (x, _70_2523) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _70_2526 -> begin
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
in (match (_70_2534) with
| (tps, u_tc) -> begin
(
# 1954 "FStar.TypeChecker.Tc.fst"
let _70_2554 = (match ((let _151_1082 = (FStar_Syntax_Subst.compress t)
in _151_1082.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(
# 1959 "FStar.TypeChecker.Tc.fst"
let _70_2542 = (FStar_Util.first_N ntps bs)
in (match (_70_2542) with
| (_70_2540, bs') -> begin
(
# 1960 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (
# 1961 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _70_2548 -> (match (_70_2548) with
| (x, _70_2547) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _151_1085 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _151_1085))))
end))
end
| _70_2551 -> begin
([], t)
end)
in (match (_70_2554) with
| (arguments, result) -> begin
(
# 1965 "FStar.TypeChecker.Tc.fst"
let _70_2555 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1088 = (FStar_Syntax_Print.lid_to_string c)
in (let _151_1087 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _151_1086 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _151_1088 _151_1087 _151_1086))))
end else begin
()
end
in (
# 1971 "FStar.TypeChecker.Tc.fst"
let _70_2560 = (tc_tparams env arguments)
in (match (_70_2560) with
| (arguments, env', us) -> begin
(
# 1972 "FStar.TypeChecker.Tc.fst"
let _70_2564 = (tc_trivial_guard env' result)
in (match (_70_2564) with
| (result, _70_2563) -> begin
(
# 1973 "FStar.TypeChecker.Tc.fst"
let _70_2568 = (FStar_Syntax_Util.head_and_args result)
in (match (_70_2568) with
| (head, _70_2567) -> begin
(
# 1974 "FStar.TypeChecker.Tc.fst"
let _70_2573 = (match ((let _151_1089 = (FStar_Syntax_Subst.compress head)
in _151_1089.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _70_2572 -> begin
(let _151_1093 = (let _151_1092 = (let _151_1091 = (let _151_1090 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _151_1090))
in (_151_1091, r))
in FStar_Syntax_Syntax.Error (_151_1092))
in (Prims.raise _151_1093))
end)
in (
# 1977 "FStar.TypeChecker.Tc.fst"
let g = (FStar_List.fold_left2 (fun g _70_2579 u_x -> (match (_70_2579) with
| (x, _70_2578) -> begin
(
# 1978 "FStar.TypeChecker.Tc.fst"
let _70_2581 = ()
in (let _151_1097 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _151_1097)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (
# 1984 "FStar.TypeChecker.Tc.fst"
let t = (let _151_1101 = (let _151_1099 = (FStar_All.pipe_right tps (FStar_List.map (fun _70_2587 -> (match (_70_2587) with
| (x, _70_2586) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _151_1099 arguments))
in (let _151_1100 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _151_1101 _151_1100)))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _70_2590 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1992 "FStar.TypeChecker.Tc.fst"
let generalize_and_inst_within = (fun env g tcs datas -> (
# 1993 "FStar.TypeChecker.Tc.fst"
let _70_2596 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 1994 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _70_7 -> (match (_70_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_70_2600, _70_2602, tps, k, _70_2606, _70_2608, _70_2610, _70_2612) -> begin
(let _151_1112 = (let _151_1111 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _151_1111))
in (FStar_Syntax_Syntax.null_binder _151_1112))
end
| _70_2616 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 1997 "FStar.TypeChecker.Tc.fst"
let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _70_8 -> (match (_70_8) with
| FStar_Syntax_Syntax.Sig_datacon (_70_2620, _70_2622, t, _70_2625, _70_2627, _70_2629, _70_2631, _70_2633) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _70_2637 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2000 "FStar.TypeChecker.Tc.fst"
let t = (let _151_1114 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _151_1114))
in (
# 2001 "FStar.TypeChecker.Tc.fst"
let _70_2640 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1115 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _151_1115))
end else begin
()
end
in (
# 2002 "FStar.TypeChecker.Tc.fst"
let _70_2644 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_70_2644) with
| (uvs, t) -> begin
(
# 2003 "FStar.TypeChecker.Tc.fst"
let _70_2646 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1119 = (let _151_1117 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _151_1117 (FStar_String.concat ", ")))
in (let _151_1118 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _151_1119 _151_1118)))
end else begin
()
end
in (
# 2006 "FStar.TypeChecker.Tc.fst"
let _70_2650 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_70_2650) with
| (uvs, t) -> begin
(
# 2007 "FStar.TypeChecker.Tc.fst"
let _70_2654 = (FStar_Syntax_Util.arrow_formals t)
in (match (_70_2654) with
| (args, _70_2653) -> begin
(
# 2008 "FStar.TypeChecker.Tc.fst"
let _70_2657 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_70_2657) with
| (tc_types, data_types) -> begin
(
# 2009 "FStar.TypeChecker.Tc.fst"
let tcs = (FStar_List.map2 (fun _70_2661 se -> (match (_70_2661) with
| (x, _70_2660) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _70_2665, tps, _70_2668, mutuals, datas, quals, r) -> begin
(
# 2011 "FStar.TypeChecker.Tc.fst"
let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (
# 2012 "FStar.TypeChecker.Tc.fst"
let _70_2691 = (match ((let _151_1122 = (FStar_Syntax_Subst.compress ty)
in _151_1122.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 2014 "FStar.TypeChecker.Tc.fst"
let _70_2682 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_70_2682) with
| (tps, rest) -> begin
(
# 2015 "FStar.TypeChecker.Tc.fst"
let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _70_2685 -> begin
(let _151_1123 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _151_1123 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _70_2688 -> begin
([], ty)
end)
in (match (_70_2691) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _70_2693 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (
# 2025 "FStar.TypeChecker.Tc.fst"
let datas = (match (uvs) with
| [] -> begin
datas
end
| _70_2697 -> begin
(
# 2028 "FStar.TypeChecker.Tc.fst"
let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _151_1124 -> FStar_Syntax_Syntax.U_name (_151_1124))))
in (
# 2029 "FStar.TypeChecker.Tc.fst"
let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _70_9 -> (match (_70_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _70_2702, _70_2704, _70_2706, _70_2708, _70_2710, _70_2712, _70_2714) -> begin
(tc, uvs_universes)
end
| _70_2718 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _70_2723 d -> (match (_70_2723) with
| (t, _70_2722) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _70_2727, _70_2729, tc, ntps, quals, mutuals, r) -> begin
(
# 2033 "FStar.TypeChecker.Tc.fst"
let ty = (let _151_1128 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _151_1128 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _70_2739 -> begin
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
# 2039 "FStar.TypeChecker.Tc.fst"
let _70_2749 = (FStar_All.pipe_right ses (FStar_List.partition (fun _70_10 -> (match (_70_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_70_2743) -> begin
true
end
| _70_2746 -> begin
false
end))))
in (match (_70_2749) with
| (tys, datas) -> begin
(
# 2041 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2044 "FStar.TypeChecker.Tc.fst"
let _70_2766 = (FStar_List.fold_right (fun tc _70_2755 -> (match (_70_2755) with
| (env, all_tcs, g) -> begin
(
# 2045 "FStar.TypeChecker.Tc.fst"
let _70_2759 = (tc_tycon env tc)
in (match (_70_2759) with
| (env, tc, tc_u) -> begin
(
# 2046 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (
# 2047 "FStar.TypeChecker.Tc.fst"
let _70_2761 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1132 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _151_1132))
end else begin
()
end
in (let _151_1133 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _151_1133))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_70_2766) with
| (env, tcs, g) -> begin
(
# 2054 "FStar.TypeChecker.Tc.fst"
let _70_2776 = (FStar_List.fold_right (fun se _70_2770 -> (match (_70_2770) with
| (datas, g) -> begin
(
# 2055 "FStar.TypeChecker.Tc.fst"
let _70_2773 = (tc_data env tcs se)
in (match (_70_2773) with
| (data, g') -> begin
(let _151_1136 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _151_1136))
end))
end)) datas ([], g))
in (match (_70_2776) with
| (datas, g) -> begin
(
# 2060 "FStar.TypeChecker.Tc.fst"
let _70_2779 = (let _151_1137 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _151_1137 datas))
in (match (_70_2779) with
| (tcs, datas) -> begin
(let _151_1139 = (let _151_1138 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _151_1138))
in FStar_Syntax_Syntax.Sig_bundle (_151_1139))
end))
end))
end)))
end)))))))))

# 2063 "FStar.TypeChecker.Tc.fst"
let rec tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.env) = (fun env se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(
# 2076 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2077 "FStar.TypeChecker.Tc.fst"
let se = (tc_lex_t env ses quals lids)
in (let _151_1144 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _151_1144))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(
# 2081 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2082 "FStar.TypeChecker.Tc.fst"
let se = (tc_inductive env ses quals lids)
in (let _151_1145 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _151_1145))))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(match (p) with
| FStar_Syntax_Syntax.SetOptions (o) -> begin
(match ((FStar_Options.set_options o)) with
| FStar_Getopt.GoOn -> begin
(se, env)
end
| FStar_Getopt.Help -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Failed to process pragma: use \'fstar --help\' to see which options are available", r))))
end
| FStar_Getopt.Die (s) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Failed to process pragma: " s), r))))
end)
end
| FStar_Syntax_Syntax.ResetOptions -> begin
(
# 2094 "FStar.TypeChecker.Tc.fst"
let _70_2815 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (
# 2095 "FStar.TypeChecker.Tc.fst"
let _70_2817 = (let _151_1146 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _151_1146 Prims.ignore))
in (se, env)))
end)
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(
# 2100 "FStar.TypeChecker.Tc.fst"
let ne = (tc_eff_decl env ne)
in (
# 2101 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (
# 2102 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(
# 2106 "FStar.TypeChecker.Tc.fst"
let _70_2832 = (let _151_1147 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _151_1147))
in (match (_70_2832) with
| (a, wp_a_src) -> begin
(
# 2107 "FStar.TypeChecker.Tc.fst"
let _70_2835 = (let _151_1148 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _151_1148))
in (match (_70_2835) with
| (b, wp_b_tgt) -> begin
(
# 2108 "FStar.TypeChecker.Tc.fst"
let wp_a_tgt = (let _151_1152 = (let _151_1151 = (let _151_1150 = (let _151_1149 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _151_1149))
in FStar_Syntax_Syntax.NT (_151_1150))
in (_151_1151)::[])
in (FStar_Syntax_Subst.subst _151_1152 wp_b_tgt))
in (
# 2109 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1157 = (let _151_1155 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1154 = (let _151_1153 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_151_1153)::[])
in (_151_1155)::_151_1154))
in (let _151_1156 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _151_1157 _151_1156)))
in (
# 2110 "FStar.TypeChecker.Tc.fst"
let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (
# 2111 "FStar.TypeChecker.Tc.fst"
let sub = (
# 2111 "FStar.TypeChecker.Tc.fst"
let _70_2839 = sub
in {FStar_Syntax_Syntax.source = _70_2839.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _70_2839.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
in (
# 2112 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect ((sub, r))
in (
# 2113 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(
# 2117 "FStar.TypeChecker.Tc.fst"
let _70_2852 = ()
in (
# 2118 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2119 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2120 "FStar.TypeChecker.Tc.fst"
let _70_2858 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_70_2858) with
| (tps, c) -> begin
(
# 2121 "FStar.TypeChecker.Tc.fst"
let _70_2862 = (tc_tparams env tps)
in (match (_70_2862) with
| (tps, env, us) -> begin
(
# 2122 "FStar.TypeChecker.Tc.fst"
let _70_2866 = (tc_comp env c)
in (match (_70_2866) with
| (c, u, g) -> begin
(
# 2123 "FStar.TypeChecker.Tc.fst"
let _70_2867 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2124 "FStar.TypeChecker.Tc.fst"
let tags = (FStar_All.pipe_right tags (FStar_List.map (fun _70_11 -> (match (_70_11) with
| FStar_Syntax_Syntax.DefaultEffect (None) -> begin
(
# 2126 "FStar.TypeChecker.Tc.fst"
let c' = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let _151_1160 = (FStar_All.pipe_right c'.FStar_Syntax_Syntax.effect_name (fun _151_1159 -> Some (_151_1159)))
in FStar_Syntax_Syntax.DefaultEffect (_151_1160)))
end
| t -> begin
t
end))))
in (
# 2129 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 2130 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.close_comp tps c)
in (
# 2131 "FStar.TypeChecker.Tc.fst"
let _70_2879 = (let _151_1161 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _151_1161))
in (match (_70_2879) with
| (uvs, t) -> begin
(
# 2132 "FStar.TypeChecker.Tc.fst"
let _70_2898 = (match ((let _151_1163 = (let _151_1162 = (FStar_Syntax_Subst.compress t)
in _151_1162.FStar_Syntax_Syntax.n)
in (tps, _151_1163))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_70_2882, c)) -> begin
([], c)
end
| (_70_2888, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _70_2895 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_70_2898) with
| (tps, c) -> begin
(
# 2136 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_effect_abbrev ((lid, uvs, tps, c, tags, r))
in (
# 2137 "FStar.TypeChecker.Tc.fst"
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
# 2141 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2142 "FStar.TypeChecker.Tc.fst"
let _70_2909 = ()
in (
# 2143 "FStar.TypeChecker.Tc.fst"
let k = (let _151_1164 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _151_1164))
in (
# 2144 "FStar.TypeChecker.Tc.fst"
let _70_2914 = (check_and_gen env t k)
in (match (_70_2914) with
| (uvs, t) -> begin
(
# 2145 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (
# 2146 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(
# 2150 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2151 "FStar.TypeChecker.Tc.fst"
let _70_2927 = (FStar_Syntax_Util.type_u ())
in (match (_70_2927) with
| (k, _70_2926) -> begin
(
# 2152 "FStar.TypeChecker.Tc.fst"
let phi = (let _151_1165 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _151_1165 (norm env)))
in (
# 2153 "FStar.TypeChecker.Tc.fst"
let _70_2929 = (FStar_TypeChecker_Util.check_uvars r phi)
in (
# 2154 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))
in (
# 2155 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(
# 2159 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2160 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (
# 2161 "FStar.TypeChecker.Tc.fst"
let _70_2942 = (tc_term env e)
in (match (_70_2942) with
| (e, c, g1) -> begin
(
# 2162 "FStar.TypeChecker.Tc.fst"
let _70_2947 = (let _151_1169 = (let _151_1166 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_151_1166))
in (let _151_1168 = (let _151_1167 = (c.FStar_Syntax_Syntax.comp ())
in (e, _151_1167))
in (check_expected_effect env _151_1169 _151_1168)))
in (match (_70_2947) with
| (e, _70_2945, g) -> begin
(
# 2163 "FStar.TypeChecker.Tc.fst"
let _70_2948 = (let _151_1170 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _151_1170))
in (
# 2164 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, r))
in (
# 2165 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(
# 2169 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2170 "FStar.TypeChecker.Tc.fst"
let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
if (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q')) then begin
Some (q)
end else begin
(let _151_1180 = (let _151_1179 = (let _151_1178 = (let _151_1177 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Inconsistent qualifier annotations on %s" _151_1177))
in (_151_1178, r))
in FStar_Syntax_Syntax.Error (_151_1179))
in (Prims.raise _151_1180))
end
end))
in (
# 2181 "FStar.TypeChecker.Tc.fst"
let _70_2992 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _70_2969 lb -> (match (_70_2969) with
| (gen, lbs, quals_opt) -> begin
(
# 2182 "FStar.TypeChecker.Tc.fst"
let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2183 "FStar.TypeChecker.Tc.fst"
let _70_2988 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(
# 2187 "FStar.TypeChecker.Tc.fst"
let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (
# 2188 "FStar.TypeChecker.Tc.fst"
let _70_2983 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _70_2982 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _151_1183 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _151_1183, quals_opt))))
end)
in (match (_70_2988) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_70_2992) with
| (should_generalize, lbs', quals_opt) -> begin
(
# 2197 "FStar.TypeChecker.Tc.fst"
let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _70_12 -> (match (_70_12) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _70_3001 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (
# 2204 "FStar.TypeChecker.Tc.fst"
let lbs' = (FStar_List.rev lbs')
in (
# 2207 "FStar.TypeChecker.Tc.fst"
let e = (let _151_1187 = (let _151_1186 = (let _151_1185 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _151_1185))
in FStar_Syntax_Syntax.Tm_let (_151_1186))
in (FStar_Syntax_Syntax.mk _151_1187 None r))
in (
# 2210 "FStar.TypeChecker.Tc.fst"
let _70_3035 = (match ((tc_maybe_toplevel_term (
# 2210 "FStar.TypeChecker.Tc.fst"
let _70_3005 = env
in {FStar_TypeChecker_Env.solver = _70_3005.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_3005.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_3005.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_3005.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_3005.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_3005.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_3005.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_3005.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_3005.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_3005.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_3005.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _70_3005.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _70_3005.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_3005.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_3005.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_3005.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_3005.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_3005.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_3005.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_3005.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _70_3012; FStar_Syntax_Syntax.pos = _70_3010; FStar_Syntax_Syntax.vars = _70_3008}, _70_3019, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(
# 2213 "FStar.TypeChecker.Tc.fst"
let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_70_3023, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _70_3029 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _70_3032 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_70_3035) with
| (se, lbs) -> begin
(
# 2220 "FStar.TypeChecker.Tc.fst"
let _70_3041 = if (log env) then begin
(let _151_1195 = (let _151_1194 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 2222 "FStar.TypeChecker.Tc.fst"
let should_log = (match ((let _151_1191 = (let _151_1190 = (let _151_1189 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _151_1189.FStar_Syntax_Syntax.fv_name)
in _151_1190.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _151_1191))) with
| None -> begin
true
end
| _70_3039 -> begin
false
end)
in if should_log then begin
(let _151_1193 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _151_1192 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _151_1193 _151_1192)))
end else begin
""
end))))
in (FStar_All.pipe_right _151_1194 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _151_1195))
end else begin
()
end
in (
# 2229 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end))))
end))

# 2233 "FStar.TypeChecker.Tc.fst"
let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (
# 2257 "FStar.TypeChecker.Tc.fst"
let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _70_13 -> (match (_70_13) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _70_3051 -> begin
false
end)))))
in (
# 2258 "FStar.TypeChecker.Tc.fst"
let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _70_3061 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_70_3063) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _70_3074, _70_3076) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _70_3082 -> (match (_70_3082) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _70_3088, _70_3090, quals, r) -> begin
(
# 2272 "FStar.TypeChecker.Tc.fst"
let dec = (let _151_1211 = (let _151_1210 = (let _151_1209 = (let _151_1208 = (let _151_1207 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _151_1207))
in FStar_Syntax_Syntax.Tm_arrow (_151_1208))
in (FStar_Syntax_Syntax.mk _151_1209 None r))
in (l, us, _151_1210, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_151_1211))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _70_3100, _70_3102, _70_3104, _70_3106, r) -> begin
(
# 2275 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _70_3112 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_70_3114, _70_3116, quals, _70_3119) -> begin
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
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _70_14 -> (match (_70_14) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _70_3138 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_70_3140) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _70_3156, _70_3158, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(
# 2305 "FStar.TypeChecker.Tc.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2306 "FStar.TypeChecker.Tc.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))) then begin
([], hidden)
end else begin
(
# 2309 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::[], (FStar_Ident.range_of_lid lid)))
in ((dec)::[], (lid)::hidden))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (is_abstract quals) then begin
(let _151_1218 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _151_1217 = (let _151_1216 = (let _151_1215 = (let _151_1214 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _151_1214.FStar_Syntax_Syntax.fv_name)
in _151_1215.FStar_Syntax_Syntax.v)
in (_151_1216, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_151_1217)))))
in (_151_1218, hidden))
end else begin
((se)::[], hidden)
end
end))))

# 2318 "FStar.TypeChecker.Tc.fst"
let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (
# 2319 "FStar.TypeChecker.Tc.fst"
let _70_3197 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _70_3178 se -> (match (_70_3178) with
| (ses, exports, env, hidden) -> begin
(
# 2321 "FStar.TypeChecker.Tc.fst"
let _70_3180 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1225 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _151_1225))
end else begin
()
end
in (
# 2324 "FStar.TypeChecker.Tc.fst"
let _70_3184 = (tc_decl env se)
in (match (_70_3184) with
| (se, env) -> begin
(
# 2326 "FStar.TypeChecker.Tc.fst"
let _70_3185 = if ((FStar_ST.read FStar_Options.log_types) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _151_1226 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _151_1226))
end else begin
()
end
in (
# 2329 "FStar.TypeChecker.Tc.fst"
let _70_3187 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (
# 2331 "FStar.TypeChecker.Tc.fst"
let _70_3191 = (for_export hidden se)
in (match (_70_3191) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_70_3197) with
| (ses, exports, env, _70_3196) -> begin
(let _151_1227 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _151_1227, env))
end)))

# 2336 "FStar.TypeChecker.Tc.fst"
let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2337 "FStar.TypeChecker.Tc.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 2338 "FStar.TypeChecker.Tc.fst"
let msg = (Prims.strcat "Internals for " name)
in (
# 2339 "FStar.TypeChecker.Tc.fst"
let env = (
# 2339 "FStar.TypeChecker.Tc.fst"
let _70_3202 = env
in (let _151_1232 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _70_3202.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_3202.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_3202.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_3202.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_3202.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_3202.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_3202.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_3202.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_3202.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_3202.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_3202.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_3202.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_3202.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _70_3202.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _70_3202.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_3202.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _151_1232; FStar_TypeChecker_Env.default_effects = _70_3202.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_3202.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_3202.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_3202.FStar_TypeChecker_Env.use_bv_sorts}))
in (
# 2340 "FStar.TypeChecker.Tc.fst"
let _70_3205 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (
# 2341 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (
# 2342 "FStar.TypeChecker.Tc.fst"
let _70_3211 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_70_3211) with
| (ses, exports, env) -> begin
((
# 2343 "FStar.TypeChecker.Tc.fst"
let _70_3212 = modul
in {FStar_Syntax_Syntax.name = _70_3212.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _70_3212.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _70_3212.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))

# 2345 "FStar.TypeChecker.Tc.fst"
let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (
# 2346 "FStar.TypeChecker.Tc.fst"
let _70_3220 = (tc_decls env decls)
in (match (_70_3220) with
| (ses, exports, env) -> begin
(
# 2347 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2347 "FStar.TypeChecker.Tc.fst"
let _70_3221 = modul
in {FStar_Syntax_Syntax.name = _70_3221.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _70_3221.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _70_3221.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))

# 2350 "FStar.TypeChecker.Tc.fst"
let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (
# 2351 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2351 "FStar.TypeChecker.Tc.fst"
let _70_3227 = modul
in {FStar_Syntax_Syntax.name = _70_3227.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _70_3227.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (
# 2352 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.finish_module env modul)
in (
# 2353 "FStar.TypeChecker.Tc.fst"
let _70_3237 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(
# 2355 "FStar.TypeChecker.Tc.fst"
let _70_3231 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (
# 2356 "FStar.TypeChecker.Tc.fst"
let _70_3233 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (
# 2357 "FStar.TypeChecker.Tc.fst"
let _70_3235 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _151_1245 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _151_1245 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))

# 2362 "FStar.TypeChecker.Tc.fst"
let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2363 "FStar.TypeChecker.Tc.fst"
let _70_3244 = (tc_partial_modul env modul)
in (match (_70_3244) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

# 2366 "FStar.TypeChecker.Tc.fst"
let add_modul_to_tcenv : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_TypeChecker_Env.env = (fun en m -> (
# 2367 "FStar.TypeChecker.Tc.fst"
let do_sigelt = (fun en elt -> (
# 2368 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt en elt)
in (
# 2369 "FStar.TypeChecker.Tc.fst"
let _70_3251 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env elt)
in env)))
in (
# 2372 "FStar.TypeChecker.Tc.fst"
let en = (FStar_TypeChecker_Env.set_current_module en m.FStar_Syntax_Syntax.name)
in (let _151_1258 = (FStar_List.fold_left do_sigelt en m.FStar_Syntax_Syntax.exports)
in (FStar_TypeChecker_Env.finish_module _151_1258 m)))))

# 2375 "FStar.TypeChecker.Tc.fst"
let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 2376 "FStar.TypeChecker.Tc.fst"
let _70_3256 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _151_1263 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _151_1263))
end else begin
()
end
in (
# 2378 "FStar.TypeChecker.Tc.fst"
let env = (
# 2378 "FStar.TypeChecker.Tc.fst"
let _70_3258 = env
in {FStar_TypeChecker_Env.solver = _70_3258.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_3258.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_3258.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_3258.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_3258.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_3258.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_3258.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_3258.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_3258.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_3258.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_3258.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_3258.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_3258.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _70_3258.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_3258.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_3258.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_3258.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_3258.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_3258.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_3258.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_3258.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 2379 "FStar.TypeChecker.Tc.fst"
let _70_3264 = (tc_tot_or_gtot_term env e)
in (match (_70_3264) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected a total term; got a ghost term", e.FStar_Syntax_Syntax.pos))))
end
end)))))

# 2384 "FStar.TypeChecker.Tc.fst"
let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (
# 2385 "FStar.TypeChecker.Tc.fst"
let _70_3267 = if ((let _151_1268 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _151_1268)) <> 0) then begin
(let _151_1269 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _151_1269))
end else begin
()
end
in (
# 2387 "FStar.TypeChecker.Tc.fst"
let _70_3271 = (tc_modul env m)
in (match (_70_3271) with
| (m, env) -> begin
(
# 2388 "FStar.TypeChecker.Tc.fst"
let _70_3272 = if (FStar_Options.should_dump m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _151_1270 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _151_1270))
end else begin
()
end
in (m, env))
end))))




