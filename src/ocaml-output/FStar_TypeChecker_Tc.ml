
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
let precedes = (let _151_149 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.precedes_lid _151_149))
in (
# 208 "FStar.TypeChecker.Tc.fst"
let decreases_clause = (fun bs c -> (
# 210 "FStar.TypeChecker.Tc.fst"
let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _70_234 -> (match (_70_234) with
| (b, _70_233) -> begin
(
# 212 "FStar.TypeChecker.Tc.fst"
let t = (let _151_157 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _151_157))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _70_243 -> begin
(let _151_158 = (FStar_Syntax_Syntax.bv_to_name b)
in (_151_158)::[])
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
| FStar_Syntax_Syntax.Tm_fvar (fv, _70_252) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _70_256 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (
# 222 "FStar.TypeChecker.Tc.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _70_3 -> (match (_70_3) with
| FStar_Syntax_Syntax.DECREASES (_70_260) -> begin
true
end
| _70_263 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _70_268 -> begin
(
# 226 "FStar.TypeChecker.Tc.fst"
let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| x::[] -> begin
x
end
| _70_273 -> begin
(mk_lex_list xs)
end))
end)))))
in (
# 231 "FStar.TypeChecker.Tc.fst"
let previous_dec = (decreases_clause actuals expected_c)
in (
# 232 "FStar.TypeChecker.Tc.fst"
let guard_one_letrec = (fun _70_278 -> (match (_70_278) with
| (l, t) -> begin
(match ((let _151_164 = (FStar_Syntax_Subst.compress t)
in _151_164.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 236 "FStar.TypeChecker.Tc.fst"
let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _70_285 -> (match (_70_285) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _151_168 = (let _151_167 = (let _151_166 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_151_166))
in (FStar_Syntax_Syntax.new_bv _151_167 x.FStar_Syntax_Syntax.sort))
in (_151_168, imp))
end else begin
(x, imp)
end
end))))
in (
# 237 "FStar.TypeChecker.Tc.fst"
let _70_289 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_70_289) with
| (formals, c) -> begin
(
# 238 "FStar.TypeChecker.Tc.fst"
let dec = (decreases_clause formals c)
in (
# 239 "FStar.TypeChecker.Tc.fst"
let precedes = (let _151_172 = (let _151_171 = (FStar_Syntax_Syntax.as_arg dec)
in (let _151_170 = (let _151_169 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_151_169)::[])
in (_151_171)::_151_170))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _151_172 None r))
in (
# 240 "FStar.TypeChecker.Tc.fst"
let _70_296 = (FStar_Util.prefix formals)
in (match (_70_296) with
| (bs, (last, imp)) -> begin
(
# 241 "FStar.TypeChecker.Tc.fst"
let last = (
# 241 "FStar.TypeChecker.Tc.fst"
let _70_297 = last
in (let _151_173 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _70_297.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_297.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _151_173}))
in (
# 242 "FStar.TypeChecker.Tc.fst"
let refined_formals = (FStar_List.append bs (((last, imp))::[]))
in (
# 243 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (
# 244 "FStar.TypeChecker.Tc.fst"
let _70_302 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_176 = (FStar_Syntax_Print.lbname_to_string l)
in (let _151_175 = (FStar_Syntax_Print.term_to_string t)
in (let _151_174 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _151_176 _151_175 _151_174))))
end else begin
()
end
in (l, t')))))
end))))
end)))
end
| _70_305 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end))

# 256 "FStar.TypeChecker.Tc.fst"
let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (
# 256 "FStar.TypeChecker.Tc.fst"
let _70_308 = env
in {FStar_TypeChecker_Env.solver = _70_308.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_308.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_308.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_308.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_308.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_308.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_308.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_308.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_308.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_308.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_308.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_308.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_308.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _70_308.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_308.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_308.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_308.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_308.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_308.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_308.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_308.FStar_TypeChecker_Env.use_bv_sorts}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 261 "FStar.TypeChecker.Tc.fst"
let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (
# 262 "FStar.TypeChecker.Tc.fst"
let _70_313 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_245 = (let _151_243 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _151_243))
in (let _151_244 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _151_245 _151_244)))
end else begin
()
end
in (
# 263 "FStar.TypeChecker.Tc.fst"
let top = e
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_70_317) -> begin
(let _151_249 = (FStar_Syntax_Subst.compress e)
in (tc_term env _151_249))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(
# 280 "FStar.TypeChecker.Tc.fst"
let _70_358 = (tc_tot_or_gtot_term env e)
in (match (_70_358) with
| (e, c, g) -> begin
(
# 281 "FStar.TypeChecker.Tc.fst"
let g = (
# 281 "FStar.TypeChecker.Tc.fst"
let _70_359 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _70_359.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _70_359.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _70_359.FStar_TypeChecker_Env.implicits})
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(
# 285 "FStar.TypeChecker.Tc.fst"
let _70_369 = (FStar_Syntax_Util.type_u ())
in (match (_70_369) with
| (t, u) -> begin
(
# 286 "FStar.TypeChecker.Tc.fst"
let _70_373 = (tc_check_tot_or_gtot_term env e t)
in (match (_70_373) with
| (e, c, g) -> begin
(
# 287 "FStar.TypeChecker.Tc.fst"
let _70_380 = (
# 288 "FStar.TypeChecker.Tc.fst"
let _70_377 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_377) with
| (env, _70_376) -> begin
(tc_pats env pats)
end))
in (match (_70_380) with
| (pats, g') -> begin
(
# 290 "FStar.TypeChecker.Tc.fst"
let g' = (
# 290 "FStar.TypeChecker.Tc.fst"
let _70_381 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _70_381.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _70_381.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _70_381.FStar_TypeChecker_Env.implicits})
in (let _151_251 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_pattern (pats)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _151_250 = (FStar_TypeChecker_Rel.conj_guard g g')
in (_151_251, c, _151_250))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _151_252 = (FStar_Syntax_Subst.compress e)
in _151_252.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_70_390, {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _70_397; FStar_Syntax_Syntax.lbtyp = _70_395; FStar_Syntax_Syntax.lbeff = _70_393; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 298 "FStar.TypeChecker.Tc.fst"
let _70_408 = (let _151_253 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _151_253 e1))
in (match (_70_408) with
| (e1, c1, g1) -> begin
(
# 299 "FStar.TypeChecker.Tc.fst"
let _70_412 = (tc_term env e2)
in (match (_70_412) with
| (e2, c2, g2) -> begin
(
# 300 "FStar.TypeChecker.Tc.fst"
let c = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (None, c2))
in (
# 301 "FStar.TypeChecker.Tc.fst"
let e = (let _151_258 = (let _151_257 = (let _151_256 = (let _151_255 = (let _151_254 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Common.t_unit, e1))
in (_151_254)::[])
in (false, _151_255))
in (_151_256, e2))
in FStar_Syntax_Syntax.Tm_let (_151_257))
in (FStar_Syntax_Syntax.mk _151_258 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 302 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _151_259 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _151_259)))))
end))
end))
end
| _70_417 -> begin
(
# 305 "FStar.TypeChecker.Tc.fst"
let _70_421 = (tc_term env e)
in (match (_70_421) with
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
let _70_430 = (tc_term env e)
in (match (_70_430) with
| (e, c, g) -> begin
(
# 312 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, m))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _70_435) -> begin
(
# 316 "FStar.TypeChecker.Tc.fst"
let _70_440 = (FStar_Syntax_Util.type_u ())
in (match (_70_440) with
| (k, u) -> begin
(
# 317 "FStar.TypeChecker.Tc.fst"
let _70_445 = (tc_check_tot_or_gtot_term env t k)
in (match (_70_445) with
| (t, _70_443, f) -> begin
(
# 318 "FStar.TypeChecker.Tc.fst"
let _70_449 = (let _151_260 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _151_260 e))
in (match (_70_449) with
| (e, c, g) -> begin
(
# 319 "FStar.TypeChecker.Tc.fst"
let _70_453 = (let _151_264 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _70_450 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _151_264 e c f))
in (match (_70_453) with
| (c, f) -> begin
(
# 320 "FStar.TypeChecker.Tc.fst"
let _70_457 = (let _151_265 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, t, Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _151_265 c))
in (match (_70_457) with
| (e, c, f2) -> begin
(let _151_267 = (let _151_266 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _151_266))
in (e, c, _151_267))
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
let env = (let _151_269 = (let _151_268 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _151_268 Prims.fst))
in (FStar_All.pipe_right _151_269 instantiate_both))
in (
# 326 "FStar.TypeChecker.Tc.fst"
let _70_464 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_271 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _151_270 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _151_271 _151_270)))
end else begin
()
end
in (
# 330 "FStar.TypeChecker.Tc.fst"
let _70_469 = (tc_term (no_inst env) head)
in (match (_70_469) with
| (head, chead, g_head) -> begin
(
# 331 "FStar.TypeChecker.Tc.fst"
let _70_473 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _151_272 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _151_272))
end else begin
(let _151_273 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _151_273))
end
in (match (_70_473) with
| (e, c, g) -> begin
(
# 334 "FStar.TypeChecker.Tc.fst"
let _70_474 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _151_274 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _151_274))
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
let _70_481 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_280 = (FStar_Syntax_Print.term_to_string e)
in (let _151_279 = (let _151_275 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _151_275))
in (let _151_278 = (let _151_277 = (FStar_TypeChecker_Env.expected_typ env0)
in (FStar_All.pipe_right _151_277 (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end))))
in (FStar_Util.print3 "(%s) About to check %s against expected typ %s\n" _151_280 _151_279 _151_278))))
end else begin
()
end
in (
# 346 "FStar.TypeChecker.Tc.fst"
let _70_486 = (comp_check_expected_typ env0 e c)
in (match (_70_486) with
| (e, c, g') -> begin
(
# 347 "FStar.TypeChecker.Tc.fst"
let _70_487 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_283 = (FStar_Syntax_Print.term_to_string e)
in (let _151_282 = (let _151_281 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _151_281))
in (FStar_Util.print2 "(%s) checked ... got %s\n" _151_283 _151_282)))
end else begin
()
end
in (
# 351 "FStar.TypeChecker.Tc.fst"
let gimp = (match ((let _151_284 = (FStar_Syntax_Subst.compress head)
in _151_284.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _70_491) -> begin
(
# 354 "FStar.TypeChecker.Tc.fst"
let imp = (env0, u, e, c.FStar_Syntax_Syntax.res_typ, e.FStar_Syntax_Syntax.pos)
in (
# 355 "FStar.TypeChecker.Tc.fst"
let _70_495 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _70_495.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _70_495.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _70_495.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _70_498 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (
# 357 "FStar.TypeChecker.Tc.fst"
let gres = (let _151_285 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _151_285))
in (
# 358 "FStar.TypeChecker.Tc.fst"
let _70_501 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _151_286 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print1 "Guard from application node is %s\n" _151_286))
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
let _70_509 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_509) with
| (env1, topt) -> begin
(
# 364 "FStar.TypeChecker.Tc.fst"
let env1 = (instantiate_both env1)
in (
# 365 "FStar.TypeChecker.Tc.fst"
let _70_514 = (tc_term env1 e1)
in (match (_70_514) with
| (e1, c1, g1) -> begin
(
# 366 "FStar.TypeChecker.Tc.fst"
let _70_525 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(
# 369 "FStar.TypeChecker.Tc.fst"
let _70_521 = (FStar_Syntax_Util.type_u ())
in (match (_70_521) with
| (k, _70_520) -> begin
(
# 370 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _151_287 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_151_287, res_t)))
end))
end)
in (match (_70_525) with
| (env_branches, res_t) -> begin
(
# 373 "FStar.TypeChecker.Tc.fst"
let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (
# 374 "FStar.TypeChecker.Tc.fst"
let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (
# 375 "FStar.TypeChecker.Tc.fst"
let _70_542 = (
# 376 "FStar.TypeChecker.Tc.fst"
let _70_539 = (FStar_List.fold_right (fun _70_533 _70_536 -> (match ((_70_533, _70_536)) with
| ((_70_529, f, c, g), (caccum, gaccum)) -> begin
(let _151_290 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _151_290))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_70_539) with
| (cases, g) -> begin
(let _151_291 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_151_291, g))
end))
in (match (_70_542) with
| (c_branches, g_branches) -> begin
(
# 380 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (guard_x), c_branches))
in (
# 381 "FStar.TypeChecker.Tc.fst"
let e = (let _151_295 = (let _151_294 = (let _151_293 = (FStar_List.map (fun _70_551 -> (match (_70_551) with
| (f, _70_546, _70_548, _70_550) -> begin
f
end)) t_eqns)
in (e1, _151_293))
in FStar_Syntax_Syntax.Tm_match (_151_294))
in (FStar_Syntax_Syntax.mk _151_295 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (
# 382 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, cres.FStar_Syntax_Syntax.res_typ, Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (
# 383 "FStar.TypeChecker.Tc.fst"
let _70_554 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _151_298 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _151_297 = (let _151_296 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _151_296))
in (FStar_Util.print2 "(%s) comp type = %s\n" _151_298 _151_297)))
end else begin
()
end
in (let _151_299 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _151_299))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_70_566); FStar_Syntax_Syntax.lbunivs = _70_564; FStar_Syntax_Syntax.lbtyp = _70_562; FStar_Syntax_Syntax.lbeff = _70_560; FStar_Syntax_Syntax.lbdef = _70_558}::[]), _70_572) -> begin
(
# 390 "FStar.TypeChecker.Tc.fst"
let _70_575 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_300 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _151_300))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _70_579), _70_582) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_70_597); FStar_Syntax_Syntax.lbunivs = _70_595; FStar_Syntax_Syntax.lbtyp = _70_593; FStar_Syntax_Syntax.lbeff = _70_591; FStar_Syntax_Syntax.lbdef = _70_589}::_70_587), _70_603) -> begin
(
# 397 "FStar.TypeChecker.Tc.fst"
let _70_606 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_301 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _151_301))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _70_610), _70_613) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 410 "FStar.TypeChecker.Tc.fst"
let check_instantiated_fvar = (fun env v dc e t -> (
# 411 "FStar.TypeChecker.Tc.fst"
let _70_627 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_70_627) with
| (e, t, implicits) -> begin
(
# 413 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _151_315 = (let _151_314 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_314))
in FStar_Util.Inr (_151_315))
end
in (
# 414 "FStar.TypeChecker.Tc.fst"
let is_data_ctor = (fun _70_4 -> (match (_70_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _70_637 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _151_321 = (let _151_320 = (let _151_319 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _151_318 = (FStar_TypeChecker_Env.get_range env)
in (_151_319, _151_318)))
in FStar_Syntax_Syntax.Error (_151_320))
in (Prims.raise _151_321))
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
let g = (match ((let _151_322 = (FStar_Syntax_Subst.compress t1)
in _151_322.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_70_648) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _70_651 -> begin
(
# 433 "FStar.TypeChecker.Tc.fst"
let imp = (env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (
# 434 "FStar.TypeChecker.Tc.fst"
let _70_653 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _70_653.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _70_653.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _70_653.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 439 "FStar.TypeChecker.Tc.fst"
let _70_659 = (FStar_Syntax_Util.type_u ())
in (match (_70_659) with
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
let _70_664 = x
in {FStar_Syntax_Syntax.ppname = _70_664.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_664.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (
# 446 "FStar.TypeChecker.Tc.fst"
let _70_670 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_70_670) with
| (e, t, implicits) -> begin
(
# 447 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _151_324 = (let _151_323 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_323))
in FStar_Util.Inr (_151_324))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (v, dc); FStar_Syntax_Syntax.tk = _70_677; FStar_Syntax_Syntax.pos = _70_675; FStar_Syntax_Syntax.vars = _70_673}, us) -> begin
(
# 451 "FStar.TypeChecker.Tc.fst"
let us = (FStar_List.map (tc_universe env) us)
in (
# 452 "FStar.TypeChecker.Tc.fst"
let _70_689 = (FStar_TypeChecker_Env.lookup_lid env v.FStar_Syntax_Syntax.v)
in (match (_70_689) with
| (us', t) -> begin
(
# 453 "FStar.TypeChecker.Tc.fst"
let _70_696 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _151_327 = (let _151_326 = (let _151_325 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _151_325))
in FStar_Syntax_Syntax.Error (_151_326))
in (Prims.raise _151_327))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _70_695 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (
# 458 "FStar.TypeChecker.Tc.fst"
let e = (let _151_330 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (((
# 458 "FStar.TypeChecker.Tc.fst"
let _70_698 = v
in {FStar_Syntax_Syntax.v = _70_698.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _70_698.FStar_Syntax_Syntax.p}), dc))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _151_330 us))
in (check_instantiated_fvar env v dc e t)))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (v, dc) -> begin
(
# 462 "FStar.TypeChecker.Tc.fst"
let _70_707 = (FStar_TypeChecker_Env.lookup_lid env v.FStar_Syntax_Syntax.v)
in (match (_70_707) with
| (us, t) -> begin
(
# 463 "FStar.TypeChecker.Tc.fst"
let e = (let _151_331 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (((
# 463 "FStar.TypeChecker.Tc.fst"
let _70_708 = v
in {FStar_Syntax_Syntax.v = _70_708.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _70_708.FStar_Syntax_Syntax.p}), dc))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _151_331 us))
in (check_instantiated_fvar env v dc e t))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(
# 467 "FStar.TypeChecker.Tc.fst"
let t = (tc_constant env top.FStar_Syntax_Syntax.pos c)
in (
# 468 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 472 "FStar.TypeChecker.Tc.fst"
let _70_721 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_70_721) with
| (bs, c) -> begin
(
# 473 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 474 "FStar.TypeChecker.Tc.fst"
let _70_726 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_726) with
| (env, _70_725) -> begin
(
# 475 "FStar.TypeChecker.Tc.fst"
let _70_731 = (tc_binders env bs)
in (match (_70_731) with
| (bs, env, g, us) -> begin
(
# 476 "FStar.TypeChecker.Tc.fst"
let _70_735 = (tc_comp env c)
in (match (_70_735) with
| (c, uc, f) -> begin
(
# 477 "FStar.TypeChecker.Tc.fst"
let e = (
# 477 "FStar.TypeChecker.Tc.fst"
let _70_736 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _70_736.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _70_736.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _70_736.FStar_Syntax_Syntax.vars})
in (
# 478 "FStar.TypeChecker.Tc.fst"
let _70_739 = (check_smt_pat env e bs c)
in (
# 479 "FStar.TypeChecker.Tc.fst"
let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (
# 480 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 481 "FStar.TypeChecker.Tc.fst"
let g = (let _151_332 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _151_332))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(
# 485 "FStar.TypeChecker.Tc.fst"
let u = (tc_universe env u)
in (
# 486 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) None top.FStar_Syntax_Syntax.pos)
in (
# 487 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 491 "FStar.TypeChecker.Tc.fst"
let _70_755 = (let _151_334 = (let _151_333 = (FStar_Syntax_Syntax.mk_binder x)
in (_151_333)::[])
in (FStar_Syntax_Subst.open_term _151_334 phi))
in (match (_70_755) with
| (x, phi) -> begin
(
# 492 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 493 "FStar.TypeChecker.Tc.fst"
let _70_760 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_760) with
| (env, _70_759) -> begin
(
# 494 "FStar.TypeChecker.Tc.fst"
let _70_765 = (let _151_335 = (FStar_List.hd x)
in (tc_binder env _151_335))
in (match (_70_765) with
| (x, env, f1, u) -> begin
(
# 495 "FStar.TypeChecker.Tc.fst"
let _70_766 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_338 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _151_337 = (FStar_Syntax_Print.term_to_string phi)
in (let _151_336 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _151_338 _151_337 _151_336))))
end else begin
()
end
in (
# 498 "FStar.TypeChecker.Tc.fst"
let _70_771 = (FStar_Syntax_Util.type_u ())
in (match (_70_771) with
| (t_phi, _70_770) -> begin
(
# 499 "FStar.TypeChecker.Tc.fst"
let _70_776 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_70_776) with
| (phi, _70_774, f2) -> begin
(
# 500 "FStar.TypeChecker.Tc.fst"
let e = (
# 500 "FStar.TypeChecker.Tc.fst"
let _70_777 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _70_777.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _70_777.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _70_777.FStar_Syntax_Syntax.vars})
in (
# 501 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 502 "FStar.TypeChecker.Tc.fst"
let g = (let _151_339 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _151_339))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _70_785) -> begin
(
# 506 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (
# 507 "FStar.TypeChecker.Tc.fst"
let _70_791 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_340 = (FStar_Syntax_Print.term_to_string (
# 508 "FStar.TypeChecker.Tc.fst"
let _70_789 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _70_789.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _70_789.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _70_789.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _151_340))
end else begin
()
end
in (
# 509 "FStar.TypeChecker.Tc.fst"
let _70_795 = (FStar_Syntax_Subst.open_term bs body)
in (match (_70_795) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _70_797 -> begin
(let _151_342 = (let _151_341 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _151_341))
in (FStar_All.failwith _151_342))
end)))))
and tc_constant : FStar_TypeChecker_Env.env  ->  FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun env r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_70_803) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_70_806) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int32 (_70_809) -> begin
FStar_TypeChecker_Common.t_int32
end
| FStar_Const.Const_int64 (_70_812) -> begin
FStar_TypeChecker_Common.t_int64
end
| FStar_Const.Const_string (_70_815) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_70_818) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_70_821) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_uint8 (_70_824) -> begin
FStar_TypeChecker_Common.t_uint8
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_70_828) -> begin
(
# 528 "FStar.TypeChecker.Tc.fst"
let fail = (fun _70_831 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Range constant cannot be checked in this context; expected an instance of \'range_of\'", r))))
end))
in (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(fail ())
end
| Some (t) -> begin
if (let _151_348 = (FStar_Syntax_Util.destruct t FStar_Syntax_Const.range_of_lid)
in (FStar_Option.isSome _151_348)) then begin
t
end else begin
(fail ())
end
end))
end
| _70_836 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 549 "FStar.TypeChecker.Tc.fst"
let _70_843 = (FStar_Syntax_Util.type_u ())
in (match (_70_843) with
| (k, u) -> begin
(
# 550 "FStar.TypeChecker.Tc.fst"
let _70_848 = (tc_check_tot_or_gtot_term env t k)
in (match (_70_848) with
| (t, _70_846, g) -> begin
(let _151_351 = (FStar_Syntax_Syntax.mk_Total t)
in (_151_351, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 554 "FStar.TypeChecker.Tc.fst"
let _70_853 = (FStar_Syntax_Util.type_u ())
in (match (_70_853) with
| (k, u) -> begin
(
# 555 "FStar.TypeChecker.Tc.fst"
let _70_858 = (tc_check_tot_or_gtot_term env t k)
in (match (_70_858) with
| (t, _70_856, g) -> begin
(let _151_352 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_151_352, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 559 "FStar.TypeChecker.Tc.fst"
let head = (FStar_Syntax_Syntax.fvar None c.FStar_Syntax_Syntax.effect_name (FStar_Ident.range_of_lid c.FStar_Syntax_Syntax.effect_name))
in (
# 560 "FStar.TypeChecker.Tc.fst"
let tc = (let _151_354 = (let _151_353 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_151_353)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _151_354 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 561 "FStar.TypeChecker.Tc.fst"
let _70_867 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_70_867) with
| (tc, _70_865, f) -> begin
(
# 562 "FStar.TypeChecker.Tc.fst"
let _70_871 = (FStar_Syntax_Util.head_and_args tc)
in (match (_70_871) with
| (_70_869, args) -> begin
(
# 563 "FStar.TypeChecker.Tc.fst"
let _70_874 = (let _151_356 = (FStar_List.hd args)
in (let _151_355 = (FStar_List.tl args)
in (_151_356, _151_355)))
in (match (_70_874) with
| (res, args) -> begin
(
# 564 "FStar.TypeChecker.Tc.fst"
let _70_890 = (let _151_358 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _70_5 -> (match (_70_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(
# 566 "FStar.TypeChecker.Tc.fst"
let _70_881 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_881) with
| (env, _70_880) -> begin
(
# 567 "FStar.TypeChecker.Tc.fst"
let _70_886 = (tc_tot_or_gtot_term env e)
in (match (_70_886) with
| (e, _70_884, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _151_358 FStar_List.unzip))
in (match (_70_890) with
| (flags, guards) -> begin
(
# 570 "FStar.TypeChecker.Tc.fst"
let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| _70_895 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _151_360 = (FStar_Syntax_Syntax.mk_Comp (
# 573 "FStar.TypeChecker.Tc.fst"
let _70_897 = c
in {FStar_Syntax_Syntax.effect_name = _70_897.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _70_897.FStar_Syntax_Syntax.flags}))
in (let _151_359 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_151_360, u, _151_359))))
end))
end))
end))
end))))
end))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (
# 580 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun u -> (
# 581 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_70_905) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _151_365 = (aux u)
in FStar_Syntax_Syntax.U_succ (_151_365))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _151_366 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_151_366))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _151_370 = (let _151_369 = (let _151_368 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _151_367 = (FStar_TypeChecker_Env.get_range env)
in (_151_368, _151_367)))
in FStar_Syntax_Syntax.Error (_151_369))
in (Prims.raise _151_370))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _151_371 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_371 Prims.snd))
end
| _70_920 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (
# 603 "FStar.TypeChecker.Tc.fst"
let fail = (fun msg t -> (let _151_380 = (let _151_379 = (let _151_378 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_151_378, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_151_379))
in (Prims.raise _151_380)))
in (
# 612 "FStar.TypeChecker.Tc.fst"
let check_binders = (fun env bs bs_expected -> (
# 617 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun _70_938 bs bs_expected -> (match (_70_938) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| ((hd, imp)::bs, (hd_expected, imp')::bs_expected) -> begin
(
# 621 "FStar.TypeChecker.Tc.fst"
let _70_969 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _151_397 = (let _151_396 = (let _151_395 = (let _151_393 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _151_393))
in (let _151_394 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_151_395, _151_394)))
in FStar_Syntax_Syntax.Error (_151_396))
in (Prims.raise _151_397))
end
| _70_968 -> begin
()
end)
in (
# 628 "FStar.TypeChecker.Tc.fst"
let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (
# 629 "FStar.TypeChecker.Tc.fst"
let _70_986 = (match ((let _151_398 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _151_398.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _70_974 -> begin
(
# 632 "FStar.TypeChecker.Tc.fst"
let _70_975 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_399 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _151_399))
end else begin
()
end
in (
# 633 "FStar.TypeChecker.Tc.fst"
let _70_981 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_70_981) with
| (t, _70_979, g1) -> begin
(
# 634 "FStar.TypeChecker.Tc.fst"
let g2 = (let _151_401 = (FStar_TypeChecker_Env.get_range env)
in (let _151_400 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _151_401 "Type annotation on parameter incompatible with the expected type" _151_400)))
in (
# 638 "FStar.TypeChecker.Tc.fst"
let g = (let _151_402 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _151_402))
in (t, g)))
end)))
end)
in (match (_70_986) with
| (t, g) -> begin
(
# 640 "FStar.TypeChecker.Tc.fst"
let hd = (
# 640 "FStar.TypeChecker.Tc.fst"
let _70_987 = hd
in {FStar_Syntax_Syntax.ppname = _70_987.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_987.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 641 "FStar.TypeChecker.Tc.fst"
let b = (hd, imp)
in (
# 642 "FStar.TypeChecker.Tc.fst"
let b_expected = (hd_expected, imp')
in (
# 643 "FStar.TypeChecker.Tc.fst"
let env = (maybe_push_binding env b)
in (
# 644 "FStar.TypeChecker.Tc.fst"
let subst = (let _151_403 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _151_403))
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
# 654 "FStar.TypeChecker.Tc.fst"
let rec expected_function_typ = (fun env t0 -> (match (t0) with
| None -> begin
(
# 664 "FStar.TypeChecker.Tc.fst"
let _70_1007 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _70_1006 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (
# 665 "FStar.TypeChecker.Tc.fst"
let _70_1014 = (tc_binders env bs)
in (match (_70_1014) with
| (bs, envbody, g, _70_1013) -> begin
(None, bs, [], None, envbody, g)
end)))
end
| Some (t) -> begin
(
# 669 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 670 "FStar.TypeChecker.Tc.fst"
let rec as_function_typ = (fun norm t -> (match ((let _151_412 = (FStar_Syntax_Subst.compress t)
in _151_412.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 674 "FStar.TypeChecker.Tc.fst"
let _70_1041 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _70_1040 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 675 "FStar.TypeChecker.Tc.fst"
let _70_1048 = (tc_binders env bs)
in (match (_70_1048) with
| (bs, envbody, g, _70_1047) -> begin
(
# 676 "FStar.TypeChecker.Tc.fst"
let _70_1052 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_70_1052) with
| (envbody, _70_1051) -> begin
(Some ((t, true)), bs, [], None, envbody, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _70_1055) -> begin
(
# 682 "FStar.TypeChecker.Tc.fst"
let _70_1065 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_70_1065) with
| (_70_1059, bs, bs', copt, env, g) -> begin
(Some ((t, false)), bs, bs', copt, env, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 686 "FStar.TypeChecker.Tc.fst"
let _70_1072 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_70_1072) with
| (bs_expected, c_expected) -> begin
(
# 693 "FStar.TypeChecker.Tc.fst"
let check_actuals_against_formals = (fun env bs bs_expected -> (
# 694 "FStar.TypeChecker.Tc.fst"
let rec handle_more = (fun _70_1083 c_expected -> (match (_70_1083) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _151_423 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _151_423))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(
# 699 "FStar.TypeChecker.Tc.fst"
let c = (let _151_424 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _151_424))
in (let _151_425 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _151_425)))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(
# 703 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.subst_comp subst c_expected)
in if (FStar_Syntax_Util.is_total_comp c) then begin
(
# 706 "FStar.TypeChecker.Tc.fst"
let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 709 "FStar.TypeChecker.Tc.fst"
let _70_1104 = (check_binders env more_bs bs_expected)
in (match (_70_1104) with
| (env, bs', more, guard', subst) -> begin
(let _151_427 = (let _151_426 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _151_426, subst))
in (handle_more _151_427 c_expected))
end))
end
| _70_1106 -> begin
(let _151_429 = (let _151_428 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _151_428))
in (fail _151_429 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _151_430 = (check_binders env bs bs_expected)
in (handle_more _151_430 c_expected))))
in (
# 716 "FStar.TypeChecker.Tc.fst"
let mk_letrec_env = (fun envbody bs c -> (
# 717 "FStar.TypeChecker.Tc.fst"
let letrecs = (guard_letrecs envbody bs c)
in (
# 718 "FStar.TypeChecker.Tc.fst"
let envbody = (
# 718 "FStar.TypeChecker.Tc.fst"
let _70_1112 = envbody
in {FStar_TypeChecker_Env.solver = _70_1112.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1112.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1112.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1112.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1112.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1112.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1112.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1112.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1112.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1112.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1112.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1112.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _70_1112.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _70_1112.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_1112.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_1112.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1112.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1112.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1112.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1112.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1112.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _70_1117 _70_1120 -> (match ((_70_1117, _70_1120)) with
| ((env, letrec_binders), (l, t)) -> begin
(
# 720 "FStar.TypeChecker.Tc.fst"
let _70_1126 = (let _151_440 = (let _151_439 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _151_439 Prims.fst))
in (tc_term _151_440 t))
in (match (_70_1126) with
| (t, _70_1123, _70_1125) -> begin
(
# 721 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (
# 722 "FStar.TypeChecker.Tc.fst"
let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _151_441 = (FStar_Syntax_Syntax.mk_binder (
# 723 "FStar.TypeChecker.Tc.fst"
let _70_1130 = x
in {FStar_Syntax_Syntax.ppname = _70_1130.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_1130.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_151_441)::letrec_binders)
end
| _70_1133 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (
# 728 "FStar.TypeChecker.Tc.fst"
let _70_1139 = (check_actuals_against_formals env bs bs_expected)
in (match (_70_1139) with
| (envbody, bs, g, c) -> begin
(
# 729 "FStar.TypeChecker.Tc.fst"
let _70_1142 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_70_1142) with
| (envbody, letrecs) -> begin
(
# 730 "FStar.TypeChecker.Tc.fst"
let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, g))
end))
end))))
end))
end
| _70_1145 -> begin
if (not (norm)) then begin
(let _151_442 = (unfold_whnf env t)
in (as_function_typ true _151_442))
end else begin
(
# 738 "FStar.TypeChecker.Tc.fst"
let _70_1154 = (expected_function_typ env None)
in (match (_70_1154) with
| (_70_1147, bs, _70_1150, c_opt, envbody, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (
# 742 "FStar.TypeChecker.Tc.fst"
let use_eq = env.FStar_TypeChecker_Env.use_eq
in (
# 743 "FStar.TypeChecker.Tc.fst"
let _70_1158 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_1158) with
| (env, topt) -> begin
(
# 744 "FStar.TypeChecker.Tc.fst"
let _70_1162 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_443 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _151_443 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (
# 748 "FStar.TypeChecker.Tc.fst"
let _70_1170 = (expected_function_typ env topt)
in (match (_70_1170) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, g) -> begin
(
# 749 "FStar.TypeChecker.Tc.fst"
let _70_1176 = (tc_term (
# 749 "FStar.TypeChecker.Tc.fst"
let _70_1171 = envbody
in {FStar_TypeChecker_Env.solver = _70_1171.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1171.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1171.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1171.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1171.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1171.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1171.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1171.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1171.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1171.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1171.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1171.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_1171.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _70_1171.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _70_1171.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1171.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1171.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1171.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1171.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1171.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_70_1176) with
| (body, cbody, guard_body) -> begin
(
# 750 "FStar.TypeChecker.Tc.fst"
let _70_1177 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_447 = (FStar_Syntax_Print.term_to_string body)
in (let _151_446 = (let _151_444 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _151_444))
in (let _151_445 = (FStar_TypeChecker_Rel.guard_to_string env guard_body)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _151_447 _151_446 _151_445))))
end else begin
()
end
in (
# 755 "FStar.TypeChecker.Tc.fst"
let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (
# 757 "FStar.TypeChecker.Tc.fst"
let _70_1180 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _151_450 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _151_449 = (let _151_448 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _151_448))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _151_450 _151_449)))
end else begin
()
end
in (
# 761 "FStar.TypeChecker.Tc.fst"
let _70_1187 = (let _151_452 = (let _151_451 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _151_451))
in (check_expected_effect (
# 761 "FStar.TypeChecker.Tc.fst"
let _70_1182 = envbody
in {FStar_TypeChecker_Env.solver = _70_1182.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1182.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1182.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1182.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1182.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1182.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1182.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1182.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1182.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1182.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1182.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1182.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_1182.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _70_1182.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _70_1182.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _70_1182.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1182.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1182.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1182.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1182.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1182.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _151_452))
in (match (_70_1187) with
| (body, cbody, guard) -> begin
(
# 762 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (
# 763 "FStar.TypeChecker.Tc.fst"
let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _151_453 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _151_453))
end else begin
(
# 765 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (
# 768 "FStar.TypeChecker.Tc.fst"
let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (
# 769 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.abs bs body (Some ((FStar_Syntax_Util.lcomp_of_comp cbody))))
in (
# 770 "FStar.TypeChecker.Tc.fst"
let _70_1210 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(
# 772 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_70_1199) -> begin
(e, t, guard)
end
| _70_1202 -> begin
(
# 781 "FStar.TypeChecker.Tc.fst"
let _70_1205 = if use_teq then begin
(let _151_454 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _151_454))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_70_1205) with
| (e, guard') -> begin
(let _151_455 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _151_455))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_70_1210) with
| (e, tfun, guard) -> begin
(
# 791 "FStar.TypeChecker.Tc.fst"
let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (
# 792 "FStar.TypeChecker.Tc.fst"
let _70_1214 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_70_1214) with
| (c, g) -> begin
(e, c, g)
end)))
end))))))
end)))))
end))
end)))
end)))))))
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead ghead args expected_topt -> (
# 800 "FStar.TypeChecker.Tc.fst"
let n_args = (FStar_List.length args)
in (
# 801 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 802 "FStar.TypeChecker.Tc.fst"
let thead = chead.FStar_Syntax_Syntax.res_typ
in (
# 803 "FStar.TypeChecker.Tc.fst"
let _70_1224 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_464 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _151_463 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _151_464 _151_463)))
end else begin
()
end
in (
# 804 "FStar.TypeChecker.Tc.fst"
let rec check_function_app = (fun norm tf -> (match ((let _151_469 = (FStar_Syntax_Util.unrefine tf)
in _151_469.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 808 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| (e, imp)::tl -> begin
(
# 811 "FStar.TypeChecker.Tc.fst"
let _70_1258 = (tc_term env e)
in (match (_70_1258) with
| (e, c, g_e) -> begin
(
# 812 "FStar.TypeChecker.Tc.fst"
let _70_1262 = (tc_args env tl)
in (match (_70_1262) with
| (args, comps, g_rest) -> begin
(let _151_474 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, (c)::comps, _151_474))
end))
end))
end))
in (
# 820 "FStar.TypeChecker.Tc.fst"
let _70_1266 = (tc_args env args)
in (match (_70_1266) with
| (args, comps, g_args) -> begin
(
# 821 "FStar.TypeChecker.Tc.fst"
let bs = (let _151_476 = (FStar_All.pipe_right comps (FStar_List.map (fun c -> (c.FStar_Syntax_Syntax.res_typ, None))))
in (FStar_Syntax_Util.null_binders_of_tks _151_476))
in (
# 822 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _70_1273 -> begin
FStar_Syntax_Util.ml_comp
end)
in (
# 825 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _151_491 = (FStar_Syntax_Subst.compress t)
in _151_491.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_70_1279) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _70_1284 -> begin
ml_or_tot
end)
end)
in (
# 832 "FStar.TypeChecker.Tc.fst"
let cres = (let _151_496 = (let _151_495 = (let _151_494 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_494 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _151_495))
in (ml_or_tot _151_496 r))
in (
# 833 "FStar.TypeChecker.Tc.fst"
let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (
# 834 "FStar.TypeChecker.Tc.fst"
let _70_1288 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _151_499 = (FStar_Syntax_Print.term_to_string head)
in (let _151_498 = (FStar_Syntax_Print.term_to_string tf)
in (let _151_497 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _151_499 _151_498 _151_497))))
end else begin
()
end
in (
# 839 "FStar.TypeChecker.Tc.fst"
let _70_1290 = (let _151_500 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _151_500))
in (
# 840 "FStar.TypeChecker.Tc.fst"
let comp = (let _151_503 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_TypeChecker_Util.bind env None c (None, out))) ((chead)::comps) _151_503))
in (let _151_505 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _151_504 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_151_505, comp, _151_504)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 844 "FStar.TypeChecker.Tc.fst"
let _70_1301 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_70_1301) with
| (bs, c) -> begin
(
# 846 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun _70_1309 bs cres args -> (match (_70_1309) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (_70_1316)))::rest, (_70_1324, None)::_70_1322) -> begin
(
# 857 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 858 "FStar.TypeChecker.Tc.fst"
let _70_1330 = (check_no_escape (Some (head)) env fvs t)
in (
# 859 "FStar.TypeChecker.Tc.fst"
let _70_1336 = (FStar_TypeChecker_Util.new_implicit_var env t)
in (match (_70_1336) with
| (varg, _70_1334, implicits) -> begin
(
# 860 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (
# 861 "FStar.TypeChecker.Tc.fst"
let arg = (let _151_514 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _151_514))
in (let _151_516 = (let _151_515 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _151_515, fvs))
in (tc_args _151_516 rest cres args))))
end))))
end
| ((x, aqual)::rest, (e, aq)::rest') -> begin
(
# 865 "FStar.TypeChecker.Tc.fst"
let _70_1368 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _70_1367 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (
# 870 "FStar.TypeChecker.Tc.fst"
let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 871 "FStar.TypeChecker.Tc.fst"
let x = (
# 871 "FStar.TypeChecker.Tc.fst"
let _70_1371 = x
in {FStar_Syntax_Syntax.ppname = _70_1371.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_1371.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (
# 872 "FStar.TypeChecker.Tc.fst"
let _70_1374 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _151_517 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _151_517))
end else begin
()
end
in (
# 873 "FStar.TypeChecker.Tc.fst"
let _70_1376 = (check_no_escape (Some (head)) env fvs targ)
in (
# 874 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (
# 875 "FStar.TypeChecker.Tc.fst"
let env = (
# 875 "FStar.TypeChecker.Tc.fst"
let _70_1379 = env
in {FStar_TypeChecker_Env.solver = _70_1379.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1379.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1379.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1379.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1379.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1379.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1379.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1379.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1379.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1379.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1379.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1379.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_1379.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _70_1379.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _70_1379.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _70_1379.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1379.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1379.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1379.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1379.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1379.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 876 "FStar.TypeChecker.Tc.fst"
let _70_1382 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_520 = (FStar_Syntax_Print.tag_of_term e)
in (let _151_519 = (FStar_Syntax_Print.term_to_string e)
in (let _151_518 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _151_520 _151_519 _151_518))))
end else begin
()
end
in (
# 877 "FStar.TypeChecker.Tc.fst"
let _70_1387 = (tc_term env e)
in (match (_70_1387) with
| (e, c, g_e) -> begin
(
# 878 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (
# 880 "FStar.TypeChecker.Tc.fst"
let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(
# 882 "FStar.TypeChecker.Tc.fst"
let subst = (let _151_521 = (FStar_List.hd bs)
in (maybe_extend_subst subst _151_521 e))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(
# 885 "FStar.TypeChecker.Tc.fst"
let subst = (let _151_522 = (FStar_List.hd bs)
in (maybe_extend_subst subst _151_522 e))
in (
# 886 "FStar.TypeChecker.Tc.fst"
let _70_1394 = (((Some (x), c))::comps, g)
in (match (_70_1394) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _151_523 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _151_523)) then begin
(
# 890 "FStar.TypeChecker.Tc.fst"
let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (
# 891 "FStar.TypeChecker.Tc.fst"
let arg' = (let _151_524 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _151_524))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (newx), c))::comps, g, fvs) rest cres rest')))
end else begin
(let _151_528 = (let _151_527 = (let _151_526 = (let _151_525 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _151_525))
in (_151_526)::arg_rets)
in (subst, (arg)::outargs, _151_527, ((Some (x), c))::comps, g, (x)::fvs))
in (tc_args _151_528 rest cres rest'))
end
end
end))
end))))))))))
end
| (_70_1398, []) -> begin
(
# 900 "FStar.TypeChecker.Tc.fst"
let _70_1401 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (
# 901 "FStar.TypeChecker.Tc.fst"
let _70_1419 = (match (bs) with
| [] -> begin
(
# 904 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (
# 910 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (
# 912 "FStar.TypeChecker.Tc.fst"
let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _70_1409 -> (match (_70_1409) with
| (_70_1407, c) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (
# 919 "FStar.TypeChecker.Tc.fst"
let cres = if refine_with_equality then begin
(let _151_530 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _151_530 cres))
end else begin
(
# 925 "FStar.TypeChecker.Tc.fst"
let _70_1411 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_533 = (FStar_Syntax_Print.term_to_string head)
in (let _151_532 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _151_531 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _151_533 _151_532 _151_531))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _70_1415 -> begin
(
# 934 "FStar.TypeChecker.Tc.fst"
let g = (let _151_534 = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (FStar_All.pipe_right _151_534 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _151_539 = (let _151_538 = (let _151_537 = (let _151_536 = (let _151_535 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _151_535))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _151_536))
in (FStar_Syntax_Syntax.mk_Total _151_537))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_538))
in (_151_539, g)))
end)
in (match (_70_1419) with
| (cres, g) -> begin
(
# 937 "FStar.TypeChecker.Tc.fst"
let _70_1420 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_540 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _151_540))
end else begin
()
end
in (
# 938 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_List.fold_left (fun out c -> (FStar_TypeChecker_Util.bind env None (Prims.snd c) ((Prims.fst c), out))) cres comps)
in (
# 939 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.bind env None chead (None, comp))
in (
# 940 "FStar.TypeChecker.Tc.fst"
let app = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev outargs) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (
# 941 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.record_application_site env app comp)
in (
# 942 "FStar.TypeChecker.Tc.fst"
let _70_1430 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp g)
in (match (_70_1430) with
| (comp, g) -> begin
(
# 943 "FStar.TypeChecker.Tc.fst"
let _70_1431 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_546 = (FStar_TypeChecker_Normalize.term_to_string env app)
in (let _151_545 = (let _151_544 = (comp.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Print.comp_to_string _151_544))
in (FStar_Util.print2 "\t Type of app term %s is %s\n" _151_546 _151_545)))
end else begin
()
end
in (app, comp, g))
end)))))))
end)))
end
| ([], arg::_70_1435) -> begin
(
# 949 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun norm tres -> (
# 950 "FStar.TypeChecker.Tc.fst"
let tres = (let _151_551 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _151_551 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(
# 953 "FStar.TypeChecker.Tc.fst"
let _70_1447 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_552 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _151_552))
end else begin
()
end
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs (FStar_Syntax_Util.lcomp_of_comp cres') args))
end
| _70_1450 when (not (norm)) -> begin
(let _151_553 = (unfold_whnf env tres)
in (aux true _151_553))
end
| _70_1452 -> begin
(let _151_559 = (let _151_558 = (let _151_557 = (let _151_555 = (FStar_TypeChecker_Normalize.term_to_string env tf)
in (let _151_554 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _151_555 _151_554)))
in (let _151_556 = (FStar_Syntax_Syntax.argpos arg)
in (_151_557, _151_556)))
in FStar_Syntax_Syntax.Error (_151_558))
in (Prims.raise _151_559))
end)))
in (aux false cres.FStar_Syntax_Syntax.res_typ))
end)
end))
in (tc_args ([], [], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs (FStar_Syntax_Util.lcomp_of_comp c) args))
end))
end
| _70_1454 -> begin
if (not (norm)) then begin
(let _151_560 = (unfold_whnf env tf)
in (check_function_app true _151_560))
end else begin
(let _151_563 = (let _151_562 = (let _151_561 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_151_561, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_151_562))
in (Prims.raise _151_563))
end
end))
in (let _151_565 = (let _151_564 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _151_564))
in (check_function_app false _151_565))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (
# 979 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 980 "FStar.TypeChecker.Tc.fst"
let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(
# 983 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in (
# 984 "FStar.TypeChecker.Tc.fst"
let _70_1490 = (FStar_List.fold_left2 (fun _70_1471 _70_1474 _70_1477 -> (match ((_70_1471, _70_1474, _70_1477)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(
# 985 "FStar.TypeChecker.Tc.fst"
let _70_1478 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 986 "FStar.TypeChecker.Tc.fst"
let _70_1483 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_70_1483) with
| (e, c, g) -> begin
(
# 987 "FStar.TypeChecker.Tc.fst"
let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (
# 988 "FStar.TypeChecker.Tc.fst"
let g = (let _151_575 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _151_575 g))
in (
# 989 "FStar.TypeChecker.Tc.fst"
let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _151_579 = (let _151_577 = (let _151_576 = (FStar_Syntax_Syntax.as_arg e)
in (_151_576)::[])
in (FStar_List.append seen _151_577))
in (let _151_578 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_151_579, _151_578, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_70_1490) with
| (args, guard, ghost) -> begin
(
# 993 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (
# 994 "FStar.TypeChecker.Tc.fst"
let c = if ghost then begin
(let _151_580 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _151_580 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (
# 995 "FStar.TypeChecker.Tc.fst"
let _70_1495 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_70_1495) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _70_1497 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (
# 1015 "FStar.TypeChecker.Tc.fst"
let _70_1504 = (FStar_Syntax_Subst.open_branch branch)
in (match (_70_1504) with
| (pattern, when_clause, branch_exp) -> begin
(
# 1016 "FStar.TypeChecker.Tc.fst"
let _70_1509 = branch
in (match (_70_1509) with
| (cpat, _70_1507, cbr) -> begin
(
# 1019 "FStar.TypeChecker.Tc.fst"
let tc_pat = (fun allow_implicits pat_t p0 -> (
# 1026 "FStar.TypeChecker.Tc.fst"
let _70_1517 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_70_1517) with
| (pat_bvs, exps, p) -> begin
(
# 1027 "FStar.TypeChecker.Tc.fst"
let _70_1518 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_592 = (FStar_Syntax_Print.pat_to_string p0)
in (let _151_591 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _151_592 _151_591)))
end else begin
()
end
in (
# 1029 "FStar.TypeChecker.Tc.fst"
let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (
# 1030 "FStar.TypeChecker.Tc.fst"
let _70_1524 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_70_1524) with
| (env1, _70_1523) -> begin
(
# 1031 "FStar.TypeChecker.Tc.fst"
let env1 = (
# 1031 "FStar.TypeChecker.Tc.fst"
let _70_1525 = env1
in {FStar_TypeChecker_Env.solver = _70_1525.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1525.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1525.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1525.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1525.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1525.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1525.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1525.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _70_1525.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1525.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1525.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_1525.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _70_1525.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _70_1525.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_1525.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_1525.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1525.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1525.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1525.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1525.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1525.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1032 "FStar.TypeChecker.Tc.fst"
let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (
# 1033 "FStar.TypeChecker.Tc.fst"
let _70_1564 = (let _151_615 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (
# 1034 "FStar.TypeChecker.Tc.fst"
let _70_1530 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_595 = (FStar_Syntax_Print.term_to_string e)
in (let _151_594 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _151_595 _151_594)))
end else begin
()
end
in (
# 1037 "FStar.TypeChecker.Tc.fst"
let _70_1535 = (tc_term env1 e)
in (match (_70_1535) with
| (e, lc, g) -> begin
(
# 1039 "FStar.TypeChecker.Tc.fst"
let _70_1536 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_597 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _151_596 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _151_597 _151_596)))
end else begin
()
end
in (
# 1042 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (
# 1043 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (
# 1044 "FStar.TypeChecker.Tc.fst"
let _70_1542 = (let _151_598 = (FStar_TypeChecker_Rel.discharge_guard env (
# 1044 "FStar.TypeChecker.Tc.fst"
let _70_1540 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _70_1540.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _70_1540.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _70_1540.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _151_598 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1045 "FStar.TypeChecker.Tc.fst"
let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (
# 1046 "FStar.TypeChecker.Tc.fst"
let uvars_to_string = (fun uvs -> (let _151_603 = (let _151_602 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _151_602 (FStar_List.map (fun _70_1550 -> (match (_70_1550) with
| (u, _70_1549) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _151_603 (FStar_String.concat ", "))))
in (
# 1047 "FStar.TypeChecker.Tc.fst"
let uvs1 = (FStar_Syntax_Free.uvars e')
in (
# 1048 "FStar.TypeChecker.Tc.fst"
let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (
# 1049 "FStar.TypeChecker.Tc.fst"
let _70_1558 = if (let _151_604 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _151_604)) then begin
(
# 1050 "FStar.TypeChecker.Tc.fst"
let unresolved = (let _151_605 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _151_605 FStar_Util.set_elements))
in (let _151_613 = (let _151_612 = (let _151_611 = (let _151_610 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _151_609 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _151_608 = (let _151_607 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _70_1557 -> (match (_70_1557) with
| (u, _70_1556) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _151_607 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _151_610 _151_609 _151_608))))
in (_151_611, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_151_612))
in (Prims.raise _151_613)))
end else begin
()
end
in (
# 1057 "FStar.TypeChecker.Tc.fst"
let _70_1560 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_614 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _151_614))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _151_615 FStar_List.unzip))
in (match (_70_1564) with
| (exps, norm_exps) -> begin
(
# 1062 "FStar.TypeChecker.Tc.fst"
let p = (FStar_TypeChecker_Util.decorate_pattern env p exps)
in (p, pat_bvs, pat_env, exps, norm_exps))
end))))
end))))
end)))
in (
# 1066 "FStar.TypeChecker.Tc.fst"
let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (
# 1067 "FStar.TypeChecker.Tc.fst"
let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (
# 1068 "FStar.TypeChecker.Tc.fst"
let _70_1571 = (let _151_616 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _151_616 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_70_1571) with
| (scrutinee_env, _70_1570) -> begin
(
# 1071 "FStar.TypeChecker.Tc.fst"
let _70_1577 = (tc_pat true pat_t pattern)
in (match (_70_1577) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(
# 1074 "FStar.TypeChecker.Tc.fst"
let _70_1587 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(
# 1081 "FStar.TypeChecker.Tc.fst"
let _70_1584 = (let _151_617 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _151_617 e))
in (match (_70_1584) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_70_1587) with
| (when_clause, g_when) -> begin
(
# 1085 "FStar.TypeChecker.Tc.fst"
let _70_1591 = (tc_term pat_env branch_exp)
in (match (_70_1591) with
| (branch_exp, c, g_branch) -> begin
(
# 1089 "FStar.TypeChecker.Tc.fst"
let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _151_619 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _151_618 -> Some (_151_618)) _151_619))
end)
in (
# 1096 "FStar.TypeChecker.Tc.fst"
let _70_1647 = (
# 1099 "FStar.TypeChecker.Tc.fst"
let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (
# 1100 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _70_1609 -> begin
(
# 1106 "FStar.TypeChecker.Tc.fst"
let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _151_623 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _151_622 -> Some (_151_622)) _151_623))
end))
end))) None))
in (
# 1111 "FStar.TypeChecker.Tc.fst"
let _70_1617 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_70_1617) with
| (c, g_branch) -> begin
(
# 1115 "FStar.TypeChecker.Tc.fst"
let _70_1642 = (match ((eqs, when_condition)) with
| (None, None) -> begin
(c, g_when)
end
| (Some (f), None) -> begin
(
# 1121 "FStar.TypeChecker.Tc.fst"
let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1122 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _151_626 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _151_625 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_151_626, _151_625)))))
end
| (Some (f), Some (w)) -> begin
(
# 1127 "FStar.TypeChecker.Tc.fst"
let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1128 "FStar.TypeChecker.Tc.fst"
let g_fw = (let _151_627 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_151_627))
in (let _151_630 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _151_629 = (let _151_628 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _151_628 g_when))
in (_151_630, _151_629)))))
end
| (None, Some (w)) -> begin
(
# 1133 "FStar.TypeChecker.Tc.fst"
let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (
# 1134 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _151_631 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_151_631, g_when))))
end)
in (match (_70_1642) with
| (c_weak, g_when_weak) -> begin
(
# 1139 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _151_633 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _151_632 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_151_633, _151_632, g_branch))))
end))
end)))
in (match (_70_1647) with
| (c, g_when, g_branch) -> begin
(
# 1157 "FStar.TypeChecker.Tc.fst"
let branch_guard = (
# 1159 "FStar.TypeChecker.Tc.fst"
let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (
# 1160 "FStar.TypeChecker.Tc.fst"
let discriminate = (fun scrutinee_tm f -> if ((let _151_643 = (let _151_642 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _151_642))
in (FStar_List.length _151_643)) > 1) then begin
(
# 1163 "FStar.TypeChecker.Tc.fst"
let disc = (let _151_644 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar None _151_644 (FStar_Ident.range_of_lid f.FStar_Syntax_Syntax.v)))
in (
# 1164 "FStar.TypeChecker.Tc.fst"
let disc = (let _151_646 = (let _151_645 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_151_645)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _151_646 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _151_647 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_151_647)::[])))
end else begin
[]
end)
in (
# 1168 "FStar.TypeChecker.Tc.fst"
let fail = (fun _70_1657 -> (match (()) with
| () -> begin
(let _151_653 = (let _151_652 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _151_651 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _151_650 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _151_652 _151_651 _151_650))))
in (FStar_All.failwith _151_653))
end))
in (
# 1174 "FStar.TypeChecker.Tc.fst"
let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (f, _70_1662) -> begin
f
end
| FStar_Syntax_Syntax.Tm_uinst (t, _70_1667) -> begin
(head_constructor t)
end
| _70_1671 -> begin
(fail ())
end))
in (
# 1179 "FStar.TypeChecker.Tc.fst"
let pat_exp = (let _151_656 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _151_656 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_70_1696) -> begin
(let _151_661 = (let _151_660 = (let _151_659 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _151_658 = (let _151_657 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_151_657)::[])
in (_151_659)::_151_658))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _151_660 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_151_661)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 1188 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _151_662 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _151_662))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 1193 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(
# 1196 "FStar.TypeChecker.Tc.fst"
let sub_term_guards = (let _151_668 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _70_1714 -> (match (_70_1714) with
| (ei, _70_1713) -> begin
(
# 1197 "FStar.TypeChecker.Tc.fst"
let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (
# 1198 "FStar.TypeChecker.Tc.fst"
let sub_term = (let _151_667 = (FStar_Syntax_Syntax.fvar None projector f.FStar_Syntax_Syntax.p)
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
| _70_1719 -> begin
[]
end))))))
in (
# 1204 "FStar.TypeChecker.Tc.fst"
let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid scrutinee_tm.FStar_Syntax_Syntax.pos)
end else begin
(
# 1207 "FStar.TypeChecker.Tc.fst"
let t = (let _151_674 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _151_674))
in (
# 1208 "FStar.TypeChecker.Tc.fst"
let _70_1727 = (FStar_Syntax_Util.type_u ())
in (match (_70_1727) with
| (k, _70_1726) -> begin
(
# 1209 "FStar.TypeChecker.Tc.fst"
let _70_1733 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_70_1733) with
| (t, _70_1730, _70_1732) -> begin
t
end))
end)))
end)
in (
# 1213 "FStar.TypeChecker.Tc.fst"
let branch_guard = (let _151_675 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _151_675 FStar_Syntax_Util.mk_disj_l))
in (
# 1216 "FStar.TypeChecker.Tc.fst"
let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
in (
# 1222 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (
# 1224 "FStar.TypeChecker.Tc.fst"
let _70_1741 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
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
# 1238 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1241 "FStar.TypeChecker.Tc.fst"
let _70_1758 = (check_let_bound_def true env lb)
in (match (_70_1758) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(
# 1244 "FStar.TypeChecker.Tc.fst"
let _70_1770 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(
# 1247 "FStar.TypeChecker.Tc.fst"
let g1 = (let _151_680 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _151_680 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1248 "FStar.TypeChecker.Tc.fst"
let _70_1765 = (let _151_684 = (let _151_683 = (let _151_682 = (let _151_681 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _151_681))
in (_151_682)::[])
in (FStar_TypeChecker_Util.generalize env _151_683))
in (FStar_List.hd _151_684))
in (match (_70_1765) with
| (_70_1761, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_70_1770) with
| (g1, e1, univ_vars, c1) -> begin
(
# 1252 "FStar.TypeChecker.Tc.fst"
let _70_1780 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(
# 1254 "FStar.TypeChecker.Tc.fst"
let _70_1773 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_70_1773) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(
# 1257 "FStar.TypeChecker.Tc.fst"
let _70_1774 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
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
# 1261 "FStar.TypeChecker.Tc.fst"
let _70_1776 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _151_687 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _151_687)))
end
in (match (_70_1780) with
| (e2, c1) -> begin
(
# 1266 "FStar.TypeChecker.Tc.fst"
let cres = (let _151_688 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_688))
in (
# 1267 "FStar.TypeChecker.Tc.fst"
let _70_1782 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1269 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _151_689 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_151_689, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _70_1786 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1286 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1289 "FStar.TypeChecker.Tc.fst"
let env = (
# 1289 "FStar.TypeChecker.Tc.fst"
let _70_1797 = env
in {FStar_TypeChecker_Env.solver = _70_1797.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1797.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1797.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1797.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1797.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1797.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1797.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1797.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1797.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1797.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1797.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1797.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_1797.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _70_1797.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_1797.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_1797.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1797.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1797.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1797.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1797.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1797.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1290 "FStar.TypeChecker.Tc.fst"
let _70_1806 = (let _151_693 = (let _151_692 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _151_692 Prims.fst))
in (check_let_bound_def false _151_693 lb))
in (match (_70_1806) with
| (e1, _70_1802, c1, g1, annotated) -> begin
(
# 1291 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (
# 1292 "FStar.TypeChecker.Tc.fst"
let x = (
# 1292 "FStar.TypeChecker.Tc.fst"
let _70_1808 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _70_1808.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_1808.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (
# 1293 "FStar.TypeChecker.Tc.fst"
let _70_1813 = (let _151_695 = (let _151_694 = (FStar_Syntax_Syntax.mk_binder x)
in (_151_694)::[])
in (FStar_Syntax_Subst.open_term _151_695 e2))
in (match (_70_1813) with
| (xb, e2) -> begin
(
# 1294 "FStar.TypeChecker.Tc.fst"
let xbinder = (FStar_List.hd xb)
in (
# 1295 "FStar.TypeChecker.Tc.fst"
let x = (Prims.fst xbinder)
in (
# 1296 "FStar.TypeChecker.Tc.fst"
let _70_1819 = (let _151_696 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _151_696 e2))
in (match (_70_1819) with
| (e2, c2, g2) -> begin
(
# 1297 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (x), c2))
in (
# 1298 "FStar.TypeChecker.Tc.fst"
let e = (let _151_699 = (let _151_698 = (let _151_697 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _151_697))
in FStar_Syntax_Syntax.Tm_let (_151_698))
in (FStar_Syntax_Syntax.mk _151_699 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 1299 "FStar.TypeChecker.Tc.fst"
let x_eq_e1 = (let _151_702 = (let _151_701 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _151_701 e1))
in (FStar_All.pipe_left (fun _151_700 -> FStar_TypeChecker_Common.NonTrivial (_151_700)) _151_702))
in (
# 1300 "FStar.TypeChecker.Tc.fst"
let g2 = (let _151_704 = (let _151_703 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _151_703 g2))
in (FStar_TypeChecker_Rel.close_guard xb _151_704))
in (
# 1302 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if annotated then begin
(e, cres, guard)
end else begin
(
# 1306 "FStar.TypeChecker.Tc.fst"
let _70_1825 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end)))))
end))))
end))))
end)))
end
| _70_1828 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1315 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1318 "FStar.TypeChecker.Tc.fst"
let _70_1840 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_70_1840) with
| (lbs, e2) -> begin
(
# 1320 "FStar.TypeChecker.Tc.fst"
let _70_1843 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_1843) with
| (env0, topt) -> begin
(
# 1321 "FStar.TypeChecker.Tc.fst"
let _70_1846 = (build_let_rec_env true env0 lbs)
in (match (_70_1846) with
| (lbs, rec_env) -> begin
(
# 1322 "FStar.TypeChecker.Tc.fst"
let _70_1849 = (check_let_recs rec_env lbs)
in (match (_70_1849) with
| (lbs, g_lbs) -> begin
(
# 1323 "FStar.TypeChecker.Tc.fst"
let g_lbs = (let _151_707 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _151_707 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1325 "FStar.TypeChecker.Tc.fst"
let all_lb_names = (let _151_710 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _151_710 (fun _151_709 -> Some (_151_709))))
in (
# 1327 "FStar.TypeChecker.Tc.fst"
let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(
# 1333 "FStar.TypeChecker.Tc.fst"
let ecs = (let _151_714 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _151_713 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _151_713)))))
in (FStar_TypeChecker_Util.generalize env _151_714))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _70_1860 -> (match (_70_1860) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (
# 1340 "FStar.TypeChecker.Tc.fst"
let cres = (let _151_716 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_716))
in (
# 1341 "FStar.TypeChecker.Tc.fst"
let _70_1863 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1343 "FStar.TypeChecker.Tc.fst"
let _70_1867 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_70_1867) with
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
| _70_1869 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1354 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1357 "FStar.TypeChecker.Tc.fst"
let _70_1881 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_70_1881) with
| (lbs, e2) -> begin
(
# 1359 "FStar.TypeChecker.Tc.fst"
let _70_1884 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_1884) with
| (env0, topt) -> begin
(
# 1360 "FStar.TypeChecker.Tc.fst"
let _70_1887 = (build_let_rec_env false env0 lbs)
in (match (_70_1887) with
| (lbs, rec_env) -> begin
(
# 1361 "FStar.TypeChecker.Tc.fst"
let _70_1890 = (check_let_recs rec_env lbs)
in (match (_70_1890) with
| (lbs, g_lbs) -> begin
(
# 1363 "FStar.TypeChecker.Tc.fst"
let _70_1908 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _70_1893 _70_1902 -> (match ((_70_1893, _70_1902)) with
| ((bvs, env), {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _70_1900; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _70_1897; FStar_Syntax_Syntax.lbdef = _70_1895}) -> begin
(
# 1364 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env x ([], t))
in (let _151_724 = (let _151_723 = (
# 1365 "FStar.TypeChecker.Tc.fst"
let _70_1904 = (FStar_Util.left x)
in {FStar_Syntax_Syntax.ppname = _70_1904.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_1904.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (_151_723)::bvs)
in (_151_724, env)))
end)) ([], env)))
in (match (_70_1908) with
| (bvs, env) -> begin
(
# 1366 "FStar.TypeChecker.Tc.fst"
let bvs = (FStar_List.rev bvs)
in (
# 1368 "FStar.TypeChecker.Tc.fst"
let _70_1913 = (tc_term env e2)
in (match (_70_1913) with
| (e2, cres, g2) -> begin
(
# 1369 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (
# 1370 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (
# 1371 "FStar.TypeChecker.Tc.fst"
let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (
# 1372 "FStar.TypeChecker.Tc.fst"
let cres = (
# 1372 "FStar.TypeChecker.Tc.fst"
let _70_1917 = cres
in {FStar_Syntax_Syntax.eff_name = _70_1917.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _70_1917.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _70_1917.FStar_Syntax_Syntax.comp})
in (
# 1374 "FStar.TypeChecker.Tc.fst"
let _70_1922 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_70_1922) with
| (lbs, e2) -> begin
(
# 1375 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_70_1925) -> begin
(e, cres, guard)
end
| None -> begin
(
# 1379 "FStar.TypeChecker.Tc.fst"
let _70_1928 = (check_no_escape None env bvs tres)
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
| _70_1931 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (
# 1390 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1391 "FStar.TypeChecker.Tc.fst"
let _70_1964 = (FStar_List.fold_left (fun _70_1938 lb -> (match (_70_1938) with
| (lbs, env) -> begin
(
# 1392 "FStar.TypeChecker.Tc.fst"
let _70_1943 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_70_1943) with
| (univ_vars, t, check_t) -> begin
(
# 1393 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (
# 1394 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (
# 1395 "FStar.TypeChecker.Tc.fst"
let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(
# 1400 "FStar.TypeChecker.Tc.fst"
let _70_1952 = (let _151_731 = (let _151_730 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _151_730))
in (tc_check_tot_or_gtot_term (
# 1400 "FStar.TypeChecker.Tc.fst"
let _70_1946 = env0
in {FStar_TypeChecker_Env.solver = _70_1946.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1946.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1946.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1946.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1946.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1946.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1946.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1946.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1946.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1946.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1946.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1946.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_1946.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _70_1946.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _70_1946.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_1946.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1946.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1946.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1946.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1946.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1946.FStar_TypeChecker_Env.use_bv_sorts}) t _151_731))
in (match (_70_1952) with
| (t, _70_1950, g) -> begin
(
# 1401 "FStar.TypeChecker.Tc.fst"
let _70_1953 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (
# 1403 "FStar.TypeChecker.Tc.fst"
let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(
# 1405 "FStar.TypeChecker.Tc.fst"
let _70_1956 = env
in {FStar_TypeChecker_Env.solver = _70_1956.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1956.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1956.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1956.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1956.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1956.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1956.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1956.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1956.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1956.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1956.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1956.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _70_1956.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _70_1956.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_1956.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_1956.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1956.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1956.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1956.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1956.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1956.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (
# 1407 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1407 "FStar.TypeChecker.Tc.fst"
let _70_1959 = lb
in {FStar_Syntax_Syntax.lbname = _70_1959.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _70_1959.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_70_1964) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (
# 1414 "FStar.TypeChecker.Tc.fst"
let _70_1977 = (let _151_736 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 1415 "FStar.TypeChecker.Tc.fst"
let _70_1971 = (let _151_735 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _151_735 lb.FStar_Syntax_Syntax.lbdef))
in (match (_70_1971) with
| (e, c, g) -> begin
(
# 1416 "FStar.TypeChecker.Tc.fst"
let _70_1972 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1418 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _151_736 FStar_List.unzip))
in (match (_70_1977) with
| (lbs, gs) -> begin
(
# 1420 "FStar.TypeChecker.Tc.fst"
let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (
# 1434 "FStar.TypeChecker.Tc.fst"
let _70_1985 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_1985) with
| (env1, _70_1984) -> begin
(
# 1435 "FStar.TypeChecker.Tc.fst"
let e1 = lb.FStar_Syntax_Syntax.lbdef
in (
# 1438 "FStar.TypeChecker.Tc.fst"
let _70_1991 = (check_lbtyp top_level env lb)
in (match (_70_1991) with
| (topt, wf_annot, univ_vars, env1) -> begin
(
# 1440 "FStar.TypeChecker.Tc.fst"
let _70_1992 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1444 "FStar.TypeChecker.Tc.fst"
let _70_1999 = (tc_maybe_toplevel_term (
# 1444 "FStar.TypeChecker.Tc.fst"
let _70_1994 = env1
in {FStar_TypeChecker_Env.solver = _70_1994.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1994.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1994.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1994.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1994.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1994.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1994.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1994.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1994.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1994.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1994.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1994.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_1994.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _70_1994.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_1994.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_1994.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1994.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1994.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1994.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1994.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1994.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_70_1999) with
| (e1, c1, g1) -> begin
(
# 1447 "FStar.TypeChecker.Tc.fst"
let _70_2003 = (let _151_743 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _70_2000 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _151_743 e1 c1 wf_annot))
in (match (_70_2003) with
| (c1, guard_f) -> begin
(
# 1450 "FStar.TypeChecker.Tc.fst"
let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (
# 1452 "FStar.TypeChecker.Tc.fst"
let _70_2005 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
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
# 1464 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 1467 "FStar.TypeChecker.Tc.fst"
let _70_2012 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _70_2015 -> begin
(
# 1471 "FStar.TypeChecker.Tc.fst"
let _70_2018 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_70_2018) with
| (univ_vars, t) -> begin
(
# 1472 "FStar.TypeChecker.Tc.fst"
let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _151_749 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _151_749))
end else begin
(
# 1479 "FStar.TypeChecker.Tc.fst"
let _70_2023 = (FStar_Syntax_Util.type_u ())
in (match (_70_2023) with
| (k, _70_2022) -> begin
(
# 1480 "FStar.TypeChecker.Tc.fst"
let _70_2028 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_70_2028) with
| (t, _70_2026, g) -> begin
(
# 1481 "FStar.TypeChecker.Tc.fst"
let _70_2029 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _151_752 = (let _151_750 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _151_750))
in (let _151_751 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _151_752 _151_751)))
end else begin
()
end
in (
# 1485 "FStar.TypeChecker.Tc.fst"
let t = (norm env1 t)
in (let _151_753 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _151_753))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _70_2035 -> (match (_70_2035) with
| (x, imp) -> begin
(
# 1490 "FStar.TypeChecker.Tc.fst"
let _70_2038 = (FStar_Syntax_Util.type_u ())
in (match (_70_2038) with
| (tu, u) -> begin
(
# 1491 "FStar.TypeChecker.Tc.fst"
let _70_2043 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_70_2043) with
| (t, _70_2041, g) -> begin
(
# 1492 "FStar.TypeChecker.Tc.fst"
let x = ((
# 1492 "FStar.TypeChecker.Tc.fst"
let _70_2044 = x
in {FStar_Syntax_Syntax.ppname = _70_2044.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_2044.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (
# 1493 "FStar.TypeChecker.Tc.fst"
let _70_2047 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
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
# 1498 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_TypeChecker_Rel.trivial_guard, [])
end
| b::bs -> begin
(
# 1501 "FStar.TypeChecker.Tc.fst"
let _70_2062 = (tc_binder env b)
in (match (_70_2062) with
| (b, env', g, u) -> begin
(
# 1502 "FStar.TypeChecker.Tc.fst"
let _70_2067 = (aux env' bs)
in (match (_70_2067) with
| (bs, env', g', us) -> begin
(let _151_766 = (let _151_765 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _151_765))
in ((b)::bs, env', _151_766, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (
# 1507 "FStar.TypeChecker.Tc.fst"
let tc_args = (fun env args -> (FStar_List.fold_right (fun _70_2075 _70_2078 -> (match ((_70_2075, _70_2078)) with
| ((t, imp), (args, g)) -> begin
(
# 1511 "FStar.TypeChecker.Tc.fst"
let _70_2083 = (tc_term env t)
in (match (_70_2083) with
| (t, _70_2081, g') -> begin
(let _151_775 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _151_775))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _70_2087 -> (match (_70_2087) with
| (pats, g) -> begin
(
# 1514 "FStar.TypeChecker.Tc.fst"
let _70_2090 = (tc_args env p)
in (match (_70_2090) with
| (args, g') -> begin
(let _151_778 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _151_778))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1519 "FStar.TypeChecker.Tc.fst"
let _70_2096 = (tc_maybe_toplevel_term env e)
in (match (_70_2096) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(
# 1522 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (
# 1523 "FStar.TypeChecker.Tc.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 1524 "FStar.TypeChecker.Tc.fst"
let _70_2099 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_781 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _151_781))
end else begin
()
end
in (
# 1525 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 1526 "FStar.TypeChecker.Tc.fst"
let _70_2104 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _151_782 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_151_782, false))
end else begin
(let _151_783 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_151_783, true))
end
in (match (_70_2104) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _151_784 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _151_784))
end
| _70_2108 -> begin
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
# 1540 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))

# 1544 "FStar.TypeChecker.Tc.fst"
let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (
# 1545 "FStar.TypeChecker.Tc.fst"
let _70_2118 = (tc_tot_or_gtot_term env t)
in (match (_70_2118) with
| (t, c, g) -> begin
(
# 1546 "FStar.TypeChecker.Tc.fst"
let _70_2119 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))

# 1549 "FStar.TypeChecker.Tc.fst"
let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (
# 1550 "FStar.TypeChecker.Tc.fst"
let _70_2127 = (tc_check_tot_or_gtot_term env t k)
in (match (_70_2127) with
| (t, c, g) -> begin
(
# 1551 "FStar.TypeChecker.Tc.fst"
let _70_2128 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))

# 1554 "FStar.TypeChecker.Tc.fst"
let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _151_810 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _151_810)))

# 1557 "FStar.TypeChecker.Tc.fst"
let check_nogen = (fun env t k -> (
# 1558 "FStar.TypeChecker.Tc.fst"
let t = (tc_check_trivial_guard env t k)
in (let _151_814 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _151_814))))

# 1561 "FStar.TypeChecker.Tc.fst"
let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (
# 1562 "FStar.TypeChecker.Tc.fst"
let _70_2143 = (tc_binders env tps)
in (match (_70_2143) with
| (tps, env, g, us) -> begin
(
# 1563 "FStar.TypeChecker.Tc.fst"
let _70_2144 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))

# 1566 "FStar.TypeChecker.Tc.fst"
let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (
# 1567 "FStar.TypeChecker.Tc.fst"
let fail = (fun _70_2150 -> (match (()) with
| () -> begin
(let _151_829 = (let _151_828 = (let _151_827 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_151_827, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_151_828))
in (Prims.raise _151_829))
end))
in (
# 1568 "FStar.TypeChecker.Tc.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1571 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _70_2167)::(wp, _70_2163)::(_wlp, _70_2159)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _70_2171 -> begin
(fail ())
end))
end
| _70_2173 -> begin
(fail ())
end))))

# 1578 "FStar.TypeChecker.Tc.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 1581 "FStar.TypeChecker.Tc.fst"
let _70_2180 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_70_2180) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _70_2182 -> begin
(
# 1584 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow binders c)
in (
# 1585 "FStar.TypeChecker.Tc.fst"
let _70_2186 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_70_2186) with
| (uvs, t') -> begin
(match ((let _151_836 = (FStar_Syntax_Subst.compress t')
in _151_836.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _70_2192 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 1590 "FStar.TypeChecker.Tc.fst"
let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (
# 1591 "FStar.TypeChecker.Tc.fst"
let fail = (fun t -> (let _151_847 = (let _151_846 = (let _151_845 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_151_845, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_151_846))
in (Prims.raise _151_847)))
in (match ((let _151_848 = (FStar_Syntax_Subst.compress signature)
in _151_848.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1594 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _70_2213)::(wp, _70_2209)::(_wlp, _70_2205)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _70_2217 -> begin
(fail signature)
end))
end
| _70_2219 -> begin
(fail signature)
end)))

# 1601 "FStar.TypeChecker.Tc.fst"
let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (
# 1602 "FStar.TypeChecker.Tc.fst"
let _70_2224 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_70_2224) with
| (a, wp) -> begin
(
# 1603 "FStar.TypeChecker.Tc.fst"
let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _70_2227 -> begin
(
# 1607 "FStar.TypeChecker.Tc.fst"
let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (
# 1608 "FStar.TypeChecker.Tc.fst"
let op = (fun ts -> (
# 1609 "FStar.TypeChecker.Tc.fst"
let _70_2231 = ()
in (
# 1610 "FStar.TypeChecker.Tc.fst"
let t0 = (Prims.snd ts)
in (
# 1611 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (
# 1613 "FStar.TypeChecker.Tc.fst"
let _70_2235 = ed
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
in {FStar_Syntax_Syntax.qualifiers = _70_2235.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _70_2235.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _70_2235.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _70_2235.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _70_2235.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _151_867; FStar_Syntax_Syntax.bind_wp = _151_866; FStar_Syntax_Syntax.bind_wlp = _151_865; FStar_Syntax_Syntax.if_then_else = _151_864; FStar_Syntax_Syntax.ite_wp = _151_863; FStar_Syntax_Syntax.ite_wlp = _151_862; FStar_Syntax_Syntax.wp_binop = _151_861; FStar_Syntax_Syntax.wp_as_type = _151_860; FStar_Syntax_Syntax.close_wp = _151_859; FStar_Syntax_Syntax.assert_p = _151_858; FStar_Syntax_Syntax.assume_p = _151_857; FStar_Syntax_Syntax.null_wp = _151_856; FStar_Syntax_Syntax.trivial = _151_855}))))))))))))))))
end)
in (ed, a, wp))
end)))

# 1629 "FStar.TypeChecker.Tc.fst"
let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (
# 1630 "FStar.TypeChecker.Tc.fst"
let _70_2240 = ()
in (
# 1631 "FStar.TypeChecker.Tc.fst"
let _70_2244 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_70_2244) with
| (binders_un, signature_un) -> begin
(
# 1632 "FStar.TypeChecker.Tc.fst"
let _70_2249 = (tc_tparams env0 binders_un)
in (match (_70_2249) with
| (binders, env, _70_2248) -> begin
(
# 1633 "FStar.TypeChecker.Tc.fst"
let _70_2253 = (tc_trivial_guard env signature_un)
in (match (_70_2253) with
| (signature, _70_2252) -> begin
(
# 1634 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1634 "FStar.TypeChecker.Tc.fst"
let _70_2254 = ed
in {FStar_Syntax_Syntax.qualifiers = _70_2254.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _70_2254.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _70_2254.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _70_2254.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _70_2254.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _70_2254.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = _70_2254.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _70_2254.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _70_2254.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = _70_2254.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _70_2254.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _70_2254.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _70_2254.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _70_2254.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _70_2254.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _70_2254.FStar_Syntax_Syntax.trivial})
in (
# 1637 "FStar.TypeChecker.Tc.fst"
let _70_2260 = (open_effect_decl env ed)
in (match (_70_2260) with
| (ed, a, wp_a) -> begin
(
# 1638 "FStar.TypeChecker.Tc.fst"
let get_effect_signature = (fun _70_2262 -> (match (()) with
| () -> begin
(
# 1639 "FStar.TypeChecker.Tc.fst"
let _70_2266 = (tc_trivial_guard env signature_un)
in (match (_70_2266) with
| (signature, _70_2265) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (
# 1643 "FStar.TypeChecker.Tc.fst"
let env = (let _151_874 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _151_874))
in (
# 1645 "FStar.TypeChecker.Tc.fst"
let _70_2268 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _151_877 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _151_876 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _151_875 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checked effect signature: %s %s : %s\n" _151_877 _151_876 _151_875))))
end else begin
()
end
in (
# 1651 "FStar.TypeChecker.Tc.fst"
let check_and_gen' = (fun env _70_2275 k -> (match (_70_2275) with
| (_70_2273, t) -> begin
(check_and_gen env t k)
end))
in (
# 1654 "FStar.TypeChecker.Tc.fst"
let ret = (
# 1655 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_889 = (let _151_887 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_886 = (let _151_885 = (let _151_884 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _151_884))
in (_151_885)::[])
in (_151_887)::_151_886))
in (let _151_888 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _151_889 _151_888)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (
# 1658 "FStar.TypeChecker.Tc.fst"
let bind_wp = (
# 1659 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1660 "FStar.TypeChecker.Tc.fst"
let _70_2282 = (get_effect_signature ())
in (match (_70_2282) with
| (b, wp_b) -> begin
(
# 1661 "FStar.TypeChecker.Tc.fst"
let a_wp_b = (let _151_893 = (let _151_891 = (let _151_890 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _151_890))
in (_151_891)::[])
in (let _151_892 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _151_893 _151_892)))
in (
# 1662 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = a_wp_b
in (
# 1663 "FStar.TypeChecker.Tc.fst"
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
# 1669 "FStar.TypeChecker.Tc.fst"
let bind_wlp = (
# 1670 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1671 "FStar.TypeChecker.Tc.fst"
let _70_2290 = (get_effect_signature ())
in (match (_70_2290) with
| (b, wlp_b) -> begin
(
# 1672 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = (let _151_910 = (let _151_908 = (let _151_907 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _151_907))
in (_151_908)::[])
in (let _151_909 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _151_910 _151_909)))
in (
# 1673 "FStar.TypeChecker.Tc.fst"
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
# 1679 "FStar.TypeChecker.Tc.fst"
let if_then_else = (
# 1680 "FStar.TypeChecker.Tc.fst"
let p = (let _151_921 = (let _151_920 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_920 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _151_921))
in (
# 1681 "FStar.TypeChecker.Tc.fst"
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
# 1687 "FStar.TypeChecker.Tc.fst"
let ite_wp = (
# 1688 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1689 "FStar.TypeChecker.Tc.fst"
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
# 1695 "FStar.TypeChecker.Tc.fst"
let ite_wlp = (
# 1696 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1697 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_942 = (let _151_940 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_939 = (let _151_938 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (_151_938)::[])
in (_151_940)::_151_939))
in (let _151_941 = (FStar_Syntax_Syntax.mk_Total wlp_a)
in (FStar_Syntax_Util.arrow _151_942 _151_941)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wlp expected_k)))
in (
# 1702 "FStar.TypeChecker.Tc.fst"
let wp_binop = (
# 1703 "FStar.TypeChecker.Tc.fst"
let bin_op = (
# 1704 "FStar.TypeChecker.Tc.fst"
let _70_2305 = (FStar_Syntax_Util.type_u ())
in (match (_70_2305) with
| (t1, u1) -> begin
(
# 1705 "FStar.TypeChecker.Tc.fst"
let _70_2308 = (FStar_Syntax_Util.type_u ())
in (match (_70_2308) with
| (t2, u2) -> begin
(
# 1706 "FStar.TypeChecker.Tc.fst"
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
# 1708 "FStar.TypeChecker.Tc.fst"
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
# 1715 "FStar.TypeChecker.Tc.fst"
let wp_as_type = (
# 1716 "FStar.TypeChecker.Tc.fst"
let _70_2316 = (FStar_Syntax_Util.type_u ())
in (match (_70_2316) with
| (t, _70_2315) -> begin
(
# 1717 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_962 = (let _151_960 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_959 = (let _151_958 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_958)::[])
in (_151_960)::_151_959))
in (let _151_961 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _151_962 _151_961)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (
# 1722 "FStar.TypeChecker.Tc.fst"
let close_wp = (
# 1723 "FStar.TypeChecker.Tc.fst"
let b = (let _151_964 = (let _151_963 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_963 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _151_964))
in (
# 1724 "FStar.TypeChecker.Tc.fst"
let b_wp_a = (let _151_968 = (let _151_966 = (let _151_965 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _151_965))
in (_151_966)::[])
in (let _151_967 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_968 _151_967)))
in (
# 1725 "FStar.TypeChecker.Tc.fst"
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
# 1729 "FStar.TypeChecker.Tc.fst"
let assert_p = (
# 1730 "FStar.TypeChecker.Tc.fst"
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
# 1736 "FStar.TypeChecker.Tc.fst"
let assume_p = (
# 1737 "FStar.TypeChecker.Tc.fst"
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
# 1743 "FStar.TypeChecker.Tc.fst"
let null_wp = (
# 1744 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_996 = (let _151_994 = (FStar_Syntax_Syntax.mk_binder a)
in (_151_994)::[])
in (let _151_995 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_996 _151_995)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (
# 1748 "FStar.TypeChecker.Tc.fst"
let trivial_wp = (
# 1749 "FStar.TypeChecker.Tc.fst"
let _70_2332 = (FStar_Syntax_Util.type_u ())
in (match (_70_2332) with
| (t, _70_2331) -> begin
(
# 1750 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1001 = (let _151_999 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_998 = (let _151_997 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_997)::[])
in (_151_999)::_151_998))
in (let _151_1000 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _151_1001 _151_1000)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (
# 1756 "FStar.TypeChecker.Tc.fst"
let t = (let _151_1002 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _151_1002))
in (
# 1757 "FStar.TypeChecker.Tc.fst"
let _70_2338 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_70_2338) with
| (univs, t) -> begin
(
# 1758 "FStar.TypeChecker.Tc.fst"
let _70_2354 = (match ((let _151_1004 = (let _151_1003 = (FStar_Syntax_Subst.compress t)
in _151_1003.FStar_Syntax_Syntax.n)
in (binders, _151_1004))) with
| ([], _70_2341) -> begin
([], t)
end
| (_70_2344, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _70_2351 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_70_2354) with
| (binders, signature) -> begin
(
# 1762 "FStar.TypeChecker.Tc.fst"
let close = (fun ts -> (let _151_1007 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _151_1007)))
in (
# 1763 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1763 "FStar.TypeChecker.Tc.fst"
let _70_2357 = ed
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
in {FStar_Syntax_Syntax.qualifiers = _70_2357.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _70_2357.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _151_1020; FStar_Syntax_Syntax.bind_wp = _151_1019; FStar_Syntax_Syntax.bind_wlp = _151_1018; FStar_Syntax_Syntax.if_then_else = _151_1017; FStar_Syntax_Syntax.ite_wp = _151_1016; FStar_Syntax_Syntax.ite_wlp = _151_1015; FStar_Syntax_Syntax.wp_binop = _151_1014; FStar_Syntax_Syntax.wp_as_type = _151_1013; FStar_Syntax_Syntax.close_wp = _151_1012; FStar_Syntax_Syntax.assert_p = _151_1011; FStar_Syntax_Syntax.assume_p = _151_1010; FStar_Syntax_Syntax.null_wp = _151_1009; FStar_Syntax_Syntax.trivial = _151_1008}))))))))))))))
in (
# 1781 "FStar.TypeChecker.Tc.fst"
let _70_2360 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
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

# 1785 "FStar.TypeChecker.Tc.fst"
let tc_lex_t = (fun env ses quals lids -> (
# 1792 "FStar.TypeChecker.Tc.fst"
let _70_2366 = ()
in (
# 1793 "FStar.TypeChecker.Tc.fst"
let _70_2374 = ()
in (match (ses) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _70_2403, _70_2405, [], r)::FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _70_2394, r1)::FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _70_2383, r2)::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(
# 1808 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (
# 1809 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (
# 1810 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (
# 1811 "FStar.TypeChecker.Tc.fst"
let tc = FStar_Syntax_Syntax.Sig_inductive_typ ((lex_t, (u)::[], [], t, [], (FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[], [], r))
in (
# 1813 "FStar.TypeChecker.Tc.fst"
let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (
# 1814 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (let _151_1028 = (let _151_1027 = (let _151_1026 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid r1)
in (_151_1026, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_151_1027))
in (FStar_Syntax_Syntax.mk _151_1028 None r1))
in (
# 1815 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (
# 1816 "FStar.TypeChecker.Tc.fst"
let dc_lextop = FStar_Syntax_Syntax.Sig_datacon ((lex_top, (utop)::[], lex_top_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r1))
in (
# 1818 "FStar.TypeChecker.Tc.fst"
let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1819 "FStar.TypeChecker.Tc.fst"
let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1820 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (
# 1821 "FStar.TypeChecker.Tc.fst"
let a = (let _151_1029 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _151_1029))
in (
# 1822 "FStar.TypeChecker.Tc.fst"
let hd = (let _151_1030 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _151_1030))
in (
# 1823 "FStar.TypeChecker.Tc.fst"
let tl = (let _151_1034 = (let _151_1033 = (let _151_1032 = (let _151_1031 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid r2)
in (_151_1031, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_151_1032))
in (FStar_Syntax_Syntax.mk _151_1033 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _151_1034))
in (
# 1824 "FStar.TypeChecker.Tc.fst"
let res = (let _151_1037 = (let _151_1036 = (let _151_1035 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid r2)
in (_151_1035, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_151_1036))
in (FStar_Syntax_Syntax.mk _151_1037 None r2))
in (let _151_1038 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _151_1038))))))
in (
# 1826 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (
# 1827 "FStar.TypeChecker.Tc.fst"
let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _151_1040 = (let _151_1039 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _151_1039))
in FStar_Syntax_Syntax.Sig_bundle (_151_1040)))))))))))))))
end
| _70_2429 -> begin
(let _151_1042 = (let _151_1041 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _151_1041))
in (FStar_All.failwith _151_1042))
end))))

# 1833 "FStar.TypeChecker.Tc.fst"
let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (
# 1896 "FStar.TypeChecker.Tc.fst"
let warn_positivity = (fun l r -> (let _151_1056 = (let _151_1055 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _151_1055))
in (FStar_TypeChecker_Errors.warn r _151_1056)))
in (
# 1898 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1901 "FStar.TypeChecker.Tc.fst"
let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(
# 1906 "FStar.TypeChecker.Tc.fst"
let _70_2451 = ()
in (
# 1907 "FStar.TypeChecker.Tc.fst"
let _70_2453 = (warn_positivity tc r)
in (
# 1908 "FStar.TypeChecker.Tc.fst"
let _70_2457 = (FStar_Syntax_Subst.open_term tps k)
in (match (_70_2457) with
| (tps, k) -> begin
(
# 1909 "FStar.TypeChecker.Tc.fst"
let _70_2461 = (tc_tparams env tps)
in (match (_70_2461) with
| (tps, env_tps, us) -> begin
(
# 1910 "FStar.TypeChecker.Tc.fst"
let _70_2464 = (FStar_Syntax_Util.arrow_formals k)
in (match (_70_2464) with
| (indices, t) -> begin
(
# 1911 "FStar.TypeChecker.Tc.fst"
let _70_2468 = (tc_tparams env_tps indices)
in (match (_70_2468) with
| (indices, env', us') -> begin
(
# 1912 "FStar.TypeChecker.Tc.fst"
let _70_2472 = (tc_trivial_guard env' t)
in (match (_70_2472) with
| (t, _70_2471) -> begin
(
# 1913 "FStar.TypeChecker.Tc.fst"
let k = (let _151_1061 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _151_1061))
in (
# 1914 "FStar.TypeChecker.Tc.fst"
let _70_2476 = (FStar_Syntax_Util.type_u ())
in (match (_70_2476) with
| (t_type, u) -> begin
(
# 1915 "FStar.TypeChecker.Tc.fst"
let _70_2477 = (let _151_1062 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _151_1062))
in (
# 1917 "FStar.TypeChecker.Tc.fst"
let t_tc = (let _151_1063 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _151_1063))
in (
# 1918 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 1919 "FStar.TypeChecker.Tc.fst"
let k = (FStar_Syntax_Subst.close tps k)
in (let _151_1064 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (tc)) ([], t_tc))
in (_151_1064, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u))))))
end)))
end))
end))
end))
end))
end))))
end
| _70_2483 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1926 "FStar.TypeChecker.Tc.fst"
let positive_if_pure = (fun _70_2485 l -> ())
in (
# 1929 "FStar.TypeChecker.Tc.fst"
let tc_data = (fun env tcs _70_6 -> (match (_70_6) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(
# 1931 "FStar.TypeChecker.Tc.fst"
let _70_2502 = ()
in (
# 1933 "FStar.TypeChecker.Tc.fst"
let _70_2537 = (
# 1934 "FStar.TypeChecker.Tc.fst"
let tps_u_opt = (FStar_Util.find_map tcs (fun _70_2506 -> (match (_70_2506) with
| (se, u_tc) -> begin
if (let _151_1077 = (let _151_1076 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _151_1076))
in (FStar_Ident.lid_equals tc_lid _151_1077)) then begin
(
# 1936 "FStar.TypeChecker.Tc.fst"
let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_70_2508, _70_2510, tps, _70_2513, _70_2515, _70_2517, _70_2519, _70_2521) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _70_2527 -> (match (_70_2527) with
| (x, _70_2526) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _70_2529 -> begin
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
in (match (_70_2537) with
| (tps, u_tc) -> begin
(
# 1949 "FStar.TypeChecker.Tc.fst"
let _70_2557 = (match ((let _151_1079 = (FStar_Syntax_Subst.compress t)
in _151_1079.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(
# 1954 "FStar.TypeChecker.Tc.fst"
let _70_2545 = (FStar_Util.first_N ntps bs)
in (match (_70_2545) with
| (_70_2543, bs') -> begin
(
# 1955 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (
# 1956 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _70_2551 -> (match (_70_2551) with
| (x, _70_2550) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _151_1082 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _151_1082))))
end))
end
| _70_2554 -> begin
([], t)
end)
in (match (_70_2557) with
| (arguments, result) -> begin
(
# 1960 "FStar.TypeChecker.Tc.fst"
let _70_2558 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1085 = (FStar_Syntax_Print.lid_to_string c)
in (let _151_1084 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _151_1083 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _151_1085 _151_1084 _151_1083))))
end else begin
()
end
in (
# 1966 "FStar.TypeChecker.Tc.fst"
let _70_2563 = (tc_tparams env arguments)
in (match (_70_2563) with
| (arguments, env', us) -> begin
(
# 1967 "FStar.TypeChecker.Tc.fst"
let _70_2567 = (tc_trivial_guard env' result)
in (match (_70_2567) with
| (result, _70_2566) -> begin
(
# 1968 "FStar.TypeChecker.Tc.fst"
let _70_2571 = (FStar_Syntax_Util.head_and_args result)
in (match (_70_2571) with
| (head, _70_2570) -> begin
(
# 1969 "FStar.TypeChecker.Tc.fst"
let _70_2579 = (match ((let _151_1086 = (FStar_Syntax_Subst.compress head)
in _151_1086.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _70_2574) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v tc_lid) -> begin
()
end
| _70_2578 -> begin
(let _151_1090 = (let _151_1089 = (let _151_1088 = (let _151_1087 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _151_1087))
in (_151_1088, r))
in FStar_Syntax_Syntax.Error (_151_1089))
in (Prims.raise _151_1090))
end)
in (
# 1972 "FStar.TypeChecker.Tc.fst"
let g = (FStar_List.fold_left2 (fun g _70_2585 u_x -> (match (_70_2585) with
| (x, _70_2584) -> begin
(
# 1973 "FStar.TypeChecker.Tc.fst"
let _70_2587 = ()
in (let _151_1094 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _151_1094)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (
# 1979 "FStar.TypeChecker.Tc.fst"
let t = (let _151_1098 = (let _151_1096 = (FStar_All.pipe_right tps (FStar_List.map (fun _70_2593 -> (match (_70_2593) with
| (x, _70_2592) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _151_1096 arguments))
in (let _151_1097 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _151_1098 _151_1097)))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _70_2596 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1987 "FStar.TypeChecker.Tc.fst"
let generalize_and_inst_within = (fun env g tcs datas -> (
# 1988 "FStar.TypeChecker.Tc.fst"
let _70_2602 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 1989 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _70_7 -> (match (_70_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_70_2606, _70_2608, tps, k, _70_2612, _70_2614, _70_2616, _70_2618) -> begin
(let _151_1109 = (let _151_1108 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _151_1108))
in (FStar_Syntax_Syntax.null_binder _151_1109))
end
| _70_2622 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 1992 "FStar.TypeChecker.Tc.fst"
let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _70_8 -> (match (_70_8) with
| FStar_Syntax_Syntax.Sig_datacon (_70_2626, _70_2628, t, _70_2631, _70_2633, _70_2635, _70_2637, _70_2639) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _70_2643 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 1995 "FStar.TypeChecker.Tc.fst"
let t = (let _151_1111 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _151_1111))
in (
# 1996 "FStar.TypeChecker.Tc.fst"
let _70_2646 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1112 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _151_1112))
end else begin
()
end
in (
# 1997 "FStar.TypeChecker.Tc.fst"
let _70_2650 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_70_2650) with
| (uvs, t) -> begin
(
# 1998 "FStar.TypeChecker.Tc.fst"
let _70_2652 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1116 = (let _151_1114 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _151_1114 (FStar_String.concat ", ")))
in (let _151_1115 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _151_1116 _151_1115)))
end else begin
()
end
in (
# 2001 "FStar.TypeChecker.Tc.fst"
let _70_2656 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_70_2656) with
| (uvs, t) -> begin
(
# 2002 "FStar.TypeChecker.Tc.fst"
let _70_2660 = (FStar_Syntax_Util.arrow_formals t)
in (match (_70_2660) with
| (args, _70_2659) -> begin
(
# 2003 "FStar.TypeChecker.Tc.fst"
let _70_2663 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_70_2663) with
| (tc_types, data_types) -> begin
(
# 2004 "FStar.TypeChecker.Tc.fst"
let tcs = (FStar_List.map2 (fun _70_2667 se -> (match (_70_2667) with
| (x, _70_2666) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _70_2671, tps, _70_2674, mutuals, datas, quals, r) -> begin
(
# 2006 "FStar.TypeChecker.Tc.fst"
let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (
# 2007 "FStar.TypeChecker.Tc.fst"
let _70_2697 = (match ((let _151_1119 = (FStar_Syntax_Subst.compress ty)
in _151_1119.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 2009 "FStar.TypeChecker.Tc.fst"
let _70_2688 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_70_2688) with
| (tps, rest) -> begin
(
# 2010 "FStar.TypeChecker.Tc.fst"
let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _70_2691 -> begin
(let _151_1120 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _151_1120 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _70_2694 -> begin
([], ty)
end)
in (match (_70_2697) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _70_2699 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (
# 2020 "FStar.TypeChecker.Tc.fst"
let datas = (match (uvs) with
| [] -> begin
datas
end
| _70_2703 -> begin
(
# 2023 "FStar.TypeChecker.Tc.fst"
let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _151_1121 -> FStar_Syntax_Syntax.U_name (_151_1121))))
in (
# 2024 "FStar.TypeChecker.Tc.fst"
let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _70_9 -> (match (_70_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _70_2708, _70_2710, _70_2712, _70_2714, _70_2716, _70_2718, _70_2720) -> begin
(tc, uvs_universes)
end
| _70_2724 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _70_2729 d -> (match (_70_2729) with
| (t, _70_2728) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _70_2733, _70_2735, tc, ntps, quals, mutuals, r) -> begin
(
# 2028 "FStar.TypeChecker.Tc.fst"
let ty = (let _151_1125 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _151_1125 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _70_2745 -> begin
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
# 2034 "FStar.TypeChecker.Tc.fst"
let _70_2755 = (FStar_All.pipe_right ses (FStar_List.partition (fun _70_10 -> (match (_70_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_70_2749) -> begin
true
end
| _70_2752 -> begin
false
end))))
in (match (_70_2755) with
| (tys, datas) -> begin
(
# 2036 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2039 "FStar.TypeChecker.Tc.fst"
let _70_2772 = (FStar_List.fold_right (fun tc _70_2761 -> (match (_70_2761) with
| (env, all_tcs, g) -> begin
(
# 2040 "FStar.TypeChecker.Tc.fst"
let _70_2765 = (tc_tycon env tc)
in (match (_70_2765) with
| (env, tc, tc_u) -> begin
(
# 2041 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (
# 2042 "FStar.TypeChecker.Tc.fst"
let _70_2767 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1129 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _151_1129))
end else begin
()
end
in (let _151_1130 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _151_1130))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_70_2772) with
| (env, tcs, g) -> begin
(
# 2049 "FStar.TypeChecker.Tc.fst"
let _70_2782 = (FStar_List.fold_right (fun se _70_2776 -> (match (_70_2776) with
| (datas, g) -> begin
(
# 2050 "FStar.TypeChecker.Tc.fst"
let _70_2779 = (tc_data env tcs se)
in (match (_70_2779) with
| (data, g') -> begin
(let _151_1133 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _151_1133))
end))
end)) datas ([], g))
in (match (_70_2782) with
| (datas, g) -> begin
(
# 2055 "FStar.TypeChecker.Tc.fst"
let _70_2785 = (let _151_1134 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _151_1134 datas))
in (match (_70_2785) with
| (tcs, datas) -> begin
(let _151_1136 = (let _151_1135 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _151_1135))
in FStar_Syntax_Syntax.Sig_bundle (_151_1136))
end))
end))
end)))
end)))))))))

# 2058 "FStar.TypeChecker.Tc.fst"
let rec tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.env) = (fun env se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(
# 2071 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2072 "FStar.TypeChecker.Tc.fst"
let se = (tc_lex_t env ses quals lids)
in (let _151_1141 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _151_1141))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(
# 2076 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2077 "FStar.TypeChecker.Tc.fst"
let se = (tc_inductive env ses quals lids)
in (let _151_1142 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _151_1142))))
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
# 2089 "FStar.TypeChecker.Tc.fst"
let _70_2821 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (
# 2090 "FStar.TypeChecker.Tc.fst"
let _70_2823 = (let _151_1143 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _151_1143 Prims.ignore))
in (se, env)))
end)
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(
# 2095 "FStar.TypeChecker.Tc.fst"
let ne = (tc_eff_decl env ne)
in (
# 2096 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (
# 2097 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(
# 2101 "FStar.TypeChecker.Tc.fst"
let _70_2838 = (let _151_1144 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _151_1144))
in (match (_70_2838) with
| (a, wp_a_src) -> begin
(
# 2102 "FStar.TypeChecker.Tc.fst"
let _70_2841 = (let _151_1145 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _151_1145))
in (match (_70_2841) with
| (b, wp_b_tgt) -> begin
(
# 2103 "FStar.TypeChecker.Tc.fst"
let wp_a_tgt = (let _151_1149 = (let _151_1148 = (let _151_1147 = (let _151_1146 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _151_1146))
in FStar_Syntax_Syntax.NT (_151_1147))
in (_151_1148)::[])
in (FStar_Syntax_Subst.subst _151_1149 wp_b_tgt))
in (
# 2104 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1154 = (let _151_1152 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1151 = (let _151_1150 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_151_1150)::[])
in (_151_1152)::_151_1151))
in (let _151_1153 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _151_1154 _151_1153)))
in (
# 2105 "FStar.TypeChecker.Tc.fst"
let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (
# 2106 "FStar.TypeChecker.Tc.fst"
let sub = (
# 2106 "FStar.TypeChecker.Tc.fst"
let _70_2845 = sub
in {FStar_Syntax_Syntax.source = _70_2845.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _70_2845.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
in (
# 2107 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect ((sub, r))
in (
# 2108 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(
# 2112 "FStar.TypeChecker.Tc.fst"
let _70_2858 = ()
in (
# 2113 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2114 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2115 "FStar.TypeChecker.Tc.fst"
let _70_2864 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_70_2864) with
| (tps, c) -> begin
(
# 2116 "FStar.TypeChecker.Tc.fst"
let _70_2868 = (tc_tparams env tps)
in (match (_70_2868) with
| (tps, env, us) -> begin
(
# 2117 "FStar.TypeChecker.Tc.fst"
let _70_2872 = (tc_comp env c)
in (match (_70_2872) with
| (c, u, g) -> begin
(
# 2118 "FStar.TypeChecker.Tc.fst"
let _70_2873 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2119 "FStar.TypeChecker.Tc.fst"
let tags = (FStar_All.pipe_right tags (FStar_List.map (fun _70_11 -> (match (_70_11) with
| FStar_Syntax_Syntax.DefaultEffect (None) -> begin
(
# 2121 "FStar.TypeChecker.Tc.fst"
let c' = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let _151_1157 = (FStar_All.pipe_right c'.FStar_Syntax_Syntax.effect_name (fun _151_1156 -> Some (_151_1156)))
in FStar_Syntax_Syntax.DefaultEffect (_151_1157)))
end
| t -> begin
t
end))))
in (
# 2124 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 2125 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.close_comp tps c)
in (
# 2126 "FStar.TypeChecker.Tc.fst"
let _70_2885 = (let _151_1158 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _151_1158))
in (match (_70_2885) with
| (uvs, t) -> begin
(
# 2127 "FStar.TypeChecker.Tc.fst"
let _70_2904 = (match ((let _151_1160 = (let _151_1159 = (FStar_Syntax_Subst.compress t)
in _151_1159.FStar_Syntax_Syntax.n)
in (tps, _151_1160))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_70_2888, c)) -> begin
([], c)
end
| (_70_2894, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _70_2901 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_70_2904) with
| (tps, c) -> begin
(
# 2131 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_effect_abbrev ((lid, uvs, tps, c, tags, r))
in (
# 2132 "FStar.TypeChecker.Tc.fst"
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
# 2136 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2137 "FStar.TypeChecker.Tc.fst"
let _70_2915 = ()
in (
# 2138 "FStar.TypeChecker.Tc.fst"
let k = (let _151_1161 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _151_1161))
in (
# 2139 "FStar.TypeChecker.Tc.fst"
let _70_2920 = (check_and_gen env t k)
in (match (_70_2920) with
| (uvs, t) -> begin
(
# 2140 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (
# 2141 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(
# 2145 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2146 "FStar.TypeChecker.Tc.fst"
let _70_2933 = (FStar_Syntax_Util.type_u ())
in (match (_70_2933) with
| (k, _70_2932) -> begin
(
# 2147 "FStar.TypeChecker.Tc.fst"
let phi = (let _151_1162 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _151_1162 (norm env)))
in (
# 2148 "FStar.TypeChecker.Tc.fst"
let _70_2935 = (FStar_TypeChecker_Util.check_uvars r phi)
in (
# 2149 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))
in (
# 2150 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(
# 2154 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2155 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (
# 2156 "FStar.TypeChecker.Tc.fst"
let _70_2948 = (tc_term env e)
in (match (_70_2948) with
| (e, c, g1) -> begin
(
# 2157 "FStar.TypeChecker.Tc.fst"
let _70_2953 = (let _151_1166 = (let _151_1163 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_151_1163))
in (let _151_1165 = (let _151_1164 = (c.FStar_Syntax_Syntax.comp ())
in (e, _151_1164))
in (check_expected_effect env _151_1166 _151_1165)))
in (match (_70_2953) with
| (e, _70_2951, g) -> begin
(
# 2158 "FStar.TypeChecker.Tc.fst"
let _70_2954 = (let _151_1167 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _151_1167))
in (
# 2159 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, r))
in (
# 2160 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(
# 2164 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2165 "FStar.TypeChecker.Tc.fst"
let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
if (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q')) then begin
Some (q)
end else begin
(let _151_1177 = (let _151_1176 = (let _151_1175 = (let _151_1174 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Inconsistent qualifier annotations on %s" _151_1174))
in (_151_1175, r))
in FStar_Syntax_Syntax.Error (_151_1176))
in (Prims.raise _151_1177))
end
end))
in (
# 2176 "FStar.TypeChecker.Tc.fst"
let _70_2998 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _70_2975 lb -> (match (_70_2975) with
| (gen, lbs, quals_opt) -> begin
(
# 2177 "FStar.TypeChecker.Tc.fst"
let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2178 "FStar.TypeChecker.Tc.fst"
let _70_2994 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(
# 2182 "FStar.TypeChecker.Tc.fst"
let quals_opt = (check_quals_eq lbname quals_opt quals)
in (
# 2183 "FStar.TypeChecker.Tc.fst"
let _70_2989 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _70_2988 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _151_1180 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _151_1180, quals_opt))))
end)
in (match (_70_2994) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_70_2998) with
| (should_generalize, lbs', quals_opt) -> begin
(
# 2192 "FStar.TypeChecker.Tc.fst"
let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _70_12 -> (match (_70_12) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _70_3007 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (
# 2199 "FStar.TypeChecker.Tc.fst"
let lbs' = (FStar_List.rev lbs')
in (
# 2202 "FStar.TypeChecker.Tc.fst"
let e = (let _151_1184 = (let _151_1183 = (let _151_1182 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _151_1182))
in FStar_Syntax_Syntax.Tm_let (_151_1183))
in (FStar_Syntax_Syntax.mk _151_1184 None r))
in (
# 2205 "FStar.TypeChecker.Tc.fst"
let _70_3041 = (match ((tc_maybe_toplevel_term (
# 2205 "FStar.TypeChecker.Tc.fst"
let _70_3011 = env
in {FStar_TypeChecker_Env.solver = _70_3011.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_3011.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_3011.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_3011.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_3011.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_3011.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_3011.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_3011.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_3011.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_3011.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_3011.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _70_3011.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _70_3011.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_3011.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_3011.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_3011.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_3011.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_3011.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_3011.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_3011.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _70_3018; FStar_Syntax_Syntax.pos = _70_3016; FStar_Syntax_Syntax.vars = _70_3014}, _70_3025, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(
# 2208 "FStar.TypeChecker.Tc.fst"
let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_70_3029, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _70_3035 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _70_3038 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_70_3041) with
| (se, lbs) -> begin
(
# 2215 "FStar.TypeChecker.Tc.fst"
let _70_3047 = if (log env) then begin
(let _151_1190 = (let _151_1189 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 2217 "FStar.TypeChecker.Tc.fst"
let should_log = (match ((let _151_1186 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _151_1186))) with
| None -> begin
true
end
| _70_3045 -> begin
false
end)
in if should_log then begin
(let _151_1188 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _151_1187 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _151_1188 _151_1187)))
end else begin
""
end))))
in (FStar_All.pipe_right _151_1189 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _151_1190))
end else begin
()
end
in (
# 2224 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end))))
end))

# 2228 "FStar.TypeChecker.Tc.fst"
let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (
# 2252 "FStar.TypeChecker.Tc.fst"
let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _70_13 -> (match (_70_13) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _70_3057 -> begin
false
end)))))
in (
# 2253 "FStar.TypeChecker.Tc.fst"
let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _70_3067 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_70_3069) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _70_3080, _70_3082) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _70_3088 -> (match (_70_3088) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _70_3094, _70_3096, quals, r) -> begin
(
# 2267 "FStar.TypeChecker.Tc.fst"
let dec = (let _151_1206 = (let _151_1205 = (let _151_1204 = (let _151_1203 = (let _151_1202 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _151_1202))
in FStar_Syntax_Syntax.Tm_arrow (_151_1203))
in (FStar_Syntax_Syntax.mk _151_1204 None r))
in (l, us, _151_1205, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_151_1206))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _70_3106, _70_3108, _70_3110, _70_3112, r) -> begin
(
# 2270 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _70_3118 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_70_3120, _70_3122, quals, _70_3125) -> begin
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
| _70_3144 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_70_3146) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _70_3162, _70_3164, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(
# 2300 "FStar.TypeChecker.Tc.fst"
let lid = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals lid))) then begin
([], hidden)
end else begin
(
# 2303 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((lid, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::[], (FStar_Ident.range_of_lid lid)))
in ((dec)::[], (lid)::hidden))
end)
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (is_abstract quals) then begin
(let _151_1211 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _151_1210 = (let _151_1209 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (_151_1209, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_151_1210)))))
in (_151_1211, hidden))
end else begin
((se)::[], hidden)
end
end))))

# 2312 "FStar.TypeChecker.Tc.fst"
let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (
# 2313 "FStar.TypeChecker.Tc.fst"
let _70_3202 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _70_3183 se -> (match (_70_3183) with
| (ses, exports, env, hidden) -> begin
(
# 2315 "FStar.TypeChecker.Tc.fst"
let _70_3185 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1218 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _151_1218))
end else begin
()
end
in (
# 2318 "FStar.TypeChecker.Tc.fst"
let _70_3189 = (tc_decl env se)
in (match (_70_3189) with
| (se, env) -> begin
(
# 2320 "FStar.TypeChecker.Tc.fst"
let _70_3190 = if ((FStar_ST.read FStar_Options.log_types) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _151_1219 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _151_1219))
end else begin
()
end
in (
# 2323 "FStar.TypeChecker.Tc.fst"
let _70_3192 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (
# 2325 "FStar.TypeChecker.Tc.fst"
let _70_3196 = (for_export hidden se)
in (match (_70_3196) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_70_3202) with
| (ses, exports, env, _70_3201) -> begin
(let _151_1220 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _151_1220, env))
end)))

# 2330 "FStar.TypeChecker.Tc.fst"
let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2331 "FStar.TypeChecker.Tc.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 2332 "FStar.TypeChecker.Tc.fst"
let msg = (Prims.strcat "Internals for " name)
in (
# 2333 "FStar.TypeChecker.Tc.fst"
let env = (
# 2333 "FStar.TypeChecker.Tc.fst"
let _70_3207 = env
in (let _151_1225 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _70_3207.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_3207.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_3207.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_3207.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_3207.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_3207.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_3207.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_3207.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_3207.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_3207.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_3207.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_3207.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_3207.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _70_3207.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _70_3207.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_3207.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _151_1225; FStar_TypeChecker_Env.default_effects = _70_3207.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_3207.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_3207.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_3207.FStar_TypeChecker_Env.use_bv_sorts}))
in (
# 2334 "FStar.TypeChecker.Tc.fst"
let _70_3210 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (
# 2335 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (
# 2336 "FStar.TypeChecker.Tc.fst"
let _70_3216 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_70_3216) with
| (ses, exports, env) -> begin
((
# 2337 "FStar.TypeChecker.Tc.fst"
let _70_3217 = modul
in {FStar_Syntax_Syntax.name = _70_3217.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _70_3217.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _70_3217.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))

# 2339 "FStar.TypeChecker.Tc.fst"
let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (
# 2340 "FStar.TypeChecker.Tc.fst"
let _70_3225 = (tc_decls env decls)
in (match (_70_3225) with
| (ses, exports, env) -> begin
(
# 2341 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2341 "FStar.TypeChecker.Tc.fst"
let _70_3226 = modul
in {FStar_Syntax_Syntax.name = _70_3226.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _70_3226.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _70_3226.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))

# 2344 "FStar.TypeChecker.Tc.fst"
let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (
# 2345 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2345 "FStar.TypeChecker.Tc.fst"
let _70_3232 = modul
in {FStar_Syntax_Syntax.name = _70_3232.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _70_3232.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (
# 2346 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.finish_module env modul)
in (
# 2347 "FStar.TypeChecker.Tc.fst"
let _70_3242 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(
# 2349 "FStar.TypeChecker.Tc.fst"
let _70_3236 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (
# 2350 "FStar.TypeChecker.Tc.fst"
let _70_3238 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (
# 2351 "FStar.TypeChecker.Tc.fst"
let _70_3240 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _151_1238 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _151_1238 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))

# 2356 "FStar.TypeChecker.Tc.fst"
let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2357 "FStar.TypeChecker.Tc.fst"
let _70_3249 = (tc_partial_modul env modul)
in (match (_70_3249) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

# 2360 "FStar.TypeChecker.Tc.fst"
let add_modul_to_tcenv : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_TypeChecker_Env.env = (fun en m -> (
# 2361 "FStar.TypeChecker.Tc.fst"
let do_sigelt = (fun en elt -> (
# 2362 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt en elt)
in (
# 2363 "FStar.TypeChecker.Tc.fst"
let _70_3256 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env elt)
in env)))
in (
# 2366 "FStar.TypeChecker.Tc.fst"
let en = (FStar_TypeChecker_Env.set_current_module en m.FStar_Syntax_Syntax.name)
in (let _151_1251 = (FStar_List.fold_left do_sigelt en m.FStar_Syntax_Syntax.exports)
in (FStar_TypeChecker_Env.finish_module _151_1251 m)))))

# 2369 "FStar.TypeChecker.Tc.fst"
let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 2370 "FStar.TypeChecker.Tc.fst"
let _70_3261 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _151_1256 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _151_1256))
end else begin
()
end
in (
# 2372 "FStar.TypeChecker.Tc.fst"
let env = (
# 2372 "FStar.TypeChecker.Tc.fst"
let _70_3263 = env
in {FStar_TypeChecker_Env.solver = _70_3263.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_3263.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_3263.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_3263.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_3263.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_3263.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_3263.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_3263.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_3263.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_3263.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_3263.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_3263.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_3263.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _70_3263.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_3263.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_3263.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_3263.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_3263.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_3263.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_3263.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_3263.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 2373 "FStar.TypeChecker.Tc.fst"
let _70_3269 = (tc_tot_or_gtot_term env e)
in (match (_70_3269) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected a total term; got a ghost term", e.FStar_Syntax_Syntax.pos))))
end
end)))))

# 2378 "FStar.TypeChecker.Tc.fst"
let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (
# 2379 "FStar.TypeChecker.Tc.fst"
let _70_3272 = if ((let _151_1261 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _151_1261)) <> 0) then begin
(let _151_1262 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _151_1262))
end else begin
()
end
in (
# 2381 "FStar.TypeChecker.Tc.fst"
let _70_3276 = (tc_modul env m)
in (match (_70_3276) with
| (m, env) -> begin
(
# 2382 "FStar.TypeChecker.Tc.fst"
let _70_3277 = if (FStar_Options.should_dump m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _151_1263 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _151_1263))
end else begin
()
end
in (m, env))
end))))




