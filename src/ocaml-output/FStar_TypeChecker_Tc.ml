
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
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(
# 280 "FStar.TypeChecker.Tc.fst"
let _70_357 = (FStar_Syntax_Util.type_u ())
in (match (_70_357) with
| (t, u) -> begin
(
# 281 "FStar.TypeChecker.Tc.fst"
let _70_361 = (tc_check_tot_or_gtot_term env e t)
in (match (_70_361) with
| (e, c, g) -> begin
(
# 282 "FStar.TypeChecker.Tc.fst"
let _70_368 = (
# 283 "FStar.TypeChecker.Tc.fst"
let _70_365 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_365) with
| (env, _70_364) -> begin
(tc_pats env pats)
end))
in (match (_70_368) with
| (pats, g') -> begin
(
# 285 "FStar.TypeChecker.Tc.fst"
let g' = (
# 285 "FStar.TypeChecker.Tc.fst"
let _70_369 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _70_369.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _70_369.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _70_369.FStar_TypeChecker_Env.implicits})
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
| FStar_Syntax_Syntax.Tm_let ((_70_378, {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _70_385; FStar_Syntax_Syntax.lbtyp = _70_383; FStar_Syntax_Syntax.lbeff = _70_381; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 293 "FStar.TypeChecker.Tc.fst"
let _70_396 = (let _151_253 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _151_253 e1))
in (match (_70_396) with
| (e1, c1, g1) -> begin
(
# 294 "FStar.TypeChecker.Tc.fst"
let _70_400 = (tc_term env e2)
in (match (_70_400) with
| (e2, c2, g2) -> begin
(
# 295 "FStar.TypeChecker.Tc.fst"
let c = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (None, c2))
in (
# 296 "FStar.TypeChecker.Tc.fst"
let e = (let _151_258 = (let _151_257 = (let _151_256 = (let _151_255 = (let _151_254 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Common.t_unit, e1))
in (_151_254)::[])
in (false, _151_255))
in (_151_256, e2))
in FStar_Syntax_Syntax.Tm_let (_151_257))
in (FStar_Syntax_Syntax.mk _151_258 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 297 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _151_259 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _151_259)))))
end))
end))
end
| _70_405 -> begin
(
# 300 "FStar.TypeChecker.Tc.fst"
let _70_409 = (tc_term env e)
in (match (_70_409) with
| (e, c, g) -> begin
(
# 301 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(
# 306 "FStar.TypeChecker.Tc.fst"
let _70_418 = (tc_term env e)
in (match (_70_418) with
| (e, c, g) -> begin
(
# 307 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, m))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _70_423) -> begin
(
# 311 "FStar.TypeChecker.Tc.fst"
let _70_428 = (FStar_Syntax_Util.type_u ())
in (match (_70_428) with
| (k, u) -> begin
(
# 312 "FStar.TypeChecker.Tc.fst"
let _70_433 = (tc_check_tot_or_gtot_term env t k)
in (match (_70_433) with
| (t, _70_431, f) -> begin
(
# 313 "FStar.TypeChecker.Tc.fst"
let _70_437 = (let _151_260 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _151_260 e))
in (match (_70_437) with
| (e, c, g) -> begin
(
# 314 "FStar.TypeChecker.Tc.fst"
let _70_441 = (let _151_264 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _70_438 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _151_264 e c f))
in (match (_70_441) with
| (c, f) -> begin
(
# 315 "FStar.TypeChecker.Tc.fst"
let _70_445 = (let _151_265 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, t, Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _151_265 c))
in (match (_70_445) with
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
# 319 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 320 "FStar.TypeChecker.Tc.fst"
let env = (let _151_269 = (let _151_268 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _151_268 Prims.fst))
in (FStar_All.pipe_right _151_269 instantiate_both))
in (
# 321 "FStar.TypeChecker.Tc.fst"
let _70_452 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_271 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _151_270 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _151_271 _151_270)))
end else begin
()
end
in (
# 325 "FStar.TypeChecker.Tc.fst"
let _70_457 = (tc_term (no_inst env) head)
in (match (_70_457) with
| (head, chead, g_head) -> begin
(
# 326 "FStar.TypeChecker.Tc.fst"
let _70_461 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _151_272 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _151_272))
end else begin
(let _151_273 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _151_273))
end
in (match (_70_461) with
| (e, c, g) -> begin
(
# 329 "FStar.TypeChecker.Tc.fst"
let _70_462 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _151_274 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _151_274))
end else begin
()
end
in (
# 331 "FStar.TypeChecker.Tc.fst"
let c = if (((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) && (not ((FStar_Syntax_Util.is_lcomp_partial_return c)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)) then begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e c)
end else begin
c
end
in (
# 336 "FStar.TypeChecker.Tc.fst"
let _70_469 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
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
# 341 "FStar.TypeChecker.Tc.fst"
let _70_474 = (comp_check_expected_typ env0 e c)
in (match (_70_474) with
| (e, c, g') -> begin
(
# 342 "FStar.TypeChecker.Tc.fst"
let _70_475 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_283 = (FStar_Syntax_Print.term_to_string e)
in (let _151_282 = (let _151_281 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _151_281))
in (FStar_Util.print2 "(%s) checked ... got %s\n" _151_283 _151_282)))
end else begin
()
end
in (
# 346 "FStar.TypeChecker.Tc.fst"
let gimp = (match ((let _151_284 = (FStar_Syntax_Subst.compress head)
in _151_284.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _70_479) -> begin
(
# 349 "FStar.TypeChecker.Tc.fst"
let imp = (env0, u, e, c.FStar_Syntax_Syntax.res_typ, e.FStar_Syntax_Syntax.pos)
in (
# 350 "FStar.TypeChecker.Tc.fst"
let _70_483 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _70_483.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _70_483.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _70_483.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _70_486 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (
# 352 "FStar.TypeChecker.Tc.fst"
let gres = (let _151_285 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _151_285))
in (
# 353 "FStar.TypeChecker.Tc.fst"
let _70_489 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
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
# 358 "FStar.TypeChecker.Tc.fst"
let _70_497 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_497) with
| (env1, topt) -> begin
(
# 359 "FStar.TypeChecker.Tc.fst"
let env1 = (instantiate_both env1)
in (
# 360 "FStar.TypeChecker.Tc.fst"
let _70_502 = (tc_term env1 e1)
in (match (_70_502) with
| (e1, c1, g1) -> begin
(
# 361 "FStar.TypeChecker.Tc.fst"
let _70_513 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(
# 364 "FStar.TypeChecker.Tc.fst"
let _70_509 = (FStar_Syntax_Util.type_u ())
in (match (_70_509) with
| (k, _70_508) -> begin
(
# 365 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _151_287 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_151_287, res_t)))
end))
end)
in (match (_70_513) with
| (env_branches, res_t) -> begin
(
# 368 "FStar.TypeChecker.Tc.fst"
let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (
# 369 "FStar.TypeChecker.Tc.fst"
let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (
# 370 "FStar.TypeChecker.Tc.fst"
let _70_530 = (
# 371 "FStar.TypeChecker.Tc.fst"
let _70_527 = (FStar_List.fold_right (fun _70_521 _70_524 -> (match ((_70_521, _70_524)) with
| ((_70_517, f, c, g), (caccum, gaccum)) -> begin
(let _151_290 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _151_290))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_70_527) with
| (cases, g) -> begin
(let _151_291 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_151_291, g))
end))
in (match (_70_530) with
| (c_branches, g_branches) -> begin
(
# 375 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (guard_x), c_branches))
in (
# 376 "FStar.TypeChecker.Tc.fst"
let e = (let _151_295 = (let _151_294 = (let _151_293 = (FStar_List.map (fun _70_539 -> (match (_70_539) with
| (f, _70_534, _70_536, _70_538) -> begin
f
end)) t_eqns)
in (e1, _151_293))
in FStar_Syntax_Syntax.Tm_match (_151_294))
in (FStar_Syntax_Syntax.mk _151_295 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (
# 377 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, cres.FStar_Syntax_Syntax.res_typ, Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (
# 378 "FStar.TypeChecker.Tc.fst"
let _70_542 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
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
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_70_554); FStar_Syntax_Syntax.lbunivs = _70_552; FStar_Syntax_Syntax.lbtyp = _70_550; FStar_Syntax_Syntax.lbeff = _70_548; FStar_Syntax_Syntax.lbdef = _70_546}::[]), _70_560) -> begin
(
# 385 "FStar.TypeChecker.Tc.fst"
let _70_563 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_300 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _151_300))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _70_567), _70_570) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_70_585); FStar_Syntax_Syntax.lbunivs = _70_583; FStar_Syntax_Syntax.lbtyp = _70_581; FStar_Syntax_Syntax.lbeff = _70_579; FStar_Syntax_Syntax.lbdef = _70_577}::_70_575), _70_591) -> begin
(
# 392 "FStar.TypeChecker.Tc.fst"
let _70_594 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_301 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _151_301))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _70_598), _70_601) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 405 "FStar.TypeChecker.Tc.fst"
let check_instantiated_fvar = (fun env v dc e t -> (
# 406 "FStar.TypeChecker.Tc.fst"
let _70_615 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_70_615) with
| (e, t, implicits) -> begin
(
# 408 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _151_315 = (let _151_314 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_314))
in FStar_Util.Inr (_151_315))
end
in (
# 409 "FStar.TypeChecker.Tc.fst"
let is_data_ctor = (fun _70_4 -> (match (_70_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _70_625 -> begin
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
# 419 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (
# 420 "FStar.TypeChecker.Tc.fst"
let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(FStar_All.failwith "Impossible: Violation of locally nameless convention")
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(
# 426 "FStar.TypeChecker.Tc.fst"
let g = (match ((let _151_322 = (FStar_Syntax_Subst.compress t1)
in _151_322.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_70_636) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _70_639 -> begin
(
# 428 "FStar.TypeChecker.Tc.fst"
let imp = (env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (
# 429 "FStar.TypeChecker.Tc.fst"
let _70_641 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _70_641.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _70_641.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _70_641.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 434 "FStar.TypeChecker.Tc.fst"
let _70_647 = (FStar_Syntax_Util.type_u ())
in (match (_70_647) with
| (t, u) -> begin
(
# 435 "FStar.TypeChecker.Tc.fst"
let e = (FStar_TypeChecker_Util.new_uvar env t)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))
end))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 439 "FStar.TypeChecker.Tc.fst"
let t = if env.FStar_TypeChecker_Env.use_bv_sorts then begin
x.FStar_Syntax_Syntax.sort
end else begin
(FStar_TypeChecker_Env.lookup_bv env x)
end
in (
# 440 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.bv_to_name (
# 440 "FStar.TypeChecker.Tc.fst"
let _70_652 = x
in {FStar_Syntax_Syntax.ppname = _70_652.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_652.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (
# 441 "FStar.TypeChecker.Tc.fst"
let _70_658 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_70_658) with
| (e, t, implicits) -> begin
(
# 442 "FStar.TypeChecker.Tc.fst"
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
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (v, dc); FStar_Syntax_Syntax.tk = _70_665; FStar_Syntax_Syntax.pos = _70_663; FStar_Syntax_Syntax.vars = _70_661}, us) -> begin
(
# 446 "FStar.TypeChecker.Tc.fst"
let us = (FStar_List.map (tc_universe env) us)
in (
# 447 "FStar.TypeChecker.Tc.fst"
let _70_677 = (FStar_TypeChecker_Env.lookup_lid env v.FStar_Syntax_Syntax.v)
in (match (_70_677) with
| (us', t) -> begin
(
# 448 "FStar.TypeChecker.Tc.fst"
let _70_684 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _151_327 = (let _151_326 = (let _151_325 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _151_325))
in FStar_Syntax_Syntax.Error (_151_326))
in (Prims.raise _151_327))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _70_683 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (
# 453 "FStar.TypeChecker.Tc.fst"
let e = (let _151_330 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (((
# 453 "FStar.TypeChecker.Tc.fst"
let _70_686 = v
in {FStar_Syntax_Syntax.v = _70_686.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _70_686.FStar_Syntax_Syntax.p}), dc))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _151_330 us))
in (check_instantiated_fvar env v dc e t)))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (v, dc) -> begin
(
# 457 "FStar.TypeChecker.Tc.fst"
let _70_695 = (FStar_TypeChecker_Env.lookup_lid env v.FStar_Syntax_Syntax.v)
in (match (_70_695) with
| (us, t) -> begin
(
# 458 "FStar.TypeChecker.Tc.fst"
let e = (let _151_331 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (((
# 458 "FStar.TypeChecker.Tc.fst"
let _70_696 = v
in {FStar_Syntax_Syntax.v = _70_696.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _70_696.FStar_Syntax_Syntax.p}), dc))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _151_331 us))
in (check_instantiated_fvar env v dc e t))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(
# 462 "FStar.TypeChecker.Tc.fst"
let t = (tc_constant env top.FStar_Syntax_Syntax.pos c)
in (
# 463 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 467 "FStar.TypeChecker.Tc.fst"
let _70_709 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_70_709) with
| (bs, c) -> begin
(
# 468 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 469 "FStar.TypeChecker.Tc.fst"
let _70_714 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_714) with
| (env, _70_713) -> begin
(
# 470 "FStar.TypeChecker.Tc.fst"
let _70_719 = (tc_binders env bs)
in (match (_70_719) with
| (bs, env, g, us) -> begin
(
# 471 "FStar.TypeChecker.Tc.fst"
let _70_723 = (tc_comp env c)
in (match (_70_723) with
| (c, uc, f) -> begin
(
# 472 "FStar.TypeChecker.Tc.fst"
let e = (
# 472 "FStar.TypeChecker.Tc.fst"
let _70_724 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _70_724.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _70_724.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _70_724.FStar_Syntax_Syntax.vars})
in (
# 473 "FStar.TypeChecker.Tc.fst"
let _70_727 = (check_smt_pat env e bs c)
in (
# 474 "FStar.TypeChecker.Tc.fst"
let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (
# 475 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 476 "FStar.TypeChecker.Tc.fst"
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
# 480 "FStar.TypeChecker.Tc.fst"
let u = (tc_universe env u)
in (
# 481 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) None top.FStar_Syntax_Syntax.pos)
in (
# 482 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 486 "FStar.TypeChecker.Tc.fst"
let _70_743 = (let _151_334 = (let _151_333 = (FStar_Syntax_Syntax.mk_binder x)
in (_151_333)::[])
in (FStar_Syntax_Subst.open_term _151_334 phi))
in (match (_70_743) with
| (x, phi) -> begin
(
# 487 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 488 "FStar.TypeChecker.Tc.fst"
let _70_748 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_748) with
| (env, _70_747) -> begin
(
# 489 "FStar.TypeChecker.Tc.fst"
let _70_753 = (let _151_335 = (FStar_List.hd x)
in (tc_binder env _151_335))
in (match (_70_753) with
| (x, env, f1, u) -> begin
(
# 490 "FStar.TypeChecker.Tc.fst"
let _70_754 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_338 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _151_337 = (FStar_Syntax_Print.term_to_string phi)
in (let _151_336 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _151_338 _151_337 _151_336))))
end else begin
()
end
in (
# 493 "FStar.TypeChecker.Tc.fst"
let _70_759 = (FStar_Syntax_Util.type_u ())
in (match (_70_759) with
| (t_phi, _70_758) -> begin
(
# 494 "FStar.TypeChecker.Tc.fst"
let _70_764 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_70_764) with
| (phi, _70_762, f2) -> begin
(
# 495 "FStar.TypeChecker.Tc.fst"
let e = (
# 495 "FStar.TypeChecker.Tc.fst"
let _70_765 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _70_765.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _70_765.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _70_765.FStar_Syntax_Syntax.vars})
in (
# 496 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 497 "FStar.TypeChecker.Tc.fst"
let g = (let _151_339 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _151_339))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _70_773) -> begin
(
# 501 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (
# 502 "FStar.TypeChecker.Tc.fst"
let _70_779 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_340 = (FStar_Syntax_Print.term_to_string (
# 503 "FStar.TypeChecker.Tc.fst"
let _70_777 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _70_777.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _70_777.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _70_777.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _151_340))
end else begin
()
end
in (
# 504 "FStar.TypeChecker.Tc.fst"
let _70_783 = (FStar_Syntax_Subst.open_term bs body)
in (match (_70_783) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _70_785 -> begin
(let _151_342 = (let _151_341 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _151_341))
in (FStar_All.failwith _151_342))
end)))))
and tc_constant : FStar_TypeChecker_Env.env  ->  FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun env r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_70_791) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_70_794) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int32 (_70_797) -> begin
FStar_TypeChecker_Common.t_int32
end
| FStar_Const.Const_int64 (_70_800) -> begin
FStar_TypeChecker_Common.t_int64
end
| FStar_Const.Const_string (_70_803) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_70_806) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_70_809) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_uint8 (_70_812) -> begin
FStar_TypeChecker_Common.t_uint8
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_70_816) -> begin
(
# 523 "FStar.TypeChecker.Tc.fst"
let fail = (fun _70_819 -> (match (()) with
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
| _70_824 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 544 "FStar.TypeChecker.Tc.fst"
let _70_831 = (FStar_Syntax_Util.type_u ())
in (match (_70_831) with
| (k, u) -> begin
(
# 545 "FStar.TypeChecker.Tc.fst"
let _70_836 = (tc_check_tot_or_gtot_term env t k)
in (match (_70_836) with
| (t, _70_834, g) -> begin
(let _151_351 = (FStar_Syntax_Syntax.mk_Total t)
in (_151_351, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 549 "FStar.TypeChecker.Tc.fst"
let _70_841 = (FStar_Syntax_Util.type_u ())
in (match (_70_841) with
| (k, u) -> begin
(
# 550 "FStar.TypeChecker.Tc.fst"
let _70_846 = (tc_check_tot_or_gtot_term env t k)
in (match (_70_846) with
| (t, _70_844, g) -> begin
(let _151_352 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_151_352, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 554 "FStar.TypeChecker.Tc.fst"
let head = (FStar_Syntax_Syntax.fvar None c.FStar_Syntax_Syntax.effect_name (FStar_Ident.range_of_lid c.FStar_Syntax_Syntax.effect_name))
in (
# 555 "FStar.TypeChecker.Tc.fst"
let tc = (let _151_354 = (let _151_353 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_151_353)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _151_354 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 556 "FStar.TypeChecker.Tc.fst"
let _70_855 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_70_855) with
| (tc, _70_853, f) -> begin
(
# 557 "FStar.TypeChecker.Tc.fst"
let _70_859 = (FStar_Syntax_Util.head_and_args tc)
in (match (_70_859) with
| (_70_857, args) -> begin
(
# 558 "FStar.TypeChecker.Tc.fst"
let _70_862 = (let _151_356 = (FStar_List.hd args)
in (let _151_355 = (FStar_List.tl args)
in (_151_356, _151_355)))
in (match (_70_862) with
| (res, args) -> begin
(
# 559 "FStar.TypeChecker.Tc.fst"
let _70_878 = (let _151_358 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _70_5 -> (match (_70_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(
# 561 "FStar.TypeChecker.Tc.fst"
let _70_869 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_869) with
| (env, _70_868) -> begin
(
# 562 "FStar.TypeChecker.Tc.fst"
let _70_874 = (tc_tot_or_gtot_term env e)
in (match (_70_874) with
| (e, _70_872, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _151_358 FStar_List.unzip))
in (match (_70_878) with
| (flags, guards) -> begin
(
# 565 "FStar.TypeChecker.Tc.fst"
let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| _70_883 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _151_360 = (FStar_Syntax_Syntax.mk_Comp (
# 568 "FStar.TypeChecker.Tc.fst"
let _70_885 = c
in {FStar_Syntax_Syntax.effect_name = _70_885.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _70_885.FStar_Syntax_Syntax.flags}))
in (let _151_359 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_151_360, u, _151_359))))
end))
end))
end))
end))))
end))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (
# 575 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun u -> (
# 576 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_70_893) -> begin
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
| _70_908 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (
# 598 "FStar.TypeChecker.Tc.fst"
let fail = (fun msg t -> (let _151_380 = (let _151_379 = (let _151_378 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_151_378, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_151_379))
in (Prims.raise _151_380)))
in (
# 607 "FStar.TypeChecker.Tc.fst"
let check_binders = (fun env bs bs_expected -> (
# 612 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun _70_926 bs bs_expected -> (match (_70_926) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| ((hd, imp)::bs, (hd_expected, imp')::bs_expected) -> begin
(
# 616 "FStar.TypeChecker.Tc.fst"
let _70_957 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _151_397 = (let _151_396 = (let _151_395 = (let _151_393 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _151_393))
in (let _151_394 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_151_395, _151_394)))
in FStar_Syntax_Syntax.Error (_151_396))
in (Prims.raise _151_397))
end
| _70_956 -> begin
()
end)
in (
# 623 "FStar.TypeChecker.Tc.fst"
let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (
# 624 "FStar.TypeChecker.Tc.fst"
let _70_974 = (match ((let _151_398 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _151_398.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _70_962 -> begin
(
# 627 "FStar.TypeChecker.Tc.fst"
let _70_963 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_399 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _151_399))
end else begin
()
end
in (
# 628 "FStar.TypeChecker.Tc.fst"
let _70_969 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_70_969) with
| (t, _70_967, g1) -> begin
(
# 629 "FStar.TypeChecker.Tc.fst"
let g2 = (let _151_401 = (FStar_TypeChecker_Env.get_range env)
in (let _151_400 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _151_401 "Type annotation on parameter incompatible with the expected type" _151_400)))
in (
# 633 "FStar.TypeChecker.Tc.fst"
let g = (let _151_402 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _151_402))
in (t, g)))
end)))
end)
in (match (_70_974) with
| (t, g) -> begin
(
# 635 "FStar.TypeChecker.Tc.fst"
let hd = (
# 635 "FStar.TypeChecker.Tc.fst"
let _70_975 = hd
in {FStar_Syntax_Syntax.ppname = _70_975.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_975.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 636 "FStar.TypeChecker.Tc.fst"
let b = (hd, imp)
in (
# 637 "FStar.TypeChecker.Tc.fst"
let b_expected = (hd_expected, imp')
in (
# 638 "FStar.TypeChecker.Tc.fst"
let env = (maybe_push_binding env b)
in (
# 639 "FStar.TypeChecker.Tc.fst"
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
# 649 "FStar.TypeChecker.Tc.fst"
let rec expected_function_typ = (fun env t0 -> (match (t0) with
| None -> begin
(
# 659 "FStar.TypeChecker.Tc.fst"
let _70_995 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _70_994 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (
# 660 "FStar.TypeChecker.Tc.fst"
let _70_1002 = (tc_binders env bs)
in (match (_70_1002) with
| (bs, envbody, g, _70_1001) -> begin
(None, bs, [], None, envbody, g)
end)))
end
| Some (t) -> begin
(
# 664 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 665 "FStar.TypeChecker.Tc.fst"
let rec as_function_typ = (fun norm t -> (match ((let _151_412 = (FStar_Syntax_Subst.compress t)
in _151_412.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 669 "FStar.TypeChecker.Tc.fst"
let _70_1029 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _70_1028 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 670 "FStar.TypeChecker.Tc.fst"
let _70_1036 = (tc_binders env bs)
in (match (_70_1036) with
| (bs, envbody, g, _70_1035) -> begin
(
# 671 "FStar.TypeChecker.Tc.fst"
let _70_1040 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_70_1040) with
| (envbody, _70_1039) -> begin
(Some ((t, true)), bs, [], None, envbody, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _70_1043) -> begin
(
# 677 "FStar.TypeChecker.Tc.fst"
let _70_1053 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_70_1053) with
| (_70_1047, bs, bs', copt, env, g) -> begin
(Some ((t, false)), bs, bs', copt, env, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 681 "FStar.TypeChecker.Tc.fst"
let _70_1060 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_70_1060) with
| (bs_expected, c_expected) -> begin
(
# 688 "FStar.TypeChecker.Tc.fst"
let check_actuals_against_formals = (fun env bs bs_expected -> (
# 689 "FStar.TypeChecker.Tc.fst"
let rec handle_more = (fun _70_1071 c_expected -> (match (_70_1071) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _151_423 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _151_423))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(
# 694 "FStar.TypeChecker.Tc.fst"
let c = (let _151_424 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _151_424))
in (let _151_425 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _151_425)))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(
# 698 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.subst_comp subst c_expected)
in if (FStar_Syntax_Util.is_total_comp c) then begin
(
# 701 "FStar.TypeChecker.Tc.fst"
let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 704 "FStar.TypeChecker.Tc.fst"
let _70_1092 = (check_binders env more_bs bs_expected)
in (match (_70_1092) with
| (env, bs', more, guard', subst) -> begin
(let _151_427 = (let _151_426 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _151_426, subst))
in (handle_more _151_427 c_expected))
end))
end
| _70_1094 -> begin
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
# 711 "FStar.TypeChecker.Tc.fst"
let mk_letrec_env = (fun envbody bs c -> (
# 712 "FStar.TypeChecker.Tc.fst"
let letrecs = (guard_letrecs envbody bs c)
in (
# 713 "FStar.TypeChecker.Tc.fst"
let envbody = (
# 713 "FStar.TypeChecker.Tc.fst"
let _70_1100 = envbody
in {FStar_TypeChecker_Env.solver = _70_1100.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1100.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1100.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1100.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1100.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1100.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1100.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1100.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1100.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1100.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1100.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1100.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _70_1100.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _70_1100.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_1100.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_1100.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1100.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1100.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1100.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1100.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1100.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _70_1105 _70_1108 -> (match ((_70_1105, _70_1108)) with
| ((env, letrec_binders), (l, t)) -> begin
(
# 715 "FStar.TypeChecker.Tc.fst"
let _70_1114 = (let _151_440 = (let _151_439 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _151_439 Prims.fst))
in (tc_term _151_440 t))
in (match (_70_1114) with
| (t, _70_1111, _70_1113) -> begin
(
# 716 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (
# 717 "FStar.TypeChecker.Tc.fst"
let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _151_441 = (FStar_Syntax_Syntax.mk_binder (
# 718 "FStar.TypeChecker.Tc.fst"
let _70_1118 = x
in {FStar_Syntax_Syntax.ppname = _70_1118.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_1118.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_151_441)::letrec_binders)
end
| _70_1121 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (
# 723 "FStar.TypeChecker.Tc.fst"
let _70_1127 = (check_actuals_against_formals env bs bs_expected)
in (match (_70_1127) with
| (envbody, bs, g, c) -> begin
(
# 724 "FStar.TypeChecker.Tc.fst"
let _70_1130 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_70_1130) with
| (envbody, letrecs) -> begin
(
# 725 "FStar.TypeChecker.Tc.fst"
let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, g))
end))
end))))
end))
end
| _70_1133 -> begin
if (not (norm)) then begin
(let _151_442 = (unfold_whnf env t)
in (as_function_typ true _151_442))
end else begin
(
# 733 "FStar.TypeChecker.Tc.fst"
let _70_1142 = (expected_function_typ env None)
in (match (_70_1142) with
| (_70_1135, bs, _70_1138, c_opt, envbody, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (
# 737 "FStar.TypeChecker.Tc.fst"
let use_eq = env.FStar_TypeChecker_Env.use_eq
in (
# 738 "FStar.TypeChecker.Tc.fst"
let _70_1146 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_1146) with
| (env, topt) -> begin
(
# 739 "FStar.TypeChecker.Tc.fst"
let _70_1150 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
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
# 743 "FStar.TypeChecker.Tc.fst"
let _70_1158 = (expected_function_typ env topt)
in (match (_70_1158) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, g) -> begin
(
# 744 "FStar.TypeChecker.Tc.fst"
let _70_1164 = (tc_term (
# 744 "FStar.TypeChecker.Tc.fst"
let _70_1159 = envbody
in {FStar_TypeChecker_Env.solver = _70_1159.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1159.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1159.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1159.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1159.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1159.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1159.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1159.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1159.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1159.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1159.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1159.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_1159.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _70_1159.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _70_1159.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1159.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1159.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1159.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1159.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1159.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_70_1164) with
| (body, cbody, guard_body) -> begin
(
# 745 "FStar.TypeChecker.Tc.fst"
let _70_1165 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_447 = (FStar_Syntax_Print.term_to_string body)
in (let _151_446 = (let _151_444 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _151_444))
in (let _151_445 = (FStar_TypeChecker_Rel.guard_to_string env guard_body)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _151_447 _151_446 _151_445))))
end else begin
()
end
in (
# 750 "FStar.TypeChecker.Tc.fst"
let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (
# 752 "FStar.TypeChecker.Tc.fst"
let _70_1168 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _151_450 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _151_449 = (let _151_448 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _151_448))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _151_450 _151_449)))
end else begin
()
end
in (
# 756 "FStar.TypeChecker.Tc.fst"
let _70_1175 = (let _151_452 = (let _151_451 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _151_451))
in (check_expected_effect (
# 756 "FStar.TypeChecker.Tc.fst"
let _70_1170 = envbody
in {FStar_TypeChecker_Env.solver = _70_1170.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1170.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1170.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1170.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1170.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1170.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1170.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1170.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1170.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1170.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1170.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1170.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_1170.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _70_1170.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _70_1170.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _70_1170.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1170.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1170.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1170.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1170.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1170.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _151_452))
in (match (_70_1175) with
| (body, cbody, guard) -> begin
(
# 757 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (
# 758 "FStar.TypeChecker.Tc.fst"
let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _151_453 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _151_453))
end else begin
(
# 760 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (
# 763 "FStar.TypeChecker.Tc.fst"
let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (
# 764 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.abs bs body (Some ((FStar_Syntax_Util.lcomp_of_comp cbody))))
in (
# 765 "FStar.TypeChecker.Tc.fst"
let _70_1198 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(
# 767 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_70_1187) -> begin
(e, t, guard)
end
| _70_1190 -> begin
(
# 776 "FStar.TypeChecker.Tc.fst"
let _70_1193 = if use_teq then begin
(let _151_454 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _151_454))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_70_1193) with
| (e, guard') -> begin
(let _151_455 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _151_455))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_70_1198) with
| (e, tfun, guard) -> begin
(
# 786 "FStar.TypeChecker.Tc.fst"
let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (
# 787 "FStar.TypeChecker.Tc.fst"
let _70_1202 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_70_1202) with
| (c, g) -> begin
(e, c, g)
end)))
end))))))
end)))))
end))
end)))
end)))))))
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead ghead args expected_topt -> (
# 795 "FStar.TypeChecker.Tc.fst"
let n_args = (FStar_List.length args)
in (
# 796 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 797 "FStar.TypeChecker.Tc.fst"
let thead = chead.FStar_Syntax_Syntax.res_typ
in (
# 798 "FStar.TypeChecker.Tc.fst"
let _70_1212 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_464 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _151_463 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _151_464 _151_463)))
end else begin
()
end
in (
# 799 "FStar.TypeChecker.Tc.fst"
let rec check_function_app = (fun norm tf -> (match ((let _151_469 = (FStar_Syntax_Util.unrefine tf)
in _151_469.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 803 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| (e, imp)::tl -> begin
(
# 806 "FStar.TypeChecker.Tc.fst"
let _70_1246 = (tc_term env e)
in (match (_70_1246) with
| (e, c, g_e) -> begin
(
# 807 "FStar.TypeChecker.Tc.fst"
let _70_1250 = (tc_args env tl)
in (match (_70_1250) with
| (args, comps, g_rest) -> begin
(let _151_474 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, (c)::comps, _151_474))
end))
end))
end))
in (
# 815 "FStar.TypeChecker.Tc.fst"
let _70_1254 = (tc_args env args)
in (match (_70_1254) with
| (args, comps, g_args) -> begin
(
# 816 "FStar.TypeChecker.Tc.fst"
let bs = (let _151_476 = (FStar_All.pipe_right comps (FStar_List.map (fun c -> (c.FStar_Syntax_Syntax.res_typ, None))))
in (FStar_Syntax_Util.null_binders_of_tks _151_476))
in (
# 817 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _70_1261 -> begin
FStar_Syntax_Util.ml_comp
end)
in (
# 820 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _151_491 = (FStar_Syntax_Subst.compress t)
in _151_491.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_70_1267) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _70_1272 -> begin
ml_or_tot
end)
end)
in (
# 827 "FStar.TypeChecker.Tc.fst"
let cres = (let _151_496 = (let _151_495 = (let _151_494 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_494 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _151_495))
in (ml_or_tot _151_496 r))
in (
# 828 "FStar.TypeChecker.Tc.fst"
let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (
# 829 "FStar.TypeChecker.Tc.fst"
let _70_1276 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _151_499 = (FStar_Syntax_Print.term_to_string head)
in (let _151_498 = (FStar_Syntax_Print.term_to_string tf)
in (let _151_497 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _151_499 _151_498 _151_497))))
end else begin
()
end
in (
# 834 "FStar.TypeChecker.Tc.fst"
let _70_1278 = (let _151_500 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _151_500))
in (
# 835 "FStar.TypeChecker.Tc.fst"
let comp = (let _151_503 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_TypeChecker_Util.bind env None c (None, out))) ((chead)::comps) _151_503))
in (let _151_505 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _151_504 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_151_505, comp, _151_504)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 839 "FStar.TypeChecker.Tc.fst"
let _70_1289 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_70_1289) with
| (bs, c) -> begin
(
# 841 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun _70_1297 bs cres args -> (match (_70_1297) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (_70_1304)))::rest, (_70_1312, None)::_70_1310) -> begin
(
# 852 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 853 "FStar.TypeChecker.Tc.fst"
let _70_1318 = (check_no_escape (Some (head)) env fvs t)
in (
# 854 "FStar.TypeChecker.Tc.fst"
let _70_1324 = (FStar_TypeChecker_Util.new_implicit_var env t)
in (match (_70_1324) with
| (varg, _70_1322, implicits) -> begin
(
# 855 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (
# 856 "FStar.TypeChecker.Tc.fst"
let arg = (let _151_514 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _151_514))
in (let _151_516 = (let _151_515 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _151_515, fvs))
in (tc_args _151_516 rest cres args))))
end))))
end
| ((x, aqual)::rest, (e, aq)::rest') -> begin
(
# 860 "FStar.TypeChecker.Tc.fst"
let _70_1356 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _70_1355 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (
# 865 "FStar.TypeChecker.Tc.fst"
let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 866 "FStar.TypeChecker.Tc.fst"
let x = (
# 866 "FStar.TypeChecker.Tc.fst"
let _70_1359 = x
in {FStar_Syntax_Syntax.ppname = _70_1359.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_1359.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (
# 867 "FStar.TypeChecker.Tc.fst"
let _70_1362 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _151_517 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _151_517))
end else begin
()
end
in (
# 868 "FStar.TypeChecker.Tc.fst"
let _70_1364 = (check_no_escape (Some (head)) env fvs targ)
in (
# 869 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (
# 870 "FStar.TypeChecker.Tc.fst"
let env = (
# 870 "FStar.TypeChecker.Tc.fst"
let _70_1367 = env
in {FStar_TypeChecker_Env.solver = _70_1367.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1367.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1367.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1367.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1367.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1367.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1367.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1367.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1367.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1367.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1367.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1367.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_1367.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _70_1367.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _70_1367.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _70_1367.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1367.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1367.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1367.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1367.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1367.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 871 "FStar.TypeChecker.Tc.fst"
let _70_1370 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_520 = (FStar_Syntax_Print.tag_of_term e)
in (let _151_519 = (FStar_Syntax_Print.term_to_string e)
in (let _151_518 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _151_520 _151_519 _151_518))))
end else begin
()
end
in (
# 872 "FStar.TypeChecker.Tc.fst"
let _70_1375 = (tc_term env e)
in (match (_70_1375) with
| (e, c, g_e) -> begin
(
# 873 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (
# 875 "FStar.TypeChecker.Tc.fst"
let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(
# 877 "FStar.TypeChecker.Tc.fst"
let subst = (let _151_521 = (FStar_List.hd bs)
in (maybe_extend_subst subst _151_521 e))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(
# 880 "FStar.TypeChecker.Tc.fst"
let subst = (let _151_522 = (FStar_List.hd bs)
in (maybe_extend_subst subst _151_522 e))
in (
# 881 "FStar.TypeChecker.Tc.fst"
let _70_1382 = (((Some (x), c))::comps, g)
in (match (_70_1382) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _151_523 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _151_523)) then begin
(
# 885 "FStar.TypeChecker.Tc.fst"
let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (
# 886 "FStar.TypeChecker.Tc.fst"
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
| (_70_1386, []) -> begin
(
# 895 "FStar.TypeChecker.Tc.fst"
let _70_1389 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (
# 896 "FStar.TypeChecker.Tc.fst"
let _70_1407 = (match (bs) with
| [] -> begin
(
# 899 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (
# 905 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (
# 907 "FStar.TypeChecker.Tc.fst"
let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _70_1397 -> (match (_70_1397) with
| (_70_1395, c) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (
# 914 "FStar.TypeChecker.Tc.fst"
let cres = if refine_with_equality then begin
(let _151_530 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _151_530 cres))
end else begin
(
# 920 "FStar.TypeChecker.Tc.fst"
let _70_1399 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
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
| _70_1403 -> begin
(
# 929 "FStar.TypeChecker.Tc.fst"
let g = (let _151_534 = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (FStar_All.pipe_right _151_534 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _151_539 = (let _151_538 = (let _151_537 = (let _151_536 = (let _151_535 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _151_535))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _151_536))
in (FStar_Syntax_Syntax.mk_Total _151_537))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_538))
in (_151_539, g)))
end)
in (match (_70_1407) with
| (cres, g) -> begin
(
# 932 "FStar.TypeChecker.Tc.fst"
let _70_1408 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_540 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _151_540))
end else begin
()
end
in (
# 933 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_List.fold_left (fun out c -> (FStar_TypeChecker_Util.bind env None (Prims.snd c) ((Prims.fst c), out))) cres comps)
in (
# 934 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.bind env None chead (None, comp))
in (
# 935 "FStar.TypeChecker.Tc.fst"
let app = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev outargs) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (
# 936 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.record_application_site env app comp)
in (
# 937 "FStar.TypeChecker.Tc.fst"
let _70_1418 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp g)
in (match (_70_1418) with
| (comp, g) -> begin
(
# 938 "FStar.TypeChecker.Tc.fst"
let _70_1419 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
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
| ([], arg::_70_1423) -> begin
(
# 944 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun norm tres -> (
# 945 "FStar.TypeChecker.Tc.fst"
let tres = (let _151_551 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _151_551 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(
# 948 "FStar.TypeChecker.Tc.fst"
let _70_1435 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_552 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _151_552))
end else begin
()
end
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs (FStar_Syntax_Util.lcomp_of_comp cres') args))
end
| _70_1438 when (not (norm)) -> begin
(let _151_553 = (unfold_whnf env tres)
in (aux true _151_553))
end
| _70_1440 -> begin
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
| _70_1442 -> begin
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
# 974 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 975 "FStar.TypeChecker.Tc.fst"
let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(
# 978 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in (
# 979 "FStar.TypeChecker.Tc.fst"
let _70_1478 = (FStar_List.fold_left2 (fun _70_1459 _70_1462 _70_1465 -> (match ((_70_1459, _70_1462, _70_1465)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(
# 980 "FStar.TypeChecker.Tc.fst"
let _70_1466 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 981 "FStar.TypeChecker.Tc.fst"
let _70_1471 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_70_1471) with
| (e, c, g) -> begin
(
# 982 "FStar.TypeChecker.Tc.fst"
let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (
# 983 "FStar.TypeChecker.Tc.fst"
let g = (let _151_575 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _151_575 g))
in (
# 984 "FStar.TypeChecker.Tc.fst"
let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _151_579 = (let _151_577 = (let _151_576 = (FStar_Syntax_Syntax.as_arg e)
in (_151_576)::[])
in (FStar_List.append seen _151_577))
in (let _151_578 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_151_579, _151_578, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_70_1478) with
| (args, guard, ghost) -> begin
(
# 988 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (
# 989 "FStar.TypeChecker.Tc.fst"
let c = if ghost then begin
(let _151_580 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _151_580 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (
# 990 "FStar.TypeChecker.Tc.fst"
let _70_1483 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_70_1483) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _70_1485 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (
# 1010 "FStar.TypeChecker.Tc.fst"
let _70_1492 = (FStar_Syntax_Subst.open_branch branch)
in (match (_70_1492) with
| (pattern, when_clause, branch_exp) -> begin
(
# 1011 "FStar.TypeChecker.Tc.fst"
let _70_1497 = branch
in (match (_70_1497) with
| (cpat, _70_1495, cbr) -> begin
(
# 1014 "FStar.TypeChecker.Tc.fst"
let tc_pat = (fun allow_implicits pat_t p0 -> (
# 1021 "FStar.TypeChecker.Tc.fst"
let _70_1505 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_70_1505) with
| (pat_bvs, exps, p) -> begin
(
# 1022 "FStar.TypeChecker.Tc.fst"
let _70_1506 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_592 = (FStar_Syntax_Print.pat_to_string p0)
in (let _151_591 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _151_592 _151_591)))
end else begin
()
end
in (
# 1024 "FStar.TypeChecker.Tc.fst"
let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (
# 1025 "FStar.TypeChecker.Tc.fst"
let _70_1512 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_70_1512) with
| (env1, _70_1511) -> begin
(
# 1026 "FStar.TypeChecker.Tc.fst"
let env1 = (
# 1026 "FStar.TypeChecker.Tc.fst"
let _70_1513 = env1
in {FStar_TypeChecker_Env.solver = _70_1513.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1513.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1513.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1513.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1513.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1513.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1513.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1513.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _70_1513.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1513.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1513.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_1513.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _70_1513.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _70_1513.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_1513.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_1513.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1513.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1513.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1513.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1513.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1513.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1027 "FStar.TypeChecker.Tc.fst"
let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (
# 1028 "FStar.TypeChecker.Tc.fst"
let _70_1552 = (let _151_615 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (
# 1029 "FStar.TypeChecker.Tc.fst"
let _70_1518 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_595 = (FStar_Syntax_Print.term_to_string e)
in (let _151_594 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _151_595 _151_594)))
end else begin
()
end
in (
# 1032 "FStar.TypeChecker.Tc.fst"
let _70_1523 = (tc_term env1 e)
in (match (_70_1523) with
| (e, lc, g) -> begin
(
# 1034 "FStar.TypeChecker.Tc.fst"
let _70_1524 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_597 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _151_596 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _151_597 _151_596)))
end else begin
()
end
in (
# 1037 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (
# 1038 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (
# 1039 "FStar.TypeChecker.Tc.fst"
let _70_1530 = (let _151_598 = (FStar_TypeChecker_Rel.discharge_guard env (
# 1039 "FStar.TypeChecker.Tc.fst"
let _70_1528 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _70_1528.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _70_1528.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _70_1528.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _151_598 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1040 "FStar.TypeChecker.Tc.fst"
let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (
# 1041 "FStar.TypeChecker.Tc.fst"
let uvars_to_string = (fun uvs -> (let _151_603 = (let _151_602 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _151_602 (FStar_List.map (fun _70_1538 -> (match (_70_1538) with
| (u, _70_1537) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _151_603 (FStar_String.concat ", "))))
in (
# 1042 "FStar.TypeChecker.Tc.fst"
let uvs1 = (FStar_Syntax_Free.uvars e')
in (
# 1043 "FStar.TypeChecker.Tc.fst"
let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (
# 1044 "FStar.TypeChecker.Tc.fst"
let _70_1546 = if (let _151_604 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _151_604)) then begin
(
# 1045 "FStar.TypeChecker.Tc.fst"
let unresolved = (let _151_605 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _151_605 FStar_Util.set_elements))
in (let _151_613 = (let _151_612 = (let _151_611 = (let _151_610 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _151_609 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _151_608 = (let _151_607 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _70_1545 -> (match (_70_1545) with
| (u, _70_1544) -> begin
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
# 1052 "FStar.TypeChecker.Tc.fst"
let _70_1548 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_614 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _151_614))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _151_615 FStar_List.unzip))
in (match (_70_1552) with
| (exps, norm_exps) -> begin
(
# 1057 "FStar.TypeChecker.Tc.fst"
let p = (FStar_TypeChecker_Util.decorate_pattern env p exps)
in (p, pat_bvs, pat_env, exps, norm_exps))
end))))
end))))
end)))
in (
# 1061 "FStar.TypeChecker.Tc.fst"
let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (
# 1062 "FStar.TypeChecker.Tc.fst"
let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (
# 1063 "FStar.TypeChecker.Tc.fst"
let _70_1559 = (let _151_616 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _151_616 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_70_1559) with
| (scrutinee_env, _70_1558) -> begin
(
# 1066 "FStar.TypeChecker.Tc.fst"
let _70_1565 = (tc_pat true pat_t pattern)
in (match (_70_1565) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(
# 1069 "FStar.TypeChecker.Tc.fst"
let _70_1575 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(
# 1076 "FStar.TypeChecker.Tc.fst"
let _70_1572 = (let _151_617 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _151_617 e))
in (match (_70_1572) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_70_1575) with
| (when_clause, g_when) -> begin
(
# 1080 "FStar.TypeChecker.Tc.fst"
let _70_1579 = (tc_term pat_env branch_exp)
in (match (_70_1579) with
| (branch_exp, c, g_branch) -> begin
(
# 1084 "FStar.TypeChecker.Tc.fst"
let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _151_619 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _151_618 -> Some (_151_618)) _151_619))
end)
in (
# 1091 "FStar.TypeChecker.Tc.fst"
let _70_1635 = (
# 1094 "FStar.TypeChecker.Tc.fst"
let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (
# 1095 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _70_1597 -> begin
(
# 1101 "FStar.TypeChecker.Tc.fst"
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
# 1106 "FStar.TypeChecker.Tc.fst"
let _70_1605 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_70_1605) with
| (c, g_branch) -> begin
(
# 1110 "FStar.TypeChecker.Tc.fst"
let _70_1630 = (match ((eqs, when_condition)) with
| (None, None) -> begin
(c, g_when)
end
| (Some (f), None) -> begin
(
# 1116 "FStar.TypeChecker.Tc.fst"
let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1117 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _151_626 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _151_625 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_151_626, _151_625)))))
end
| (Some (f), Some (w)) -> begin
(
# 1122 "FStar.TypeChecker.Tc.fst"
let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1123 "FStar.TypeChecker.Tc.fst"
let g_fw = (let _151_627 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_151_627))
in (let _151_630 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _151_629 = (let _151_628 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _151_628 g_when))
in (_151_630, _151_629)))))
end
| (None, Some (w)) -> begin
(
# 1128 "FStar.TypeChecker.Tc.fst"
let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (
# 1129 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _151_631 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_151_631, g_when))))
end)
in (match (_70_1630) with
| (c_weak, g_when_weak) -> begin
(
# 1134 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _151_633 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _151_632 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_151_633, _151_632, g_branch))))
end))
end)))
in (match (_70_1635) with
| (c, g_when, g_branch) -> begin
(
# 1152 "FStar.TypeChecker.Tc.fst"
let branch_guard = (
# 1154 "FStar.TypeChecker.Tc.fst"
let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (
# 1155 "FStar.TypeChecker.Tc.fst"
let discriminate = (fun scrutinee_tm f -> if ((let _151_643 = (let _151_642 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _151_642))
in (FStar_List.length _151_643)) > 1) then begin
(
# 1158 "FStar.TypeChecker.Tc.fst"
let disc = (let _151_644 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar None _151_644 (FStar_Ident.range_of_lid f.FStar_Syntax_Syntax.v)))
in (
# 1159 "FStar.TypeChecker.Tc.fst"
let disc = (let _151_646 = (let _151_645 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_151_645)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _151_646 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _151_647 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_151_647)::[])))
end else begin
[]
end)
in (
# 1163 "FStar.TypeChecker.Tc.fst"
let fail = (fun _70_1645 -> (match (()) with
| () -> begin
(let _151_653 = (let _151_652 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _151_651 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _151_650 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _151_652 _151_651 _151_650))))
in (FStar_All.failwith _151_653))
end))
in (
# 1169 "FStar.TypeChecker.Tc.fst"
let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (f, _70_1650) -> begin
f
end
| FStar_Syntax_Syntax.Tm_uinst (t, _70_1655) -> begin
(head_constructor t)
end
| _70_1659 -> begin
(fail ())
end))
in (
# 1174 "FStar.TypeChecker.Tc.fst"
let pat_exp = (let _151_656 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _151_656 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_70_1684) -> begin
(let _151_661 = (let _151_660 = (let _151_659 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _151_658 = (let _151_657 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_151_657)::[])
in (_151_659)::_151_658))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _151_660 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_151_661)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 1183 "FStar.TypeChecker.Tc.fst"
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
# 1188 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(
# 1191 "FStar.TypeChecker.Tc.fst"
let sub_term_guards = (let _151_668 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _70_1702 -> (match (_70_1702) with
| (ei, _70_1701) -> begin
(
# 1192 "FStar.TypeChecker.Tc.fst"
let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (
# 1193 "FStar.TypeChecker.Tc.fst"
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
| _70_1707 -> begin
[]
end))))))
in (
# 1199 "FStar.TypeChecker.Tc.fst"
let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid scrutinee_tm.FStar_Syntax_Syntax.pos)
end else begin
(
# 1202 "FStar.TypeChecker.Tc.fst"
let t = (let _151_674 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _151_674))
in (
# 1203 "FStar.TypeChecker.Tc.fst"
let _70_1715 = (FStar_Syntax_Util.type_u ())
in (match (_70_1715) with
| (k, _70_1714) -> begin
(
# 1204 "FStar.TypeChecker.Tc.fst"
let _70_1721 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_70_1721) with
| (t, _70_1718, _70_1720) -> begin
t
end))
end)))
end)
in (
# 1208 "FStar.TypeChecker.Tc.fst"
let branch_guard = (let _151_675 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _151_675 FStar_Syntax_Util.mk_disj_l))
in (
# 1211 "FStar.TypeChecker.Tc.fst"
let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
in (
# 1217 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (
# 1219 "FStar.TypeChecker.Tc.fst"
let _70_1729 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
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
# 1233 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1236 "FStar.TypeChecker.Tc.fst"
let _70_1746 = (check_let_bound_def true env lb)
in (match (_70_1746) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(
# 1239 "FStar.TypeChecker.Tc.fst"
let _70_1758 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(
# 1242 "FStar.TypeChecker.Tc.fst"
let g1 = (let _151_680 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _151_680 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1243 "FStar.TypeChecker.Tc.fst"
let _70_1753 = (let _151_684 = (let _151_683 = (let _151_682 = (let _151_681 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _151_681))
in (_151_682)::[])
in (FStar_TypeChecker_Util.generalize env _151_683))
in (FStar_List.hd _151_684))
in (match (_70_1753) with
| (_70_1749, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_70_1758) with
| (g1, e1, univ_vars, c1) -> begin
(
# 1247 "FStar.TypeChecker.Tc.fst"
let _70_1768 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(
# 1249 "FStar.TypeChecker.Tc.fst"
let _70_1761 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_70_1761) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(
# 1252 "FStar.TypeChecker.Tc.fst"
let _70_1762 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
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
# 1256 "FStar.TypeChecker.Tc.fst"
let _70_1764 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _151_687 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _151_687)))
end
in (match (_70_1768) with
| (e2, c1) -> begin
(
# 1261 "FStar.TypeChecker.Tc.fst"
let cres = (let _151_688 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_688))
in (
# 1262 "FStar.TypeChecker.Tc.fst"
let _70_1770 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1264 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _151_689 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_151_689, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _70_1774 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1281 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1284 "FStar.TypeChecker.Tc.fst"
let env = (
# 1284 "FStar.TypeChecker.Tc.fst"
let _70_1785 = env
in {FStar_TypeChecker_Env.solver = _70_1785.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1785.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1785.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1785.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1785.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1785.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1785.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1785.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1785.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1785.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1785.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1785.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_1785.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _70_1785.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_1785.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_1785.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1785.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1785.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1785.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1785.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1785.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1285 "FStar.TypeChecker.Tc.fst"
let _70_1794 = (let _151_693 = (let _151_692 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _151_692 Prims.fst))
in (check_let_bound_def false _151_693 lb))
in (match (_70_1794) with
| (e1, _70_1790, c1, g1, annotated) -> begin
(
# 1286 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (
# 1287 "FStar.TypeChecker.Tc.fst"
let x = (
# 1287 "FStar.TypeChecker.Tc.fst"
let _70_1796 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _70_1796.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_1796.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (
# 1288 "FStar.TypeChecker.Tc.fst"
let _70_1801 = (let _151_695 = (let _151_694 = (FStar_Syntax_Syntax.mk_binder x)
in (_151_694)::[])
in (FStar_Syntax_Subst.open_term _151_695 e2))
in (match (_70_1801) with
| (xb, e2) -> begin
(
# 1289 "FStar.TypeChecker.Tc.fst"
let xbinder = (FStar_List.hd xb)
in (
# 1290 "FStar.TypeChecker.Tc.fst"
let x = (Prims.fst xbinder)
in (
# 1291 "FStar.TypeChecker.Tc.fst"
let _70_1807 = (let _151_696 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _151_696 e2))
in (match (_70_1807) with
| (e2, c2, g2) -> begin
(
# 1292 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (x), c2))
in (
# 1293 "FStar.TypeChecker.Tc.fst"
let e = (let _151_699 = (let _151_698 = (let _151_697 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _151_697))
in FStar_Syntax_Syntax.Tm_let (_151_698))
in (FStar_Syntax_Syntax.mk _151_699 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 1294 "FStar.TypeChecker.Tc.fst"
let x_eq_e1 = (let _151_702 = (let _151_701 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _151_701 e1))
in (FStar_All.pipe_left (fun _151_700 -> FStar_TypeChecker_Common.NonTrivial (_151_700)) _151_702))
in (
# 1295 "FStar.TypeChecker.Tc.fst"
let g2 = (let _151_704 = (let _151_703 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _151_703 g2))
in (FStar_TypeChecker_Rel.close_guard xb _151_704))
in (
# 1297 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if annotated then begin
(e, cres, guard)
end else begin
(
# 1301 "FStar.TypeChecker.Tc.fst"
let _70_1813 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end)))))
end))))
end))))
end)))
end
| _70_1816 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1310 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1313 "FStar.TypeChecker.Tc.fst"
let _70_1828 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_70_1828) with
| (lbs, e2) -> begin
(
# 1315 "FStar.TypeChecker.Tc.fst"
let _70_1831 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_1831) with
| (env0, topt) -> begin
(
# 1316 "FStar.TypeChecker.Tc.fst"
let _70_1834 = (build_let_rec_env true env0 lbs)
in (match (_70_1834) with
| (lbs, rec_env) -> begin
(
# 1317 "FStar.TypeChecker.Tc.fst"
let _70_1837 = (check_let_recs rec_env lbs)
in (match (_70_1837) with
| (lbs, g_lbs) -> begin
(
# 1318 "FStar.TypeChecker.Tc.fst"
let g_lbs = (let _151_707 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _151_707 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1320 "FStar.TypeChecker.Tc.fst"
let all_lb_names = (let _151_710 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _151_710 (fun _151_709 -> Some (_151_709))))
in (
# 1322 "FStar.TypeChecker.Tc.fst"
let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(
# 1328 "FStar.TypeChecker.Tc.fst"
let ecs = (let _151_714 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _151_713 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _151_713)))))
in (FStar_TypeChecker_Util.generalize env _151_714))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _70_1848 -> (match (_70_1848) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (
# 1335 "FStar.TypeChecker.Tc.fst"
let cres = (let _151_716 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_716))
in (
# 1336 "FStar.TypeChecker.Tc.fst"
let _70_1851 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1338 "FStar.TypeChecker.Tc.fst"
let _70_1855 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_70_1855) with
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
| _70_1857 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1349 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1352 "FStar.TypeChecker.Tc.fst"
let _70_1869 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_70_1869) with
| (lbs, e2) -> begin
(
# 1354 "FStar.TypeChecker.Tc.fst"
let _70_1872 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_1872) with
| (env0, topt) -> begin
(
# 1355 "FStar.TypeChecker.Tc.fst"
let _70_1875 = (build_let_rec_env false env0 lbs)
in (match (_70_1875) with
| (lbs, rec_env) -> begin
(
# 1356 "FStar.TypeChecker.Tc.fst"
let _70_1878 = (check_let_recs rec_env lbs)
in (match (_70_1878) with
| (lbs, g_lbs) -> begin
(
# 1358 "FStar.TypeChecker.Tc.fst"
let _70_1896 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _70_1881 _70_1890 -> (match ((_70_1881, _70_1890)) with
| ((bvs, env), {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _70_1888; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _70_1885; FStar_Syntax_Syntax.lbdef = _70_1883}) -> begin
(
# 1359 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env x ([], t))
in (let _151_724 = (let _151_723 = (
# 1360 "FStar.TypeChecker.Tc.fst"
let _70_1892 = (FStar_Util.left x)
in {FStar_Syntax_Syntax.ppname = _70_1892.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_1892.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (_151_723)::bvs)
in (_151_724, env)))
end)) ([], env)))
in (match (_70_1896) with
| (bvs, env) -> begin
(
# 1361 "FStar.TypeChecker.Tc.fst"
let bvs = (FStar_List.rev bvs)
in (
# 1363 "FStar.TypeChecker.Tc.fst"
let _70_1901 = (tc_term env e2)
in (match (_70_1901) with
| (e2, cres, g2) -> begin
(
# 1364 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (
# 1365 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (
# 1366 "FStar.TypeChecker.Tc.fst"
let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (
# 1367 "FStar.TypeChecker.Tc.fst"
let cres = (
# 1367 "FStar.TypeChecker.Tc.fst"
let _70_1905 = cres
in {FStar_Syntax_Syntax.eff_name = _70_1905.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _70_1905.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _70_1905.FStar_Syntax_Syntax.comp})
in (
# 1369 "FStar.TypeChecker.Tc.fst"
let _70_1910 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_70_1910) with
| (lbs, e2) -> begin
(
# 1370 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_70_1913) -> begin
(e, cres, guard)
end
| None -> begin
(
# 1374 "FStar.TypeChecker.Tc.fst"
let _70_1916 = (check_no_escape None env bvs tres)
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
| _70_1919 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (
# 1385 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1386 "FStar.TypeChecker.Tc.fst"
let _70_1952 = (FStar_List.fold_left (fun _70_1926 lb -> (match (_70_1926) with
| (lbs, env) -> begin
(
# 1387 "FStar.TypeChecker.Tc.fst"
let _70_1931 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_70_1931) with
| (univ_vars, t, check_t) -> begin
(
# 1388 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (
# 1389 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (
# 1390 "FStar.TypeChecker.Tc.fst"
let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(
# 1395 "FStar.TypeChecker.Tc.fst"
let _70_1940 = (let _151_731 = (let _151_730 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _151_730))
in (tc_check_tot_or_gtot_term (
# 1395 "FStar.TypeChecker.Tc.fst"
let _70_1934 = env0
in {FStar_TypeChecker_Env.solver = _70_1934.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1934.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1934.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1934.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1934.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1934.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1934.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1934.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1934.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1934.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1934.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1934.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_1934.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _70_1934.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _70_1934.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_1934.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1934.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1934.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1934.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1934.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1934.FStar_TypeChecker_Env.use_bv_sorts}) t _151_731))
in (match (_70_1940) with
| (t, _70_1938, g) -> begin
(
# 1396 "FStar.TypeChecker.Tc.fst"
let _70_1941 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (
# 1398 "FStar.TypeChecker.Tc.fst"
let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(
# 1400 "FStar.TypeChecker.Tc.fst"
let _70_1944 = env
in {FStar_TypeChecker_Env.solver = _70_1944.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1944.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1944.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1944.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1944.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1944.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1944.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1944.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1944.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1944.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1944.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1944.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _70_1944.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _70_1944.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_1944.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_1944.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1944.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1944.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1944.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1944.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1944.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (
# 1402 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1402 "FStar.TypeChecker.Tc.fst"
let _70_1947 = lb
in {FStar_Syntax_Syntax.lbname = _70_1947.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _70_1947.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_70_1952) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (
# 1409 "FStar.TypeChecker.Tc.fst"
let _70_1965 = (let _151_736 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 1410 "FStar.TypeChecker.Tc.fst"
let _70_1959 = (let _151_735 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _151_735 lb.FStar_Syntax_Syntax.lbdef))
in (match (_70_1959) with
| (e, c, g) -> begin
(
# 1411 "FStar.TypeChecker.Tc.fst"
let _70_1960 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1413 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _151_736 FStar_List.unzip))
in (match (_70_1965) with
| (lbs, gs) -> begin
(
# 1415 "FStar.TypeChecker.Tc.fst"
let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (
# 1429 "FStar.TypeChecker.Tc.fst"
let _70_1973 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_70_1973) with
| (env1, _70_1972) -> begin
(
# 1430 "FStar.TypeChecker.Tc.fst"
let e1 = lb.FStar_Syntax_Syntax.lbdef
in (
# 1433 "FStar.TypeChecker.Tc.fst"
let _70_1979 = (check_lbtyp top_level env lb)
in (match (_70_1979) with
| (topt, wf_annot, univ_vars, env1) -> begin
(
# 1435 "FStar.TypeChecker.Tc.fst"
let _70_1980 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1439 "FStar.TypeChecker.Tc.fst"
let _70_1987 = (tc_maybe_toplevel_term (
# 1439 "FStar.TypeChecker.Tc.fst"
let _70_1982 = env1
in {FStar_TypeChecker_Env.solver = _70_1982.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1982.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1982.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1982.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1982.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1982.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1982.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1982.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1982.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1982.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1982.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1982.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_1982.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _70_1982.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_1982.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_1982.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1982.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1982.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1982.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1982.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1982.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_70_1987) with
| (e1, c1, g1) -> begin
(
# 1442 "FStar.TypeChecker.Tc.fst"
let _70_1991 = (let _151_743 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _70_1988 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _151_743 e1 c1 wf_annot))
in (match (_70_1991) with
| (c1, guard_f) -> begin
(
# 1445 "FStar.TypeChecker.Tc.fst"
let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (
# 1447 "FStar.TypeChecker.Tc.fst"
let _70_1993 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
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
# 1459 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 1462 "FStar.TypeChecker.Tc.fst"
let _70_2000 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _70_2003 -> begin
(
# 1466 "FStar.TypeChecker.Tc.fst"
let _70_2006 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_70_2006) with
| (univ_vars, t) -> begin
(
# 1467 "FStar.TypeChecker.Tc.fst"
let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _151_749 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _151_749))
end else begin
(
# 1474 "FStar.TypeChecker.Tc.fst"
let _70_2011 = (FStar_Syntax_Util.type_u ())
in (match (_70_2011) with
| (k, _70_2010) -> begin
(
# 1475 "FStar.TypeChecker.Tc.fst"
let _70_2016 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_70_2016) with
| (t, _70_2014, g) -> begin
(
# 1476 "FStar.TypeChecker.Tc.fst"
let _70_2017 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _151_752 = (let _151_750 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _151_750))
in (let _151_751 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _151_752 _151_751)))
end else begin
()
end
in (
# 1480 "FStar.TypeChecker.Tc.fst"
let t = (norm env1 t)
in (let _151_753 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _151_753))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _70_2023 -> (match (_70_2023) with
| (x, imp) -> begin
(
# 1485 "FStar.TypeChecker.Tc.fst"
let _70_2026 = (FStar_Syntax_Util.type_u ())
in (match (_70_2026) with
| (tu, u) -> begin
(
# 1486 "FStar.TypeChecker.Tc.fst"
let _70_2031 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_70_2031) with
| (t, _70_2029, g) -> begin
(
# 1487 "FStar.TypeChecker.Tc.fst"
let x = ((
# 1487 "FStar.TypeChecker.Tc.fst"
let _70_2032 = x
in {FStar_Syntax_Syntax.ppname = _70_2032.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_2032.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (
# 1488 "FStar.TypeChecker.Tc.fst"
let _70_2035 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
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
# 1493 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_TypeChecker_Rel.trivial_guard, [])
end
| b::bs -> begin
(
# 1496 "FStar.TypeChecker.Tc.fst"
let _70_2050 = (tc_binder env b)
in (match (_70_2050) with
| (b, env', g, u) -> begin
(
# 1497 "FStar.TypeChecker.Tc.fst"
let _70_2055 = (aux env' bs)
in (match (_70_2055) with
| (bs, env', g', us) -> begin
(let _151_766 = (let _151_765 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _151_765))
in ((b)::bs, env', _151_766, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (
# 1502 "FStar.TypeChecker.Tc.fst"
let tc_args = (fun env args -> (FStar_List.fold_right (fun _70_2063 _70_2066 -> (match ((_70_2063, _70_2066)) with
| ((t, imp), (args, g)) -> begin
(
# 1506 "FStar.TypeChecker.Tc.fst"
let _70_2071 = (tc_term env t)
in (match (_70_2071) with
| (t, _70_2069, g') -> begin
(let _151_775 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _151_775))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _70_2075 -> (match (_70_2075) with
| (pats, g) -> begin
(
# 1509 "FStar.TypeChecker.Tc.fst"
let _70_2078 = (tc_args env p)
in (match (_70_2078) with
| (args, g') -> begin
(let _151_778 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _151_778))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1514 "FStar.TypeChecker.Tc.fst"
let _70_2084 = (tc_maybe_toplevel_term env e)
in (match (_70_2084) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(
# 1517 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (
# 1518 "FStar.TypeChecker.Tc.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 1519 "FStar.TypeChecker.Tc.fst"
let _70_2087 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_781 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _151_781))
end else begin
()
end
in (
# 1520 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 1521 "FStar.TypeChecker.Tc.fst"
let _70_2092 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _151_782 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_151_782, false))
end else begin
(let _151_783 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_151_783, true))
end
in (match (_70_2092) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _151_784 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _151_784))
end
| _70_2096 -> begin
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
# 1535 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))

# 1539 "FStar.TypeChecker.Tc.fst"
let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (
# 1540 "FStar.TypeChecker.Tc.fst"
let _70_2106 = (tc_tot_or_gtot_term env t)
in (match (_70_2106) with
| (t, c, g) -> begin
(
# 1541 "FStar.TypeChecker.Tc.fst"
let _70_2107 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))

# 1544 "FStar.TypeChecker.Tc.fst"
let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (
# 1545 "FStar.TypeChecker.Tc.fst"
let _70_2115 = (tc_check_tot_or_gtot_term env t k)
in (match (_70_2115) with
| (t, c, g) -> begin
(
# 1546 "FStar.TypeChecker.Tc.fst"
let _70_2116 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))

# 1549 "FStar.TypeChecker.Tc.fst"
let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _151_810 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _151_810)))

# 1552 "FStar.TypeChecker.Tc.fst"
let check_nogen = (fun env t k -> (
# 1553 "FStar.TypeChecker.Tc.fst"
let t = (tc_check_trivial_guard env t k)
in (let _151_814 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _151_814))))

# 1556 "FStar.TypeChecker.Tc.fst"
let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (
# 1557 "FStar.TypeChecker.Tc.fst"
let _70_2131 = (tc_binders env tps)
in (match (_70_2131) with
| (tps, env, g, us) -> begin
(
# 1558 "FStar.TypeChecker.Tc.fst"
let _70_2132 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))

# 1561 "FStar.TypeChecker.Tc.fst"
let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (
# 1562 "FStar.TypeChecker.Tc.fst"
let fail = (fun _70_2138 -> (match (()) with
| () -> begin
(let _151_829 = (let _151_828 = (let _151_827 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_151_827, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_151_828))
in (Prims.raise _151_829))
end))
in (
# 1563 "FStar.TypeChecker.Tc.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1566 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _70_2155)::(wp, _70_2151)::(_wlp, _70_2147)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _70_2159 -> begin
(fail ())
end))
end
| _70_2161 -> begin
(fail ())
end))))

# 1573 "FStar.TypeChecker.Tc.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 1576 "FStar.TypeChecker.Tc.fst"
let _70_2168 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_70_2168) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _70_2170 -> begin
(
# 1579 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow binders c)
in (
# 1580 "FStar.TypeChecker.Tc.fst"
let _70_2174 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_70_2174) with
| (uvs, t') -> begin
(match ((let _151_836 = (FStar_Syntax_Subst.compress t')
in _151_836.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _70_2180 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 1585 "FStar.TypeChecker.Tc.fst"
let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (
# 1586 "FStar.TypeChecker.Tc.fst"
let fail = (fun t -> (let _151_847 = (let _151_846 = (let _151_845 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_151_845, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_151_846))
in (Prims.raise _151_847)))
in (match ((let _151_848 = (FStar_Syntax_Subst.compress signature)
in _151_848.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1589 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _70_2201)::(wp, _70_2197)::(_wlp, _70_2193)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _70_2205 -> begin
(fail signature)
end))
end
| _70_2207 -> begin
(fail signature)
end)))

# 1596 "FStar.TypeChecker.Tc.fst"
let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (
# 1597 "FStar.TypeChecker.Tc.fst"
let _70_2212 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_70_2212) with
| (a, wp) -> begin
(
# 1598 "FStar.TypeChecker.Tc.fst"
let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _70_2215 -> begin
(
# 1602 "FStar.TypeChecker.Tc.fst"
let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (
# 1603 "FStar.TypeChecker.Tc.fst"
let op = (fun ts -> (
# 1604 "FStar.TypeChecker.Tc.fst"
let _70_2219 = ()
in (
# 1605 "FStar.TypeChecker.Tc.fst"
let t0 = (Prims.snd ts)
in (
# 1606 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (
# 1608 "FStar.TypeChecker.Tc.fst"
let _70_2223 = ed
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
in {FStar_Syntax_Syntax.qualifiers = _70_2223.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _70_2223.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _70_2223.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _70_2223.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _70_2223.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _151_867; FStar_Syntax_Syntax.bind_wp = _151_866; FStar_Syntax_Syntax.bind_wlp = _151_865; FStar_Syntax_Syntax.if_then_else = _151_864; FStar_Syntax_Syntax.ite_wp = _151_863; FStar_Syntax_Syntax.ite_wlp = _151_862; FStar_Syntax_Syntax.wp_binop = _151_861; FStar_Syntax_Syntax.wp_as_type = _151_860; FStar_Syntax_Syntax.close_wp = _151_859; FStar_Syntax_Syntax.assert_p = _151_858; FStar_Syntax_Syntax.assume_p = _151_857; FStar_Syntax_Syntax.null_wp = _151_856; FStar_Syntax_Syntax.trivial = _151_855}))))))))))))))))
end)
in (ed, a, wp))
end)))

# 1624 "FStar.TypeChecker.Tc.fst"
let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (
# 1625 "FStar.TypeChecker.Tc.fst"
let _70_2228 = ()
in (
# 1626 "FStar.TypeChecker.Tc.fst"
let _70_2232 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_70_2232) with
| (binders_un, signature_un) -> begin
(
# 1627 "FStar.TypeChecker.Tc.fst"
let _70_2237 = (tc_tparams env0 binders_un)
in (match (_70_2237) with
| (binders, env, _70_2236) -> begin
(
# 1628 "FStar.TypeChecker.Tc.fst"
let _70_2241 = (tc_trivial_guard env signature_un)
in (match (_70_2241) with
| (signature, _70_2240) -> begin
(
# 1629 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1629 "FStar.TypeChecker.Tc.fst"
let _70_2242 = ed
in {FStar_Syntax_Syntax.qualifiers = _70_2242.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _70_2242.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _70_2242.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _70_2242.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _70_2242.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _70_2242.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = _70_2242.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _70_2242.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _70_2242.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = _70_2242.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _70_2242.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _70_2242.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _70_2242.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _70_2242.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _70_2242.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _70_2242.FStar_Syntax_Syntax.trivial})
in (
# 1632 "FStar.TypeChecker.Tc.fst"
let _70_2248 = (open_effect_decl env ed)
in (match (_70_2248) with
| (ed, a, wp_a) -> begin
(
# 1633 "FStar.TypeChecker.Tc.fst"
let get_effect_signature = (fun _70_2250 -> (match (()) with
| () -> begin
(
# 1634 "FStar.TypeChecker.Tc.fst"
let _70_2254 = (tc_trivial_guard env signature_un)
in (match (_70_2254) with
| (signature, _70_2253) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (
# 1638 "FStar.TypeChecker.Tc.fst"
let env = (let _151_874 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _151_874))
in (
# 1640 "FStar.TypeChecker.Tc.fst"
let _70_2256 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _151_877 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _151_876 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _151_875 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checked effect signature: %s %s : %s\n" _151_877 _151_876 _151_875))))
end else begin
()
end
in (
# 1646 "FStar.TypeChecker.Tc.fst"
let check_and_gen' = (fun env _70_2263 k -> (match (_70_2263) with
| (_70_2261, t) -> begin
(check_and_gen env t k)
end))
in (
# 1649 "FStar.TypeChecker.Tc.fst"
let ret = (
# 1650 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_889 = (let _151_887 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_886 = (let _151_885 = (let _151_884 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _151_884))
in (_151_885)::[])
in (_151_887)::_151_886))
in (let _151_888 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _151_889 _151_888)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (
# 1653 "FStar.TypeChecker.Tc.fst"
let bind_wp = (
# 1654 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1655 "FStar.TypeChecker.Tc.fst"
let _70_2270 = (get_effect_signature ())
in (match (_70_2270) with
| (b, wp_b) -> begin
(
# 1656 "FStar.TypeChecker.Tc.fst"
let a_wp_b = (let _151_893 = (let _151_891 = (let _151_890 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _151_890))
in (_151_891)::[])
in (let _151_892 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _151_893 _151_892)))
in (
# 1657 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = a_wp_b
in (
# 1658 "FStar.TypeChecker.Tc.fst"
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
# 1664 "FStar.TypeChecker.Tc.fst"
let bind_wlp = (
# 1665 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1666 "FStar.TypeChecker.Tc.fst"
let _70_2278 = (get_effect_signature ())
in (match (_70_2278) with
| (b, wlp_b) -> begin
(
# 1667 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = (let _151_910 = (let _151_908 = (let _151_907 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _151_907))
in (_151_908)::[])
in (let _151_909 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _151_910 _151_909)))
in (
# 1668 "FStar.TypeChecker.Tc.fst"
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
# 1674 "FStar.TypeChecker.Tc.fst"
let if_then_else = (
# 1675 "FStar.TypeChecker.Tc.fst"
let p = (let _151_921 = (let _151_920 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_920 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _151_921))
in (
# 1676 "FStar.TypeChecker.Tc.fst"
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
# 1682 "FStar.TypeChecker.Tc.fst"
let ite_wp = (
# 1683 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1684 "FStar.TypeChecker.Tc.fst"
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
# 1690 "FStar.TypeChecker.Tc.fst"
let ite_wlp = (
# 1691 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1692 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_942 = (let _151_940 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_939 = (let _151_938 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (_151_938)::[])
in (_151_940)::_151_939))
in (let _151_941 = (FStar_Syntax_Syntax.mk_Total wlp_a)
in (FStar_Syntax_Util.arrow _151_942 _151_941)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wlp expected_k)))
in (
# 1697 "FStar.TypeChecker.Tc.fst"
let wp_binop = (
# 1698 "FStar.TypeChecker.Tc.fst"
let bin_op = (
# 1699 "FStar.TypeChecker.Tc.fst"
let _70_2293 = (FStar_Syntax_Util.type_u ())
in (match (_70_2293) with
| (t1, u1) -> begin
(
# 1700 "FStar.TypeChecker.Tc.fst"
let _70_2296 = (FStar_Syntax_Util.type_u ())
in (match (_70_2296) with
| (t2, u2) -> begin
(
# 1701 "FStar.TypeChecker.Tc.fst"
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
# 1703 "FStar.TypeChecker.Tc.fst"
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
# 1710 "FStar.TypeChecker.Tc.fst"
let wp_as_type = (
# 1711 "FStar.TypeChecker.Tc.fst"
let _70_2304 = (FStar_Syntax_Util.type_u ())
in (match (_70_2304) with
| (t, _70_2303) -> begin
(
# 1712 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_962 = (let _151_960 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_959 = (let _151_958 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_958)::[])
in (_151_960)::_151_959))
in (let _151_961 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _151_962 _151_961)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (
# 1717 "FStar.TypeChecker.Tc.fst"
let close_wp = (
# 1718 "FStar.TypeChecker.Tc.fst"
let b = (let _151_964 = (let _151_963 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_963 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _151_964))
in (
# 1719 "FStar.TypeChecker.Tc.fst"
let b_wp_a = (let _151_968 = (let _151_966 = (let _151_965 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _151_965))
in (_151_966)::[])
in (let _151_967 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_968 _151_967)))
in (
# 1720 "FStar.TypeChecker.Tc.fst"
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
# 1724 "FStar.TypeChecker.Tc.fst"
let assert_p = (
# 1725 "FStar.TypeChecker.Tc.fst"
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
# 1731 "FStar.TypeChecker.Tc.fst"
let assume_p = (
# 1732 "FStar.TypeChecker.Tc.fst"
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
# 1738 "FStar.TypeChecker.Tc.fst"
let null_wp = (
# 1739 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_996 = (let _151_994 = (FStar_Syntax_Syntax.mk_binder a)
in (_151_994)::[])
in (let _151_995 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_996 _151_995)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (
# 1743 "FStar.TypeChecker.Tc.fst"
let trivial_wp = (
# 1744 "FStar.TypeChecker.Tc.fst"
let _70_2320 = (FStar_Syntax_Util.type_u ())
in (match (_70_2320) with
| (t, _70_2319) -> begin
(
# 1745 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1001 = (let _151_999 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_998 = (let _151_997 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_997)::[])
in (_151_999)::_151_998))
in (let _151_1000 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _151_1001 _151_1000)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (
# 1751 "FStar.TypeChecker.Tc.fst"
let t = (let _151_1002 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _151_1002))
in (
# 1752 "FStar.TypeChecker.Tc.fst"
let _70_2326 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_70_2326) with
| (univs, t) -> begin
(
# 1753 "FStar.TypeChecker.Tc.fst"
let _70_2342 = (match ((let _151_1004 = (let _151_1003 = (FStar_Syntax_Subst.compress t)
in _151_1003.FStar_Syntax_Syntax.n)
in (binders, _151_1004))) with
| ([], _70_2329) -> begin
([], t)
end
| (_70_2332, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _70_2339 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_70_2342) with
| (binders, signature) -> begin
(
# 1757 "FStar.TypeChecker.Tc.fst"
let close = (fun ts -> (let _151_1007 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _151_1007)))
in (
# 1758 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1758 "FStar.TypeChecker.Tc.fst"
let _70_2345 = ed
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
in {FStar_Syntax_Syntax.qualifiers = _70_2345.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _70_2345.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _151_1020; FStar_Syntax_Syntax.bind_wp = _151_1019; FStar_Syntax_Syntax.bind_wlp = _151_1018; FStar_Syntax_Syntax.if_then_else = _151_1017; FStar_Syntax_Syntax.ite_wp = _151_1016; FStar_Syntax_Syntax.ite_wlp = _151_1015; FStar_Syntax_Syntax.wp_binop = _151_1014; FStar_Syntax_Syntax.wp_as_type = _151_1013; FStar_Syntax_Syntax.close_wp = _151_1012; FStar_Syntax_Syntax.assert_p = _151_1011; FStar_Syntax_Syntax.assume_p = _151_1010; FStar_Syntax_Syntax.null_wp = _151_1009; FStar_Syntax_Syntax.trivial = _151_1008}))))))))))))))
in (
# 1776 "FStar.TypeChecker.Tc.fst"
let _70_2348 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
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

# 1780 "FStar.TypeChecker.Tc.fst"
let tc_lex_t = (fun env ses quals lids -> (
# 1787 "FStar.TypeChecker.Tc.fst"
let _70_2354 = ()
in (
# 1788 "FStar.TypeChecker.Tc.fst"
let _70_2362 = ()
in (match (ses) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _70_2391, _70_2393, [], r)::FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _70_2382, r1)::FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _70_2371, r2)::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(
# 1803 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (
# 1804 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (
# 1805 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (
# 1806 "FStar.TypeChecker.Tc.fst"
let tc = FStar_Syntax_Syntax.Sig_inductive_typ ((lex_t, (u)::[], [], t, [], (FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[], [], r))
in (
# 1808 "FStar.TypeChecker.Tc.fst"
let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (
# 1809 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (let _151_1028 = (let _151_1027 = (let _151_1026 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid r1)
in (_151_1026, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_151_1027))
in (FStar_Syntax_Syntax.mk _151_1028 None r1))
in (
# 1810 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (
# 1811 "FStar.TypeChecker.Tc.fst"
let dc_lextop = FStar_Syntax_Syntax.Sig_datacon ((lex_top, (utop)::[], lex_top_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r1))
in (
# 1813 "FStar.TypeChecker.Tc.fst"
let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1814 "FStar.TypeChecker.Tc.fst"
let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1815 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (
# 1816 "FStar.TypeChecker.Tc.fst"
let a = (let _151_1029 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _151_1029))
in (
# 1817 "FStar.TypeChecker.Tc.fst"
let hd = (let _151_1030 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _151_1030))
in (
# 1818 "FStar.TypeChecker.Tc.fst"
let tl = (let _151_1034 = (let _151_1033 = (let _151_1032 = (let _151_1031 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid r2)
in (_151_1031, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_151_1032))
in (FStar_Syntax_Syntax.mk _151_1033 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _151_1034))
in (
# 1819 "FStar.TypeChecker.Tc.fst"
let res = (let _151_1037 = (let _151_1036 = (let _151_1035 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid r2)
in (_151_1035, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_151_1036))
in (FStar_Syntax_Syntax.mk _151_1037 None r2))
in (let _151_1038 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _151_1038))))))
in (
# 1821 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (
# 1822 "FStar.TypeChecker.Tc.fst"
let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _151_1040 = (let _151_1039 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _151_1039))
in FStar_Syntax_Syntax.Sig_bundle (_151_1040)))))))))))))))
end
| _70_2417 -> begin
(let _151_1042 = (let _151_1041 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _151_1041))
in (FStar_All.failwith _151_1042))
end))))

# 1828 "FStar.TypeChecker.Tc.fst"
let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (
# 1891 "FStar.TypeChecker.Tc.fst"
let warn_positivity = (fun l r -> (let _151_1056 = (let _151_1055 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _151_1055))
in (FStar_TypeChecker_Errors.warn r _151_1056)))
in (
# 1893 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1896 "FStar.TypeChecker.Tc.fst"
let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(
# 1901 "FStar.TypeChecker.Tc.fst"
let _70_2439 = ()
in (
# 1902 "FStar.TypeChecker.Tc.fst"
let _70_2441 = (warn_positivity tc r)
in (
# 1903 "FStar.TypeChecker.Tc.fst"
let _70_2445 = (FStar_Syntax_Subst.open_term tps k)
in (match (_70_2445) with
| (tps, k) -> begin
(
# 1904 "FStar.TypeChecker.Tc.fst"
let _70_2449 = (tc_tparams env tps)
in (match (_70_2449) with
| (tps, env_tps, us) -> begin
(
# 1905 "FStar.TypeChecker.Tc.fst"
let _70_2452 = (FStar_Syntax_Util.arrow_formals k)
in (match (_70_2452) with
| (indices, t) -> begin
(
# 1906 "FStar.TypeChecker.Tc.fst"
let _70_2456 = (tc_tparams env_tps indices)
in (match (_70_2456) with
| (indices, env', us') -> begin
(
# 1907 "FStar.TypeChecker.Tc.fst"
let _70_2460 = (tc_trivial_guard env' t)
in (match (_70_2460) with
| (t, _70_2459) -> begin
(
# 1908 "FStar.TypeChecker.Tc.fst"
let k = (let _151_1061 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _151_1061))
in (
# 1909 "FStar.TypeChecker.Tc.fst"
let _70_2464 = (FStar_Syntax_Util.type_u ())
in (match (_70_2464) with
| (t_type, u) -> begin
(
# 1910 "FStar.TypeChecker.Tc.fst"
let _70_2465 = (let _151_1062 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _151_1062))
in (
# 1912 "FStar.TypeChecker.Tc.fst"
let t_tc = (let _151_1063 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _151_1063))
in (
# 1913 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 1914 "FStar.TypeChecker.Tc.fst"
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
| _70_2471 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1921 "FStar.TypeChecker.Tc.fst"
let positive_if_pure = (fun _70_2473 l -> ())
in (
# 1924 "FStar.TypeChecker.Tc.fst"
let tc_data = (fun env tcs _70_6 -> (match (_70_6) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(
# 1926 "FStar.TypeChecker.Tc.fst"
let _70_2490 = ()
in (
# 1928 "FStar.TypeChecker.Tc.fst"
let _70_2525 = (
# 1929 "FStar.TypeChecker.Tc.fst"
let tps_u_opt = (FStar_Util.find_map tcs (fun _70_2494 -> (match (_70_2494) with
| (se, u_tc) -> begin
if (let _151_1077 = (let _151_1076 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _151_1076))
in (FStar_Ident.lid_equals tc_lid _151_1077)) then begin
(
# 1931 "FStar.TypeChecker.Tc.fst"
let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_70_2496, _70_2498, tps, _70_2501, _70_2503, _70_2505, _70_2507, _70_2509) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _70_2515 -> (match (_70_2515) with
| (x, _70_2514) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _70_2517 -> begin
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
in (match (_70_2525) with
| (tps, u_tc) -> begin
(
# 1944 "FStar.TypeChecker.Tc.fst"
let _70_2545 = (match ((let _151_1079 = (FStar_Syntax_Subst.compress t)
in _151_1079.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(
# 1949 "FStar.TypeChecker.Tc.fst"
let _70_2533 = (FStar_Util.first_N ntps bs)
in (match (_70_2533) with
| (_70_2531, bs') -> begin
(
# 1950 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (
# 1951 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _70_2539 -> (match (_70_2539) with
| (x, _70_2538) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _151_1082 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _151_1082))))
end))
end
| _70_2542 -> begin
([], t)
end)
in (match (_70_2545) with
| (arguments, result) -> begin
(
# 1955 "FStar.TypeChecker.Tc.fst"
let _70_2546 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1085 = (FStar_Syntax_Print.lid_to_string c)
in (let _151_1084 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _151_1083 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _151_1085 _151_1084 _151_1083))))
end else begin
()
end
in (
# 1961 "FStar.TypeChecker.Tc.fst"
let _70_2551 = (tc_tparams env arguments)
in (match (_70_2551) with
| (arguments, env', us) -> begin
(
# 1962 "FStar.TypeChecker.Tc.fst"
let _70_2555 = (tc_trivial_guard env' result)
in (match (_70_2555) with
| (result, _70_2554) -> begin
(
# 1963 "FStar.TypeChecker.Tc.fst"
let _70_2559 = (FStar_Syntax_Util.head_and_args result)
in (match (_70_2559) with
| (head, _70_2558) -> begin
(
# 1964 "FStar.TypeChecker.Tc.fst"
let _70_2567 = (match ((let _151_1086 = (FStar_Syntax_Subst.compress head)
in _151_1086.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _70_2562) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v tc_lid) -> begin
()
end
| _70_2566 -> begin
(let _151_1090 = (let _151_1089 = (let _151_1088 = (let _151_1087 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _151_1087))
in (_151_1088, r))
in FStar_Syntax_Syntax.Error (_151_1089))
in (Prims.raise _151_1090))
end)
in (
# 1967 "FStar.TypeChecker.Tc.fst"
let g = (FStar_List.fold_left2 (fun g _70_2573 u_x -> (match (_70_2573) with
| (x, _70_2572) -> begin
(
# 1968 "FStar.TypeChecker.Tc.fst"
let _70_2575 = ()
in (let _151_1094 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _151_1094)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (
# 1974 "FStar.TypeChecker.Tc.fst"
let t = (let _151_1098 = (let _151_1096 = (FStar_All.pipe_right tps (FStar_List.map (fun _70_2581 -> (match (_70_2581) with
| (x, _70_2580) -> begin
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
| _70_2584 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1982 "FStar.TypeChecker.Tc.fst"
let generalize_and_inst_within = (fun env g tcs datas -> (
# 1983 "FStar.TypeChecker.Tc.fst"
let _70_2590 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 1984 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _70_7 -> (match (_70_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_70_2594, _70_2596, tps, k, _70_2600, _70_2602, _70_2604, _70_2606) -> begin
(let _151_1109 = (let _151_1108 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _151_1108))
in (FStar_Syntax_Syntax.null_binder _151_1109))
end
| _70_2610 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 1987 "FStar.TypeChecker.Tc.fst"
let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _70_8 -> (match (_70_8) with
| FStar_Syntax_Syntax.Sig_datacon (_70_2614, _70_2616, t, _70_2619, _70_2621, _70_2623, _70_2625, _70_2627) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _70_2631 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 1990 "FStar.TypeChecker.Tc.fst"
let t = (let _151_1111 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _151_1111))
in (
# 1991 "FStar.TypeChecker.Tc.fst"
let _70_2634 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1112 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _151_1112))
end else begin
()
end
in (
# 1992 "FStar.TypeChecker.Tc.fst"
let _70_2638 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_70_2638) with
| (uvs, t) -> begin
(
# 1993 "FStar.TypeChecker.Tc.fst"
let _70_2640 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1116 = (let _151_1114 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _151_1114 (FStar_String.concat ", ")))
in (let _151_1115 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _151_1116 _151_1115)))
end else begin
()
end
in (
# 1996 "FStar.TypeChecker.Tc.fst"
let _70_2644 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_70_2644) with
| (uvs, t) -> begin
(
# 1997 "FStar.TypeChecker.Tc.fst"
let _70_2648 = (FStar_Syntax_Util.arrow_formals t)
in (match (_70_2648) with
| (args, _70_2647) -> begin
(
# 1998 "FStar.TypeChecker.Tc.fst"
let _70_2651 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_70_2651) with
| (tc_types, data_types) -> begin
(
# 1999 "FStar.TypeChecker.Tc.fst"
let tcs = (FStar_List.map2 (fun _70_2655 se -> (match (_70_2655) with
| (x, _70_2654) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _70_2659, tps, _70_2662, mutuals, datas, quals, r) -> begin
(
# 2001 "FStar.TypeChecker.Tc.fst"
let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (
# 2002 "FStar.TypeChecker.Tc.fst"
let _70_2685 = (match ((let _151_1119 = (FStar_Syntax_Subst.compress ty)
in _151_1119.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 2004 "FStar.TypeChecker.Tc.fst"
let _70_2676 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_70_2676) with
| (tps, rest) -> begin
(
# 2005 "FStar.TypeChecker.Tc.fst"
let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _70_2679 -> begin
(let _151_1120 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _151_1120 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _70_2682 -> begin
([], ty)
end)
in (match (_70_2685) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _70_2687 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (
# 2015 "FStar.TypeChecker.Tc.fst"
let datas = (match (uvs) with
| [] -> begin
datas
end
| _70_2691 -> begin
(
# 2018 "FStar.TypeChecker.Tc.fst"
let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _151_1121 -> FStar_Syntax_Syntax.U_name (_151_1121))))
in (
# 2019 "FStar.TypeChecker.Tc.fst"
let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _70_9 -> (match (_70_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _70_2696, _70_2698, _70_2700, _70_2702, _70_2704, _70_2706, _70_2708) -> begin
(tc, uvs_universes)
end
| _70_2712 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _70_2717 d -> (match (_70_2717) with
| (t, _70_2716) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _70_2721, _70_2723, tc, ntps, quals, mutuals, r) -> begin
(
# 2023 "FStar.TypeChecker.Tc.fst"
let ty = (let _151_1125 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _151_1125 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _70_2733 -> begin
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
# 2029 "FStar.TypeChecker.Tc.fst"
let _70_2743 = (FStar_All.pipe_right ses (FStar_List.partition (fun _70_10 -> (match (_70_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_70_2737) -> begin
true
end
| _70_2740 -> begin
false
end))))
in (match (_70_2743) with
| (tys, datas) -> begin
(
# 2031 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2034 "FStar.TypeChecker.Tc.fst"
let _70_2760 = (FStar_List.fold_right (fun tc _70_2749 -> (match (_70_2749) with
| (env, all_tcs, g) -> begin
(
# 2035 "FStar.TypeChecker.Tc.fst"
let _70_2753 = (tc_tycon env tc)
in (match (_70_2753) with
| (env, tc, tc_u) -> begin
(
# 2036 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (
# 2037 "FStar.TypeChecker.Tc.fst"
let _70_2755 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1129 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _151_1129))
end else begin
()
end
in (let _151_1130 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _151_1130))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_70_2760) with
| (env, tcs, g) -> begin
(
# 2044 "FStar.TypeChecker.Tc.fst"
let _70_2770 = (FStar_List.fold_right (fun se _70_2764 -> (match (_70_2764) with
| (datas, g) -> begin
(
# 2045 "FStar.TypeChecker.Tc.fst"
let _70_2767 = (tc_data env tcs se)
in (match (_70_2767) with
| (data, g') -> begin
(let _151_1133 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _151_1133))
end))
end)) datas ([], g))
in (match (_70_2770) with
| (datas, g) -> begin
(
# 2050 "FStar.TypeChecker.Tc.fst"
let _70_2773 = (let _151_1134 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _151_1134 datas))
in (match (_70_2773) with
| (tcs, datas) -> begin
(let _151_1136 = (let _151_1135 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _151_1135))
in FStar_Syntax_Syntax.Sig_bundle (_151_1136))
end))
end))
end)))
end)))))))))

# 2053 "FStar.TypeChecker.Tc.fst"
let rec tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.env) = (fun env se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(
# 2066 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2067 "FStar.TypeChecker.Tc.fst"
let se = (tc_lex_t env ses quals lids)
in (let _151_1141 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _151_1141))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(
# 2071 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2072 "FStar.TypeChecker.Tc.fst"
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
# 2084 "FStar.TypeChecker.Tc.fst"
let _70_2809 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (
# 2085 "FStar.TypeChecker.Tc.fst"
let _70_2811 = (let _151_1143 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _151_1143 Prims.ignore))
in (se, env)))
end)
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(
# 2090 "FStar.TypeChecker.Tc.fst"
let ne = (tc_eff_decl env ne)
in (
# 2091 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (
# 2092 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(
# 2096 "FStar.TypeChecker.Tc.fst"
let _70_2826 = (let _151_1144 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _151_1144))
in (match (_70_2826) with
| (a, wp_a_src) -> begin
(
# 2097 "FStar.TypeChecker.Tc.fst"
let _70_2829 = (let _151_1145 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _151_1145))
in (match (_70_2829) with
| (b, wp_b_tgt) -> begin
(
# 2098 "FStar.TypeChecker.Tc.fst"
let wp_a_tgt = (let _151_1149 = (let _151_1148 = (let _151_1147 = (let _151_1146 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _151_1146))
in FStar_Syntax_Syntax.NT (_151_1147))
in (_151_1148)::[])
in (FStar_Syntax_Subst.subst _151_1149 wp_b_tgt))
in (
# 2099 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1154 = (let _151_1152 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1151 = (let _151_1150 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_151_1150)::[])
in (_151_1152)::_151_1151))
in (let _151_1153 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _151_1154 _151_1153)))
in (
# 2100 "FStar.TypeChecker.Tc.fst"
let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (
# 2101 "FStar.TypeChecker.Tc.fst"
let sub = (
# 2101 "FStar.TypeChecker.Tc.fst"
let _70_2833 = sub
in {FStar_Syntax_Syntax.source = _70_2833.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _70_2833.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
in (
# 2102 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect ((sub, r))
in (
# 2103 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(
# 2107 "FStar.TypeChecker.Tc.fst"
let _70_2846 = ()
in (
# 2108 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2109 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2110 "FStar.TypeChecker.Tc.fst"
let _70_2852 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_70_2852) with
| (tps, c) -> begin
(
# 2111 "FStar.TypeChecker.Tc.fst"
let _70_2856 = (tc_tparams env tps)
in (match (_70_2856) with
| (tps, env, us) -> begin
(
# 2112 "FStar.TypeChecker.Tc.fst"
let _70_2860 = (tc_comp env c)
in (match (_70_2860) with
| (c, u, g) -> begin
(
# 2113 "FStar.TypeChecker.Tc.fst"
let _70_2861 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2114 "FStar.TypeChecker.Tc.fst"
let tags = (FStar_All.pipe_right tags (FStar_List.map (fun _70_11 -> (match (_70_11) with
| FStar_Syntax_Syntax.DefaultEffect (None) -> begin
(
# 2116 "FStar.TypeChecker.Tc.fst"
let c' = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let _151_1157 = (FStar_All.pipe_right c'.FStar_Syntax_Syntax.effect_name (fun _151_1156 -> Some (_151_1156)))
in FStar_Syntax_Syntax.DefaultEffect (_151_1157)))
end
| t -> begin
t
end))))
in (
# 2119 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 2120 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.close_comp tps c)
in (
# 2121 "FStar.TypeChecker.Tc.fst"
let _70_2873 = (let _151_1158 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _151_1158))
in (match (_70_2873) with
| (uvs, t) -> begin
(
# 2122 "FStar.TypeChecker.Tc.fst"
let _70_2892 = (match ((let _151_1160 = (let _151_1159 = (FStar_Syntax_Subst.compress t)
in _151_1159.FStar_Syntax_Syntax.n)
in (tps, _151_1160))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_70_2876, c)) -> begin
([], c)
end
| (_70_2882, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _70_2889 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_70_2892) with
| (tps, c) -> begin
(
# 2126 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_effect_abbrev ((lid, uvs, tps, c, tags, r))
in (
# 2127 "FStar.TypeChecker.Tc.fst"
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
# 2131 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2132 "FStar.TypeChecker.Tc.fst"
let _70_2903 = ()
in (
# 2133 "FStar.TypeChecker.Tc.fst"
let k = (let _151_1161 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _151_1161))
in (
# 2134 "FStar.TypeChecker.Tc.fst"
let _70_2908 = (check_and_gen env t k)
in (match (_70_2908) with
| (uvs, t) -> begin
(
# 2135 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (
# 2136 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(
# 2140 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2141 "FStar.TypeChecker.Tc.fst"
let _70_2921 = (FStar_Syntax_Util.type_u ())
in (match (_70_2921) with
| (k, _70_2920) -> begin
(
# 2142 "FStar.TypeChecker.Tc.fst"
let phi = (let _151_1162 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _151_1162 (norm env)))
in (
# 2143 "FStar.TypeChecker.Tc.fst"
let _70_2923 = (FStar_TypeChecker_Util.check_uvars r phi)
in (
# 2144 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))
in (
# 2145 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(
# 2149 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2150 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (
# 2151 "FStar.TypeChecker.Tc.fst"
let _70_2936 = (tc_term env e)
in (match (_70_2936) with
| (e, c, g1) -> begin
(
# 2152 "FStar.TypeChecker.Tc.fst"
let _70_2941 = (let _151_1166 = (let _151_1163 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_151_1163))
in (let _151_1165 = (let _151_1164 = (c.FStar_Syntax_Syntax.comp ())
in (e, _151_1164))
in (check_expected_effect env _151_1166 _151_1165)))
in (match (_70_2941) with
| (e, _70_2939, g) -> begin
(
# 2153 "FStar.TypeChecker.Tc.fst"
let _70_2942 = (let _151_1167 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _151_1167))
in (
# 2154 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, r))
in (
# 2155 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(
# 2159 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2160 "FStar.TypeChecker.Tc.fst"
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
# 2171 "FStar.TypeChecker.Tc.fst"
let _70_2986 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _70_2963 lb -> (match (_70_2963) with
| (gen, lbs, quals_opt) -> begin
(
# 2172 "FStar.TypeChecker.Tc.fst"
let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2173 "FStar.TypeChecker.Tc.fst"
let _70_2982 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(
# 2177 "FStar.TypeChecker.Tc.fst"
let quals_opt = (check_quals_eq lbname quals_opt quals)
in (
# 2178 "FStar.TypeChecker.Tc.fst"
let _70_2977 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _70_2976 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _151_1180 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _151_1180, quals_opt))))
end)
in (match (_70_2982) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_70_2986) with
| (should_generalize, lbs', quals_opt) -> begin
(
# 2187 "FStar.TypeChecker.Tc.fst"
let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _70_12 -> (match (_70_12) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _70_2995 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (
# 2194 "FStar.TypeChecker.Tc.fst"
let lbs' = (FStar_List.rev lbs')
in (
# 2197 "FStar.TypeChecker.Tc.fst"
let e = (let _151_1184 = (let _151_1183 = (let _151_1182 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _151_1182))
in FStar_Syntax_Syntax.Tm_let (_151_1183))
in (FStar_Syntax_Syntax.mk _151_1184 None r))
in (
# 2200 "FStar.TypeChecker.Tc.fst"
let _70_3029 = (match ((tc_maybe_toplevel_term (
# 2200 "FStar.TypeChecker.Tc.fst"
let _70_2999 = env
in {FStar_TypeChecker_Env.solver = _70_2999.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_2999.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_2999.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_2999.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_2999.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_2999.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_2999.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_2999.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_2999.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_2999.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_2999.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _70_2999.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _70_2999.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_2999.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_2999.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_2999.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_2999.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_2999.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_2999.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_2999.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _70_3006; FStar_Syntax_Syntax.pos = _70_3004; FStar_Syntax_Syntax.vars = _70_3002}, _70_3013, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(
# 2203 "FStar.TypeChecker.Tc.fst"
let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_70_3017, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _70_3023 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _70_3026 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_70_3029) with
| (se, lbs) -> begin
(
# 2210 "FStar.TypeChecker.Tc.fst"
let _70_3035 = if (log env) then begin
(let _151_1190 = (let _151_1189 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 2212 "FStar.TypeChecker.Tc.fst"
let should_log = (match ((let _151_1186 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _151_1186))) with
| None -> begin
true
end
| _70_3033 -> begin
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
# 2219 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end))))
end))

# 2223 "FStar.TypeChecker.Tc.fst"
let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (
# 2247 "FStar.TypeChecker.Tc.fst"
let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _70_13 -> (match (_70_13) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _70_3045 -> begin
false
end)))))
in (
# 2248 "FStar.TypeChecker.Tc.fst"
let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _70_3055 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_70_3057) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _70_3068, _70_3070) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _70_3076 -> (match (_70_3076) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _70_3082, _70_3084, quals, r) -> begin
(
# 2262 "FStar.TypeChecker.Tc.fst"
let dec = (let _151_1206 = (let _151_1205 = (let _151_1204 = (let _151_1203 = (let _151_1202 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _151_1202))
in FStar_Syntax_Syntax.Tm_arrow (_151_1203))
in (FStar_Syntax_Syntax.mk _151_1204 None r))
in (l, us, _151_1205, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_151_1206))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _70_3094, _70_3096, _70_3098, _70_3100, r) -> begin
(
# 2265 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _70_3106 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_70_3108, _70_3110, quals, _70_3113) -> begin
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
| _70_3132 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_70_3134) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _70_3150, _70_3152, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(
# 2295 "FStar.TypeChecker.Tc.fst"
let lid = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals lid))) then begin
([], hidden)
end else begin
(
# 2298 "FStar.TypeChecker.Tc.fst"
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

# 2307 "FStar.TypeChecker.Tc.fst"
let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (
# 2308 "FStar.TypeChecker.Tc.fst"
let _70_3190 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _70_3171 se -> (match (_70_3171) with
| (ses, exports, env, hidden) -> begin
(
# 2310 "FStar.TypeChecker.Tc.fst"
let _70_3173 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1218 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _151_1218))
end else begin
()
end
in (
# 2313 "FStar.TypeChecker.Tc.fst"
let _70_3177 = (tc_decl env se)
in (match (_70_3177) with
| (se, env) -> begin
(
# 2315 "FStar.TypeChecker.Tc.fst"
let _70_3178 = if ((FStar_ST.read FStar_Options.log_types) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _151_1219 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _151_1219))
end else begin
()
end
in (
# 2318 "FStar.TypeChecker.Tc.fst"
let _70_3180 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (
# 2320 "FStar.TypeChecker.Tc.fst"
let _70_3184 = (for_export hidden se)
in (match (_70_3184) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_70_3190) with
| (ses, exports, env, _70_3189) -> begin
(let _151_1220 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _151_1220, env))
end)))

# 2325 "FStar.TypeChecker.Tc.fst"
let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2326 "FStar.TypeChecker.Tc.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 2327 "FStar.TypeChecker.Tc.fst"
let msg = (Prims.strcat "Internals for " name)
in (
# 2328 "FStar.TypeChecker.Tc.fst"
let env = (
# 2328 "FStar.TypeChecker.Tc.fst"
let _70_3195 = env
in (let _151_1225 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _70_3195.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_3195.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_3195.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_3195.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_3195.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_3195.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_3195.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_3195.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_3195.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_3195.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_3195.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_3195.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_3195.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _70_3195.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _70_3195.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_3195.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _151_1225; FStar_TypeChecker_Env.default_effects = _70_3195.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_3195.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_3195.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_3195.FStar_TypeChecker_Env.use_bv_sorts}))
in (
# 2329 "FStar.TypeChecker.Tc.fst"
let _70_3198 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (
# 2330 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (
# 2331 "FStar.TypeChecker.Tc.fst"
let _70_3204 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_70_3204) with
| (ses, exports, env) -> begin
((
# 2332 "FStar.TypeChecker.Tc.fst"
let _70_3205 = modul
in {FStar_Syntax_Syntax.name = _70_3205.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _70_3205.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _70_3205.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))

# 2334 "FStar.TypeChecker.Tc.fst"
let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (
# 2335 "FStar.TypeChecker.Tc.fst"
let _70_3213 = (tc_decls env decls)
in (match (_70_3213) with
| (ses, exports, env) -> begin
(
# 2336 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2336 "FStar.TypeChecker.Tc.fst"
let _70_3214 = modul
in {FStar_Syntax_Syntax.name = _70_3214.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _70_3214.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _70_3214.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))

# 2339 "FStar.TypeChecker.Tc.fst"
let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (
# 2340 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2340 "FStar.TypeChecker.Tc.fst"
let _70_3220 = modul
in {FStar_Syntax_Syntax.name = _70_3220.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _70_3220.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (
# 2341 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.finish_module env modul)
in (
# 2342 "FStar.TypeChecker.Tc.fst"
let _70_3230 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(
# 2344 "FStar.TypeChecker.Tc.fst"
let _70_3224 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (
# 2345 "FStar.TypeChecker.Tc.fst"
let _70_3226 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (
# 2346 "FStar.TypeChecker.Tc.fst"
let _70_3228 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _151_1238 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _151_1238 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))

# 2351 "FStar.TypeChecker.Tc.fst"
let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2352 "FStar.TypeChecker.Tc.fst"
let _70_3237 = (tc_partial_modul env modul)
in (match (_70_3237) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

# 2355 "FStar.TypeChecker.Tc.fst"
let add_modul_to_tcenv : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_TypeChecker_Env.env = (fun en m -> (
# 2356 "FStar.TypeChecker.Tc.fst"
let do_sigelt = (fun en elt -> (
# 2357 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt en elt)
in (
# 2358 "FStar.TypeChecker.Tc.fst"
let _70_3244 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env elt)
in env)))
in (
# 2361 "FStar.TypeChecker.Tc.fst"
let en = (FStar_TypeChecker_Env.set_current_module en m.FStar_Syntax_Syntax.name)
in (let _151_1251 = (FStar_List.fold_left do_sigelt en m.FStar_Syntax_Syntax.exports)
in (FStar_TypeChecker_Env.finish_module _151_1251 m)))))

# 2364 "FStar.TypeChecker.Tc.fst"
let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 2365 "FStar.TypeChecker.Tc.fst"
let _70_3249 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _151_1256 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _151_1256))
end else begin
()
end
in (
# 2367 "FStar.TypeChecker.Tc.fst"
let env = (
# 2367 "FStar.TypeChecker.Tc.fst"
let _70_3251 = env
in {FStar_TypeChecker_Env.solver = _70_3251.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_3251.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_3251.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_3251.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_3251.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_3251.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_3251.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_3251.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_3251.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_3251.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_3251.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_3251.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_3251.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _70_3251.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _70_3251.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _70_3251.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_3251.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_3251.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_3251.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_3251.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_3251.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 2368 "FStar.TypeChecker.Tc.fst"
let _70_3257 = (tc_tot_or_gtot_term env e)
in (match (_70_3257) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected a total term; got a ghost term", e.FStar_Syntax_Syntax.pos))))
end
end)))))

# 2373 "FStar.TypeChecker.Tc.fst"
let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (
# 2374 "FStar.TypeChecker.Tc.fst"
let _70_3260 = if ((let _151_1261 = (FStar_ST.read FStar_Options.debug)
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
# 2376 "FStar.TypeChecker.Tc.fst"
let _70_3264 = (tc_modul env m)
in (match (_70_3264) with
| (m, env) -> begin
(
# 2377 "FStar.TypeChecker.Tc.fst"
let _70_3265 = if (FStar_Options.should_dump m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _151_1263 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _151_1263))
end else begin
()
end
in (m, env))
end))))




