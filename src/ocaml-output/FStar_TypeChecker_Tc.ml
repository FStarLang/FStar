
open Prims
# 42 "FStar.TypeChecker.Tc.fst"
let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_ST.read FStar_Options.log_types) && (not ((let _153_3 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _153_3))))))

# 43 "FStar.TypeChecker.Tc.fst"
let rng : FStar_TypeChecker_Env.env  ->  FStar_Range.range = (fun env -> (FStar_TypeChecker_Env.get_range env))

# 44 "FStar.TypeChecker.Tc.fst"
let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (
# 44 "FStar.TypeChecker.Tc.fst"
let _71_18 = env
in {FStar_TypeChecker_Env.solver = _71_18.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _71_18.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _71_18.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _71_18.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _71_18.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _71_18.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _71_18.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _71_18.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _71_18.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _71_18.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _71_18.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _71_18.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _71_18.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _71_18.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _71_18.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _71_18.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _71_18.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _71_18.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _71_18.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _71_18.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _71_18.FStar_TypeChecker_Env.use_bv_sorts}))

# 45 "FStar.TypeChecker.Tc.fst"
let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (
# 45 "FStar.TypeChecker.Tc.fst"
let _71_21 = env
in {FStar_TypeChecker_Env.solver = _71_21.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _71_21.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _71_21.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _71_21.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _71_21.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _71_21.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _71_21.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _71_21.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _71_21.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _71_21.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _71_21.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _71_21.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _71_21.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _71_21.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _71_21.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _71_21.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _71_21.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _71_21.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _71_21.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _71_21.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _71_21.FStar_TypeChecker_Env.use_bv_sorts}))

# 46 "FStar.TypeChecker.Tc.fst"
let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (
# 48 "FStar.TypeChecker.Tc.fst"
let r = if (tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
v.FStar_Syntax_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos tl.FStar_Syntax_Syntax.pos)
end
in (let _153_17 = (let _153_16 = (FStar_Syntax_Syntax.as_arg v)
in (let _153_15 = (let _153_14 = (FStar_Syntax_Syntax.as_arg tl)
in (_153_14)::[])
in (_153_16)::_153_15))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _153_17 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))

# 51 "FStar.TypeChecker.Tc.fst"
let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _71_1 -> (match (_71_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _71_31 -> begin
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
let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _153_30 = (steps env)
in (FStar_TypeChecker_Normalize.normalize _153_30 env t)))

# 60 "FStar.TypeChecker.Tc.fst"
let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _153_35 = (steps env)
in (FStar_TypeChecker_Normalize.normalize_comp _153_35 env c)))

# 61 "FStar.TypeChecker.Tc.fst"
let fxv_check : FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv Prims.list * (FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv  ->  Prims.bool))  ->  Prims.unit = (fun head env kt fvs -> (
# 62 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun try_norm t -> if (FStar_Util.set_is_empty fvs) then begin
()
end else begin
(
# 64 "FStar.TypeChecker.Tc.fst"
let fvs' = (let _153_54 = if try_norm then begin
(norm env t)
end else begin
t
end
in (FStar_Syntax_Free.names _153_54))
in (
# 65 "FStar.TypeChecker.Tc.fst"
let a = (FStar_Util.set_intersect fvs fvs')
in if (FStar_Util.set_is_empty a) then begin
()
end else begin
if (not (try_norm)) then begin
(aux true t)
end else begin
(
# 69 "FStar.TypeChecker.Tc.fst"
let fail = (fun _71_49 -> (match (()) with
| () -> begin
(
# 70 "FStar.TypeChecker.Tc.fst"
let escaping = (let _153_58 = (let _153_57 = (FStar_Util.set_elements a)
in (FStar_All.pipe_right _153_57 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _153_58 (FStar_String.concat ", ")))
in (
# 71 "FStar.TypeChecker.Tc.fst"
let msg = if ((FStar_Util.set_count a) > 1) then begin
(let _153_59 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'{%s}\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" escaping _153_59))
end else begin
(let _153_60 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variable \'%s\' in the type of \'%s\' escapes because of impure applications; add explicit let-bindings" escaping _153_60))
end
in (let _153_63 = (let _153_62 = (let _153_61 = (FStar_TypeChecker_Env.get_range env)
in (msg, _153_61))
in FStar_Syntax_Syntax.Error (_153_62))
in (Prims.raise _153_63))))
end))
in (
# 77 "FStar.TypeChecker.Tc.fst"
let s = (let _153_64 = (FStar_TypeChecker_Recheck.check t)
in (FStar_TypeChecker_Util.new_uvar env _153_64))
in (match ((FStar_TypeChecker_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g)
end
| _71_56 -> begin
(fail ())
end)))
end
end))
end)
in (aux false kt)))

# 84 "FStar.TypeChecker.Tc.fst"
let check_no_escape : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun env bs t -> (
# 85 "FStar.TypeChecker.Tc.fst"
let fvs = (FStar_Syntax_Free.names t)
in if (FStar_Util.for_some (fun x -> (FStar_Util.set_mem x fvs)) bs) then begin
(
# 87 "FStar.TypeChecker.Tc.fst"
let _71_65 = (FStar_Syntax_Util.type_u ())
in (match (_71_65) with
| (k, _71_64) -> begin
(
# 88 "FStar.TypeChecker.Tc.fst"
let tnarrow = (FStar_TypeChecker_Util.new_uvar env k)
in (let _153_72 = (FStar_TypeChecker_Rel.teq env t tnarrow)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _153_72)))
end))
end else begin
()
end))

# 91 "FStar.TypeChecker.Tc.fst"
let maybe_push_binding : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder  ->  FStar_TypeChecker_Env.env = (fun env b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
env
end else begin
(
# 93 "FStar.TypeChecker.Tc.fst"
let _71_69 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_78 = (FStar_Syntax_Print.bv_to_string (Prims.fst b))
in (let _153_77 = (FStar_Syntax_Print.term_to_string (Prims.fst b).FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _153_78 _153_77)))
end else begin
()
end
in (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))
end)

# 97 "FStar.TypeChecker.Tc.fst"
let maybe_make_subst = (fun _71_2 -> (match (_71_2) with
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Syntax_Syntax.NT ((x, e)))::[]
end
| _71_78 -> begin
[]
end))

# 101 "FStar.TypeChecker.Tc.fst"
let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.subst_t = (fun s b v -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
s
end else begin
(FStar_Syntax_Syntax.NT (((Prims.fst b), v)))::s
end)

# 105 "FStar.TypeChecker.Tc.fst"
let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (
# 106 "FStar.TypeChecker.Tc.fst"
let _71_84 = lc
in {FStar_Syntax_Syntax.eff_name = _71_84.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _71_84.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _71_86 -> (match (()) with
| () -> begin
(let _153_91 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _153_91 t))
end))}))

# 108 "FStar.TypeChecker.Tc.fst"
let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (
# 109 "FStar.TypeChecker.Tc.fst"
let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _153_100 = if (not ((FStar_Syntax_Util.is_pure_or_ghost_function t))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _153_100))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (
# 114 "FStar.TypeChecker.Tc.fst"
let t = lc.FStar_Syntax_Syntax.res_typ
in (
# 115 "FStar.TypeChecker.Tc.fst"
let _71_118 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, guard)
end
| Some (t') -> begin
(
# 118 "FStar.TypeChecker.Tc.fst"
let _71_100 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_102 = (FStar_Syntax_Print.term_to_string t)
in (let _153_101 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _153_102 _153_101)))
end else begin
()
end
in (
# 120 "FStar.TypeChecker.Tc.fst"
let _71_104 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_71_104) with
| (e, lc) -> begin
(
# 121 "FStar.TypeChecker.Tc.fst"
let t = lc.FStar_Syntax_Syntax.res_typ
in (
# 122 "FStar.TypeChecker.Tc.fst"
let _71_108 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_71_108) with
| (e, g) -> begin
(
# 123 "FStar.TypeChecker.Tc.fst"
let _71_109 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_104 = (FStar_Syntax_Print.term_to_string t)
in (let _153_103 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _153_104 _153_103)))
end else begin
()
end
in (
# 125 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (
# 126 "FStar.TypeChecker.Tc.fst"
let _71_114 = (let _153_110 = (FStar_All.pipe_left (fun _153_109 -> Some (_153_109)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _153_110 env e lc g))
in (match (_71_114) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))))
end)))
end)))
end)
in (match (_71_118) with
| (e, lc, g) -> begin
(
# 128 "FStar.TypeChecker.Tc.fst"
let _71_119 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_111 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _153_111))
end else begin
()
end
in (e, lc, g))
end)))))

# 132 "FStar.TypeChecker.Tc.fst"
let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (t) -> begin
(
# 136 "FStar.TypeChecker.Tc.fst"
let _71_129 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_71_129) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))

# 139 "FStar.TypeChecker.Tc.fst"
let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _71_134 -> (match (_71_134) with
| (e, c) -> begin
(
# 140 "FStar.TypeChecker.Tc.fst"
let expected_c_opt = (match (copt) with
| Some (_71_136) -> begin
copt
end
| None -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
(
# 145 "FStar.TypeChecker.Tc.fst"
let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 146 "FStar.TypeChecker.Tc.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (match ((FStar_TypeChecker_Env.default_effect env md.FStar_Syntax_Syntax.mname)) with
| None -> begin
None
end
| Some (l) -> begin
(
# 150 "FStar.TypeChecker.Tc.fst"
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
# 154 "FStar.TypeChecker.Tc.fst"
let def = (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.effect_name = l; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = flags})
in Some (def)))
end)))
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _153_124 = (norm_c env c)
in (e, _153_124, FStar_TypeChecker_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(
# 163 "FStar.TypeChecker.Tc.fst"
let _71_150 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_127 = (FStar_Syntax_Print.term_to_string e)
in (let _153_126 = (FStar_Syntax_Print.comp_to_string c)
in (let _153_125 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _153_127 _153_126 _153_125))))
end else begin
()
end
in (
# 166 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 167 "FStar.TypeChecker.Tc.fst"
let _71_153 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_130 = (FStar_Syntax_Print.term_to_string e)
in (let _153_129 = (FStar_Syntax_Print.comp_to_string c)
in (let _153_128 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _153_130 _153_129 _153_128))))
end else begin
()
end
in (
# 172 "FStar.TypeChecker.Tc.fst"
let _71_159 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_71_159) with
| (e, _71_157, g) -> begin
(
# 173 "FStar.TypeChecker.Tc.fst"
let g = (let _153_131 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _153_131 "could not prove post-condition" g))
in (
# 174 "FStar.TypeChecker.Tc.fst"
let _71_161 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_133 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _153_132 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _153_133 _153_132)))
end else begin
()
end
in (e, expected_c, g)))
end)))))
end))
end))

# 177 "FStar.TypeChecker.Tc.fst"
let no_logical_guard = (fun env _71_167 -> (match (_71_167) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
(te, kt, f)
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _153_139 = (let _153_138 = (let _153_137 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _153_136 = (FStar_TypeChecker_Env.get_range env)
in (_153_137, _153_136)))
in FStar_Syntax_Syntax.Error (_153_138))
in (Prims.raise _153_139))
end)
end))

# 182 "FStar.TypeChecker.Tc.fst"
let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _153_142 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _153_142))
end))

# 186 "FStar.TypeChecker.Tc.fst"
let with_implicits = (fun imps _71_179 -> (match (_71_179) with
| (e, l, g) -> begin
(e, l, (
# 186 "FStar.TypeChecker.Tc.fst"
let _71_180 = g
in {FStar_TypeChecker_Env.guard_f = _71_180.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _71_180.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _71_180.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (FStar_List.append imps g.FStar_TypeChecker_Env.implicits)}))
end))

# 187 "FStar.TypeChecker.Tc.fst"
let add_implicit : (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun u g -> (
# 187 "FStar.TypeChecker.Tc.fst"
let _71_184 = g
in {FStar_TypeChecker_Env.guard_f = _71_184.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _71_184.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _71_184.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (u)::g.FStar_TypeChecker_Env.implicits}))

# 192 "FStar.TypeChecker.Tc.fst"
let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _71_202; FStar_Syntax_Syntax.result_typ = _71_200; FStar_Syntax_Syntax.effect_args = _pre::_post::(pats, _71_194)::[]; FStar_Syntax_Syntax.flags = _71_191}) -> begin
(
# 196 "FStar.TypeChecker.Tc.fst"
let pat_vars = (FStar_Syntax_Free.names pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _71_209 -> (match (_71_209) with
| (b, _71_208) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _71_213) -> begin
(let _153_155 = (let _153_154 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _153_154))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _153_155))
end))
end
| _71_217 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end)

# 207 "FStar.TypeChecker.Tc.fst"
let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun env actuals expected_c -> (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(
# 211 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 212 "FStar.TypeChecker.Tc.fst"
let env = (
# 212 "FStar.TypeChecker.Tc.fst"
let _71_224 = env
in {FStar_TypeChecker_Env.solver = _71_224.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _71_224.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _71_224.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _71_224.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _71_224.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _71_224.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _71_224.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _71_224.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _71_224.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _71_224.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _71_224.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _71_224.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _71_224.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _71_224.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _71_224.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _71_224.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _71_224.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _71_224.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _71_224.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _71_224.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _71_224.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 213 "FStar.TypeChecker.Tc.fst"
let precedes = (let _153_162 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.precedes_lid _153_162))
in (
# 215 "FStar.TypeChecker.Tc.fst"
let decreases_clause = (fun bs c -> (
# 217 "FStar.TypeChecker.Tc.fst"
let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _71_236 -> (match (_71_236) with
| (b, _71_235) -> begin
(
# 219 "FStar.TypeChecker.Tc.fst"
let t = (let _153_170 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _153_170))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _71_245 -> begin
(let _153_171 = (FStar_Syntax_Syntax.bv_to_name b)
in (_153_171)::[])
end))
end)))))
in (
# 224 "FStar.TypeChecker.Tc.fst"
let as_lex_list = (fun dec -> (
# 225 "FStar.TypeChecker.Tc.fst"
let _71_251 = (FStar_Syntax_Util.head_and_args dec)
in (match (_71_251) with
| (head, _71_250) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _71_254) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _71_258 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (
# 229 "FStar.TypeChecker.Tc.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _71_3 -> (match (_71_3) with
| FStar_Syntax_Syntax.DECREASES (_71_262) -> begin
true
end
| _71_265 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _71_270 -> begin
(
# 233 "FStar.TypeChecker.Tc.fst"
let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| x::[] -> begin
x
end
| _71_275 -> begin
(mk_lex_list xs)
end))
end)))))
in (
# 238 "FStar.TypeChecker.Tc.fst"
let previous_dec = (decreases_clause actuals expected_c)
in (
# 239 "FStar.TypeChecker.Tc.fst"
let guard_one_letrec = (fun _71_280 -> (match (_71_280) with
| (l, t) -> begin
(match ((let _153_177 = (FStar_Syntax_Subst.compress t)
in _153_177.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 243 "FStar.TypeChecker.Tc.fst"
let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _71_287 -> (match (_71_287) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _153_181 = (let _153_180 = (let _153_179 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_153_179))
in (FStar_Syntax_Syntax.new_bv _153_180 x.FStar_Syntax_Syntax.sort))
in (_153_181, imp))
end else begin
(x, imp)
end
end))))
in (
# 244 "FStar.TypeChecker.Tc.fst"
let _71_291 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_71_291) with
| (formals, c) -> begin
(
# 245 "FStar.TypeChecker.Tc.fst"
let dec = (decreases_clause formals c)
in (
# 246 "FStar.TypeChecker.Tc.fst"
let precedes = (let _153_185 = (let _153_184 = (FStar_Syntax_Syntax.as_arg dec)
in (let _153_183 = (let _153_182 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_153_182)::[])
in (_153_184)::_153_183))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _153_185 None r))
in (
# 247 "FStar.TypeChecker.Tc.fst"
let _71_298 = (FStar_Util.prefix formals)
in (match (_71_298) with
| (bs, (last, imp)) -> begin
(
# 248 "FStar.TypeChecker.Tc.fst"
let last = (
# 248 "FStar.TypeChecker.Tc.fst"
let _71_299 = last
in (let _153_186 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _71_299.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _71_299.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _153_186}))
in (
# 249 "FStar.TypeChecker.Tc.fst"
let refined_formals = (FStar_List.append bs (((last, imp))::[]))
in (
# 250 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (
# 251 "FStar.TypeChecker.Tc.fst"
let _71_304 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_189 = (FStar_Syntax_Print.lbname_to_string l)
in (let _153_188 = (FStar_Syntax_Print.term_to_string t)
in (let _153_187 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _153_189 _153_188 _153_187))))
end else begin
()
end
in (l, t')))))
end))))
end)))
end
| _71_307 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end))

# 263 "FStar.TypeChecker.Tc.fst"
let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (
# 263 "FStar.TypeChecker.Tc.fst"
let _71_310 = env
in {FStar_TypeChecker_Env.solver = _71_310.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _71_310.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _71_310.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _71_310.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _71_310.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _71_310.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _71_310.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _71_310.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _71_310.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _71_310.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _71_310.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _71_310.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _71_310.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _71_310.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _71_310.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _71_310.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _71_310.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _71_310.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _71_310.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _71_310.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _71_310.FStar_TypeChecker_Env.use_bv_sorts}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 268 "FStar.TypeChecker.Tc.fst"
let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (
# 269 "FStar.TypeChecker.Tc.fst"
let _71_315 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_255 = (let _153_253 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _153_253))
in (let _153_254 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _153_255 _153_254)))
end else begin
()
end
in (
# 270 "FStar.TypeChecker.Tc.fst"
let top = e
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_71_319) -> begin
(let _153_259 = (FStar_Syntax_Subst.compress e)
in (tc_term env _153_259))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(
# 287 "FStar.TypeChecker.Tc.fst"
let _71_359 = (FStar_Syntax_Util.type_u ())
in (match (_71_359) with
| (t, u) -> begin
(
# 288 "FStar.TypeChecker.Tc.fst"
let _71_363 = (tc_check_tot_or_gtot_term env e t)
in (match (_71_363) with
| (e, c, g) -> begin
(
# 289 "FStar.TypeChecker.Tc.fst"
let _71_370 = (
# 290 "FStar.TypeChecker.Tc.fst"
let _71_367 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_71_367) with
| (env, _71_366) -> begin
(tc_pats env pats)
end))
in (match (_71_370) with
| (pats, g') -> begin
(
# 292 "FStar.TypeChecker.Tc.fst"
let g' = (
# 292 "FStar.TypeChecker.Tc.fst"
let _71_371 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _71_371.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _71_371.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _71_371.FStar_TypeChecker_Env.implicits})
in (let _153_261 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_pattern (pats)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _153_260 = (FStar_TypeChecker_Rel.conj_guard g g')
in (_153_261, c, _153_260))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _153_262 = (FStar_Syntax_Subst.compress e)
in _153_262.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_71_380, {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _71_387; FStar_Syntax_Syntax.lbtyp = _71_385; FStar_Syntax_Syntax.lbeff = _71_383; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 300 "FStar.TypeChecker.Tc.fst"
let _71_398 = (let _153_263 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Recheck.t_unit)
in (tc_term _153_263 e1))
in (match (_71_398) with
| (e1, c1, g1) -> begin
(
# 301 "FStar.TypeChecker.Tc.fst"
let _71_402 = (tc_term env e2)
in (match (_71_402) with
| (e2, c2, g2) -> begin
(
# 302 "FStar.TypeChecker.Tc.fst"
let c = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (None, c2))
in (
# 303 "FStar.TypeChecker.Tc.fst"
let e = (let _153_268 = (let _153_267 = (let _153_266 = (let _153_265 = (let _153_264 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Recheck.t_unit, e1))
in (_153_264)::[])
in (false, _153_265))
in (_153_266, e2))
in FStar_Syntax_Syntax.Tm_let (_153_267))
in (FStar_Syntax_Syntax.mk _153_268 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 304 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _153_269 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _153_269)))))
end))
end))
end
| _71_407 -> begin
(
# 307 "FStar.TypeChecker.Tc.fst"
let _71_411 = (tc_term env e)
in (match (_71_411) with
| (e, c, g) -> begin
(
# 308 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(
# 313 "FStar.TypeChecker.Tc.fst"
let _71_420 = (tc_term env e)
in (match (_71_420) with
| (e, c, g) -> begin
(
# 314 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, m))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _71_425) -> begin
(
# 318 "FStar.TypeChecker.Tc.fst"
let _71_430 = (FStar_Syntax_Util.type_u ())
in (match (_71_430) with
| (k, u) -> begin
(
# 319 "FStar.TypeChecker.Tc.fst"
let _71_435 = (tc_check_tot_or_gtot_term env t k)
in (match (_71_435) with
| (t, _71_433, f) -> begin
(
# 320 "FStar.TypeChecker.Tc.fst"
let _71_439 = (let _153_270 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _153_270 e))
in (match (_71_439) with
| (e, c, g) -> begin
(
# 321 "FStar.TypeChecker.Tc.fst"
let _71_443 = (let _153_274 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _71_440 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _153_274 e c f))
in (match (_71_443) with
| (c, f) -> begin
(
# 322 "FStar.TypeChecker.Tc.fst"
let _71_447 = (let _153_275 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, t, Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _153_275 c))
in (match (_71_447) with
| (e, c, f2) -> begin
(let _153_277 = (let _153_276 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _153_276))
in (e, c, _153_277))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 326 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 327 "FStar.TypeChecker.Tc.fst"
let env = (let _153_279 = (let _153_278 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _153_278 Prims.fst))
in (FStar_All.pipe_right _153_279 instantiate_both))
in (
# 328 "FStar.TypeChecker.Tc.fst"
let _71_454 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_281 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _153_280 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _153_281 _153_280)))
end else begin
()
end
in (
# 332 "FStar.TypeChecker.Tc.fst"
let _71_459 = (tc_term (no_inst env) head)
in (match (_71_459) with
| (head, chead, g_head) -> begin
(
# 333 "FStar.TypeChecker.Tc.fst"
let _71_463 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _153_282 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _153_282))
end else begin
(let _153_283 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _153_283))
end
in (match (_71_463) with
| (e, c, g) -> begin
(
# 336 "FStar.TypeChecker.Tc.fst"
let _71_464 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _153_284 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _153_284))
end else begin
()
end
in (
# 338 "FStar.TypeChecker.Tc.fst"
let c = if (((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) && (not ((FStar_Syntax_Util.is_lcomp_partial_return c)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)) then begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e c)
end else begin
c
end
in (
# 343 "FStar.TypeChecker.Tc.fst"
let _71_471 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_290 = (FStar_Syntax_Print.term_to_string e)
in (let _153_289 = (let _153_285 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _153_285))
in (let _153_288 = (let _153_287 = (FStar_TypeChecker_Env.expected_typ env0)
in (FStar_All.pipe_right _153_287 (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end))))
in (FStar_Util.print3 "(%s) About to check %s against expected typ %s\n" _153_290 _153_289 _153_288))))
end else begin
()
end
in (
# 348 "FStar.TypeChecker.Tc.fst"
let _71_476 = (comp_check_expected_typ env0 e c)
in (match (_71_476) with
| (e, c, g') -> begin
(
# 349 "FStar.TypeChecker.Tc.fst"
let _71_477 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_293 = (FStar_Syntax_Print.term_to_string e)
in (let _153_292 = (let _153_291 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _153_291))
in (FStar_Util.print2 "(%s) checked ... got %s\n" _153_293 _153_292)))
end else begin
()
end
in (
# 353 "FStar.TypeChecker.Tc.fst"
let gimp = (match ((let _153_294 = (FStar_Syntax_Subst.compress head)
in _153_294.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _71_481) -> begin
(
# 356 "FStar.TypeChecker.Tc.fst"
let imp = (env0, u, e, c.FStar_Syntax_Syntax.res_typ, e.FStar_Syntax_Syntax.pos)
in (
# 357 "FStar.TypeChecker.Tc.fst"
let _71_485 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _71_485.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _71_485.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _71_485.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _71_488 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (
# 359 "FStar.TypeChecker.Tc.fst"
let gres = (let _153_295 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _153_295))
in (
# 360 "FStar.TypeChecker.Tc.fst"
let _71_491 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _153_296 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print1 "Guard from application node is %s\n" _153_296))
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
# 365 "FStar.TypeChecker.Tc.fst"
let _71_499 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_71_499) with
| (env1, topt) -> begin
(
# 366 "FStar.TypeChecker.Tc.fst"
let env1 = (instantiate_both env1)
in (
# 367 "FStar.TypeChecker.Tc.fst"
let _71_504 = (tc_term env1 e1)
in (match (_71_504) with
| (e1, c1, g1) -> begin
(
# 368 "FStar.TypeChecker.Tc.fst"
let _71_515 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(
# 371 "FStar.TypeChecker.Tc.fst"
let _71_511 = (FStar_Syntax_Util.type_u ())
in (match (_71_511) with
| (k, _71_510) -> begin
(
# 372 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _153_297 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_153_297, res_t)))
end))
end)
in (match (_71_515) with
| (env_branches, res_t) -> begin
(
# 375 "FStar.TypeChecker.Tc.fst"
let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (
# 376 "FStar.TypeChecker.Tc.fst"
let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (
# 377 "FStar.TypeChecker.Tc.fst"
let _71_532 = (
# 378 "FStar.TypeChecker.Tc.fst"
let _71_529 = (FStar_List.fold_right (fun _71_523 _71_526 -> (match ((_71_523, _71_526)) with
| ((_71_519, f, c, g), (caccum, gaccum)) -> begin
(let _153_300 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _153_300))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_71_529) with
| (cases, g) -> begin
(let _153_301 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_153_301, g))
end))
in (match (_71_532) with
| (c_branches, g_branches) -> begin
(
# 382 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (guard_x), c_branches))
in (
# 383 "FStar.TypeChecker.Tc.fst"
let e = (let _153_305 = (let _153_304 = (let _153_303 = (FStar_List.map (fun _71_541 -> (match (_71_541) with
| (f, _71_536, _71_538, _71_540) -> begin
f
end)) t_eqns)
in (e1, _153_303))
in FStar_Syntax_Syntax.Tm_match (_153_304))
in (FStar_Syntax_Syntax.mk _153_305 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (
# 384 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, cres.FStar_Syntax_Syntax.res_typ, Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (
# 385 "FStar.TypeChecker.Tc.fst"
let _71_544 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _153_308 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _153_307 = (let _153_306 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _153_306))
in (FStar_Util.print2 "(%s) comp type = %s\n" _153_308 _153_307)))
end else begin
()
end
in (let _153_309 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _153_309))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_71_556); FStar_Syntax_Syntax.lbunivs = _71_554; FStar_Syntax_Syntax.lbtyp = _71_552; FStar_Syntax_Syntax.lbeff = _71_550; FStar_Syntax_Syntax.lbdef = _71_548}::[]), _71_562) -> begin
(
# 392 "FStar.TypeChecker.Tc.fst"
let _71_565 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_310 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _153_310))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _71_569), _71_572) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_71_587); FStar_Syntax_Syntax.lbunivs = _71_585; FStar_Syntax_Syntax.lbtyp = _71_583; FStar_Syntax_Syntax.lbeff = _71_581; FStar_Syntax_Syntax.lbdef = _71_579}::_71_577), _71_593) -> begin
(
# 399 "FStar.TypeChecker.Tc.fst"
let _71_596 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_311 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _153_311))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _71_600), _71_603) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 412 "FStar.TypeChecker.Tc.fst"
let check_instantiated_fvar = (fun env v dc e t -> (
# 413 "FStar.TypeChecker.Tc.fst"
let _71_617 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_71_617) with
| (e, t, implicits) -> begin
(
# 415 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _153_325 = (let _153_324 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _153_324))
in FStar_Util.Inr (_153_325))
end
in (
# 416 "FStar.TypeChecker.Tc.fst"
let is_data_ctor = (fun _71_4 -> (match (_71_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _71_627 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _153_331 = (let _153_330 = (let _153_329 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _153_328 = (FStar_TypeChecker_Env.get_range env)
in (_153_329, _153_328)))
in FStar_Syntax_Syntax.Error (_153_330))
in (Prims.raise _153_331))
end else begin
(value_check_expected_typ env e tc implicits)
end))
end)))
in (
# 426 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (
# 427 "FStar.TypeChecker.Tc.fst"
let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(FStar_All.failwith "Impossible: Violation of locally nameless convention")
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(
# 433 "FStar.TypeChecker.Tc.fst"
let g = (match ((let _153_332 = (FStar_Syntax_Subst.compress t1)
in _153_332.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_71_638) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _71_641 -> begin
(
# 435 "FStar.TypeChecker.Tc.fst"
let imp = (env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (
# 436 "FStar.TypeChecker.Tc.fst"
let _71_643 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _71_643.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _71_643.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _71_643.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 441 "FStar.TypeChecker.Tc.fst"
let _71_649 = (FStar_Syntax_Util.type_u ())
in (match (_71_649) with
| (t, u) -> begin
(
# 442 "FStar.TypeChecker.Tc.fst"
let e = (FStar_TypeChecker_Util.new_uvar env t)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))
end))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 446 "FStar.TypeChecker.Tc.fst"
let t = if env.FStar_TypeChecker_Env.use_bv_sorts then begin
x.FStar_Syntax_Syntax.sort
end else begin
(FStar_TypeChecker_Env.lookup_bv env x)
end
in (
# 447 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.bv_to_name (
# 447 "FStar.TypeChecker.Tc.fst"
let _71_654 = x
in {FStar_Syntax_Syntax.ppname = _71_654.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _71_654.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (
# 448 "FStar.TypeChecker.Tc.fst"
let _71_660 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_71_660) with
| (e, t, implicits) -> begin
(
# 449 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _153_334 = (let _153_333 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _153_333))
in FStar_Util.Inr (_153_334))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (v, dc); FStar_Syntax_Syntax.tk = _71_667; FStar_Syntax_Syntax.pos = _71_665; FStar_Syntax_Syntax.vars = _71_663}, us) -> begin
(
# 453 "FStar.TypeChecker.Tc.fst"
let us = (FStar_List.map (tc_universe env) us)
in (
# 454 "FStar.TypeChecker.Tc.fst"
let _71_679 = (FStar_TypeChecker_Env.lookup_lid env v.FStar_Syntax_Syntax.v)
in (match (_71_679) with
| (us', t) -> begin
(
# 455 "FStar.TypeChecker.Tc.fst"
let _71_686 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _153_337 = (let _153_336 = (let _153_335 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _153_335))
in FStar_Syntax_Syntax.Error (_153_336))
in (Prims.raise _153_337))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _71_685 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (
# 460 "FStar.TypeChecker.Tc.fst"
let e = (let _153_340 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (((
# 460 "FStar.TypeChecker.Tc.fst"
let _71_688 = v
in {FStar_Syntax_Syntax.v = _71_688.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _71_688.FStar_Syntax_Syntax.p}), dc))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _153_340 us))
in (check_instantiated_fvar env v dc e t)))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (v, dc) -> begin
(
# 464 "FStar.TypeChecker.Tc.fst"
let _71_697 = (FStar_TypeChecker_Env.lookup_lid env v.FStar_Syntax_Syntax.v)
in (match (_71_697) with
| (us, t) -> begin
(
# 465 "FStar.TypeChecker.Tc.fst"
let e = (let _153_341 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (((
# 465 "FStar.TypeChecker.Tc.fst"
let _71_698 = v
in {FStar_Syntax_Syntax.v = _71_698.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _71_698.FStar_Syntax_Syntax.p}), dc))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _153_341 us))
in (check_instantiated_fvar env v dc e t))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(
# 469 "FStar.TypeChecker.Tc.fst"
let t = (FStar_TypeChecker_Recheck.check e)
in (
# 470 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 474 "FStar.TypeChecker.Tc.fst"
let _71_711 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_71_711) with
| (bs, c) -> begin
(
# 475 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 476 "FStar.TypeChecker.Tc.fst"
let _71_716 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_71_716) with
| (env, _71_715) -> begin
(
# 477 "FStar.TypeChecker.Tc.fst"
let _71_721 = (tc_binders env bs)
in (match (_71_721) with
| (bs, env, g, us) -> begin
(
# 478 "FStar.TypeChecker.Tc.fst"
let _71_725 = (tc_comp env c)
in (match (_71_725) with
| (c, uc, f) -> begin
(
# 479 "FStar.TypeChecker.Tc.fst"
let e = (
# 479 "FStar.TypeChecker.Tc.fst"
let _71_726 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _71_726.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _71_726.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _71_726.FStar_Syntax_Syntax.vars})
in (
# 480 "FStar.TypeChecker.Tc.fst"
let _71_729 = (check_smt_pat env e bs c)
in (
# 481 "FStar.TypeChecker.Tc.fst"
let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (
# 482 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 483 "FStar.TypeChecker.Tc.fst"
let g = (let _153_342 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _153_342))
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
let _71_745 = (let _153_344 = (let _153_343 = (FStar_Syntax_Syntax.mk_binder x)
in (_153_343)::[])
in (FStar_Syntax_Subst.open_term _153_344 phi))
in (match (_71_745) with
| (x, phi) -> begin
(
# 494 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 495 "FStar.TypeChecker.Tc.fst"
let _71_750 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_71_750) with
| (env, _71_749) -> begin
(
# 496 "FStar.TypeChecker.Tc.fst"
let _71_755 = (let _153_345 = (FStar_List.hd x)
in (tc_binder env _153_345))
in (match (_71_755) with
| (x, env, f1, u) -> begin
(
# 497 "FStar.TypeChecker.Tc.fst"
let _71_756 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_348 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _153_347 = (FStar_Syntax_Print.term_to_string phi)
in (let _153_346 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _153_348 _153_347 _153_346))))
end else begin
()
end
in (
# 500 "FStar.TypeChecker.Tc.fst"
let _71_761 = (FStar_Syntax_Util.type_u ())
in (match (_71_761) with
| (t_phi, _71_760) -> begin
(
# 501 "FStar.TypeChecker.Tc.fst"
let _71_766 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_71_766) with
| (phi, _71_764, f2) -> begin
(
# 502 "FStar.TypeChecker.Tc.fst"
let e = (
# 502 "FStar.TypeChecker.Tc.fst"
let _71_767 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _71_767.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _71_767.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _71_767.FStar_Syntax_Syntax.vars})
in (
# 503 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 504 "FStar.TypeChecker.Tc.fst"
let g = (let _153_349 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _153_349))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _71_775) -> begin
(
# 508 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (
# 509 "FStar.TypeChecker.Tc.fst"
let _71_781 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_350 = (FStar_Syntax_Print.term_to_string (
# 510 "FStar.TypeChecker.Tc.fst"
let _71_779 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _71_779.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _71_779.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _71_779.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _153_350))
end else begin
()
end
in (
# 511 "FStar.TypeChecker.Tc.fst"
let _71_785 = (FStar_Syntax_Subst.open_term bs body)
in (match (_71_785) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _71_787 -> begin
(let _153_352 = (let _153_351 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _153_351))
in (FStar_All.failwith _153_352))
end)))))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 525 "FStar.TypeChecker.Tc.fst"
let _71_794 = (FStar_Syntax_Util.type_u ())
in (match (_71_794) with
| (k, u) -> begin
(
# 526 "FStar.TypeChecker.Tc.fst"
let _71_799 = (tc_check_tot_or_gtot_term env t k)
in (match (_71_799) with
| (t, _71_797, g) -> begin
(let _153_355 = (FStar_Syntax_Syntax.mk_Total t)
in (_153_355, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 530 "FStar.TypeChecker.Tc.fst"
let _71_804 = (FStar_Syntax_Util.type_u ())
in (match (_71_804) with
| (k, u) -> begin
(
# 531 "FStar.TypeChecker.Tc.fst"
let _71_809 = (tc_check_tot_or_gtot_term env t k)
in (match (_71_809) with
| (t, _71_807, g) -> begin
(let _153_356 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_153_356, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 535 "FStar.TypeChecker.Tc.fst"
let kc = (FStar_TypeChecker_Env.lookup_effect_lid env c.FStar_Syntax_Syntax.effect_name)
in (
# 536 "FStar.TypeChecker.Tc.fst"
let _71_813 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_358 = (FStar_Syntax_Print.lid_to_string c.FStar_Syntax_Syntax.effect_name)
in (let _153_357 = (FStar_Syntax_Print.term_to_string kc)
in (FStar_Util.print2 "Type of effect %s is %s\n" _153_358 _153_357)))
end else begin
()
end
in (
# 537 "FStar.TypeChecker.Tc.fst"
let head = (FStar_Syntax_Syntax.fvar None c.FStar_Syntax_Syntax.effect_name (FStar_Ident.range_of_lid c.FStar_Syntax_Syntax.effect_name))
in (
# 538 "FStar.TypeChecker.Tc.fst"
let tc = (let _153_360 = (let _153_359 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_153_359)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _153_360 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 539 "FStar.TypeChecker.Tc.fst"
let _71_821 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_71_821) with
| (tc, _71_819, f) -> begin
(
# 540 "FStar.TypeChecker.Tc.fst"
let _71_825 = (FStar_Syntax_Util.head_and_args tc)
in (match (_71_825) with
| (_71_823, args) -> begin
(
# 541 "FStar.TypeChecker.Tc.fst"
let _71_828 = (let _153_362 = (FStar_List.hd args)
in (let _153_361 = (FStar_List.tl args)
in (_153_362, _153_361)))
in (match (_71_828) with
| (res, args) -> begin
(
# 542 "FStar.TypeChecker.Tc.fst"
let _71_844 = (let _153_364 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _71_5 -> (match (_71_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(
# 544 "FStar.TypeChecker.Tc.fst"
let _71_835 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_71_835) with
| (env, _71_834) -> begin
(
# 545 "FStar.TypeChecker.Tc.fst"
let _71_840 = (tc_tot_or_gtot_term env e)
in (match (_71_840) with
| (e, _71_838, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _153_364 FStar_List.unzip))
in (match (_71_844) with
| (flags, guards) -> begin
(
# 548 "FStar.TypeChecker.Tc.fst"
let u = (match ((FStar_TypeChecker_Recheck.check (Prims.fst res))) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type (u); FStar_Syntax_Syntax.tk = _71_850; FStar_Syntax_Syntax.pos = _71_848; FStar_Syntax_Syntax.vars = _71_846} -> begin
u
end
| _71_855 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _153_366 = (FStar_Syntax_Syntax.mk_Comp (
# 551 "FStar.TypeChecker.Tc.fst"
let _71_857 = c
in {FStar_Syntax_Syntax.effect_name = _71_857.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _71_857.FStar_Syntax_Syntax.flags}))
in (let _153_365 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_153_366, u, _153_365))))
end))
end))
end))
end))))))
end))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (
# 558 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun u -> (
# 559 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_71_865) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _153_371 = (aux u)
in FStar_Syntax_Syntax.U_succ (_153_371))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _153_372 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_153_372))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _153_376 = (let _153_375 = (let _153_374 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _153_373 = (FStar_TypeChecker_Env.get_range env)
in (_153_374, _153_373)))
in FStar_Syntax_Syntax.Error (_153_375))
in (Prims.raise _153_376))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _153_377 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_377 Prims.snd))
end
| _71_880 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (
# 581 "FStar.TypeChecker.Tc.fst"
let fail = (fun msg t -> (let _153_386 = (let _153_385 = (let _153_384 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_153_384, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_153_385))
in (Prims.raise _153_386)))
in (
# 590 "FStar.TypeChecker.Tc.fst"
let check_binders = (fun env bs bs_expected -> (
# 595 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun _71_898 bs bs_expected -> (match (_71_898) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| ((hd, imp)::bs, (hd_expected, imp')::bs_expected) -> begin
(
# 599 "FStar.TypeChecker.Tc.fst"
let _71_929 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _153_403 = (let _153_402 = (let _153_401 = (let _153_399 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _153_399))
in (let _153_400 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_153_401, _153_400)))
in FStar_Syntax_Syntax.Error (_153_402))
in (Prims.raise _153_403))
end
| _71_928 -> begin
()
end)
in (
# 606 "FStar.TypeChecker.Tc.fst"
let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (
# 607 "FStar.TypeChecker.Tc.fst"
let _71_946 = (match ((let _153_404 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _153_404.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _71_934 -> begin
(
# 610 "FStar.TypeChecker.Tc.fst"
let _71_935 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_405 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _153_405))
end else begin
()
end
in (
# 611 "FStar.TypeChecker.Tc.fst"
let _71_941 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_71_941) with
| (t, _71_939, g1) -> begin
(
# 612 "FStar.TypeChecker.Tc.fst"
let g2 = (let _153_407 = (FStar_TypeChecker_Env.get_range env)
in (let _153_406 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _153_407 "Type annotation on parameter incompatible with the expected type" _153_406)))
in (
# 616 "FStar.TypeChecker.Tc.fst"
let g = (let _153_408 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _153_408))
in (t, g)))
end)))
end)
in (match (_71_946) with
| (t, g) -> begin
(
# 618 "FStar.TypeChecker.Tc.fst"
let hd = (
# 618 "FStar.TypeChecker.Tc.fst"
let _71_947 = hd
in {FStar_Syntax_Syntax.ppname = _71_947.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _71_947.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 619 "FStar.TypeChecker.Tc.fst"
let b = (hd, imp)
in (
# 620 "FStar.TypeChecker.Tc.fst"
let b_expected = (hd_expected, imp')
in (
# 621 "FStar.TypeChecker.Tc.fst"
let env = (maybe_push_binding env b)
in (
# 622 "FStar.TypeChecker.Tc.fst"
let subst = (let _153_409 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _153_409))
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
# 632 "FStar.TypeChecker.Tc.fst"
let rec expected_function_typ = (fun env t0 -> (match (t0) with
| None -> begin
(
# 642 "FStar.TypeChecker.Tc.fst"
let _71_967 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _71_966 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (
# 643 "FStar.TypeChecker.Tc.fst"
let _71_974 = (tc_binders env bs)
in (match (_71_974) with
| (bs, envbody, g, _71_973) -> begin
(None, bs, [], None, envbody, g)
end)))
end
| Some (t) -> begin
(
# 647 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 648 "FStar.TypeChecker.Tc.fst"
let rec as_function_typ = (fun norm t -> (match ((let _153_418 = (FStar_Syntax_Subst.compress t)
in _153_418.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 652 "FStar.TypeChecker.Tc.fst"
let _71_1001 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _71_1000 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 653 "FStar.TypeChecker.Tc.fst"
let _71_1008 = (tc_binders env bs)
in (match (_71_1008) with
| (bs, envbody, g, _71_1007) -> begin
(
# 654 "FStar.TypeChecker.Tc.fst"
let _71_1012 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_71_1012) with
| (envbody, _71_1011) -> begin
(Some ((t, true)), bs, [], None, envbody, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _71_1015) -> begin
(
# 660 "FStar.TypeChecker.Tc.fst"
let _71_1025 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_71_1025) with
| (_71_1019, bs, bs', copt, env, g) -> begin
(Some ((t, false)), bs, bs', copt, env, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 664 "FStar.TypeChecker.Tc.fst"
let _71_1032 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_71_1032) with
| (bs_expected, c_expected) -> begin
(
# 671 "FStar.TypeChecker.Tc.fst"
let check_actuals_against_formals = (fun env bs bs_expected -> (
# 672 "FStar.TypeChecker.Tc.fst"
let rec handle_more = (fun _71_1043 c_expected -> (match (_71_1043) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _153_429 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _153_429))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(
# 677 "FStar.TypeChecker.Tc.fst"
let c = (let _153_430 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _153_430))
in (let _153_431 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _153_431)))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(
# 681 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.subst_comp subst c_expected)
in if (FStar_Syntax_Util.is_total_comp c) then begin
(
# 684 "FStar.TypeChecker.Tc.fst"
let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 687 "FStar.TypeChecker.Tc.fst"
let _71_1064 = (check_binders env more_bs bs_expected)
in (match (_71_1064) with
| (env, bs', more, guard', subst) -> begin
(let _153_433 = (let _153_432 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _153_432, subst))
in (handle_more _153_433 c_expected))
end))
end
| _71_1066 -> begin
(let _153_435 = (let _153_434 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _153_434))
in (fail _153_435 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _153_436 = (check_binders env bs bs_expected)
in (handle_more _153_436 c_expected))))
in (
# 694 "FStar.TypeChecker.Tc.fst"
let mk_letrec_env = (fun envbody bs c -> (
# 695 "FStar.TypeChecker.Tc.fst"
let letrecs = (guard_letrecs envbody bs c)
in (
# 696 "FStar.TypeChecker.Tc.fst"
let envbody = (
# 696 "FStar.TypeChecker.Tc.fst"
let _71_1072 = envbody
in {FStar_TypeChecker_Env.solver = _71_1072.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _71_1072.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _71_1072.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _71_1072.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _71_1072.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _71_1072.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _71_1072.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _71_1072.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _71_1072.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _71_1072.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _71_1072.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _71_1072.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _71_1072.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _71_1072.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _71_1072.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _71_1072.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _71_1072.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _71_1072.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _71_1072.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _71_1072.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _71_1072.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _71_1077 _71_1080 -> (match ((_71_1077, _71_1080)) with
| ((env, letrec_binders), (l, t)) -> begin
(
# 698 "FStar.TypeChecker.Tc.fst"
let _71_1086 = (let _153_446 = (let _153_445 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _153_445 Prims.fst))
in (tc_term _153_446 t))
in (match (_71_1086) with
| (t, _71_1083, _71_1085) -> begin
(
# 699 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (
# 700 "FStar.TypeChecker.Tc.fst"
let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _153_447 = (FStar_Syntax_Syntax.mk_binder (
# 701 "FStar.TypeChecker.Tc.fst"
let _71_1090 = x
in {FStar_Syntax_Syntax.ppname = _71_1090.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _71_1090.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_153_447)::letrec_binders)
end
| _71_1093 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (
# 706 "FStar.TypeChecker.Tc.fst"
let _71_1099 = (check_actuals_against_formals env bs bs_expected)
in (match (_71_1099) with
| (envbody, bs, g, c) -> begin
(
# 707 "FStar.TypeChecker.Tc.fst"
let _71_1102 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_71_1102) with
| (envbody, letrecs) -> begin
(
# 708 "FStar.TypeChecker.Tc.fst"
let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, g))
end))
end))))
end))
end
| _71_1105 -> begin
if (not (norm)) then begin
(let _153_448 = (unfold_whnf env t)
in (as_function_typ true _153_448))
end else begin
(
# 716 "FStar.TypeChecker.Tc.fst"
let _71_1114 = (expected_function_typ env None)
in (match (_71_1114) with
| (_71_1107, bs, _71_1110, c_opt, envbody, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (
# 720 "FStar.TypeChecker.Tc.fst"
let use_eq = env.FStar_TypeChecker_Env.use_eq
in (
# 721 "FStar.TypeChecker.Tc.fst"
let _71_1118 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_71_1118) with
| (env, topt) -> begin
(
# 722 "FStar.TypeChecker.Tc.fst"
let _71_1122 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_449 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _153_449 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (
# 726 "FStar.TypeChecker.Tc.fst"
let _71_1130 = (expected_function_typ env topt)
in (match (_71_1130) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, g) -> begin
(
# 727 "FStar.TypeChecker.Tc.fst"
let _71_1136 = (tc_term (
# 727 "FStar.TypeChecker.Tc.fst"
let _71_1131 = envbody
in {FStar_TypeChecker_Env.solver = _71_1131.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _71_1131.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _71_1131.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _71_1131.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _71_1131.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _71_1131.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _71_1131.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _71_1131.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _71_1131.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _71_1131.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _71_1131.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _71_1131.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _71_1131.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _71_1131.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _71_1131.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _71_1131.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _71_1131.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _71_1131.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _71_1131.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _71_1131.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_71_1136) with
| (body, cbody, guard_body) -> begin
(
# 728 "FStar.TypeChecker.Tc.fst"
let _71_1137 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_453 = (FStar_Syntax_Print.term_to_string body)
in (let _153_452 = (let _153_450 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _153_450))
in (let _153_451 = (FStar_TypeChecker_Rel.guard_to_string env guard_body)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _153_453 _153_452 _153_451))))
end else begin
()
end
in (
# 733 "FStar.TypeChecker.Tc.fst"
let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (
# 735 "FStar.TypeChecker.Tc.fst"
let _71_1140 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _153_456 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _153_455 = (let _153_454 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _153_454))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _153_456 _153_455)))
end else begin
()
end
in (
# 739 "FStar.TypeChecker.Tc.fst"
let _71_1147 = (let _153_458 = (let _153_457 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _153_457))
in (check_expected_effect (
# 739 "FStar.TypeChecker.Tc.fst"
let _71_1142 = envbody
in {FStar_TypeChecker_Env.solver = _71_1142.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _71_1142.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _71_1142.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _71_1142.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _71_1142.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _71_1142.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _71_1142.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _71_1142.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _71_1142.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _71_1142.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _71_1142.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _71_1142.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _71_1142.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _71_1142.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _71_1142.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _71_1142.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _71_1142.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _71_1142.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _71_1142.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _71_1142.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _71_1142.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _153_458))
in (match (_71_1147) with
| (body, cbody, guard) -> begin
(
# 740 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (
# 741 "FStar.TypeChecker.Tc.fst"
let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _153_459 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _153_459))
end else begin
(
# 743 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (
# 746 "FStar.TypeChecker.Tc.fst"
let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (
# 747 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.abs bs body (Some ((FStar_Syntax_Util.lcomp_of_comp cbody))))
in (
# 748 "FStar.TypeChecker.Tc.fst"
let _71_1170 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(
# 750 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_71_1159) -> begin
(e, t, guard)
end
| _71_1162 -> begin
(
# 759 "FStar.TypeChecker.Tc.fst"
let _71_1165 = if use_teq then begin
(let _153_460 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _153_460))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_71_1165) with
| (e, guard') -> begin
(let _153_461 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _153_461))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_71_1170) with
| (e, tfun, guard) -> begin
(
# 769 "FStar.TypeChecker.Tc.fst"
let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (
# 770 "FStar.TypeChecker.Tc.fst"
let _71_1174 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_71_1174) with
| (c, g) -> begin
(e, c, g)
end)))
end))))))
end)))))
end))
end)))
end)))))))
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead ghead args expected_topt -> (
# 778 "FStar.TypeChecker.Tc.fst"
let n_args = (FStar_List.length args)
in (
# 779 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 780 "FStar.TypeChecker.Tc.fst"
let thead = chead.FStar_Syntax_Syntax.res_typ
in (
# 781 "FStar.TypeChecker.Tc.fst"
let _71_1184 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_470 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _153_469 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _153_470 _153_469)))
end else begin
()
end
in (
# 782 "FStar.TypeChecker.Tc.fst"
let rec check_function_app = (fun norm tf -> (match ((let _153_475 = (FStar_Syntax_Util.unrefine tf)
in _153_475.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 786 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| (e, imp)::tl -> begin
(
# 789 "FStar.TypeChecker.Tc.fst"
let _71_1218 = (tc_term env e)
in (match (_71_1218) with
| (e, c, g_e) -> begin
(
# 790 "FStar.TypeChecker.Tc.fst"
let _71_1222 = (tc_args env tl)
in (match (_71_1222) with
| (args, comps, g_rest) -> begin
(let _153_480 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, (c)::comps, _153_480))
end))
end))
end))
in (
# 798 "FStar.TypeChecker.Tc.fst"
let _71_1226 = (tc_args env args)
in (match (_71_1226) with
| (args, comps, g_args) -> begin
(
# 799 "FStar.TypeChecker.Tc.fst"
let bs = (let _153_482 = (FStar_All.pipe_right comps (FStar_List.map (fun c -> (c.FStar_Syntax_Syntax.res_typ, None))))
in (FStar_Syntax_Util.null_binders_of_tks _153_482))
in (
# 800 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _71_1233 -> begin
FStar_Syntax_Util.ml_comp
end)
in (
# 803 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _153_497 = (FStar_Syntax_Subst.compress t)
in _153_497.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_71_1239) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _71_1244 -> begin
ml_or_tot
end)
end)
in (
# 810 "FStar.TypeChecker.Tc.fst"
let cres = (let _153_502 = (let _153_501 = (let _153_500 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_500 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _153_501))
in (ml_or_tot _153_502 r))
in (
# 811 "FStar.TypeChecker.Tc.fst"
let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (
# 812 "FStar.TypeChecker.Tc.fst"
let _71_1248 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _153_505 = (FStar_Syntax_Print.term_to_string head)
in (let _153_504 = (FStar_Syntax_Print.term_to_string tf)
in (let _153_503 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _153_505 _153_504 _153_503))))
end else begin
()
end
in (
# 817 "FStar.TypeChecker.Tc.fst"
let _71_1250 = (let _153_506 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _153_506))
in (
# 818 "FStar.TypeChecker.Tc.fst"
let comp = (let _153_509 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_TypeChecker_Util.bind env None c (None, out))) ((chead)::comps) _153_509))
in (let _153_511 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _153_510 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_153_511, comp, _153_510)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 822 "FStar.TypeChecker.Tc.fst"
let _71_1261 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_71_1261) with
| (bs, c) -> begin
(
# 824 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun _71_1269 bs cres args -> (match (_71_1269) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (_71_1276)))::rest, (_71_1284, None)::_71_1282) -> begin
(
# 835 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 836 "FStar.TypeChecker.Tc.fst"
let _71_1290 = (fxv_check head env t fvs)
in (
# 837 "FStar.TypeChecker.Tc.fst"
let _71_1295 = (FStar_TypeChecker_Util.new_implicit_var env t)
in (match (_71_1295) with
| (varg, u, implicits) -> begin
(
# 838 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (
# 839 "FStar.TypeChecker.Tc.fst"
let arg = (let _153_546 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _153_546))
in (let _153_552 = (let _153_551 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _153_551, fvs))
in (tc_args _153_552 rest cres args))))
end))))
end
| ((x, aqual)::rest, (e, aq)::rest') -> begin
(
# 843 "FStar.TypeChecker.Tc.fst"
let _71_1327 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _71_1326 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (
# 848 "FStar.TypeChecker.Tc.fst"
let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 849 "FStar.TypeChecker.Tc.fst"
let x = (
# 849 "FStar.TypeChecker.Tc.fst"
let _71_1330 = x
in {FStar_Syntax_Syntax.ppname = _71_1330.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _71_1330.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (
# 850 "FStar.TypeChecker.Tc.fst"
let _71_1333 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _153_553 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _153_553))
end else begin
()
end
in (
# 851 "FStar.TypeChecker.Tc.fst"
let _71_1335 = (fxv_check head env targ fvs)
in (
# 852 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (
# 853 "FStar.TypeChecker.Tc.fst"
let env = (
# 853 "FStar.TypeChecker.Tc.fst"
let _71_1338 = env
in {FStar_TypeChecker_Env.solver = _71_1338.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _71_1338.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _71_1338.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _71_1338.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _71_1338.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _71_1338.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _71_1338.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _71_1338.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _71_1338.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _71_1338.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _71_1338.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _71_1338.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _71_1338.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _71_1338.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _71_1338.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _71_1338.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _71_1338.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _71_1338.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _71_1338.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _71_1338.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _71_1338.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 854 "FStar.TypeChecker.Tc.fst"
let _71_1341 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_556 = (FStar_Syntax_Print.tag_of_term e)
in (let _153_555 = (FStar_Syntax_Print.term_to_string e)
in (let _153_554 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _153_556 _153_555 _153_554))))
end else begin
()
end
in (
# 855 "FStar.TypeChecker.Tc.fst"
let _71_1346 = (tc_term env e)
in (match (_71_1346) with
| (e, c, g_e) -> begin
(
# 856 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (
# 858 "FStar.TypeChecker.Tc.fst"
let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(
# 860 "FStar.TypeChecker.Tc.fst"
let subst = (let _153_557 = (FStar_List.hd bs)
in (maybe_extend_subst subst _153_557 e))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(
# 863 "FStar.TypeChecker.Tc.fst"
let subst = (let _153_562 = (FStar_List.hd bs)
in (maybe_extend_subst subst _153_562 e))
in (
# 864 "FStar.TypeChecker.Tc.fst"
let _71_1353 = (((Some (x), c))::comps, g)
in (match (_71_1353) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _153_567 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _153_567)) then begin
(
# 868 "FStar.TypeChecker.Tc.fst"
let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (
# 869 "FStar.TypeChecker.Tc.fst"
let arg' = (let _153_568 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _153_568))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (newx), c))::comps, g, fvs) rest cres rest')))
end else begin
(let _153_577 = (let _153_576 = (let _153_574 = (let _153_573 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _153_573))
in (_153_574)::arg_rets)
in (let _153_575 = (FStar_Util.set_add x fvs)
in (subst, (arg)::outargs, _153_576, ((Some (x), c))::comps, g, _153_575)))
in (tc_args _153_577 rest cres rest'))
end
end
end))
end))))))))))
end
| (_71_1357, []) -> begin
(
# 878 "FStar.TypeChecker.Tc.fst"
let _71_1360 = (fxv_check head env cres.FStar_Syntax_Syntax.res_typ fvs)
in (
# 879 "FStar.TypeChecker.Tc.fst"
let _71_1378 = (match (bs) with
| [] -> begin
(
# 882 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (
# 888 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (
# 890 "FStar.TypeChecker.Tc.fst"
let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _71_1368 -> (match (_71_1368) with
| (_71_1366, c) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (
# 897 "FStar.TypeChecker.Tc.fst"
let cres = if refine_with_equality then begin
(let _153_579 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _153_579 cres))
end else begin
(
# 903 "FStar.TypeChecker.Tc.fst"
let _71_1370 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_582 = (FStar_Syntax_Print.term_to_string head)
in (let _153_581 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _153_580 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _153_582 _153_581 _153_580))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _71_1374 -> begin
(
# 912 "FStar.TypeChecker.Tc.fst"
let g = (let _153_583 = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (FStar_All.pipe_right _153_583 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _153_588 = (let _153_587 = (let _153_586 = (let _153_585 = (let _153_584 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _153_584))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _153_585))
in (FStar_Syntax_Syntax.mk_Total _153_586))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _153_587))
in (_153_588, g)))
end)
in (match (_71_1378) with
| (cres, g) -> begin
(
# 915 "FStar.TypeChecker.Tc.fst"
let _71_1379 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_589 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _153_589))
end else begin
()
end
in (
# 916 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_List.fold_left (fun out c -> (FStar_TypeChecker_Util.bind env None (Prims.snd c) ((Prims.fst c), out))) cres comps)
in (
# 917 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.bind env None chead (None, comp))
in (
# 918 "FStar.TypeChecker.Tc.fst"
let app = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev outargs) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (
# 919 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.record_application_site env app comp)
in (
# 920 "FStar.TypeChecker.Tc.fst"
let _71_1389 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp g)
in (match (_71_1389) with
| (comp, g) -> begin
(
# 921 "FStar.TypeChecker.Tc.fst"
let _71_1390 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_595 = (FStar_TypeChecker_Normalize.term_to_string env app)
in (let _153_594 = (let _153_593 = (comp.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Print.comp_to_string _153_593))
in (FStar_Util.print2 "\t Type of app term %s is %s\n" _153_595 _153_594)))
end else begin
()
end
in (app, comp, g))
end)))))))
end)))
end
| ([], arg::_71_1394) -> begin
(
# 927 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun norm tres -> (
# 928 "FStar.TypeChecker.Tc.fst"
let tres = (let _153_600 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _153_600 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(
# 931 "FStar.TypeChecker.Tc.fst"
let _71_1406 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_601 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _153_601))
end else begin
()
end
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs (FStar_Syntax_Util.lcomp_of_comp cres') args))
end
| _71_1409 when (not (norm)) -> begin
(let _153_606 = (unfold_whnf env tres)
in (aux true _153_606))
end
| _71_1411 -> begin
(let _153_612 = (let _153_611 = (let _153_610 = (let _153_608 = (FStar_TypeChecker_Normalize.term_to_string env tf)
in (let _153_607 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _153_608 _153_607)))
in (let _153_609 = (FStar_Syntax_Syntax.argpos arg)
in (_153_610, _153_609)))
in FStar_Syntax_Syntax.Error (_153_611))
in (Prims.raise _153_612))
end)))
in (aux false cres.FStar_Syntax_Syntax.res_typ))
end)
end))
in (let _153_614 = (let _153_613 = (FStar_Syntax_Syntax.new_bv_set ())
in ([], [], [], [], FStar_TypeChecker_Rel.trivial_guard, _153_613))
in (tc_args _153_614 bs (FStar_Syntax_Util.lcomp_of_comp c) args)))
end))
end
| _71_1413 -> begin
if (not (norm)) then begin
(let _153_615 = (unfold_whnf env tf)
in (check_function_app true _153_615))
end else begin
(let _153_618 = (let _153_617 = (let _153_616 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_153_616, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_153_617))
in (Prims.raise _153_618))
end
end))
in (let _153_620 = (let _153_619 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _153_619))
in (check_function_app false _153_620))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (
# 957 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 958 "FStar.TypeChecker.Tc.fst"
let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(
# 961 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in (
# 962 "FStar.TypeChecker.Tc.fst"
let _71_1449 = (FStar_List.fold_left2 (fun _71_1430 _71_1433 _71_1436 -> (match ((_71_1430, _71_1433, _71_1436)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(
# 963 "FStar.TypeChecker.Tc.fst"
let _71_1437 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 964 "FStar.TypeChecker.Tc.fst"
let _71_1442 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_71_1442) with
| (e, c, g) -> begin
(
# 965 "FStar.TypeChecker.Tc.fst"
let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (
# 966 "FStar.TypeChecker.Tc.fst"
let g = (let _153_630 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _153_630 g))
in (
# 967 "FStar.TypeChecker.Tc.fst"
let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _153_634 = (let _153_632 = (let _153_631 = (FStar_Syntax_Syntax.as_arg e)
in (_153_631)::[])
in (FStar_List.append seen _153_632))
in (let _153_633 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_153_634, _153_633, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_71_1449) with
| (args, guard, ghost) -> begin
(
# 971 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (
# 972 "FStar.TypeChecker.Tc.fst"
let c = if ghost then begin
(let _153_635 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _153_635 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (
# 973 "FStar.TypeChecker.Tc.fst"
let _71_1454 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_71_1454) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _71_1456 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (
# 993 "FStar.TypeChecker.Tc.fst"
let _71_1463 = (FStar_Syntax_Subst.open_branch branch)
in (match (_71_1463) with
| (pattern, when_clause, branch_exp) -> begin
(
# 994 "FStar.TypeChecker.Tc.fst"
let _71_1468 = branch
in (match (_71_1468) with
| (cpat, _71_1466, cbr) -> begin
(
# 997 "FStar.TypeChecker.Tc.fst"
let tc_pat = (fun allow_implicits pat_t p0 -> (
# 1004 "FStar.TypeChecker.Tc.fst"
let _71_1476 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_71_1476) with
| (pat_bvs, exps, p) -> begin
(
# 1005 "FStar.TypeChecker.Tc.fst"
let _71_1477 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_647 = (FStar_Syntax_Print.pat_to_string p0)
in (let _153_646 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _153_647 _153_646)))
end else begin
()
end
in (
# 1007 "FStar.TypeChecker.Tc.fst"
let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (
# 1008 "FStar.TypeChecker.Tc.fst"
let _71_1483 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_71_1483) with
| (env1, _71_1482) -> begin
(
# 1009 "FStar.TypeChecker.Tc.fst"
let env1 = (
# 1009 "FStar.TypeChecker.Tc.fst"
let _71_1484 = env1
in {FStar_TypeChecker_Env.solver = _71_1484.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _71_1484.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _71_1484.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _71_1484.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _71_1484.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _71_1484.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _71_1484.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _71_1484.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _71_1484.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _71_1484.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _71_1484.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _71_1484.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _71_1484.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _71_1484.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _71_1484.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _71_1484.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _71_1484.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _71_1484.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _71_1484.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _71_1484.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _71_1484.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1010 "FStar.TypeChecker.Tc.fst"
let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (
# 1011 "FStar.TypeChecker.Tc.fst"
let _71_1523 = (let _153_670 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (
# 1012 "FStar.TypeChecker.Tc.fst"
let _71_1489 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_650 = (FStar_Syntax_Print.term_to_string e)
in (let _153_649 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _153_650 _153_649)))
end else begin
()
end
in (
# 1015 "FStar.TypeChecker.Tc.fst"
let _71_1494 = (tc_term env1 e)
in (match (_71_1494) with
| (e, lc, g) -> begin
(
# 1017 "FStar.TypeChecker.Tc.fst"
let _71_1495 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_652 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _153_651 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _153_652 _153_651)))
end else begin
()
end
in (
# 1020 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (
# 1021 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (
# 1022 "FStar.TypeChecker.Tc.fst"
let _71_1501 = (let _153_653 = (FStar_TypeChecker_Rel.discharge_guard env (
# 1022 "FStar.TypeChecker.Tc.fst"
let _71_1499 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _71_1499.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _71_1499.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _71_1499.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _153_653 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1023 "FStar.TypeChecker.Tc.fst"
let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (
# 1024 "FStar.TypeChecker.Tc.fst"
let uvars_to_string = (fun uvs -> (let _153_658 = (let _153_657 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _153_657 (FStar_List.map (fun _71_1509 -> (match (_71_1509) with
| (u, _71_1508) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _153_658 (FStar_String.concat ", "))))
in (
# 1025 "FStar.TypeChecker.Tc.fst"
let uvs1 = (FStar_Syntax_Free.uvars e')
in (
# 1026 "FStar.TypeChecker.Tc.fst"
let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (
# 1027 "FStar.TypeChecker.Tc.fst"
let _71_1517 = if (let _153_659 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _153_659)) then begin
(
# 1028 "FStar.TypeChecker.Tc.fst"
let unresolved = (let _153_660 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _153_660 FStar_Util.set_elements))
in (let _153_668 = (let _153_667 = (let _153_666 = (let _153_665 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _153_664 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _153_663 = (let _153_662 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _71_1516 -> (match (_71_1516) with
| (u, _71_1515) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _153_662 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _153_665 _153_664 _153_663))))
in (_153_666, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_153_667))
in (Prims.raise _153_668)))
end else begin
()
end
in (
# 1035 "FStar.TypeChecker.Tc.fst"
let _71_1519 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_669 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _153_669))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _153_670 FStar_List.unzip))
in (match (_71_1523) with
| (exps, norm_exps) -> begin
(
# 1040 "FStar.TypeChecker.Tc.fst"
let p = (FStar_TypeChecker_Util.decorate_pattern env p exps)
in (p, pat_bvs, pat_env, exps, norm_exps))
end))))
end))))
end)))
in (
# 1044 "FStar.TypeChecker.Tc.fst"
let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (
# 1045 "FStar.TypeChecker.Tc.fst"
let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (
# 1046 "FStar.TypeChecker.Tc.fst"
let _71_1530 = (let _153_671 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _153_671 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_71_1530) with
| (scrutinee_env, _71_1529) -> begin
(
# 1049 "FStar.TypeChecker.Tc.fst"
let _71_1536 = (tc_pat true pat_t pattern)
in (match (_71_1536) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(
# 1052 "FStar.TypeChecker.Tc.fst"
let _71_1546 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(
# 1059 "FStar.TypeChecker.Tc.fst"
let _71_1543 = (let _153_672 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Recheck.t_bool)
in (tc_term _153_672 e))
in (match (_71_1543) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_71_1546) with
| (when_clause, g_when) -> begin
(
# 1063 "FStar.TypeChecker.Tc.fst"
let _71_1550 = (tc_term pat_env branch_exp)
in (match (_71_1550) with
| (branch_exp, c, g_branch) -> begin
(
# 1067 "FStar.TypeChecker.Tc.fst"
let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _153_674 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _153_673 -> Some (_153_673)) _153_674))
end)
in (
# 1074 "FStar.TypeChecker.Tc.fst"
let _71_1606 = (
# 1077 "FStar.TypeChecker.Tc.fst"
let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (
# 1078 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _71_1568 -> begin
(
# 1084 "FStar.TypeChecker.Tc.fst"
let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _153_678 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _153_677 -> Some (_153_677)) _153_678))
end))
end))) None))
in (
# 1089 "FStar.TypeChecker.Tc.fst"
let _71_1576 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_71_1576) with
| (c, g_branch) -> begin
(
# 1093 "FStar.TypeChecker.Tc.fst"
let _71_1601 = (match ((eqs, when_condition)) with
| (None, None) -> begin
(c, g_when)
end
| (Some (f), None) -> begin
(
# 1099 "FStar.TypeChecker.Tc.fst"
let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1100 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _153_681 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _153_680 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_153_681, _153_680)))))
end
| (Some (f), Some (w)) -> begin
(
# 1105 "FStar.TypeChecker.Tc.fst"
let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1106 "FStar.TypeChecker.Tc.fst"
let g_fw = (let _153_682 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_153_682))
in (let _153_685 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _153_684 = (let _153_683 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _153_683 g_when))
in (_153_685, _153_684)))))
end
| (None, Some (w)) -> begin
(
# 1111 "FStar.TypeChecker.Tc.fst"
let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (
# 1112 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _153_686 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_153_686, g_when))))
end)
in (match (_71_1601) with
| (c_weak, g_when_weak) -> begin
(
# 1117 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _153_688 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _153_687 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_153_688, _153_687, g_branch))))
end))
end)))
in (match (_71_1606) with
| (c, g_when, g_branch) -> begin
(
# 1135 "FStar.TypeChecker.Tc.fst"
let branch_guard = (
# 1137 "FStar.TypeChecker.Tc.fst"
let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (
# 1138 "FStar.TypeChecker.Tc.fst"
let discriminate = (fun scrutinee_tm f -> if ((let _153_698 = (let _153_697 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _153_697))
in (FStar_List.length _153_698)) > 1) then begin
(
# 1141 "FStar.TypeChecker.Tc.fst"
let disc = (let _153_699 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar None _153_699 (FStar_Ident.range_of_lid f.FStar_Syntax_Syntax.v)))
in (
# 1142 "FStar.TypeChecker.Tc.fst"
let disc = (let _153_701 = (let _153_700 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_153_700)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _153_701 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _153_702 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_153_702)::[])))
end else begin
[]
end)
in (
# 1146 "FStar.TypeChecker.Tc.fst"
let fail = (fun _71_1616 -> (match (()) with
| () -> begin
(let _153_708 = (let _153_707 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _153_706 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _153_705 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _153_707 _153_706 _153_705))))
in (FStar_All.failwith _153_708))
end))
in (
# 1152 "FStar.TypeChecker.Tc.fst"
let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (f, _71_1621) -> begin
f
end
| FStar_Syntax_Syntax.Tm_uinst (t, _71_1626) -> begin
(head_constructor t)
end
| _71_1630 -> begin
(fail ())
end))
in (
# 1157 "FStar.TypeChecker.Tc.fst"
let pat_exp = (let _153_711 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _153_711 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_71_1655) -> begin
(let _153_716 = (let _153_715 = (let _153_714 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _153_713 = (let _153_712 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_153_712)::[])
in (_153_714)::_153_713))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _153_715 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_153_716)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 1166 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _153_717 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _153_717))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 1171 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(
# 1174 "FStar.TypeChecker.Tc.fst"
let sub_term_guards = (let _153_723 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _71_1673 -> (match (_71_1673) with
| (ei, _71_1672) -> begin
(
# 1175 "FStar.TypeChecker.Tc.fst"
let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (
# 1176 "FStar.TypeChecker.Tc.fst"
let sub_term = (let _153_722 = (FStar_Syntax_Syntax.fvar None projector f.FStar_Syntax_Syntax.p)
in (let _153_721 = (let _153_720 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_153_720)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _153_722 _153_721 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei)))
end))))
in (FStar_All.pipe_right _153_723 FStar_List.flatten))
in (let _153_724 = (discriminate scrutinee_tm f)
in (FStar_List.append _153_724 sub_term_guards)))
end)
end
| _71_1678 -> begin
[]
end))))))
in (
# 1182 "FStar.TypeChecker.Tc.fst"
let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid scrutinee_tm.FStar_Syntax_Syntax.pos)
end else begin
(
# 1185 "FStar.TypeChecker.Tc.fst"
let t = (let _153_729 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _153_729))
in (
# 1186 "FStar.TypeChecker.Tc.fst"
let _71_1686 = (FStar_Syntax_Util.type_u ())
in (match (_71_1686) with
| (k, _71_1685) -> begin
(
# 1187 "FStar.TypeChecker.Tc.fst"
let _71_1692 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_71_1692) with
| (t, _71_1689, _71_1691) -> begin
t
end))
end)))
end)
in (
# 1191 "FStar.TypeChecker.Tc.fst"
let branch_guard = (let _153_730 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _153_730 FStar_Syntax_Util.mk_disj_l))
in (
# 1194 "FStar.TypeChecker.Tc.fst"
let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
in (
# 1200 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (
# 1202 "FStar.TypeChecker.Tc.fst"
let _71_1700 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_731 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _153_731))
end else begin
()
end
in (let _153_732 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_153_732, branch_guard, c, guard)))))
end)))
end))
end))
end))
end)))))
end))
end)))
and check_top_level_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1216 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1219 "FStar.TypeChecker.Tc.fst"
let _71_1717 = (check_let_bound_def true env lb)
in (match (_71_1717) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(
# 1222 "FStar.TypeChecker.Tc.fst"
let _71_1729 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(
# 1225 "FStar.TypeChecker.Tc.fst"
let g1 = (let _153_735 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _153_735 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1226 "FStar.TypeChecker.Tc.fst"
let _71_1724 = (let _153_739 = (let _153_738 = (let _153_737 = (let _153_736 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _153_736))
in (_153_737)::[])
in (FStar_TypeChecker_Util.generalize env _153_738))
in (FStar_List.hd _153_739))
in (match (_71_1724) with
| (_71_1720, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_71_1729) with
| (g1, e1, univ_vars, c1) -> begin
(
# 1230 "FStar.TypeChecker.Tc.fst"
let _71_1739 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(
# 1232 "FStar.TypeChecker.Tc.fst"
let _71_1732 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_71_1732) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(
# 1235 "FStar.TypeChecker.Tc.fst"
let _71_1733 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _153_740 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _153_740 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _153_741 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_153_741, c1)))
end
end))
end else begin
(
# 1239 "FStar.TypeChecker.Tc.fst"
let _71_1735 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _153_742 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _153_742)))
end
in (match (_71_1739) with
| (e2, c1) -> begin
(
# 1244 "FStar.TypeChecker.Tc.fst"
let cres = (let _153_743 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Recheck.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _153_743))
in (
# 1245 "FStar.TypeChecker.Tc.fst"
let _71_1741 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Recheck.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1247 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _153_744 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Recheck.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_153_744, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _71_1745 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1264 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1267 "FStar.TypeChecker.Tc.fst"
let env = (
# 1267 "FStar.TypeChecker.Tc.fst"
let _71_1756 = env
in {FStar_TypeChecker_Env.solver = _71_1756.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _71_1756.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _71_1756.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _71_1756.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _71_1756.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _71_1756.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _71_1756.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _71_1756.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _71_1756.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _71_1756.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _71_1756.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _71_1756.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _71_1756.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _71_1756.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _71_1756.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _71_1756.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _71_1756.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _71_1756.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _71_1756.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _71_1756.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _71_1756.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1268 "FStar.TypeChecker.Tc.fst"
let _71_1765 = (let _153_748 = (let _153_747 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _153_747 Prims.fst))
in (check_let_bound_def false _153_748 lb))
in (match (_71_1765) with
| (e1, _71_1761, c1, g1, annotated) -> begin
(
# 1269 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (
# 1270 "FStar.TypeChecker.Tc.fst"
let x = (
# 1270 "FStar.TypeChecker.Tc.fst"
let _71_1767 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _71_1767.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _71_1767.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (
# 1271 "FStar.TypeChecker.Tc.fst"
let _71_1772 = (let _153_750 = (let _153_749 = (FStar_Syntax_Syntax.mk_binder x)
in (_153_749)::[])
in (FStar_Syntax_Subst.open_term _153_750 e2))
in (match (_71_1772) with
| (xb, e2) -> begin
(
# 1272 "FStar.TypeChecker.Tc.fst"
let xbinder = (FStar_List.hd xb)
in (
# 1273 "FStar.TypeChecker.Tc.fst"
let x = (Prims.fst xbinder)
in (
# 1274 "FStar.TypeChecker.Tc.fst"
let _71_1778 = (let _153_751 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _153_751 e2))
in (match (_71_1778) with
| (e2, c2, g2) -> begin
(
# 1275 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (x), c2))
in (
# 1276 "FStar.TypeChecker.Tc.fst"
let e = (let _153_754 = (let _153_753 = (let _153_752 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _153_752))
in FStar_Syntax_Syntax.Tm_let (_153_753))
in (FStar_Syntax_Syntax.mk _153_754 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 1277 "FStar.TypeChecker.Tc.fst"
let x_eq_e1 = (let _153_757 = (let _153_756 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _153_756 e1))
in (FStar_All.pipe_left (fun _153_755 -> FStar_TypeChecker_Common.NonTrivial (_153_755)) _153_757))
in (
# 1278 "FStar.TypeChecker.Tc.fst"
let g2 = (let _153_759 = (let _153_758 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _153_758 g2))
in (FStar_TypeChecker_Rel.close_guard xb _153_759))
in (
# 1280 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if annotated then begin
(e, cres, guard)
end else begin
(
# 1284 "FStar.TypeChecker.Tc.fst"
let _71_1784 = (check_no_escape env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end)))))
end))))
end))))
end)))
end
| _71_1787 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1293 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1296 "FStar.TypeChecker.Tc.fst"
let _71_1799 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_71_1799) with
| (lbs, e2) -> begin
(
# 1298 "FStar.TypeChecker.Tc.fst"
let _71_1802 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_71_1802) with
| (env0, topt) -> begin
(
# 1299 "FStar.TypeChecker.Tc.fst"
let _71_1805 = (build_let_rec_env true env0 lbs)
in (match (_71_1805) with
| (lbs, rec_env) -> begin
(
# 1300 "FStar.TypeChecker.Tc.fst"
let _71_1808 = (check_let_recs rec_env lbs)
in (match (_71_1808) with
| (lbs, g_lbs) -> begin
(
# 1301 "FStar.TypeChecker.Tc.fst"
let g_lbs = (let _153_762 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _153_762 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1303 "FStar.TypeChecker.Tc.fst"
let all_lb_names = (let _153_765 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _153_765 (fun _153_764 -> Some (_153_764))))
in (
# 1305 "FStar.TypeChecker.Tc.fst"
let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(
# 1311 "FStar.TypeChecker.Tc.fst"
let ecs = (let _153_769 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _153_768 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _153_768)))))
in (FStar_TypeChecker_Util.generalize env _153_769))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _71_1819 -> (match (_71_1819) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (
# 1318 "FStar.TypeChecker.Tc.fst"
let cres = (let _153_771 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Recheck.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _153_771))
in (
# 1319 "FStar.TypeChecker.Tc.fst"
let _71_1822 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Recheck.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1321 "FStar.TypeChecker.Tc.fst"
let _71_1826 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_71_1826) with
| (lbs, e2) -> begin
(let _153_773 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Recheck.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _153_772 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_153_773, cres, _153_772)))
end)))))))
end))
end))
end))
end))
end
| _71_1828 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1332 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1335 "FStar.TypeChecker.Tc.fst"
let _71_1840 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_71_1840) with
| (lbs, e2) -> begin
(
# 1337 "FStar.TypeChecker.Tc.fst"
let _71_1843 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_71_1843) with
| (env0, topt) -> begin
(
# 1338 "FStar.TypeChecker.Tc.fst"
let _71_1846 = (build_let_rec_env false env0 lbs)
in (match (_71_1846) with
| (lbs, rec_env) -> begin
(
# 1339 "FStar.TypeChecker.Tc.fst"
let _71_1849 = (check_let_recs rec_env lbs)
in (match (_71_1849) with
| (lbs, g_lbs) -> begin
(
# 1341 "FStar.TypeChecker.Tc.fst"
let _71_1867 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _71_1852 _71_1861 -> (match ((_71_1852, _71_1861)) with
| ((bvs, env), {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _71_1859; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _71_1856; FStar_Syntax_Syntax.lbdef = _71_1854}) -> begin
(
# 1342 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env x ([], t))
in (let _153_779 = (let _153_778 = (
# 1343 "FStar.TypeChecker.Tc.fst"
let _71_1863 = (FStar_Util.left x)
in {FStar_Syntax_Syntax.ppname = _71_1863.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _71_1863.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (_153_778)::bvs)
in (_153_779, env)))
end)) ([], env)))
in (match (_71_1867) with
| (bvs, env) -> begin
(
# 1344 "FStar.TypeChecker.Tc.fst"
let bvs = (FStar_List.rev bvs)
in (
# 1346 "FStar.TypeChecker.Tc.fst"
let _71_1872 = (tc_term env e2)
in (match (_71_1872) with
| (e2, cres, g2) -> begin
(
# 1347 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (
# 1348 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (
# 1349 "FStar.TypeChecker.Tc.fst"
let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (
# 1350 "FStar.TypeChecker.Tc.fst"
let cres = (
# 1350 "FStar.TypeChecker.Tc.fst"
let _71_1876 = cres
in {FStar_Syntax_Syntax.eff_name = _71_1876.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _71_1876.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _71_1876.FStar_Syntax_Syntax.comp})
in (
# 1352 "FStar.TypeChecker.Tc.fst"
let _71_1881 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_71_1881) with
| (lbs, e2) -> begin
(
# 1353 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_71_1884) -> begin
(e, cres, guard)
end
| None -> begin
(
# 1357 "FStar.TypeChecker.Tc.fst"
let _71_1887 = (check_no_escape env bvs tres)
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
| _71_1890 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (
# 1368 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1369 "FStar.TypeChecker.Tc.fst"
let _71_1923 = (FStar_List.fold_left (fun _71_1897 lb -> (match (_71_1897) with
| (lbs, env) -> begin
(
# 1370 "FStar.TypeChecker.Tc.fst"
let _71_1902 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_71_1902) with
| (univ_vars, t, check_t) -> begin
(
# 1371 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (
# 1372 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (
# 1373 "FStar.TypeChecker.Tc.fst"
let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(
# 1378 "FStar.TypeChecker.Tc.fst"
let _71_1911 = (let _153_786 = (let _153_785 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _153_785))
in (tc_check_tot_or_gtot_term (
# 1378 "FStar.TypeChecker.Tc.fst"
let _71_1905 = env0
in {FStar_TypeChecker_Env.solver = _71_1905.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _71_1905.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _71_1905.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _71_1905.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _71_1905.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _71_1905.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _71_1905.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _71_1905.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _71_1905.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _71_1905.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _71_1905.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _71_1905.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _71_1905.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _71_1905.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _71_1905.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _71_1905.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _71_1905.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _71_1905.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _71_1905.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _71_1905.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _71_1905.FStar_TypeChecker_Env.use_bv_sorts}) t _153_786))
in (match (_71_1911) with
| (t, _71_1909, g) -> begin
(
# 1379 "FStar.TypeChecker.Tc.fst"
let _71_1912 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (
# 1381 "FStar.TypeChecker.Tc.fst"
let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(
# 1383 "FStar.TypeChecker.Tc.fst"
let _71_1915 = env
in {FStar_TypeChecker_Env.solver = _71_1915.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _71_1915.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _71_1915.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _71_1915.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _71_1915.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _71_1915.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _71_1915.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _71_1915.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _71_1915.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _71_1915.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _71_1915.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _71_1915.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _71_1915.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _71_1915.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _71_1915.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _71_1915.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _71_1915.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _71_1915.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _71_1915.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _71_1915.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _71_1915.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (
# 1385 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1385 "FStar.TypeChecker.Tc.fst"
let _71_1918 = lb
in {FStar_Syntax_Syntax.lbname = _71_1918.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _71_1918.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_71_1923) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (
# 1392 "FStar.TypeChecker.Tc.fst"
let _71_1936 = (let _153_791 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 1393 "FStar.TypeChecker.Tc.fst"
let _71_1930 = (let _153_790 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _153_790 lb.FStar_Syntax_Syntax.lbdef))
in (match (_71_1930) with
| (e, c, g) -> begin
(
# 1394 "FStar.TypeChecker.Tc.fst"
let _71_1931 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1396 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _153_791 FStar_List.unzip))
in (match (_71_1936) with
| (lbs, gs) -> begin
(
# 1398 "FStar.TypeChecker.Tc.fst"
let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (
# 1412 "FStar.TypeChecker.Tc.fst"
let _71_1944 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_71_1944) with
| (env1, _71_1943) -> begin
(
# 1413 "FStar.TypeChecker.Tc.fst"
let e1 = lb.FStar_Syntax_Syntax.lbdef
in (
# 1416 "FStar.TypeChecker.Tc.fst"
let _71_1950 = (check_lbtyp top_level env lb)
in (match (_71_1950) with
| (topt, wf_annot, univ_vars, env1) -> begin
(
# 1418 "FStar.TypeChecker.Tc.fst"
let _71_1951 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1422 "FStar.TypeChecker.Tc.fst"
let _71_1958 = (tc_maybe_toplevel_term (
# 1422 "FStar.TypeChecker.Tc.fst"
let _71_1953 = env1
in {FStar_TypeChecker_Env.solver = _71_1953.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _71_1953.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _71_1953.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _71_1953.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _71_1953.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _71_1953.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _71_1953.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _71_1953.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _71_1953.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _71_1953.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _71_1953.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _71_1953.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _71_1953.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _71_1953.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _71_1953.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _71_1953.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _71_1953.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _71_1953.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _71_1953.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _71_1953.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _71_1953.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_71_1958) with
| (e1, c1, g1) -> begin
(
# 1425 "FStar.TypeChecker.Tc.fst"
let _71_1962 = (let _153_798 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _71_1959 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _153_798 e1 c1 wf_annot))
in (match (_71_1962) with
| (c1, guard_f) -> begin
(
# 1428 "FStar.TypeChecker.Tc.fst"
let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (
# 1430 "FStar.TypeChecker.Tc.fst"
let _71_1964 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _153_799 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _153_799))
end else begin
()
end
in (let _153_800 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _153_800))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (
# 1442 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 1445 "FStar.TypeChecker.Tc.fst"
let _71_1971 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _71_1974 -> begin
(
# 1449 "FStar.TypeChecker.Tc.fst"
let _71_1977 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_71_1977) with
| (univ_vars, t) -> begin
(
# 1450 "FStar.TypeChecker.Tc.fst"
let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _153_804 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _153_804))
end else begin
(
# 1457 "FStar.TypeChecker.Tc.fst"
let _71_1982 = (FStar_Syntax_Util.type_u ())
in (match (_71_1982) with
| (k, _71_1981) -> begin
(
# 1458 "FStar.TypeChecker.Tc.fst"
let _71_1987 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_71_1987) with
| (t, _71_1985, g) -> begin
(
# 1459 "FStar.TypeChecker.Tc.fst"
let _71_1988 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _153_807 = (let _153_805 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _153_805))
in (let _153_806 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _153_807 _153_806)))
end else begin
()
end
in (
# 1463 "FStar.TypeChecker.Tc.fst"
let t = (norm env1 t)
in (let _153_808 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _153_808))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _71_1994 -> (match (_71_1994) with
| (x, imp) -> begin
(
# 1468 "FStar.TypeChecker.Tc.fst"
let _71_1997 = (FStar_Syntax_Util.type_u ())
in (match (_71_1997) with
| (tu, u) -> begin
(
# 1469 "FStar.TypeChecker.Tc.fst"
let _71_2002 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_71_2002) with
| (t, _71_2000, g) -> begin
(
# 1470 "FStar.TypeChecker.Tc.fst"
let x = ((
# 1470 "FStar.TypeChecker.Tc.fst"
let _71_2003 = x
in {FStar_Syntax_Syntax.ppname = _71_2003.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _71_2003.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (
# 1471 "FStar.TypeChecker.Tc.fst"
let _71_2006 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_812 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _153_811 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _153_812 _153_811)))
end else begin
()
end
in (let _153_813 = (maybe_push_binding env x)
in (x, _153_813, g, u))))
end))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe Prims.list) = (fun env bs -> (
# 1476 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_TypeChecker_Rel.trivial_guard, [])
end
| b::bs -> begin
(
# 1479 "FStar.TypeChecker.Tc.fst"
let _71_2021 = (tc_binder env b)
in (match (_71_2021) with
| (b, env', g, u) -> begin
(
# 1480 "FStar.TypeChecker.Tc.fst"
let _71_2026 = (aux env' bs)
in (match (_71_2026) with
| (bs, env', g', us) -> begin
(let _153_821 = (let _153_820 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _153_820))
in ((b)::bs, env', _153_821, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (
# 1485 "FStar.TypeChecker.Tc.fst"
let tc_args = (fun env args -> (FStar_List.fold_right (fun _71_2034 _71_2037 -> (match ((_71_2034, _71_2037)) with
| ((t, imp), (args, g)) -> begin
(
# 1489 "FStar.TypeChecker.Tc.fst"
let _71_2042 = (tc_term env t)
in (match (_71_2042) with
| (t, _71_2040, g') -> begin
(let _153_830 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _153_830))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _71_2046 -> (match (_71_2046) with
| (pats, g) -> begin
(
# 1492 "FStar.TypeChecker.Tc.fst"
let _71_2049 = (tc_args env p)
in (match (_71_2049) with
| (args, g') -> begin
(let _153_833 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _153_833))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1497 "FStar.TypeChecker.Tc.fst"
let _71_2055 = (tc_maybe_toplevel_term env e)
in (match (_71_2055) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(
# 1500 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (
# 1501 "FStar.TypeChecker.Tc.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 1502 "FStar.TypeChecker.Tc.fst"
let _71_2058 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_836 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _153_836))
end else begin
()
end
in (
# 1503 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 1504 "FStar.TypeChecker.Tc.fst"
let _71_2063 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _153_837 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_153_837, false))
end else begin
(let _153_838 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_153_838, true))
end
in (match (_71_2063) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _153_839 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _153_839))
end
| _71_2067 -> begin
if allow_ghost then begin
(let _153_842 = (let _153_841 = (let _153_840 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_153_840, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_153_841))
in (Prims.raise _153_842))
end else begin
(let _153_845 = (let _153_844 = (let _153_843 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_153_843, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_153_844))
in (Prims.raise _153_845))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 1518 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))

# 1522 "FStar.TypeChecker.Tc.fst"
let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (
# 1523 "FStar.TypeChecker.Tc.fst"
let _71_2077 = (tc_tot_or_gtot_term env t)
in (match (_71_2077) with
| (t, c, g) -> begin
(
# 1524 "FStar.TypeChecker.Tc.fst"
let _71_2078 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))

# 1527 "FStar.TypeChecker.Tc.fst"
let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (
# 1528 "FStar.TypeChecker.Tc.fst"
let _71_2086 = (tc_check_tot_or_gtot_term env t k)
in (match (_71_2086) with
| (t, c, g) -> begin
(
# 1529 "FStar.TypeChecker.Tc.fst"
let _71_2087 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))

# 1532 "FStar.TypeChecker.Tc.fst"
let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _153_865 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _153_865)))

# 1535 "FStar.TypeChecker.Tc.fst"
let check_nogen = (fun env t k -> (
# 1536 "FStar.TypeChecker.Tc.fst"
let t = (tc_check_trivial_guard env t k)
in (let _153_869 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _153_869))))

# 1539 "FStar.TypeChecker.Tc.fst"
let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (
# 1540 "FStar.TypeChecker.Tc.fst"
let _71_2102 = (tc_binders env tps)
in (match (_71_2102) with
| (tps, env, g, us) -> begin
(
# 1541 "FStar.TypeChecker.Tc.fst"
let _71_2103 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))

# 1544 "FStar.TypeChecker.Tc.fst"
let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (
# 1545 "FStar.TypeChecker.Tc.fst"
let fail = (fun _71_2109 -> (match (()) with
| () -> begin
(let _153_884 = (let _153_883 = (let _153_882 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_153_882, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_153_883))
in (Prims.raise _153_884))
end))
in (
# 1546 "FStar.TypeChecker.Tc.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1549 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _71_2126)::(wp, _71_2122)::(_wlp, _71_2118)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _71_2130 -> begin
(fail ())
end))
end
| _71_2132 -> begin
(fail ())
end))))

# 1556 "FStar.TypeChecker.Tc.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 1559 "FStar.TypeChecker.Tc.fst"
let _71_2139 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_71_2139) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _71_2141 -> begin
(
# 1562 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow binders c)
in (
# 1563 "FStar.TypeChecker.Tc.fst"
let _71_2145 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_71_2145) with
| (uvs, t') -> begin
(match ((let _153_891 = (FStar_Syntax_Subst.compress t')
in _153_891.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _71_2151 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 1568 "FStar.TypeChecker.Tc.fst"
let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (
# 1569 "FStar.TypeChecker.Tc.fst"
let fail = (fun t -> (let _153_902 = (let _153_901 = (let _153_900 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_153_900, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_153_901))
in (Prims.raise _153_902)))
in (match ((let _153_903 = (FStar_Syntax_Subst.compress signature)
in _153_903.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1572 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _71_2172)::(wp, _71_2168)::(_wlp, _71_2164)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _71_2176 -> begin
(fail signature)
end))
end
| _71_2178 -> begin
(fail signature)
end)))

# 1579 "FStar.TypeChecker.Tc.fst"
let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (
# 1580 "FStar.TypeChecker.Tc.fst"
let _71_2183 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_71_2183) with
| (a, wp) -> begin
(
# 1581 "FStar.TypeChecker.Tc.fst"
let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _71_2186 -> begin
(
# 1585 "FStar.TypeChecker.Tc.fst"
let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (
# 1586 "FStar.TypeChecker.Tc.fst"
let op = (fun ts -> (
# 1587 "FStar.TypeChecker.Tc.fst"
let _71_2190 = ()
in (
# 1588 "FStar.TypeChecker.Tc.fst"
let t0 = (Prims.snd ts)
in (
# 1589 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (
# 1591 "FStar.TypeChecker.Tc.fst"
let _71_2194 = ed
in (let _153_922 = (op ed.FStar_Syntax_Syntax.ret)
in (let _153_921 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _153_920 = (op ed.FStar_Syntax_Syntax.bind_wlp)
in (let _153_919 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _153_918 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _153_917 = (op ed.FStar_Syntax_Syntax.ite_wlp)
in (let _153_916 = (op ed.FStar_Syntax_Syntax.wp_binop)
in (let _153_915 = (op ed.FStar_Syntax_Syntax.wp_as_type)
in (let _153_914 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _153_913 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _153_912 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _153_911 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _153_910 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _71_2194.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _71_2194.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _71_2194.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _71_2194.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _71_2194.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _153_922; FStar_Syntax_Syntax.bind_wp = _153_921; FStar_Syntax_Syntax.bind_wlp = _153_920; FStar_Syntax_Syntax.if_then_else = _153_919; FStar_Syntax_Syntax.ite_wp = _153_918; FStar_Syntax_Syntax.ite_wlp = _153_917; FStar_Syntax_Syntax.wp_binop = _153_916; FStar_Syntax_Syntax.wp_as_type = _153_915; FStar_Syntax_Syntax.close_wp = _153_914; FStar_Syntax_Syntax.assert_p = _153_913; FStar_Syntax_Syntax.assume_p = _153_912; FStar_Syntax_Syntax.null_wp = _153_911; FStar_Syntax_Syntax.trivial = _153_910}))))))))))))))))
end)
in (ed, a, wp))
end)))

# 1607 "FStar.TypeChecker.Tc.fst"
let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (
# 1608 "FStar.TypeChecker.Tc.fst"
let _71_2199 = ()
in (
# 1609 "FStar.TypeChecker.Tc.fst"
let _71_2203 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_71_2203) with
| (binders_un, signature_un) -> begin
(
# 1610 "FStar.TypeChecker.Tc.fst"
let _71_2208 = (tc_tparams env0 binders_un)
in (match (_71_2208) with
| (binders, env, _71_2207) -> begin
(
# 1611 "FStar.TypeChecker.Tc.fst"
let _71_2212 = (tc_trivial_guard env signature_un)
in (match (_71_2212) with
| (signature, _71_2211) -> begin
(
# 1612 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1612 "FStar.TypeChecker.Tc.fst"
let _71_2213 = ed
in {FStar_Syntax_Syntax.qualifiers = _71_2213.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _71_2213.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _71_2213.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _71_2213.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _71_2213.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _71_2213.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = _71_2213.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _71_2213.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _71_2213.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = _71_2213.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _71_2213.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _71_2213.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _71_2213.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _71_2213.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _71_2213.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _71_2213.FStar_Syntax_Syntax.trivial})
in (
# 1615 "FStar.TypeChecker.Tc.fst"
let _71_2219 = (open_effect_decl env ed)
in (match (_71_2219) with
| (ed, a, wp_a) -> begin
(
# 1616 "FStar.TypeChecker.Tc.fst"
let get_effect_signature = (fun _71_2221 -> (match (()) with
| () -> begin
(
# 1617 "FStar.TypeChecker.Tc.fst"
let _71_2225 = (tc_trivial_guard env signature_un)
in (match (_71_2225) with
| (signature, _71_2224) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (
# 1621 "FStar.TypeChecker.Tc.fst"
let env = (let _153_929 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _153_929))
in (
# 1623 "FStar.TypeChecker.Tc.fst"
let _71_2227 = if (FStar_TypeChecker_Env.debug env0 FStar_Options.Low) then begin
(let _153_932 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _153_931 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _153_930 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checked effect signature: %s %s : %s\n" _153_932 _153_931 _153_930))))
end else begin
()
end
in (
# 1629 "FStar.TypeChecker.Tc.fst"
let check_and_gen' = (fun env _71_2234 k -> (match (_71_2234) with
| (_71_2232, t) -> begin
(check_and_gen env t k)
end))
in (
# 1631 "FStar.TypeChecker.Tc.fst"
let ret = (
# 1632 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _153_944 = (let _153_942 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_941 = (let _153_940 = (let _153_939 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _153_939))
in (_153_940)::[])
in (_153_942)::_153_941))
in (let _153_943 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _153_944 _153_943)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (
# 1635 "FStar.TypeChecker.Tc.fst"
let bind_wp = (
# 1636 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1637 "FStar.TypeChecker.Tc.fst"
let _71_2241 = (get_effect_signature ())
in (match (_71_2241) with
| (b, wp_b) -> begin
(
# 1638 "FStar.TypeChecker.Tc.fst"
let a_wp_b = (let _153_948 = (let _153_946 = (let _153_945 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _153_945))
in (_153_946)::[])
in (let _153_947 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _153_948 _153_947)))
in (
# 1639 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = a_wp_b
in (
# 1640 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _153_961 = (let _153_959 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_958 = (let _153_957 = (FStar_Syntax_Syntax.mk_binder b)
in (let _153_956 = (let _153_955 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _153_954 = (let _153_953 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _153_952 = (let _153_951 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (let _153_950 = (let _153_949 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_153_949)::[])
in (_153_951)::_153_950))
in (_153_953)::_153_952))
in (_153_955)::_153_954))
in (_153_957)::_153_956))
in (_153_959)::_153_958))
in (let _153_960 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _153_961 _153_960)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k))))
end)))
in (
# 1646 "FStar.TypeChecker.Tc.fst"
let bind_wlp = (
# 1647 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1648 "FStar.TypeChecker.Tc.fst"
let _71_2249 = (get_effect_signature ())
in (match (_71_2249) with
| (b, wlp_b) -> begin
(
# 1649 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = (let _153_965 = (let _153_963 = (let _153_962 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _153_962))
in (_153_963)::[])
in (let _153_964 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _153_965 _153_964)))
in (
# 1650 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _153_974 = (let _153_972 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_971 = (let _153_970 = (FStar_Syntax_Syntax.mk_binder b)
in (let _153_969 = (let _153_968 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _153_967 = (let _153_966 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_153_966)::[])
in (_153_968)::_153_967))
in (_153_970)::_153_969))
in (_153_972)::_153_971))
in (let _153_973 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _153_974 _153_973)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wlp expected_k)))
end)))
in (
# 1656 "FStar.TypeChecker.Tc.fst"
let if_then_else = (
# 1657 "FStar.TypeChecker.Tc.fst"
let p = (let _153_976 = (let _153_975 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_975 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _153_976))
in (
# 1658 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _153_985 = (let _153_983 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_982 = (let _153_981 = (FStar_Syntax_Syntax.mk_binder p)
in (let _153_980 = (let _153_979 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _153_978 = (let _153_977 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_977)::[])
in (_153_979)::_153_978))
in (_153_981)::_153_980))
in (_153_983)::_153_982))
in (let _153_984 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_985 _153_984)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (
# 1664 "FStar.TypeChecker.Tc.fst"
let ite_wp = (
# 1665 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1666 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _153_992 = (let _153_990 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_989 = (let _153_988 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _153_987 = (let _153_986 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_986)::[])
in (_153_988)::_153_987))
in (_153_990)::_153_989))
in (let _153_991 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_992 _153_991)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k)))
in (
# 1672 "FStar.TypeChecker.Tc.fst"
let ite_wlp = (
# 1673 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1674 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _153_997 = (let _153_995 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_994 = (let _153_993 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (_153_993)::[])
in (_153_995)::_153_994))
in (let _153_996 = (FStar_Syntax_Syntax.mk_Total wlp_a)
in (FStar_Syntax_Util.arrow _153_997 _153_996)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wlp expected_k)))
in (
# 1679 "FStar.TypeChecker.Tc.fst"
let wp_binop = (
# 1680 "FStar.TypeChecker.Tc.fst"
let bin_op = (
# 1681 "FStar.TypeChecker.Tc.fst"
let _71_2264 = (FStar_Syntax_Util.type_u ())
in (match (_71_2264) with
| (t1, u1) -> begin
(
# 1682 "FStar.TypeChecker.Tc.fst"
let _71_2267 = (FStar_Syntax_Util.type_u ())
in (match (_71_2267) with
| (t2, u2) -> begin
(
# 1683 "FStar.TypeChecker.Tc.fst"
let t = (let _153_998 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_max ((u1)::(u2)::[]))) None _153_998))
in (let _153_1003 = (let _153_1001 = (FStar_Syntax_Syntax.null_binder t1)
in (let _153_1000 = (let _153_999 = (FStar_Syntax_Syntax.null_binder t2)
in (_153_999)::[])
in (_153_1001)::_153_1000))
in (let _153_1002 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _153_1003 _153_1002))))
end))
end))
in (
# 1685 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _153_1012 = (let _153_1010 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_1009 = (let _153_1008 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _153_1007 = (let _153_1006 = (FStar_Syntax_Syntax.null_binder bin_op)
in (let _153_1005 = (let _153_1004 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_1004)::[])
in (_153_1006)::_153_1005))
in (_153_1008)::_153_1007))
in (_153_1010)::_153_1009))
in (let _153_1011 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_1012 _153_1011)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_binop expected_k)))
in (
# 1692 "FStar.TypeChecker.Tc.fst"
let wp_as_type = (
# 1693 "FStar.TypeChecker.Tc.fst"
let _71_2275 = (FStar_Syntax_Util.type_u ())
in (match (_71_2275) with
| (t, _71_2274) -> begin
(
# 1694 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _153_1017 = (let _153_1015 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_1014 = (let _153_1013 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_1013)::[])
in (_153_1015)::_153_1014))
in (let _153_1016 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _153_1017 _153_1016)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (
# 1699 "FStar.TypeChecker.Tc.fst"
let close_wp = (
# 1700 "FStar.TypeChecker.Tc.fst"
let b = (let _153_1019 = (let _153_1018 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_1018 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _153_1019))
in (
# 1701 "FStar.TypeChecker.Tc.fst"
let b_wp_a = (let _153_1023 = (let _153_1021 = (let _153_1020 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _153_1020))
in (_153_1021)::[])
in (let _153_1022 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_1023 _153_1022)))
in (
# 1702 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _153_1030 = (let _153_1028 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_1027 = (let _153_1026 = (FStar_Syntax_Syntax.mk_binder b)
in (let _153_1025 = (let _153_1024 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_153_1024)::[])
in (_153_1026)::_153_1025))
in (_153_1028)::_153_1027))
in (let _153_1029 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_1030 _153_1029)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (
# 1706 "FStar.TypeChecker.Tc.fst"
let assert_p = (
# 1707 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _153_1039 = (let _153_1037 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_1036 = (let _153_1035 = (let _153_1032 = (let _153_1031 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_1031 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _153_1032))
in (let _153_1034 = (let _153_1033 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_1033)::[])
in (_153_1035)::_153_1034))
in (_153_1037)::_153_1036))
in (let _153_1038 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_1039 _153_1038)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (
# 1713 "FStar.TypeChecker.Tc.fst"
let assume_p = (
# 1714 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _153_1048 = (let _153_1046 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_1045 = (let _153_1044 = (let _153_1041 = (let _153_1040 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_1040 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _153_1041))
in (let _153_1043 = (let _153_1042 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_1042)::[])
in (_153_1044)::_153_1043))
in (_153_1046)::_153_1045))
in (let _153_1047 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_1048 _153_1047)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (
# 1720 "FStar.TypeChecker.Tc.fst"
let null_wp = (
# 1721 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _153_1051 = (let _153_1049 = (FStar_Syntax_Syntax.mk_binder a)
in (_153_1049)::[])
in (let _153_1050 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_1051 _153_1050)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (
# 1725 "FStar.TypeChecker.Tc.fst"
let trivial_wp = (
# 1726 "FStar.TypeChecker.Tc.fst"
let _71_2291 = (FStar_Syntax_Util.type_u ())
in (match (_71_2291) with
| (t, _71_2290) -> begin
(
# 1727 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _153_1056 = (let _153_1054 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_1053 = (let _153_1052 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_1052)::[])
in (_153_1054)::_153_1053))
in (let _153_1055 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _153_1056 _153_1055)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (
# 1733 "FStar.TypeChecker.Tc.fst"
let t = (let _153_1057 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _153_1057))
in (
# 1734 "FStar.TypeChecker.Tc.fst"
let _71_2297 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_71_2297) with
| (univs, t) -> begin
(
# 1735 "FStar.TypeChecker.Tc.fst"
let _71_2313 = (match ((let _153_1059 = (let _153_1058 = (FStar_Syntax_Subst.compress t)
in _153_1058.FStar_Syntax_Syntax.n)
in (binders, _153_1059))) with
| ([], _71_2300) -> begin
([], t)
end
| (_71_2303, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _71_2310 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_71_2313) with
| (binders, signature) -> begin
(
# 1739 "FStar.TypeChecker.Tc.fst"
let close = (fun ts -> (let _153_1062 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _153_1062)))
in (
# 1740 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1740 "FStar.TypeChecker.Tc.fst"
let _71_2316 = ed
in (let _153_1075 = (close ret)
in (let _153_1074 = (close bind_wp)
in (let _153_1073 = (close bind_wlp)
in (let _153_1072 = (close if_then_else)
in (let _153_1071 = (close ite_wp)
in (let _153_1070 = (close ite_wlp)
in (let _153_1069 = (close wp_binop)
in (let _153_1068 = (close wp_as_type)
in (let _153_1067 = (close close_wp)
in (let _153_1066 = (close assert_p)
in (let _153_1065 = (close assume_p)
in (let _153_1064 = (close null_wp)
in (let _153_1063 = (close trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _71_2316.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _71_2316.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _153_1075; FStar_Syntax_Syntax.bind_wp = _153_1074; FStar_Syntax_Syntax.bind_wlp = _153_1073; FStar_Syntax_Syntax.if_then_else = _153_1072; FStar_Syntax_Syntax.ite_wp = _153_1071; FStar_Syntax_Syntax.ite_wlp = _153_1070; FStar_Syntax_Syntax.wp_binop = _153_1069; FStar_Syntax_Syntax.wp_as_type = _153_1068; FStar_Syntax_Syntax.close_wp = _153_1067; FStar_Syntax_Syntax.assert_p = _153_1066; FStar_Syntax_Syntax.assume_p = _153_1065; FStar_Syntax_Syntax.null_wp = _153_1064; FStar_Syntax_Syntax.trivial = _153_1063}))))))))))))))
in (
# 1758 "FStar.TypeChecker.Tc.fst"
let _71_2319 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_1076 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _153_1076))
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

# 1762 "FStar.TypeChecker.Tc.fst"
let tc_lex_t = (fun env ses quals lids -> (
# 1769 "FStar.TypeChecker.Tc.fst"
let _71_2325 = ()
in (
# 1770 "FStar.TypeChecker.Tc.fst"
let _71_2333 = ()
in (match (ses) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _71_2362, _71_2364, [], r)::FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _71_2353, r1)::FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _71_2342, r2)::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(
# 1785 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (
# 1786 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (
# 1787 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (
# 1788 "FStar.TypeChecker.Tc.fst"
let tc = FStar_Syntax_Syntax.Sig_inductive_typ ((lex_t, (u)::[], [], t, [], (FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[], [], r))
in (
# 1790 "FStar.TypeChecker.Tc.fst"
let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (
# 1791 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (let _153_1083 = (let _153_1082 = (let _153_1081 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid r1)
in (_153_1081, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_153_1082))
in (FStar_Syntax_Syntax.mk _153_1083 None r1))
in (
# 1792 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (
# 1793 "FStar.TypeChecker.Tc.fst"
let dc_lextop = FStar_Syntax_Syntax.Sig_datacon ((lex_top, (utop)::[], lex_top_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r1))
in (
# 1795 "FStar.TypeChecker.Tc.fst"
let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1796 "FStar.TypeChecker.Tc.fst"
let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1797 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (
# 1798 "FStar.TypeChecker.Tc.fst"
let a = (let _153_1084 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _153_1084))
in (
# 1799 "FStar.TypeChecker.Tc.fst"
let hd = (let _153_1085 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _153_1085))
in (
# 1800 "FStar.TypeChecker.Tc.fst"
let tl = (let _153_1089 = (let _153_1088 = (let _153_1087 = (let _153_1086 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid r2)
in (_153_1086, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_153_1087))
in (FStar_Syntax_Syntax.mk _153_1088 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _153_1089))
in (
# 1801 "FStar.TypeChecker.Tc.fst"
let res = (let _153_1092 = (let _153_1091 = (let _153_1090 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid r2)
in (_153_1090, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_153_1091))
in (FStar_Syntax_Syntax.mk _153_1092 None r2))
in (let _153_1093 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _153_1093))))))
in (
# 1803 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (
# 1804 "FStar.TypeChecker.Tc.fst"
let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _153_1095 = (let _153_1094 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _153_1094))
in FStar_Syntax_Syntax.Sig_bundle (_153_1095)))))))))))))))
end
| _71_2388 -> begin
(let _153_1097 = (let _153_1096 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _153_1096))
in (FStar_All.failwith _153_1097))
end))))

# 1810 "FStar.TypeChecker.Tc.fst"
let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (
# 1873 "FStar.TypeChecker.Tc.fst"
let warn_positivity = (fun l r -> (let _153_1111 = (let _153_1110 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _153_1110))
in (FStar_TypeChecker_Errors.warn r _153_1111)))
in (
# 1875 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1878 "FStar.TypeChecker.Tc.fst"
let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(
# 1883 "FStar.TypeChecker.Tc.fst"
let _71_2410 = ()
in (
# 1884 "FStar.TypeChecker.Tc.fst"
let _71_2412 = (warn_positivity tc r)
in (
# 1885 "FStar.TypeChecker.Tc.fst"
let _71_2416 = (FStar_Syntax_Subst.open_term tps k)
in (match (_71_2416) with
| (tps, k) -> begin
(
# 1886 "FStar.TypeChecker.Tc.fst"
let _71_2420 = (tc_tparams env tps)
in (match (_71_2420) with
| (tps, env_tps, us) -> begin
(
# 1887 "FStar.TypeChecker.Tc.fst"
let _71_2423 = (FStar_Syntax_Util.arrow_formals k)
in (match (_71_2423) with
| (indices, t) -> begin
(
# 1888 "FStar.TypeChecker.Tc.fst"
let _71_2427 = (tc_tparams env_tps indices)
in (match (_71_2427) with
| (indices, env', us') -> begin
(
# 1889 "FStar.TypeChecker.Tc.fst"
let _71_2431 = (tc_trivial_guard env' t)
in (match (_71_2431) with
| (t, _71_2430) -> begin
(
# 1890 "FStar.TypeChecker.Tc.fst"
let k = (let _153_1116 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _153_1116))
in (
# 1891 "FStar.TypeChecker.Tc.fst"
let _71_2435 = (FStar_Syntax_Util.type_u ())
in (match (_71_2435) with
| (t_type, u) -> begin
(
# 1892 "FStar.TypeChecker.Tc.fst"
let _71_2436 = (let _153_1117 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _153_1117))
in (
# 1894 "FStar.TypeChecker.Tc.fst"
let t_tc = (let _153_1118 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _153_1118))
in (
# 1895 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 1896 "FStar.TypeChecker.Tc.fst"
let k = (FStar_Syntax_Subst.close tps k)
in (let _153_1119 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (tc)) ([], t_tc))
in (_153_1119, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u))))))
end)))
end))
end))
end))
end))
end))))
end
| _71_2442 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1903 "FStar.TypeChecker.Tc.fst"
let positive_if_pure = (fun _71_2444 l -> ())
in (
# 1906 "FStar.TypeChecker.Tc.fst"
let tc_data = (fun env tcs _71_6 -> (match (_71_6) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(
# 1908 "FStar.TypeChecker.Tc.fst"
let _71_2461 = ()
in (
# 1910 "FStar.TypeChecker.Tc.fst"
let _71_2492 = (let _153_1134 = (FStar_Util.find_map tcs (fun _71_2465 -> (match (_71_2465) with
| (se, u_tc) -> begin
if (let _153_1132 = (let _153_1131 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _153_1131))
in (FStar_Ident.lid_equals tc_lid _153_1132)) then begin
(
# 1913 "FStar.TypeChecker.Tc.fst"
let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_71_2467, _71_2469, tps, _71_2472, _71_2474, _71_2476, _71_2478, _71_2480) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _71_2486 -> (match (_71_2486) with
| (x, _71_2485) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _71_2488 -> begin
(FStar_All.failwith "Impossible")
end)
in Some ((tps, u_tc)))
end else begin
None
end
end)))
in (FStar_All.pipe_right _153_1134 FStar_Util.must))
in (match (_71_2492) with
| (tps, u_tc) -> begin
(
# 1920 "FStar.TypeChecker.Tc.fst"
let _71_2512 = (match ((let _153_1135 = (FStar_Syntax_Subst.compress t)
in _153_1135.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(
# 1925 "FStar.TypeChecker.Tc.fst"
let _71_2500 = (FStar_Util.first_N ntps bs)
in (match (_71_2500) with
| (_71_2498, bs') -> begin
(
# 1926 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (
# 1927 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _71_2506 -> (match (_71_2506) with
| (x, _71_2505) -> begin
(let _153_1139 = (let _153_1138 = (FStar_Syntax_Syntax.bv_to_name x)
in ((ntps - (1 + i)), _153_1138))
in FStar_Syntax_Syntax.DB (_153_1139))
end))))
in (let _153_1140 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _153_1140))))
end))
end
| _71_2509 -> begin
([], t)
end)
in (match (_71_2512) with
| (arguments, result) -> begin
(
# 1931 "FStar.TypeChecker.Tc.fst"
let _71_2513 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_1143 = (FStar_Syntax_Print.lid_to_string c)
in (let _153_1142 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _153_1141 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _153_1143 _153_1142 _153_1141))))
end else begin
()
end
in (
# 1937 "FStar.TypeChecker.Tc.fst"
let _71_2518 = (tc_tparams env arguments)
in (match (_71_2518) with
| (arguments, env', us) -> begin
(
# 1938 "FStar.TypeChecker.Tc.fst"
let _71_2522 = (tc_trivial_guard env' result)
in (match (_71_2522) with
| (result, _71_2521) -> begin
(
# 1939 "FStar.TypeChecker.Tc.fst"
let _71_2526 = (FStar_Syntax_Util.head_and_args result)
in (match (_71_2526) with
| (head, _71_2525) -> begin
(
# 1940 "FStar.TypeChecker.Tc.fst"
let _71_2534 = (match ((let _153_1144 = (FStar_Syntax_Subst.compress head)
in _153_1144.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _71_2529) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v tc_lid) -> begin
()
end
| _71_2533 -> begin
(let _153_1148 = (let _153_1147 = (let _153_1146 = (let _153_1145 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _153_1145))
in (_153_1146, r))
in FStar_Syntax_Syntax.Error (_153_1147))
in (Prims.raise _153_1148))
end)
in (
# 1943 "FStar.TypeChecker.Tc.fst"
let g = (FStar_List.fold_left2 (fun g _71_2540 u_x -> (match (_71_2540) with
| (x, _71_2539) -> begin
(
# 1944 "FStar.TypeChecker.Tc.fst"
let _71_2542 = ()
in (let _153_1152 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _153_1152)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (
# 1950 "FStar.TypeChecker.Tc.fst"
let t = (let _153_1156 = (let _153_1154 = (FStar_All.pipe_right tps (FStar_List.map (fun _71_2548 -> (match (_71_2548) with
| (x, _71_2547) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _153_1154 arguments))
in (let _153_1155 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _153_1156 _153_1155)))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _71_2551 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1958 "FStar.TypeChecker.Tc.fst"
let generalize_and_inst_within = (fun env g tcs datas -> (
# 1959 "FStar.TypeChecker.Tc.fst"
let _71_2557 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 1960 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _71_7 -> (match (_71_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_71_2561, _71_2563, tps, k, _71_2567, _71_2569, _71_2571, _71_2573) -> begin
(let _153_1167 = (let _153_1166 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _153_1166))
in (FStar_Syntax_Syntax.null_binder _153_1167))
end
| _71_2577 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 1963 "FStar.TypeChecker.Tc.fst"
let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _71_8 -> (match (_71_8) with
| FStar_Syntax_Syntax.Sig_datacon (_71_2581, _71_2583, t, _71_2586, _71_2588, _71_2590, _71_2592, _71_2594) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _71_2598 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 1966 "FStar.TypeChecker.Tc.fst"
let t = (let _153_1169 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Recheck.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _153_1169))
in (
# 1967 "FStar.TypeChecker.Tc.fst"
let _71_2601 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_1170 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _153_1170))
end else begin
()
end
in (
# 1968 "FStar.TypeChecker.Tc.fst"
let _71_2605 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_71_2605) with
| (uvs, t) -> begin
(
# 1969 "FStar.TypeChecker.Tc.fst"
let _71_2607 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_1174 = (let _153_1172 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _153_1172 (FStar_String.concat ", ")))
in (let _153_1173 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _153_1174 _153_1173)))
end else begin
()
end
in (
# 1972 "FStar.TypeChecker.Tc.fst"
let _71_2611 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_71_2611) with
| (uvs, t) -> begin
(
# 1973 "FStar.TypeChecker.Tc.fst"
let _71_2615 = (FStar_Syntax_Util.arrow_formals t)
in (match (_71_2615) with
| (args, _71_2614) -> begin
(
# 1974 "FStar.TypeChecker.Tc.fst"
let _71_2618 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_71_2618) with
| (tc_types, data_types) -> begin
(
# 1975 "FStar.TypeChecker.Tc.fst"
let tcs = (FStar_List.map2 (fun _71_2622 se -> (match (_71_2622) with
| (x, _71_2621) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _71_2626, tps, _71_2629, mutuals, datas, quals, r) -> begin
(
# 1977 "FStar.TypeChecker.Tc.fst"
let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (
# 1978 "FStar.TypeChecker.Tc.fst"
let _71_2652 = (match ((let _153_1177 = (FStar_Syntax_Subst.compress ty)
in _153_1177.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 1980 "FStar.TypeChecker.Tc.fst"
let _71_2643 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_71_2643) with
| (tps, rest) -> begin
(
# 1981 "FStar.TypeChecker.Tc.fst"
let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _71_2646 -> begin
(let _153_1178 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _153_1178 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _71_2649 -> begin
([], ty)
end)
in (match (_71_2652) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _71_2654 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (
# 1991 "FStar.TypeChecker.Tc.fst"
let datas = (match (uvs) with
| [] -> begin
datas
end
| _71_2658 -> begin
(
# 1994 "FStar.TypeChecker.Tc.fst"
let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _153_1179 -> FStar_Syntax_Syntax.U_name (_153_1179))))
in (
# 1995 "FStar.TypeChecker.Tc.fst"
let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _71_9 -> (match (_71_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _71_2663, _71_2665, _71_2667, _71_2669, _71_2671, _71_2673, _71_2675) -> begin
(tc, uvs_universes)
end
| _71_2679 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _71_2684 d -> (match (_71_2684) with
| (t, _71_2683) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _71_2688, _71_2690, tc, ntps, quals, mutuals, r) -> begin
(
# 1999 "FStar.TypeChecker.Tc.fst"
let ty = (let _153_1183 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _153_1183 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _71_2700 -> begin
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
# 2005 "FStar.TypeChecker.Tc.fst"
let _71_2710 = (FStar_All.pipe_right ses (FStar_List.partition (fun _71_10 -> (match (_71_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_71_2704) -> begin
true
end
| _71_2707 -> begin
false
end))))
in (match (_71_2710) with
| (tys, datas) -> begin
(
# 2007 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2010 "FStar.TypeChecker.Tc.fst"
let _71_2727 = (FStar_List.fold_right (fun tc _71_2716 -> (match (_71_2716) with
| (env, all_tcs, g) -> begin
(
# 2011 "FStar.TypeChecker.Tc.fst"
let _71_2720 = (tc_tycon env tc)
in (match (_71_2720) with
| (env, tc, tc_u) -> begin
(
# 2012 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (
# 2013 "FStar.TypeChecker.Tc.fst"
let _71_2722 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_1187 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _153_1187))
end else begin
()
end
in (let _153_1188 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _153_1188))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_71_2727) with
| (env, tcs, g) -> begin
(
# 2020 "FStar.TypeChecker.Tc.fst"
let _71_2737 = (FStar_List.fold_right (fun se _71_2731 -> (match (_71_2731) with
| (datas, g) -> begin
(
# 2021 "FStar.TypeChecker.Tc.fst"
let _71_2734 = (tc_data env tcs se)
in (match (_71_2734) with
| (data, g') -> begin
(let _153_1191 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _153_1191))
end))
end)) datas ([], g))
in (match (_71_2737) with
| (datas, g) -> begin
(
# 2026 "FStar.TypeChecker.Tc.fst"
let _71_2740 = (let _153_1192 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _153_1192 datas))
in (match (_71_2740) with
| (tcs, datas) -> begin
(let _153_1194 = (let _153_1193 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _153_1193))
in FStar_Syntax_Syntax.Sig_bundle (_153_1194))
end))
end))
end)))
end)))))))))

# 2029 "FStar.TypeChecker.Tc.fst"
let rec tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.env) = (fun env se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(
# 2042 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2043 "FStar.TypeChecker.Tc.fst"
let se = (tc_lex_t env ses quals lids)
in (let _153_1199 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _153_1199))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(
# 2047 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2048 "FStar.TypeChecker.Tc.fst"
let se = (tc_inductive env ses quals lids)
in (let _153_1200 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _153_1200))))
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
# 2060 "FStar.TypeChecker.Tc.fst"
let _71_2776 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (
# 2061 "FStar.TypeChecker.Tc.fst"
let _71_2778 = (let _153_1201 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _153_1201 Prims.ignore))
in (se, env)))
end)
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(
# 2066 "FStar.TypeChecker.Tc.fst"
let ne = (tc_eff_decl env ne)
in (
# 2067 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (
# 2068 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(
# 2072 "FStar.TypeChecker.Tc.fst"
let _71_2793 = (let _153_1202 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _153_1202))
in (match (_71_2793) with
| (a, wp_a_src) -> begin
(
# 2073 "FStar.TypeChecker.Tc.fst"
let _71_2796 = (let _153_1203 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _153_1203))
in (match (_71_2796) with
| (b, wp_b_tgt) -> begin
(
# 2074 "FStar.TypeChecker.Tc.fst"
let wp_a_tgt = (let _153_1207 = (let _153_1206 = (let _153_1205 = (let _153_1204 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _153_1204))
in FStar_Syntax_Syntax.NT (_153_1205))
in (_153_1206)::[])
in (FStar_Syntax_Subst.subst _153_1207 wp_b_tgt))
in (
# 2075 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _153_1212 = (let _153_1210 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_1209 = (let _153_1208 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_153_1208)::[])
in (_153_1210)::_153_1209))
in (let _153_1211 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _153_1212 _153_1211)))
in (
# 2076 "FStar.TypeChecker.Tc.fst"
let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (
# 2077 "FStar.TypeChecker.Tc.fst"
let sub = (
# 2077 "FStar.TypeChecker.Tc.fst"
let _71_2800 = sub
in {FStar_Syntax_Syntax.source = _71_2800.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _71_2800.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
in (
# 2078 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect ((sub, r))
in (
# 2079 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(
# 2083 "FStar.TypeChecker.Tc.fst"
let _71_2813 = ()
in (
# 2084 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2085 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2086 "FStar.TypeChecker.Tc.fst"
let _71_2819 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_71_2819) with
| (tps, c) -> begin
(
# 2087 "FStar.TypeChecker.Tc.fst"
let _71_2823 = (tc_tparams env tps)
in (match (_71_2823) with
| (tps, env, us) -> begin
(
# 2088 "FStar.TypeChecker.Tc.fst"
let _71_2827 = (tc_comp env c)
in (match (_71_2827) with
| (c, u, g) -> begin
(
# 2089 "FStar.TypeChecker.Tc.fst"
let _71_2828 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2090 "FStar.TypeChecker.Tc.fst"
let tags = (FStar_All.pipe_right tags (FStar_List.map (fun _71_11 -> (match (_71_11) with
| FStar_Syntax_Syntax.DefaultEffect (None) -> begin
(
# 2092 "FStar.TypeChecker.Tc.fst"
let c' = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let _153_1215 = (FStar_All.pipe_right c'.FStar_Syntax_Syntax.effect_name (fun _153_1214 -> Some (_153_1214)))
in FStar_Syntax_Syntax.DefaultEffect (_153_1215)))
end
| t -> begin
t
end))))
in (
# 2095 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 2096 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.close_comp tps c)
in (
# 2097 "FStar.TypeChecker.Tc.fst"
let _71_2840 = (let _153_1216 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _153_1216))
in (match (_71_2840) with
| (uvs, t) -> begin
(
# 2098 "FStar.TypeChecker.Tc.fst"
let _71_2859 = (match ((let _153_1218 = (let _153_1217 = (FStar_Syntax_Subst.compress t)
in _153_1217.FStar_Syntax_Syntax.n)
in (tps, _153_1218))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_71_2843, c)) -> begin
([], c)
end
| (_71_2849, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _71_2856 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_71_2859) with
| (tps, c) -> begin
(
# 2102 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_effect_abbrev ((lid, uvs, tps, c, tags, r))
in (
# 2103 "FStar.TypeChecker.Tc.fst"
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
# 2107 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2108 "FStar.TypeChecker.Tc.fst"
let _71_2870 = ()
in (
# 2109 "FStar.TypeChecker.Tc.fst"
let k = (let _153_1219 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _153_1219))
in (
# 2110 "FStar.TypeChecker.Tc.fst"
let _71_2875 = (check_and_gen env t k)
in (match (_71_2875) with
| (uvs, t) -> begin
(
# 2111 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (
# 2112 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(
# 2116 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2117 "FStar.TypeChecker.Tc.fst"
let _71_2888 = (FStar_Syntax_Util.type_u ())
in (match (_71_2888) with
| (k, _71_2887) -> begin
(
# 2118 "FStar.TypeChecker.Tc.fst"
let phi = (let _153_1220 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _153_1220 (norm env)))
in (
# 2119 "FStar.TypeChecker.Tc.fst"
let _71_2890 = (FStar_TypeChecker_Util.check_uvars r phi)
in (
# 2120 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))
in (
# 2121 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(
# 2125 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2126 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Recheck.t_unit)
in (
# 2127 "FStar.TypeChecker.Tc.fst"
let _71_2903 = (tc_term env e)
in (match (_71_2903) with
| (e, c, g1) -> begin
(
# 2128 "FStar.TypeChecker.Tc.fst"
let _71_2908 = (let _153_1224 = (let _153_1221 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Recheck.t_unit r)
in Some (_153_1221))
in (let _153_1223 = (let _153_1222 = (c.FStar_Syntax_Syntax.comp ())
in (e, _153_1222))
in (check_expected_effect env _153_1224 _153_1223)))
in (match (_71_2908) with
| (e, _71_2906, g) -> begin
(
# 2129 "FStar.TypeChecker.Tc.fst"
let _71_2909 = (let _153_1225 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _153_1225))
in (
# 2130 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, r))
in (
# 2131 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(
# 2135 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2136 "FStar.TypeChecker.Tc.fst"
let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
if (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q')) then begin
Some (q)
end else begin
(let _153_1235 = (let _153_1234 = (let _153_1233 = (let _153_1232 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Inconsistent qualifier annotations on %s" _153_1232))
in (_153_1233, r))
in FStar_Syntax_Syntax.Error (_153_1234))
in (Prims.raise _153_1235))
end
end))
in (
# 2147 "FStar.TypeChecker.Tc.fst"
let _71_2953 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _71_2930 lb -> (match (_71_2930) with
| (gen, lbs, quals_opt) -> begin
(
# 2148 "FStar.TypeChecker.Tc.fst"
let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2149 "FStar.TypeChecker.Tc.fst"
let _71_2949 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(
# 2153 "FStar.TypeChecker.Tc.fst"
let quals_opt = (check_quals_eq lbname quals_opt quals)
in (
# 2154 "FStar.TypeChecker.Tc.fst"
let _71_2944 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _71_2943 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _153_1238 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _153_1238, quals_opt))))
end)
in (match (_71_2949) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_71_2953) with
| (should_generalize, lbs', quals_opt) -> begin
(
# 2163 "FStar.TypeChecker.Tc.fst"
let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _71_12 -> (match (_71_12) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _71_2962 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (
# 2170 "FStar.TypeChecker.Tc.fst"
let lbs' = (FStar_List.rev lbs')
in (
# 2173 "FStar.TypeChecker.Tc.fst"
let e = (let _153_1242 = (let _153_1241 = (let _153_1240 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _153_1240))
in FStar_Syntax_Syntax.Tm_let (_153_1241))
in (FStar_Syntax_Syntax.mk _153_1242 None r))
in (
# 2176 "FStar.TypeChecker.Tc.fst"
let _71_2996 = (match ((tc_maybe_toplevel_term (
# 2176 "FStar.TypeChecker.Tc.fst"
let _71_2966 = env
in {FStar_TypeChecker_Env.solver = _71_2966.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _71_2966.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _71_2966.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _71_2966.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _71_2966.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _71_2966.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _71_2966.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _71_2966.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _71_2966.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _71_2966.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _71_2966.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _71_2966.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _71_2966.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _71_2966.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _71_2966.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _71_2966.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _71_2966.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _71_2966.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _71_2966.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _71_2966.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _71_2973; FStar_Syntax_Syntax.pos = _71_2971; FStar_Syntax_Syntax.vars = _71_2969}, _71_2980, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(
# 2179 "FStar.TypeChecker.Tc.fst"
let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_71_2984, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _71_2990 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _71_2993 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_71_2996) with
| (se, lbs) -> begin
(
# 2186 "FStar.TypeChecker.Tc.fst"
let _71_3002 = if (log env) then begin
(let _153_1248 = (let _153_1247 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 2188 "FStar.TypeChecker.Tc.fst"
let should_log = (match ((let _153_1244 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _153_1244))) with
| None -> begin
true
end
| _71_3000 -> begin
false
end)
in if should_log then begin
(let _153_1246 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _153_1245 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _153_1246 _153_1245)))
end else begin
""
end))))
in (FStar_All.pipe_right _153_1247 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _153_1248))
end else begin
()
end
in (
# 2195 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end))))
end))

# 2199 "FStar.TypeChecker.Tc.fst"
let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (
# 2223 "FStar.TypeChecker.Tc.fst"
let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _71_13 -> (match (_71_13) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _71_3012 -> begin
false
end)))))
in (
# 2224 "FStar.TypeChecker.Tc.fst"
let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _71_3022 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_71_3024) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _71_3035, _71_3037) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _71_3043 -> (match (_71_3043) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _71_3049, _71_3051, quals, r) -> begin
(
# 2238 "FStar.TypeChecker.Tc.fst"
let dec = (let _153_1264 = (let _153_1263 = (let _153_1262 = (let _153_1261 = (let _153_1260 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _153_1260))
in FStar_Syntax_Syntax.Tm_arrow (_153_1261))
in (FStar_Syntax_Syntax.mk _153_1262 None r))
in (l, us, _153_1263, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_153_1264))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _71_3061, _71_3063, _71_3065, _71_3067, r) -> begin
(
# 2241 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _71_3073 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_71_3075, _71_3077, quals, _71_3080) -> begin
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
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _71_14 -> (match (_71_14) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _71_3099 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_71_3101) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _71_3117, _71_3119, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(
# 2271 "FStar.TypeChecker.Tc.fst"
let lid = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals lid))) then begin
([], hidden)
end else begin
(
# 2274 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((lid, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::[], (FStar_Ident.range_of_lid lid)))
in ((dec)::[], (lid)::hidden))
end)
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (is_abstract quals) then begin
(let _153_1269 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _153_1268 = (let _153_1267 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (_153_1267, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_153_1268)))))
in (_153_1269, hidden))
end else begin
((se)::[], hidden)
end
end))))

# 2283 "FStar.TypeChecker.Tc.fst"
let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (
# 2284 "FStar.TypeChecker.Tc.fst"
let _71_3157 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _71_3138 se -> (match (_71_3138) with
| (ses, exports, env, hidden) -> begin
(
# 2286 "FStar.TypeChecker.Tc.fst"
let _71_3140 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_1276 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _153_1276))
end else begin
()
end
in (
# 2289 "FStar.TypeChecker.Tc.fst"
let _71_3144 = (tc_decl env se)
in (match (_71_3144) with
| (se, env) -> begin
(
# 2291 "FStar.TypeChecker.Tc.fst"
let _71_3145 = if ((FStar_ST.read FStar_Options.log_types) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _153_1277 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _153_1277))
end else begin
()
end
in (
# 2294 "FStar.TypeChecker.Tc.fst"
let _71_3147 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (
# 2296 "FStar.TypeChecker.Tc.fst"
let _71_3151 = (for_export hidden se)
in (match (_71_3151) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_71_3157) with
| (ses, exports, env, _71_3156) -> begin
(let _153_1278 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _153_1278, env))
end)))

# 2301 "FStar.TypeChecker.Tc.fst"
let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2302 "FStar.TypeChecker.Tc.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 2303 "FStar.TypeChecker.Tc.fst"
let msg = (Prims.strcat "Internals for " name)
in (
# 2304 "FStar.TypeChecker.Tc.fst"
let env = (
# 2304 "FStar.TypeChecker.Tc.fst"
let _71_3162 = env
in (let _153_1283 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _71_3162.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _71_3162.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _71_3162.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _71_3162.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _71_3162.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _71_3162.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _71_3162.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _71_3162.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _71_3162.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _71_3162.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _71_3162.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _71_3162.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _71_3162.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _71_3162.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _71_3162.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _71_3162.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _153_1283; FStar_TypeChecker_Env.default_effects = _71_3162.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _71_3162.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _71_3162.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _71_3162.FStar_TypeChecker_Env.use_bv_sorts}))
in (
# 2305 "FStar.TypeChecker.Tc.fst"
let _71_3165 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (
# 2306 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (
# 2307 "FStar.TypeChecker.Tc.fst"
let _71_3171 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_71_3171) with
| (ses, exports, env) -> begin
((
# 2308 "FStar.TypeChecker.Tc.fst"
let _71_3172 = modul
in {FStar_Syntax_Syntax.name = _71_3172.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _71_3172.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _71_3172.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))

# 2310 "FStar.TypeChecker.Tc.fst"
let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (
# 2311 "FStar.TypeChecker.Tc.fst"
let _71_3180 = (tc_decls env decls)
in (match (_71_3180) with
| (ses, exports, env) -> begin
(
# 2312 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2312 "FStar.TypeChecker.Tc.fst"
let _71_3181 = modul
in {FStar_Syntax_Syntax.name = _71_3181.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _71_3181.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _71_3181.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))

# 2315 "FStar.TypeChecker.Tc.fst"
let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (
# 2316 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2316 "FStar.TypeChecker.Tc.fst"
let _71_3187 = modul
in {FStar_Syntax_Syntax.name = _71_3187.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _71_3187.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (
# 2317 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.finish_module env modul)
in (
# 2318 "FStar.TypeChecker.Tc.fst"
let _71_3197 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(
# 2320 "FStar.TypeChecker.Tc.fst"
let _71_3191 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (
# 2321 "FStar.TypeChecker.Tc.fst"
let _71_3193 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (
# 2322 "FStar.TypeChecker.Tc.fst"
let _71_3195 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _153_1296 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _153_1296 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))

# 2327 "FStar.TypeChecker.Tc.fst"
let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2328 "FStar.TypeChecker.Tc.fst"
let _71_3204 = (tc_partial_modul env modul)
in (match (_71_3204) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

# 2331 "FStar.TypeChecker.Tc.fst"
let add_modul_to_tcenv : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_TypeChecker_Env.env = (fun en m -> (
# 2332 "FStar.TypeChecker.Tc.fst"
let do_sigelt = (fun en elt -> (
# 2333 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt en elt)
in (
# 2334 "FStar.TypeChecker.Tc.fst"
let _71_3211 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env elt)
in env)))
in (
# 2337 "FStar.TypeChecker.Tc.fst"
let en = (FStar_TypeChecker_Env.set_current_module en m.FStar_Syntax_Syntax.name)
in (let _153_1309 = (FStar_List.fold_left do_sigelt en m.FStar_Syntax_Syntax.exports)
in (FStar_TypeChecker_Env.finish_module _153_1309 m)))))

# 2340 "FStar.TypeChecker.Tc.fst"
let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 2341 "FStar.TypeChecker.Tc.fst"
let _71_3216 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _153_1314 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _153_1314))
end else begin
()
end
in (
# 2343 "FStar.TypeChecker.Tc.fst"
let env = (
# 2343 "FStar.TypeChecker.Tc.fst"
let _71_3218 = env
in {FStar_TypeChecker_Env.solver = _71_3218.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _71_3218.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _71_3218.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _71_3218.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _71_3218.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _71_3218.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _71_3218.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _71_3218.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _71_3218.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _71_3218.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _71_3218.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _71_3218.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _71_3218.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _71_3218.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _71_3218.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _71_3218.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _71_3218.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _71_3218.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _71_3218.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _71_3218.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _71_3218.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 2344 "FStar.TypeChecker.Tc.fst"
let _71_3224 = (tc_tot_or_gtot_term env e)
in (match (_71_3224) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected a total term; got a ghost term", e.FStar_Syntax_Syntax.pos))))
end
end)))))

# 2349 "FStar.TypeChecker.Tc.fst"
let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (
# 2350 "FStar.TypeChecker.Tc.fst"
let _71_3227 = if ((let _153_1319 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _153_1319)) <> 0) then begin
(let _153_1320 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _153_1320))
end else begin
()
end
in (
# 2352 "FStar.TypeChecker.Tc.fst"
let _71_3231 = (tc_modul env m)
in (match (_71_3231) with
| (m, env) -> begin
(
# 2353 "FStar.TypeChecker.Tc.fst"
let _71_3232 = if (FStar_Options.should_dump m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _153_1321 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _153_1321))
end else begin
()
end
in (m, env))
end))))




