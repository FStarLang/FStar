
open Prims
# 40 "FStar.TypeChecker.Tc.fst"
let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_ST.read FStar_Options.log_types) && (not ((let _151_3 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _151_3))))))

# 41 "FStar.TypeChecker.Tc.fst"
let rng : FStar_TypeChecker_Env.env  ->  FStar_Range.range = (fun env -> (FStar_TypeChecker_Env.get_range env))

# 42 "FStar.TypeChecker.Tc.fst"
let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (
# 42 "FStar.TypeChecker.Tc.fst"
let _72_17 = env
in {FStar_TypeChecker_Env.solver = _72_17.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _72_17.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _72_17.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _72_17.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _72_17.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _72_17.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _72_17.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _72_17.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _72_17.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _72_17.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _72_17.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _72_17.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _72_17.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _72_17.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _72_17.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _72_17.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _72_17.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _72_17.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _72_17.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _72_17.FStar_TypeChecker_Env.use_bv_sorts}))

# 43 "FStar.TypeChecker.Tc.fst"
let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (
# 43 "FStar.TypeChecker.Tc.fst"
let _72_20 = env
in {FStar_TypeChecker_Env.solver = _72_20.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _72_20.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _72_20.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _72_20.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _72_20.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _72_20.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _72_20.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _72_20.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _72_20.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _72_20.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _72_20.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _72_20.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _72_20.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _72_20.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _72_20.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _72_20.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _72_20.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _72_20.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _72_20.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _72_20.FStar_TypeChecker_Env.use_bv_sorts}))

# 44 "FStar.TypeChecker.Tc.fst"
let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (
# 46 "FStar.TypeChecker.Tc.fst"
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

# 49 "FStar.TypeChecker.Tc.fst"
let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _72_1 -> (match (_72_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _72_30 -> begin
false
end))

# 52 "FStar.TypeChecker.Tc.fst"
let steps : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Normalize.step Prims.list = (fun env -> if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::[]
end else begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]
end)

# 56 "FStar.TypeChecker.Tc.fst"
let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Unfold)::(FStar_TypeChecker_Normalize.Beta)::[]) env t))

# 57 "FStar.TypeChecker.Tc.fst"
let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _151_30 = (steps env)
in (FStar_TypeChecker_Normalize.normalize _151_30 env t)))

# 58 "FStar.TypeChecker.Tc.fst"
let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _151_35 = (steps env)
in (FStar_TypeChecker_Normalize.normalize_comp _151_35 env c)))

# 59 "FStar.TypeChecker.Tc.fst"
let fxv_check : FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv Prims.list * (FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv  ->  Prims.bool))  ->  Prims.unit = (fun head env kt fvs -> (
# 60 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun try_norm t -> if (FStar_Util.set_is_empty fvs) then begin
()
end else begin
(
# 62 "FStar.TypeChecker.Tc.fst"
let fvs' = (let _151_54 = if try_norm then begin
(norm env t)
end else begin
t
end
in (FStar_Syntax_Free.names _151_54))
in (
# 63 "FStar.TypeChecker.Tc.fst"
let a = (FStar_Util.set_intersect fvs fvs')
in if (FStar_Util.set_is_empty a) then begin
()
end else begin
if (not (try_norm)) then begin
(aux true t)
end else begin
(
# 67 "FStar.TypeChecker.Tc.fst"
let fail = (fun _72_48 -> (match (()) with
| () -> begin
(
# 68 "FStar.TypeChecker.Tc.fst"
let escaping = (let _151_58 = (let _151_57 = (FStar_Util.set_elements a)
in (FStar_All.pipe_right _151_57 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _151_58 (FStar_String.concat ", ")))
in (
# 69 "FStar.TypeChecker.Tc.fst"
let msg = if ((FStar_Util.set_count a) > 1) then begin
(let _151_59 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'{%s}\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" escaping _151_59))
end else begin
(let _151_60 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variable \'%s\' in the type of \'%s\' escapes because of impure applications; add explicit let-bindings" escaping _151_60))
end
in (let _151_63 = (let _151_62 = (let _151_61 = (FStar_TypeChecker_Env.get_range env)
in (msg, _151_61))
in FStar_Syntax_Syntax.Error (_151_62))
in (Prims.raise _151_63))))
end))
in (
# 75 "FStar.TypeChecker.Tc.fst"
let s = (let _151_64 = (FStar_TypeChecker_Recheck.check t)
in (FStar_TypeChecker_Util.new_uvar env _151_64))
in (match ((FStar_TypeChecker_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g)
end
| _72_55 -> begin
(fail ())
end)))
end
end))
end)
in (aux false kt)))

# 82 "FStar.TypeChecker.Tc.fst"
let check_no_escape : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun env bs t -> (
# 83 "FStar.TypeChecker.Tc.fst"
let fvs = (FStar_Syntax_Free.names t)
in if (FStar_Util.for_some (fun x -> (FStar_Util.set_mem x fvs)) bs) then begin
(
# 85 "FStar.TypeChecker.Tc.fst"
let _72_64 = (FStar_Syntax_Util.type_u ())
in (match (_72_64) with
| (k, _72_63) -> begin
(
# 86 "FStar.TypeChecker.Tc.fst"
let tnarrow = (FStar_TypeChecker_Util.new_uvar env k)
in (let _151_72 = (FStar_TypeChecker_Rel.teq env t tnarrow)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _151_72)))
end))
end else begin
()
end))

# 89 "FStar.TypeChecker.Tc.fst"
let maybe_push_binding : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder  ->  FStar_TypeChecker_Env.env = (fun env b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
env
end else begin
(
# 91 "FStar.TypeChecker.Tc.fst"
let _72_68 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_78 = (FStar_Syntax_Print.bv_to_string (Prims.fst b))
in (let _151_77 = (FStar_Syntax_Print.term_to_string (Prims.fst b).FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _151_78 _151_77)))
end else begin
()
end
in (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))
end)

# 95 "FStar.TypeChecker.Tc.fst"
let maybe_make_subst = (fun _72_2 -> (match (_72_2) with
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Syntax_Syntax.NT ((x, e)))::[]
end
| _72_77 -> begin
[]
end))

# 99 "FStar.TypeChecker.Tc.fst"
let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.subst_t = (fun s b v -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
s
end else begin
(FStar_Syntax_Syntax.NT (((Prims.fst b), v)))::s
end)

# 103 "FStar.TypeChecker.Tc.fst"
let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (
# 104 "FStar.TypeChecker.Tc.fst"
let _72_83 = lc
in {FStar_Syntax_Syntax.eff_name = _72_83.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _72_83.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _72_85 -> (match (()) with
| () -> begin
(let _151_91 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _151_91 t))
end))}))

# 106 "FStar.TypeChecker.Tc.fst"
let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (
# 107 "FStar.TypeChecker.Tc.fst"
let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _151_100 = if (not ((FStar_Syntax_Util.is_pure_or_ghost_function t))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _151_100))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (
# 112 "FStar.TypeChecker.Tc.fst"
let t = lc.FStar_Syntax_Syntax.res_typ
in (
# 113 "FStar.TypeChecker.Tc.fst"
let _72_117 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, guard)
end
| Some (t') -> begin
(
# 116 "FStar.TypeChecker.Tc.fst"
let _72_99 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_102 = (FStar_Syntax_Print.term_to_string t)
in (let _151_101 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _151_102 _151_101)))
end else begin
()
end
in (
# 118 "FStar.TypeChecker.Tc.fst"
let _72_103 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_72_103) with
| (e, lc) -> begin
(
# 119 "FStar.TypeChecker.Tc.fst"
let t = lc.FStar_Syntax_Syntax.res_typ
in (
# 120 "FStar.TypeChecker.Tc.fst"
let _72_107 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_72_107) with
| (e, g) -> begin
(
# 121 "FStar.TypeChecker.Tc.fst"
let _72_108 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_104 = (FStar_Syntax_Print.term_to_string t)
in (let _151_103 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _151_104 _151_103)))
end else begin
()
end
in (
# 123 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (
# 124 "FStar.TypeChecker.Tc.fst"
let _72_113 = (let _151_110 = (FStar_All.pipe_left (fun _151_109 -> Some (_151_109)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _151_110 env e lc g))
in (match (_72_113) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))))
end)))
end)))
end)
in (match (_72_117) with
| (e, lc, g) -> begin
(
# 126 "FStar.TypeChecker.Tc.fst"
let _72_118 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_111 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _151_111))
end else begin
()
end
in (e, lc, g))
end)))))

# 130 "FStar.TypeChecker.Tc.fst"
let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (t) -> begin
(
# 134 "FStar.TypeChecker.Tc.fst"
let _72_128 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_72_128) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))

# 137 "FStar.TypeChecker.Tc.fst"
let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _72_133 -> (match (_72_133) with
| (e, c) -> begin
(
# 138 "FStar.TypeChecker.Tc.fst"
let expected_c_opt = (match (copt) with
| Some (_72_135) -> begin
copt
end
| None -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
(
# 143 "FStar.TypeChecker.Tc.fst"
let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 144 "FStar.TypeChecker.Tc.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (match ((FStar_TypeChecker_Env.default_effect env md.FStar_Syntax_Syntax.mname)) with
| None -> begin
None
end
| Some (l) -> begin
(
# 148 "FStar.TypeChecker.Tc.fst"
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
# 152 "FStar.TypeChecker.Tc.fst"
let def = (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.effect_name = l; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = flags})
in Some (def)))
end)))
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _151_124 = (norm_c env c)
in (e, _151_124, FStar_TypeChecker_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(
# 161 "FStar.TypeChecker.Tc.fst"
let _72_149 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_127 = (FStar_Syntax_Print.term_to_string e)
in (let _151_126 = (FStar_Syntax_Print.comp_to_string c)
in (let _151_125 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _151_127 _151_126 _151_125))))
end else begin
()
end
in (
# 164 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 165 "FStar.TypeChecker.Tc.fst"
let _72_152 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_130 = (FStar_Syntax_Print.term_to_string e)
in (let _151_129 = (FStar_Syntax_Print.comp_to_string c)
in (let _151_128 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _151_130 _151_129 _151_128))))
end else begin
()
end
in (
# 170 "FStar.TypeChecker.Tc.fst"
let _72_158 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_72_158) with
| (e, _72_156, g) -> begin
(
# 171 "FStar.TypeChecker.Tc.fst"
let g = (let _151_131 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _151_131 "could not prove post-condition" g))
in (
# 172 "FStar.TypeChecker.Tc.fst"
let _72_160 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_133 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _151_132 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _151_133 _151_132)))
end else begin
()
end
in (e, expected_c, g)))
end)))))
end))
end))

# 175 "FStar.TypeChecker.Tc.fst"
let no_logical_guard = (fun env _72_166 -> (match (_72_166) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
(te, kt, f)
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _151_139 = (let _151_138 = (let _151_137 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _151_136 = (FStar_TypeChecker_Env.get_range env)
in (_151_137, _151_136)))
in FStar_Syntax_Syntax.Error (_151_138))
in (Prims.raise _151_139))
end)
end))

# 180 "FStar.TypeChecker.Tc.fst"
let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _151_142 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _151_142))
end))

# 184 "FStar.TypeChecker.Tc.fst"
let with_implicits = (fun imps _72_178 -> (match (_72_178) with
| (e, l, g) -> begin
(e, l, (
# 184 "FStar.TypeChecker.Tc.fst"
let _72_179 = g
in {FStar_TypeChecker_Env.guard_f = _72_179.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _72_179.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _72_179.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (FStar_List.append imps g.FStar_TypeChecker_Env.implicits)}))
end))

# 185 "FStar.TypeChecker.Tc.fst"
let add_implicit : (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun u g -> (
# 185 "FStar.TypeChecker.Tc.fst"
let _72_183 = g
in {FStar_TypeChecker_Env.guard_f = _72_183.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _72_183.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _72_183.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (u)::g.FStar_TypeChecker_Env.implicits}))

# 190 "FStar.TypeChecker.Tc.fst"
let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _72_201; FStar_Syntax_Syntax.result_typ = _72_199; FStar_Syntax_Syntax.effect_args = _pre::_post::(pats, _72_193)::[]; FStar_Syntax_Syntax.flags = _72_190}) -> begin
(
# 194 "FStar.TypeChecker.Tc.fst"
let pat_vars = (FStar_Syntax_Free.names pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _72_208 -> (match (_72_208) with
| (b, _72_207) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _72_212) -> begin
(let _151_155 = (let _151_154 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _151_154))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _151_155))
end))
end
| _72_216 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end)

# 205 "FStar.TypeChecker.Tc.fst"
let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun env actuals expected_c -> (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(
# 209 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 210 "FStar.TypeChecker.Tc.fst"
let env = (
# 210 "FStar.TypeChecker.Tc.fst"
let _72_223 = env
in {FStar_TypeChecker_Env.solver = _72_223.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _72_223.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _72_223.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _72_223.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _72_223.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _72_223.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _72_223.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _72_223.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _72_223.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _72_223.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _72_223.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _72_223.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _72_223.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _72_223.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _72_223.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _72_223.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _72_223.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _72_223.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _72_223.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _72_223.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 211 "FStar.TypeChecker.Tc.fst"
let precedes = (let _151_162 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.precedes_lid _151_162))
in (
# 213 "FStar.TypeChecker.Tc.fst"
let decreases_clause = (fun bs c -> (
# 215 "FStar.TypeChecker.Tc.fst"
let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _72_235 -> (match (_72_235) with
| (b, _72_234) -> begin
(
# 217 "FStar.TypeChecker.Tc.fst"
let t = (let _151_170 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _151_170))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _72_244 -> begin
(let _151_171 = (FStar_Syntax_Syntax.bv_to_name b)
in (_151_171)::[])
end))
end)))))
in (
# 222 "FStar.TypeChecker.Tc.fst"
let as_lex_list = (fun dec -> (
# 223 "FStar.TypeChecker.Tc.fst"
let _72_250 = (FStar_Syntax_Util.head_and_args dec)
in (match (_72_250) with
| (head, _72_249) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _72_253) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _72_257 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (
# 227 "FStar.TypeChecker.Tc.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _72_3 -> (match (_72_3) with
| FStar_Syntax_Syntax.DECREASES (_72_261) -> begin
true
end
| _72_264 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _72_269 -> begin
(
# 231 "FStar.TypeChecker.Tc.fst"
let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| x::[] -> begin
x
end
| _72_274 -> begin
(mk_lex_list xs)
end))
end)))))
in (
# 236 "FStar.TypeChecker.Tc.fst"
let previous_dec = (decreases_clause actuals expected_c)
in (
# 237 "FStar.TypeChecker.Tc.fst"
let guard_one_letrec = (fun _72_279 -> (match (_72_279) with
| (l, t) -> begin
(match ((let _151_177 = (FStar_Syntax_Subst.compress t)
in _151_177.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 241 "FStar.TypeChecker.Tc.fst"
let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _72_286 -> (match (_72_286) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _151_181 = (let _151_180 = (let _151_179 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_151_179))
in (FStar_Syntax_Syntax.new_bv _151_180 x.FStar_Syntax_Syntax.sort))
in (_151_181, imp))
end else begin
(x, imp)
end
end))))
in (
# 242 "FStar.TypeChecker.Tc.fst"
let _72_290 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_72_290) with
| (formals, c) -> begin
(
# 243 "FStar.TypeChecker.Tc.fst"
let dec = (decreases_clause formals c)
in (
# 244 "FStar.TypeChecker.Tc.fst"
let precedes = (let _151_185 = (let _151_184 = (FStar_Syntax_Syntax.as_arg dec)
in (let _151_183 = (let _151_182 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_151_182)::[])
in (_151_184)::_151_183))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _151_185 None r))
in (
# 245 "FStar.TypeChecker.Tc.fst"
let _72_297 = (FStar_Util.prefix formals)
in (match (_72_297) with
| (bs, (last, imp)) -> begin
(
# 246 "FStar.TypeChecker.Tc.fst"
let last = (
# 246 "FStar.TypeChecker.Tc.fst"
let _72_298 = last
in (let _151_186 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _72_298.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _72_298.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _151_186}))
in (
# 247 "FStar.TypeChecker.Tc.fst"
let refined_formals = (FStar_List.append bs (((last, imp))::[]))
in (
# 248 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (
# 249 "FStar.TypeChecker.Tc.fst"
let _72_303 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_189 = (FStar_Syntax_Print.lbname_to_string l)
in (let _151_188 = (FStar_Syntax_Print.term_to_string t)
in (let _151_187 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _151_189 _151_188 _151_187))))
end else begin
()
end
in (l, t')))))
end))))
end)))
end
| _72_306 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end))

# 261 "FStar.TypeChecker.Tc.fst"
let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (
# 261 "FStar.TypeChecker.Tc.fst"
let _72_309 = env
in {FStar_TypeChecker_Env.solver = _72_309.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _72_309.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _72_309.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _72_309.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _72_309.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _72_309.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _72_309.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _72_309.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _72_309.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _72_309.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _72_309.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _72_309.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _72_309.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _72_309.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _72_309.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _72_309.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _72_309.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _72_309.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _72_309.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _72_309.FStar_TypeChecker_Env.use_bv_sorts}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 266 "FStar.TypeChecker.Tc.fst"
let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (
# 267 "FStar.TypeChecker.Tc.fst"
let _72_314 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_255 = (let _151_253 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _151_253))
in (let _151_254 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _151_255 _151_254)))
end else begin
()
end
in (
# 268 "FStar.TypeChecker.Tc.fst"
let top = e
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_72_318) -> begin
(let _151_259 = (FStar_Syntax_Subst.compress e)
in (tc_term env _151_259))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(
# 285 "FStar.TypeChecker.Tc.fst"
let _72_358 = (FStar_Syntax_Util.type_u ())
in (match (_72_358) with
| (t, u) -> begin
(
# 286 "FStar.TypeChecker.Tc.fst"
let _72_362 = (tc_check_tot_or_gtot_term env e t)
in (match (_72_362) with
| (e, c, g) -> begin
(
# 287 "FStar.TypeChecker.Tc.fst"
let _72_369 = (
# 288 "FStar.TypeChecker.Tc.fst"
let _72_366 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_72_366) with
| (env, _72_365) -> begin
(tc_pats env pats)
end))
in (match (_72_369) with
| (pats, g') -> begin
(
# 290 "FStar.TypeChecker.Tc.fst"
let g' = (
# 290 "FStar.TypeChecker.Tc.fst"
let _72_370 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _72_370.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _72_370.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _72_370.FStar_TypeChecker_Env.implicits})
in (let _151_261 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_pattern (pats)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _151_260 = (FStar_TypeChecker_Rel.conj_guard g g')
in (_151_261, c, _151_260))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _151_262 = (FStar_Syntax_Subst.compress e)
in _151_262.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_72_379, {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _72_386; FStar_Syntax_Syntax.lbtyp = _72_384; FStar_Syntax_Syntax.lbeff = _72_382; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 298 "FStar.TypeChecker.Tc.fst"
let _72_397 = (let _151_263 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Recheck.t_unit)
in (tc_term _151_263 e1))
in (match (_72_397) with
| (e1, c1, g1) -> begin
(
# 299 "FStar.TypeChecker.Tc.fst"
let _72_401 = (tc_term env e2)
in (match (_72_401) with
| (e2, c2, g2) -> begin
(
# 300 "FStar.TypeChecker.Tc.fst"
let c = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (None, c2))
in (
# 301 "FStar.TypeChecker.Tc.fst"
let e = (let _151_268 = (let _151_267 = (let _151_266 = (let _151_265 = (let _151_264 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Recheck.t_unit, e1))
in (_151_264)::[])
in (false, _151_265))
in (_151_266, e2))
in FStar_Syntax_Syntax.Tm_let (_151_267))
in (FStar_Syntax_Syntax.mk _151_268 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 302 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _151_269 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _151_269)))))
end))
end))
end
| _72_406 -> begin
(
# 305 "FStar.TypeChecker.Tc.fst"
let _72_410 = (tc_term env e)
in (match (_72_410) with
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
let _72_419 = (tc_term env e)
in (match (_72_419) with
| (e, c, g) -> begin
(
# 312 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, m))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _72_424) -> begin
(
# 316 "FStar.TypeChecker.Tc.fst"
let _72_429 = (FStar_Syntax_Util.type_u ())
in (match (_72_429) with
| (k, u) -> begin
(
# 317 "FStar.TypeChecker.Tc.fst"
let _72_434 = (tc_check_tot_or_gtot_term env t k)
in (match (_72_434) with
| (t, _72_432, f) -> begin
(
# 318 "FStar.TypeChecker.Tc.fst"
let _72_438 = (let _151_270 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _151_270 e))
in (match (_72_438) with
| (e, c, g) -> begin
(
# 319 "FStar.TypeChecker.Tc.fst"
let _72_442 = (let _151_274 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _72_439 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _151_274 e c f))
in (match (_72_442) with
| (c, f) -> begin
(
# 320 "FStar.TypeChecker.Tc.fst"
let _72_446 = (let _151_275 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, t, Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _151_275 c))
in (match (_72_446) with
| (e, c, f2) -> begin
(let _151_277 = (let _151_276 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _151_276))
in (e, c, _151_277))
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
let env = (let _151_279 = (let _151_278 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _151_278 Prims.fst))
in (FStar_All.pipe_right _151_279 instantiate_both))
in (
# 326 "FStar.TypeChecker.Tc.fst"
let _72_453 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_281 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _151_280 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _151_281 _151_280)))
end else begin
()
end
in (
# 330 "FStar.TypeChecker.Tc.fst"
let _72_458 = (tc_term (no_inst env) head)
in (match (_72_458) with
| (head, chead, g_head) -> begin
(
# 331 "FStar.TypeChecker.Tc.fst"
let _72_462 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _151_282 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _151_282))
end else begin
(let _151_283 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _151_283))
end
in (match (_72_462) with
| (e, c, g) -> begin
(
# 334 "FStar.TypeChecker.Tc.fst"
let _72_463 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _151_284 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _151_284))
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
let _72_470 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_290 = (FStar_Syntax_Print.term_to_string e)
in (let _151_289 = (let _151_285 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _151_285))
in (let _151_288 = (let _151_287 = (FStar_TypeChecker_Env.expected_typ env0)
in (FStar_All.pipe_right _151_287 (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end))))
in (FStar_Util.print3 "(%s) About to check %s against expected typ %s\n" _151_290 _151_289 _151_288))))
end else begin
()
end
in (
# 346 "FStar.TypeChecker.Tc.fst"
let _72_475 = (comp_check_expected_typ env0 e c)
in (match (_72_475) with
| (e, c, g') -> begin
(
# 347 "FStar.TypeChecker.Tc.fst"
let _72_476 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_293 = (FStar_Syntax_Print.term_to_string e)
in (let _151_292 = (let _151_291 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _151_291))
in (FStar_Util.print2 "(%s) checked ... got %s\n" _151_293 _151_292)))
end else begin
()
end
in (
# 351 "FStar.TypeChecker.Tc.fst"
let gimp = (match ((let _151_294 = (FStar_Syntax_Subst.compress head)
in _151_294.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _72_480) -> begin
(
# 354 "FStar.TypeChecker.Tc.fst"
let imp = (env0, u, e, c.FStar_Syntax_Syntax.res_typ, e.FStar_Syntax_Syntax.pos)
in (
# 355 "FStar.TypeChecker.Tc.fst"
let _72_484 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _72_484.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _72_484.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _72_484.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _72_487 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (
# 357 "FStar.TypeChecker.Tc.fst"
let gres = (let _151_295 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _151_295))
in (
# 358 "FStar.TypeChecker.Tc.fst"
let _72_490 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _151_296 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print1 "Guard from application node is %s\n" _151_296))
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
let _72_498 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_72_498) with
| (env1, topt) -> begin
(
# 364 "FStar.TypeChecker.Tc.fst"
let env1 = (instantiate_both env1)
in (
# 365 "FStar.TypeChecker.Tc.fst"
let _72_503 = (tc_term env1 e1)
in (match (_72_503) with
| (e1, c1, g1) -> begin
(
# 366 "FStar.TypeChecker.Tc.fst"
let _72_514 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(
# 369 "FStar.TypeChecker.Tc.fst"
let _72_510 = (FStar_Syntax_Util.type_u ())
in (match (_72_510) with
| (k, _72_509) -> begin
(
# 370 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _151_297 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_151_297, res_t)))
end))
end)
in (match (_72_514) with
| (env_branches, res_t) -> begin
(
# 373 "FStar.TypeChecker.Tc.fst"
let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (
# 374 "FStar.TypeChecker.Tc.fst"
let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (
# 375 "FStar.TypeChecker.Tc.fst"
let _72_531 = (
# 376 "FStar.TypeChecker.Tc.fst"
let _72_528 = (FStar_List.fold_right (fun _72_522 _72_525 -> (match ((_72_522, _72_525)) with
| ((_72_518, f, c, g), (caccum, gaccum)) -> begin
(let _151_300 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _151_300))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_72_528) with
| (cases, g) -> begin
(let _151_301 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_151_301, g))
end))
in (match (_72_531) with
| (c_branches, g_branches) -> begin
(
# 380 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (guard_x), c_branches))
in (
# 381 "FStar.TypeChecker.Tc.fst"
let e = (let _151_305 = (let _151_304 = (let _151_303 = (FStar_List.map (fun _72_540 -> (match (_72_540) with
| (f, _72_535, _72_537, _72_539) -> begin
f
end)) t_eqns)
in (e1, _151_303))
in FStar_Syntax_Syntax.Tm_match (_151_304))
in (FStar_Syntax_Syntax.mk _151_305 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (
# 382 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, cres.FStar_Syntax_Syntax.res_typ, Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (
# 383 "FStar.TypeChecker.Tc.fst"
let _72_543 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _151_308 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _151_307 = (let _151_306 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _151_306))
in (FStar_Util.print2 "(%s) comp type = %s\n" _151_308 _151_307)))
end else begin
()
end
in (let _151_309 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _151_309))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_72_555); FStar_Syntax_Syntax.lbunivs = _72_553; FStar_Syntax_Syntax.lbtyp = _72_551; FStar_Syntax_Syntax.lbeff = _72_549; FStar_Syntax_Syntax.lbdef = _72_547}::[]), _72_561) -> begin
(
# 390 "FStar.TypeChecker.Tc.fst"
let _72_564 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_310 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _151_310))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _72_568), _72_571) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_72_586); FStar_Syntax_Syntax.lbunivs = _72_584; FStar_Syntax_Syntax.lbtyp = _72_582; FStar_Syntax_Syntax.lbeff = _72_580; FStar_Syntax_Syntax.lbdef = _72_578}::_72_576), _72_592) -> begin
(
# 397 "FStar.TypeChecker.Tc.fst"
let _72_595 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_311 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _151_311))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _72_599), _72_602) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 410 "FStar.TypeChecker.Tc.fst"
let check_instantiated_fvar = (fun env v dc e t -> (
# 411 "FStar.TypeChecker.Tc.fst"
let _72_616 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_72_616) with
| (e, t, implicits) -> begin
(
# 413 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _151_325 = (let _151_324 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_324))
in FStar_Util.Inr (_151_325))
end
in (
# 414 "FStar.TypeChecker.Tc.fst"
let is_data_ctor = (fun _72_4 -> (match (_72_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _72_626 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _151_331 = (let _151_330 = (let _151_329 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _151_328 = (FStar_TypeChecker_Env.get_range env)
in (_151_329, _151_328)))
in FStar_Syntax_Syntax.Error (_151_330))
in (Prims.raise _151_331))
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
let g = (match ((let _151_332 = (FStar_Syntax_Subst.compress t1)
in _151_332.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_72_637) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _72_640 -> begin
(
# 433 "FStar.TypeChecker.Tc.fst"
let imp = (env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (
# 434 "FStar.TypeChecker.Tc.fst"
let _72_642 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _72_642.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _72_642.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _72_642.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 439 "FStar.TypeChecker.Tc.fst"
let _72_648 = (FStar_Syntax_Util.type_u ())
in (match (_72_648) with
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
let _72_653 = x
in {FStar_Syntax_Syntax.ppname = _72_653.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _72_653.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (
# 446 "FStar.TypeChecker.Tc.fst"
let _72_659 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_72_659) with
| (e, t, implicits) -> begin
(
# 447 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _151_334 = (let _151_333 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_333))
in FStar_Util.Inr (_151_334))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (v, dc); FStar_Syntax_Syntax.tk = _72_666; FStar_Syntax_Syntax.pos = _72_664; FStar_Syntax_Syntax.vars = _72_662}, us) -> begin
(
# 451 "FStar.TypeChecker.Tc.fst"
let us = (FStar_List.map (tc_universe env) us)
in (
# 452 "FStar.TypeChecker.Tc.fst"
let _72_678 = (FStar_TypeChecker_Env.lookup_lid env v.FStar_Syntax_Syntax.v)
in (match (_72_678) with
| (us', t) -> begin
(
# 453 "FStar.TypeChecker.Tc.fst"
let _72_685 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _151_337 = (let _151_336 = (let _151_335 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _151_335))
in FStar_Syntax_Syntax.Error (_151_336))
in (Prims.raise _151_337))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _72_684 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (
# 458 "FStar.TypeChecker.Tc.fst"
let e = (let _151_340 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (((
# 458 "FStar.TypeChecker.Tc.fst"
let _72_687 = v
in {FStar_Syntax_Syntax.v = _72_687.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _72_687.FStar_Syntax_Syntax.p}), dc))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _151_340 us))
in (check_instantiated_fvar env v dc e t)))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (v, dc) -> begin
(
# 462 "FStar.TypeChecker.Tc.fst"
let _72_696 = (FStar_TypeChecker_Env.lookup_lid env v.FStar_Syntax_Syntax.v)
in (match (_72_696) with
| (us, t) -> begin
(
# 463 "FStar.TypeChecker.Tc.fst"
let e = (let _151_341 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (((
# 463 "FStar.TypeChecker.Tc.fst"
let _72_697 = v
in {FStar_Syntax_Syntax.v = _72_697.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _72_697.FStar_Syntax_Syntax.p}), dc))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _151_341 us))
in (check_instantiated_fvar env v dc e t))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(
# 467 "FStar.TypeChecker.Tc.fst"
let t = (FStar_TypeChecker_Recheck.check e)
in (
# 468 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 472 "FStar.TypeChecker.Tc.fst"
let _72_710 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_72_710) with
| (bs, c) -> begin
(
# 473 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 474 "FStar.TypeChecker.Tc.fst"
let _72_715 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_72_715) with
| (env, _72_714) -> begin
(
# 475 "FStar.TypeChecker.Tc.fst"
let _72_720 = (tc_binders env bs)
in (match (_72_720) with
| (bs, env, g, us) -> begin
(
# 476 "FStar.TypeChecker.Tc.fst"
let _72_724 = (tc_comp env c)
in (match (_72_724) with
| (c, uc, f) -> begin
(
# 477 "FStar.TypeChecker.Tc.fst"
let e = (
# 477 "FStar.TypeChecker.Tc.fst"
let _72_725 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _72_725.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _72_725.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _72_725.FStar_Syntax_Syntax.vars})
in (
# 478 "FStar.TypeChecker.Tc.fst"
let _72_728 = (check_smt_pat env e bs c)
in (
# 479 "FStar.TypeChecker.Tc.fst"
let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (
# 480 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 481 "FStar.TypeChecker.Tc.fst"
let g = (let _151_342 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _151_342))
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
let _72_744 = (let _151_344 = (let _151_343 = (FStar_Syntax_Syntax.mk_binder x)
in (_151_343)::[])
in (FStar_Syntax_Subst.open_term _151_344 phi))
in (match (_72_744) with
| (x, phi) -> begin
(
# 492 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 493 "FStar.TypeChecker.Tc.fst"
let _72_749 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_72_749) with
| (env, _72_748) -> begin
(
# 494 "FStar.TypeChecker.Tc.fst"
let _72_754 = (let _151_345 = (FStar_List.hd x)
in (tc_binder env _151_345))
in (match (_72_754) with
| (x, env, f1, u) -> begin
(
# 495 "FStar.TypeChecker.Tc.fst"
let _72_755 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_348 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _151_347 = (FStar_Syntax_Print.term_to_string phi)
in (let _151_346 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _151_348 _151_347 _151_346))))
end else begin
()
end
in (
# 498 "FStar.TypeChecker.Tc.fst"
let _72_760 = (FStar_Syntax_Util.type_u ())
in (match (_72_760) with
| (t_phi, _72_759) -> begin
(
# 499 "FStar.TypeChecker.Tc.fst"
let _72_765 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_72_765) with
| (phi, _72_763, f2) -> begin
(
# 500 "FStar.TypeChecker.Tc.fst"
let e = (
# 500 "FStar.TypeChecker.Tc.fst"
let _72_766 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _72_766.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _72_766.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _72_766.FStar_Syntax_Syntax.vars})
in (
# 501 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 502 "FStar.TypeChecker.Tc.fst"
let g = (let _151_349 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _151_349))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _72_774) -> begin
(
# 506 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (
# 507 "FStar.TypeChecker.Tc.fst"
let _72_780 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_350 = (FStar_Syntax_Print.term_to_string (
# 508 "FStar.TypeChecker.Tc.fst"
let _72_778 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _72_778.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _72_778.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _72_778.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _151_350))
end else begin
()
end
in (
# 509 "FStar.TypeChecker.Tc.fst"
let _72_784 = (FStar_Syntax_Subst.open_term bs body)
in (match (_72_784) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _72_786 -> begin
(let _151_352 = (let _151_351 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _151_351))
in (FStar_All.failwith _151_352))
end)))))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 523 "FStar.TypeChecker.Tc.fst"
let _72_793 = (FStar_Syntax_Util.type_u ())
in (match (_72_793) with
| (k, u) -> begin
(
# 524 "FStar.TypeChecker.Tc.fst"
let _72_798 = (tc_check_tot_or_gtot_term env t k)
in (match (_72_798) with
| (t, _72_796, g) -> begin
(let _151_355 = (FStar_Syntax_Syntax.mk_Total t)
in (_151_355, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 528 "FStar.TypeChecker.Tc.fst"
let _72_803 = (FStar_Syntax_Util.type_u ())
in (match (_72_803) with
| (k, u) -> begin
(
# 529 "FStar.TypeChecker.Tc.fst"
let _72_808 = (tc_check_tot_or_gtot_term env t k)
in (match (_72_808) with
| (t, _72_806, g) -> begin
(let _151_356 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_151_356, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 533 "FStar.TypeChecker.Tc.fst"
let kc = (FStar_TypeChecker_Env.lookup_effect_lid env c.FStar_Syntax_Syntax.effect_name)
in (
# 534 "FStar.TypeChecker.Tc.fst"
let _72_812 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_358 = (FStar_Syntax_Print.lid_to_string c.FStar_Syntax_Syntax.effect_name)
in (let _151_357 = (FStar_Syntax_Print.term_to_string kc)
in (FStar_Util.print2 "Type of effect %s is %s\n" _151_358 _151_357)))
end else begin
()
end
in (
# 535 "FStar.TypeChecker.Tc.fst"
let head = (FStar_Syntax_Syntax.fvar None c.FStar_Syntax_Syntax.effect_name (FStar_Ident.range_of_lid c.FStar_Syntax_Syntax.effect_name))
in (
# 536 "FStar.TypeChecker.Tc.fst"
let tc = (let _151_360 = (let _151_359 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_151_359)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _151_360 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 537 "FStar.TypeChecker.Tc.fst"
let _72_820 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_72_820) with
| (tc, _72_818, f) -> begin
(
# 538 "FStar.TypeChecker.Tc.fst"
let _72_824 = (FStar_Syntax_Util.head_and_args tc)
in (match (_72_824) with
| (_72_822, args) -> begin
(
# 539 "FStar.TypeChecker.Tc.fst"
let _72_827 = (let _151_362 = (FStar_List.hd args)
in (let _151_361 = (FStar_List.tl args)
in (_151_362, _151_361)))
in (match (_72_827) with
| (res, args) -> begin
(
# 540 "FStar.TypeChecker.Tc.fst"
let _72_843 = (let _151_364 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _72_5 -> (match (_72_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(
# 542 "FStar.TypeChecker.Tc.fst"
let _72_834 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_72_834) with
| (env, _72_833) -> begin
(
# 543 "FStar.TypeChecker.Tc.fst"
let _72_839 = (tc_tot_or_gtot_term env e)
in (match (_72_839) with
| (e, _72_837, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _151_364 FStar_List.unzip))
in (match (_72_843) with
| (flags, guards) -> begin
(
# 546 "FStar.TypeChecker.Tc.fst"
let u = (match ((FStar_TypeChecker_Recheck.check (Prims.fst res))) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type (u); FStar_Syntax_Syntax.tk = _72_849; FStar_Syntax_Syntax.pos = _72_847; FStar_Syntax_Syntax.vars = _72_845} -> begin
u
end
| _72_854 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _151_366 = (FStar_Syntax_Syntax.mk_Comp (
# 549 "FStar.TypeChecker.Tc.fst"
let _72_856 = c
in {FStar_Syntax_Syntax.effect_name = _72_856.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _72_856.FStar_Syntax_Syntax.flags}))
in (let _151_365 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_151_366, u, _151_365))))
end))
end))
end))
end))))))
end))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (
# 556 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun u -> (
# 557 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_72_864) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _151_371 = (aux u)
in FStar_Syntax_Syntax.U_succ (_151_371))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _151_372 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_151_372))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _151_376 = (let _151_375 = (let _151_374 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _151_373 = (FStar_TypeChecker_Env.get_range env)
in (_151_374, _151_373)))
in FStar_Syntax_Syntax.Error (_151_375))
in (Prims.raise _151_376))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _151_377 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_377 Prims.snd))
end
| _72_879 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (
# 579 "FStar.TypeChecker.Tc.fst"
let fail = (fun msg t -> (let _151_386 = (let _151_385 = (let _151_384 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_151_384, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_151_385))
in (Prims.raise _151_386)))
in (
# 588 "FStar.TypeChecker.Tc.fst"
let check_binders = (fun env bs bs_expected -> (
# 593 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun _72_897 bs bs_expected -> (match (_72_897) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| ((hd, imp)::bs, (hd_expected, imp')::bs_expected) -> begin
(
# 597 "FStar.TypeChecker.Tc.fst"
let _72_924 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit))) | ((Some (FStar_Syntax_Syntax.Implicit), None)) -> begin
(let _151_403 = (let _151_402 = (let _151_401 = (let _151_399 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _151_399))
in (let _151_400 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_151_401, _151_400)))
in FStar_Syntax_Syntax.Error (_151_402))
in (Prims.raise _151_403))
end
| _72_923 -> begin
()
end)
in (
# 604 "FStar.TypeChecker.Tc.fst"
let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (
# 605 "FStar.TypeChecker.Tc.fst"
let _72_941 = (match ((let _151_404 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _151_404.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _72_929 -> begin
(
# 608 "FStar.TypeChecker.Tc.fst"
let _72_930 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_405 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _151_405))
end else begin
()
end
in (
# 609 "FStar.TypeChecker.Tc.fst"
let _72_936 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_72_936) with
| (t, _72_934, g1) -> begin
(
# 610 "FStar.TypeChecker.Tc.fst"
let g2 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (
# 611 "FStar.TypeChecker.Tc.fst"
let g = (let _151_406 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _151_406))
in (t, g)))
end)))
end)
in (match (_72_941) with
| (t, g) -> begin
(
# 613 "FStar.TypeChecker.Tc.fst"
let hd = (
# 613 "FStar.TypeChecker.Tc.fst"
let _72_942 = hd
in {FStar_Syntax_Syntax.ppname = _72_942.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _72_942.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 614 "FStar.TypeChecker.Tc.fst"
let b = (hd, imp)
in (
# 615 "FStar.TypeChecker.Tc.fst"
let b_expected = (hd_expected, imp')
in (
# 616 "FStar.TypeChecker.Tc.fst"
let env = (maybe_push_binding env b)
in (
# 617 "FStar.TypeChecker.Tc.fst"
let subst = (let _151_407 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _151_407))
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
# 627 "FStar.TypeChecker.Tc.fst"
let rec expected_function_typ = (fun env t0 -> (match (t0) with
| None -> begin
(
# 637 "FStar.TypeChecker.Tc.fst"
let _72_962 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _72_961 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (
# 638 "FStar.TypeChecker.Tc.fst"
let _72_969 = (tc_binders env bs)
in (match (_72_969) with
| (bs, envbody, g, _72_968) -> begin
(None, bs, [], None, envbody, g)
end)))
end
| Some (t) -> begin
(
# 642 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 643 "FStar.TypeChecker.Tc.fst"
let rec as_function_typ = (fun norm t -> (match ((let _151_416 = (FStar_Syntax_Subst.compress t)
in _151_416.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 647 "FStar.TypeChecker.Tc.fst"
let _72_996 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _72_995 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 648 "FStar.TypeChecker.Tc.fst"
let _72_1003 = (tc_binders env bs)
in (match (_72_1003) with
| (bs, envbody, g, _72_1002) -> begin
(
# 649 "FStar.TypeChecker.Tc.fst"
let _72_1007 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_72_1007) with
| (envbody, _72_1006) -> begin
(Some ((t, true)), bs, [], None, envbody, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _72_1010) -> begin
(
# 655 "FStar.TypeChecker.Tc.fst"
let _72_1020 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_72_1020) with
| (_72_1014, bs, bs', copt, env, g) -> begin
(Some ((t, false)), bs, bs', copt, env, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 659 "FStar.TypeChecker.Tc.fst"
let _72_1027 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_72_1027) with
| (bs_expected, c_expected) -> begin
(
# 666 "FStar.TypeChecker.Tc.fst"
let check_actuals_against_formals = (fun env bs bs_expected -> (
# 667 "FStar.TypeChecker.Tc.fst"
let rec handle_more = (fun _72_1038 c_expected -> (match (_72_1038) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _151_427 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _151_427))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(
# 672 "FStar.TypeChecker.Tc.fst"
let c = (let _151_428 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _151_428))
in (let _151_429 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _151_429)))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(
# 676 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.subst_comp subst c_expected)
in if (FStar_Syntax_Util.is_total_comp c) then begin
(
# 679 "FStar.TypeChecker.Tc.fst"
let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 682 "FStar.TypeChecker.Tc.fst"
let _72_1059 = (check_binders env more_bs bs_expected)
in (match (_72_1059) with
| (env, bs', more, guard', subst) -> begin
(let _151_431 = (let _151_430 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _151_430, subst))
in (handle_more _151_431 c_expected))
end))
end
| _72_1061 -> begin
(let _151_433 = (let _151_432 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _151_432))
in (fail _151_433 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _151_434 = (check_binders env bs bs_expected)
in (handle_more _151_434 c_expected))))
in (
# 689 "FStar.TypeChecker.Tc.fst"
let mk_letrec_env = (fun envbody bs c -> (
# 690 "FStar.TypeChecker.Tc.fst"
let letrecs = (guard_letrecs envbody bs c)
in (
# 691 "FStar.TypeChecker.Tc.fst"
let envbody = (
# 691 "FStar.TypeChecker.Tc.fst"
let _72_1067 = envbody
in {FStar_TypeChecker_Env.solver = _72_1067.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _72_1067.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _72_1067.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _72_1067.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _72_1067.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _72_1067.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _72_1067.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _72_1067.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _72_1067.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _72_1067.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _72_1067.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _72_1067.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _72_1067.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _72_1067.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _72_1067.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _72_1067.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _72_1067.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _72_1067.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _72_1067.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _72_1067.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _72_1072 _72_1075 -> (match ((_72_1072, _72_1075)) with
| ((env, letrec_binders), (l, t)) -> begin
(
# 693 "FStar.TypeChecker.Tc.fst"
let _72_1081 = (let _151_444 = (let _151_443 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _151_443 Prims.fst))
in (tc_term _151_444 t))
in (match (_72_1081) with
| (t, _72_1078, _72_1080) -> begin
(
# 694 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (
# 695 "FStar.TypeChecker.Tc.fst"
let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _151_445 = (FStar_Syntax_Syntax.mk_binder (
# 696 "FStar.TypeChecker.Tc.fst"
let _72_1085 = x
in {FStar_Syntax_Syntax.ppname = _72_1085.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _72_1085.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_151_445)::letrec_binders)
end
| _72_1088 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (
# 701 "FStar.TypeChecker.Tc.fst"
let _72_1094 = (check_actuals_against_formals env bs bs_expected)
in (match (_72_1094) with
| (envbody, bs, g, c) -> begin
(
# 702 "FStar.TypeChecker.Tc.fst"
let _72_1097 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_72_1097) with
| (envbody, letrecs) -> begin
(
# 703 "FStar.TypeChecker.Tc.fst"
let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, g))
end))
end))))
end))
end
| _72_1100 -> begin
if (not (norm)) then begin
(let _151_446 = (unfold_whnf env t)
in (as_function_typ true _151_446))
end else begin
(
# 711 "FStar.TypeChecker.Tc.fst"
let _72_1109 = (expected_function_typ env None)
in (match (_72_1109) with
| (_72_1102, bs, _72_1105, c_opt, envbody, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (
# 715 "FStar.TypeChecker.Tc.fst"
let use_eq = env.FStar_TypeChecker_Env.use_eq
in (
# 716 "FStar.TypeChecker.Tc.fst"
let _72_1113 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_72_1113) with
| (env, topt) -> begin
(
# 717 "FStar.TypeChecker.Tc.fst"
let _72_1117 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_447 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _151_447 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (
# 721 "FStar.TypeChecker.Tc.fst"
let _72_1125 = (expected_function_typ env topt)
in (match (_72_1125) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, g) -> begin
(
# 722 "FStar.TypeChecker.Tc.fst"
let _72_1131 = (tc_term (
# 722 "FStar.TypeChecker.Tc.fst"
let _72_1126 = envbody
in {FStar_TypeChecker_Env.solver = _72_1126.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _72_1126.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _72_1126.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _72_1126.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _72_1126.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _72_1126.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _72_1126.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _72_1126.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _72_1126.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _72_1126.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _72_1126.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _72_1126.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _72_1126.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _72_1126.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _72_1126.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _72_1126.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _72_1126.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _72_1126.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _72_1126.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_72_1131) with
| (body, cbody, guard_body) -> begin
(
# 723 "FStar.TypeChecker.Tc.fst"
let _72_1132 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_453 = (FStar_Syntax_Print.term_to_string body)
in (let _151_452 = (let _151_448 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _151_448))
in (let _151_451 = (FStar_TypeChecker_Rel.guard_to_string env guard_body)
in (let _151_450 = (let _151_449 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _151_449))
in (FStar_Util.print4 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\nAgain cbody=%s\n" _151_453 _151_452 _151_451 _151_450)))))
end else begin
()
end
in (
# 727 "FStar.TypeChecker.Tc.fst"
let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (
# 729 "FStar.TypeChecker.Tc.fst"
let _72_1135 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _151_456 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _151_455 = (let _151_454 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _151_454))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _151_456 _151_455)))
end else begin
()
end
in (
# 733 "FStar.TypeChecker.Tc.fst"
let _72_1142 = (let _151_458 = (let _151_457 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _151_457))
in (check_expected_effect (
# 733 "FStar.TypeChecker.Tc.fst"
let _72_1137 = envbody
in {FStar_TypeChecker_Env.solver = _72_1137.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _72_1137.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _72_1137.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _72_1137.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _72_1137.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _72_1137.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _72_1137.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _72_1137.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _72_1137.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _72_1137.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _72_1137.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _72_1137.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _72_1137.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _72_1137.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _72_1137.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _72_1137.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _72_1137.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _72_1137.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _72_1137.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _72_1137.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _151_458))
in (match (_72_1142) with
| (body, cbody, guard) -> begin
(
# 734 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (
# 735 "FStar.TypeChecker.Tc.fst"
let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _151_459 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _151_459))
end else begin
(
# 737 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (
# 740 "FStar.TypeChecker.Tc.fst"
let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (
# 741 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.abs bs body (Some ((FStar_Syntax_Util.lcomp_of_comp cbody))))
in (
# 742 "FStar.TypeChecker.Tc.fst"
let _72_1165 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(
# 744 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_72_1154) -> begin
(e, t, guard)
end
| _72_1157 -> begin
(
# 753 "FStar.TypeChecker.Tc.fst"
let _72_1160 = if use_teq then begin
(let _151_460 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _151_460))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_72_1160) with
| (e, guard') -> begin
(let _151_461 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _151_461))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_72_1165) with
| (e, tfun, guard) -> begin
(
# 763 "FStar.TypeChecker.Tc.fst"
let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (
# 764 "FStar.TypeChecker.Tc.fst"
let _72_1169 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_72_1169) with
| (c, g) -> begin
(e, c, g)
end)))
end))))))
end)))))
end))
end)))
end)))))))
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead ghead args expected_topt -> (
# 772 "FStar.TypeChecker.Tc.fst"
let n_args = (FStar_List.length args)
in (
# 773 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 774 "FStar.TypeChecker.Tc.fst"
let thead = chead.FStar_Syntax_Syntax.res_typ
in (
# 775 "FStar.TypeChecker.Tc.fst"
let _72_1179 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_470 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _151_469 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _151_470 _151_469)))
end else begin
()
end
in (
# 776 "FStar.TypeChecker.Tc.fst"
let rec check_function_app = (fun norm tf -> (match ((let _151_475 = (FStar_Syntax_Util.unrefine tf)
in _151_475.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 780 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| (e, imp)::tl -> begin
(
# 783 "FStar.TypeChecker.Tc.fst"
let _72_1213 = (tc_term env e)
in (match (_72_1213) with
| (e, c, g_e) -> begin
(
# 784 "FStar.TypeChecker.Tc.fst"
let _72_1217 = (tc_args env tl)
in (match (_72_1217) with
| (args, comps, g_rest) -> begin
(let _151_480 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, (c)::comps, _151_480))
end))
end))
end))
in (
# 792 "FStar.TypeChecker.Tc.fst"
let _72_1221 = (tc_args env args)
in (match (_72_1221) with
| (args, comps, g_args) -> begin
(
# 793 "FStar.TypeChecker.Tc.fst"
let bs = (let _151_482 = (FStar_All.pipe_right comps (FStar_List.map (fun c -> (c.FStar_Syntax_Syntax.res_typ, None))))
in (FStar_Syntax_Util.null_binders_of_tks _151_482))
in (
# 794 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _72_1228 -> begin
FStar_Syntax_Util.ml_comp
end)
in (
# 797 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _151_497 = (FStar_Syntax_Subst.compress t)
in _151_497.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_72_1234) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _72_1239 -> begin
ml_or_tot
end)
end)
in (
# 804 "FStar.TypeChecker.Tc.fst"
let cres = (let _151_502 = (let _151_501 = (let _151_500 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_500 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _151_501))
in (ml_or_tot _151_502 r))
in (
# 805 "FStar.TypeChecker.Tc.fst"
let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (
# 806 "FStar.TypeChecker.Tc.fst"
let _72_1243 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _151_505 = (FStar_Syntax_Print.term_to_string head)
in (let _151_504 = (FStar_Syntax_Print.term_to_string tf)
in (let _151_503 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _151_505 _151_504 _151_503))))
end else begin
()
end
in (
# 811 "FStar.TypeChecker.Tc.fst"
let _72_1245 = (let _151_506 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _151_506))
in (
# 812 "FStar.TypeChecker.Tc.fst"
let comp = (let _151_509 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_TypeChecker_Util.bind env None c (None, out))) ((chead)::comps) _151_509))
in (let _151_511 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _151_510 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_151_511, comp, _151_510)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 816 "FStar.TypeChecker.Tc.fst"
let _72_1256 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_72_1256) with
| (bs, c) -> begin
(
# 818 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun _72_1264 bs cres args -> (match (_72_1264) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((x, Some (FStar_Syntax_Syntax.Implicit))::rest, (_72_1277, None)::_72_1275) -> begin
(
# 829 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 830 "FStar.TypeChecker.Tc.fst"
let _72_1283 = (fxv_check head env t fvs)
in (
# 831 "FStar.TypeChecker.Tc.fst"
let _72_1288 = (FStar_TypeChecker_Util.new_implicit_var env t)
in (match (_72_1288) with
| (varg, u, implicits) -> begin
(
# 832 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (
# 833 "FStar.TypeChecker.Tc.fst"
let arg = (let _151_546 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _151_546))
in (let _151_552 = (let _151_551 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _151_551, fvs))
in (tc_args _151_552 rest cres args))))
end))))
end
| ((x, aqual)::rest, (e, aq)::rest') -> begin
(
# 837 "FStar.TypeChecker.Tc.fst"
let _72_1316 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit), Some (FStar_Syntax_Syntax.Implicit))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _72_1315 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (
# 842 "FStar.TypeChecker.Tc.fst"
let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 843 "FStar.TypeChecker.Tc.fst"
let x = (
# 843 "FStar.TypeChecker.Tc.fst"
let _72_1319 = x
in {FStar_Syntax_Syntax.ppname = _72_1319.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _72_1319.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (
# 844 "FStar.TypeChecker.Tc.fst"
let _72_1322 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _151_553 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _151_553))
end else begin
()
end
in (
# 845 "FStar.TypeChecker.Tc.fst"
let _72_1324 = (fxv_check head env targ fvs)
in (
# 846 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (
# 847 "FStar.TypeChecker.Tc.fst"
let env = (
# 847 "FStar.TypeChecker.Tc.fst"
let _72_1327 = env
in {FStar_TypeChecker_Env.solver = _72_1327.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _72_1327.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _72_1327.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _72_1327.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _72_1327.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _72_1327.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _72_1327.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _72_1327.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _72_1327.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _72_1327.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _72_1327.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _72_1327.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _72_1327.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _72_1327.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _72_1327.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _72_1327.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _72_1327.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _72_1327.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _72_1327.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _72_1327.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 848 "FStar.TypeChecker.Tc.fst"
let _72_1330 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_556 = (FStar_Syntax_Print.tag_of_term e)
in (let _151_555 = (FStar_Syntax_Print.term_to_string e)
in (let _151_554 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _151_556 _151_555 _151_554))))
end else begin
()
end
in (
# 849 "FStar.TypeChecker.Tc.fst"
let _72_1335 = (tc_term env e)
in (match (_72_1335) with
| (e, c, g_e) -> begin
(
# 850 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (
# 852 "FStar.TypeChecker.Tc.fst"
let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(
# 854 "FStar.TypeChecker.Tc.fst"
let subst = (let _151_557 = (FStar_List.hd bs)
in (maybe_extend_subst subst _151_557 e))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(
# 857 "FStar.TypeChecker.Tc.fst"
let subst = (let _151_562 = (FStar_List.hd bs)
in (maybe_extend_subst subst _151_562 e))
in (
# 858 "FStar.TypeChecker.Tc.fst"
let _72_1342 = (((Some (x), c))::comps, g)
in (match (_72_1342) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _151_567 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _151_567)) then begin
(
# 862 "FStar.TypeChecker.Tc.fst"
let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (
# 863 "FStar.TypeChecker.Tc.fst"
let arg' = (let _151_568 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _151_568))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (newx), c))::comps, g, fvs) rest cres rest')))
end else begin
(let _151_577 = (let _151_576 = (let _151_574 = (let _151_573 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _151_573))
in (_151_574)::arg_rets)
in (let _151_575 = (FStar_Util.set_add x fvs)
in (subst, (arg)::outargs, _151_576, ((Some (x), c))::comps, g, _151_575)))
in (tc_args _151_577 rest cres rest'))
end
end
end))
end))))))))))
end
| (_72_1346, []) -> begin
(
# 872 "FStar.TypeChecker.Tc.fst"
let _72_1349 = (fxv_check head env cres.FStar_Syntax_Syntax.res_typ fvs)
in (
# 873 "FStar.TypeChecker.Tc.fst"
let _72_1367 = (match (bs) with
| [] -> begin
(
# 876 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (
# 882 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (
# 884 "FStar.TypeChecker.Tc.fst"
let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _72_1357 -> (match (_72_1357) with
| (_72_1355, c) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (
# 891 "FStar.TypeChecker.Tc.fst"
let cres = if refine_with_equality then begin
(let _151_579 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _151_579 cres))
end else begin
(
# 897 "FStar.TypeChecker.Tc.fst"
let _72_1359 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_582 = (FStar_Syntax_Print.term_to_string head)
in (let _151_581 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _151_580 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _151_582 _151_581 _151_580))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _72_1363 -> begin
(
# 906 "FStar.TypeChecker.Tc.fst"
let g = (let _151_583 = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (FStar_All.pipe_right _151_583 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _151_588 = (let _151_587 = (let _151_586 = (let _151_585 = (let _151_584 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _151_584))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _151_585))
in (FStar_Syntax_Syntax.mk_Total _151_586))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_587))
in (_151_588, g)))
end)
in (match (_72_1367) with
| (cres, g) -> begin
(
# 909 "FStar.TypeChecker.Tc.fst"
let _72_1368 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_589 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _151_589))
end else begin
()
end
in (
# 910 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_List.fold_left (fun out c -> (FStar_TypeChecker_Util.bind env None (Prims.snd c) ((Prims.fst c), out))) cres comps)
in (
# 911 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.bind env None chead (None, comp))
in (
# 912 "FStar.TypeChecker.Tc.fst"
let app = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev outargs) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (
# 913 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.record_application_site env app comp)
in (
# 914 "FStar.TypeChecker.Tc.fst"
let _72_1378 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp g)
in (match (_72_1378) with
| (comp, g) -> begin
(
# 915 "FStar.TypeChecker.Tc.fst"
let _72_1379 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_595 = (FStar_TypeChecker_Normalize.term_to_string env app)
in (let _151_594 = (let _151_593 = (comp.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Print.comp_to_string _151_593))
in (FStar_Util.print2 "\t Type of app term %s is %s\n" _151_595 _151_594)))
end else begin
()
end
in (app, comp, g))
end)))))))
end)))
end
| ([], arg::_72_1383) -> begin
(
# 921 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun norm tres -> (
# 922 "FStar.TypeChecker.Tc.fst"
let tres = (let _151_600 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _151_600 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(
# 925 "FStar.TypeChecker.Tc.fst"
let _72_1395 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_601 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _151_601))
end else begin
()
end
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs (FStar_Syntax_Util.lcomp_of_comp cres') args))
end
| _72_1398 when (not (norm)) -> begin
(let _151_606 = (unfold_whnf env tres)
in (aux true _151_606))
end
| _72_1400 -> begin
(let _151_612 = (let _151_611 = (let _151_610 = (let _151_608 = (FStar_TypeChecker_Normalize.term_to_string env tf)
in (let _151_607 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _151_608 _151_607)))
in (let _151_609 = (FStar_Syntax_Syntax.argpos arg)
in (_151_610, _151_609)))
in FStar_Syntax_Syntax.Error (_151_611))
in (Prims.raise _151_612))
end)))
in (aux false cres.FStar_Syntax_Syntax.res_typ))
end)
end))
in (let _151_614 = (let _151_613 = (FStar_Syntax_Syntax.new_bv_set ())
in ([], [], [], [], FStar_TypeChecker_Rel.trivial_guard, _151_613))
in (tc_args _151_614 bs (FStar_Syntax_Util.lcomp_of_comp c) args)))
end))
end
| _72_1402 -> begin
if (not (norm)) then begin
(let _151_615 = (unfold_whnf env tf)
in (check_function_app true _151_615))
end else begin
(let _151_618 = (let _151_617 = (let _151_616 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_151_616, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_151_617))
in (Prims.raise _151_618))
end
end))
in (let _151_620 = (let _151_619 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _151_619))
in (check_function_app false _151_620))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (
# 951 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 952 "FStar.TypeChecker.Tc.fst"
let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(
# 955 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in (
# 956 "FStar.TypeChecker.Tc.fst"
let _72_1438 = (FStar_List.fold_left2 (fun _72_1419 _72_1422 _72_1425 -> (match ((_72_1419, _72_1422, _72_1425)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(
# 957 "FStar.TypeChecker.Tc.fst"
let _72_1426 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 958 "FStar.TypeChecker.Tc.fst"
let _72_1431 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_72_1431) with
| (e, c, g) -> begin
(
# 959 "FStar.TypeChecker.Tc.fst"
let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (
# 960 "FStar.TypeChecker.Tc.fst"
let g = (let _151_630 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _151_630 g))
in (
# 961 "FStar.TypeChecker.Tc.fst"
let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _151_634 = (let _151_632 = (let _151_631 = (FStar_Syntax_Syntax.as_arg e)
in (_151_631)::[])
in (FStar_List.append seen _151_632))
in (let _151_633 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_151_634, _151_633, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_72_1438) with
| (args, guard, ghost) -> begin
(
# 965 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (
# 966 "FStar.TypeChecker.Tc.fst"
let c = if ghost then begin
(let _151_635 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _151_635 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (
# 967 "FStar.TypeChecker.Tc.fst"
let _72_1443 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_72_1443) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _72_1445 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (
# 987 "FStar.TypeChecker.Tc.fst"
let _72_1452 = (FStar_Syntax_Subst.open_branch branch)
in (match (_72_1452) with
| (pattern, when_clause, branch_exp) -> begin
(
# 988 "FStar.TypeChecker.Tc.fst"
let _72_1457 = branch
in (match (_72_1457) with
| (cpat, _72_1455, cbr) -> begin
(
# 991 "FStar.TypeChecker.Tc.fst"
let tc_pat = (fun allow_implicits pat_t p0 -> (
# 998 "FStar.TypeChecker.Tc.fst"
let _72_1465 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_72_1465) with
| (pat_bvs, exps, p) -> begin
(
# 999 "FStar.TypeChecker.Tc.fst"
let _72_1466 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_647 = (FStar_Syntax_Print.pat_to_string p0)
in (let _151_646 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _151_647 _151_646)))
end else begin
()
end
in (
# 1001 "FStar.TypeChecker.Tc.fst"
let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (
# 1002 "FStar.TypeChecker.Tc.fst"
let _72_1472 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_72_1472) with
| (env1, _72_1471) -> begin
(
# 1003 "FStar.TypeChecker.Tc.fst"
let env1 = (
# 1003 "FStar.TypeChecker.Tc.fst"
let _72_1473 = env1
in {FStar_TypeChecker_Env.solver = _72_1473.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _72_1473.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _72_1473.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _72_1473.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _72_1473.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _72_1473.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _72_1473.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _72_1473.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _72_1473.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _72_1473.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _72_1473.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _72_1473.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _72_1473.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _72_1473.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _72_1473.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _72_1473.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _72_1473.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _72_1473.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _72_1473.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _72_1473.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1004 "FStar.TypeChecker.Tc.fst"
let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (
# 1005 "FStar.TypeChecker.Tc.fst"
let _72_1512 = (let _151_670 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (
# 1006 "FStar.TypeChecker.Tc.fst"
let _72_1478 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_650 = (FStar_Syntax_Print.term_to_string e)
in (let _151_649 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _151_650 _151_649)))
end else begin
()
end
in (
# 1009 "FStar.TypeChecker.Tc.fst"
let _72_1483 = (tc_term env1 e)
in (match (_72_1483) with
| (e, lc, g) -> begin
(
# 1011 "FStar.TypeChecker.Tc.fst"
let _72_1484 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_652 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _151_651 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _151_652 _151_651)))
end else begin
()
end
in (
# 1014 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (
# 1015 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (
# 1016 "FStar.TypeChecker.Tc.fst"
let _72_1490 = (let _151_653 = (FStar_TypeChecker_Rel.discharge_guard env (
# 1016 "FStar.TypeChecker.Tc.fst"
let _72_1488 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _72_1488.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _72_1488.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _72_1488.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _151_653 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1017 "FStar.TypeChecker.Tc.fst"
let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (
# 1018 "FStar.TypeChecker.Tc.fst"
let uvars_to_string = (fun uvs -> (let _151_658 = (let _151_657 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _151_657 (FStar_List.map (fun _72_1498 -> (match (_72_1498) with
| (u, _72_1497) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _151_658 (FStar_String.concat ", "))))
in (
# 1019 "FStar.TypeChecker.Tc.fst"
let uvs1 = (FStar_Syntax_Free.uvars e')
in (
# 1020 "FStar.TypeChecker.Tc.fst"
let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (
# 1021 "FStar.TypeChecker.Tc.fst"
let _72_1506 = if (let _151_659 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _151_659)) then begin
(
# 1022 "FStar.TypeChecker.Tc.fst"
let unresolved = (let _151_660 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _151_660 FStar_Util.set_elements))
in (let _151_668 = (let _151_667 = (let _151_666 = (let _151_665 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _151_664 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _151_663 = (let _151_662 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _72_1505 -> (match (_72_1505) with
| (u, _72_1504) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _151_662 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _151_665 _151_664 _151_663))))
in (_151_666, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_151_667))
in (Prims.raise _151_668)))
end else begin
()
end
in (
# 1029 "FStar.TypeChecker.Tc.fst"
let _72_1508 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_669 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _151_669))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _151_670 FStar_List.unzip))
in (match (_72_1512) with
| (exps, norm_exps) -> begin
(
# 1034 "FStar.TypeChecker.Tc.fst"
let p = (FStar_TypeChecker_Util.decorate_pattern env p exps)
in (p, pat_bvs, pat_env, exps, norm_exps))
end))))
end))))
end)))
in (
# 1038 "FStar.TypeChecker.Tc.fst"
let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (
# 1039 "FStar.TypeChecker.Tc.fst"
let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (
# 1040 "FStar.TypeChecker.Tc.fst"
let _72_1519 = (let _151_671 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _151_671 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_72_1519) with
| (scrutinee_env, _72_1518) -> begin
(
# 1043 "FStar.TypeChecker.Tc.fst"
let _72_1525 = (tc_pat true pat_t pattern)
in (match (_72_1525) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(
# 1046 "FStar.TypeChecker.Tc.fst"
let _72_1535 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(
# 1053 "FStar.TypeChecker.Tc.fst"
let _72_1532 = (let _151_672 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Recheck.t_bool)
in (tc_term _151_672 e))
in (match (_72_1532) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_72_1535) with
| (when_clause, g_when) -> begin
(
# 1057 "FStar.TypeChecker.Tc.fst"
let _72_1539 = (tc_term pat_env branch_exp)
in (match (_72_1539) with
| (branch_exp, c, g_branch) -> begin
(
# 1061 "FStar.TypeChecker.Tc.fst"
let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _151_674 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _151_673 -> Some (_151_673)) _151_674))
end)
in (
# 1068 "FStar.TypeChecker.Tc.fst"
let _72_1595 = (
# 1071 "FStar.TypeChecker.Tc.fst"
let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (
# 1072 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _72_1557 -> begin
(
# 1078 "FStar.TypeChecker.Tc.fst"
let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _151_678 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _151_677 -> Some (_151_677)) _151_678))
end))
end))) None))
in (
# 1083 "FStar.TypeChecker.Tc.fst"
let _72_1565 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_72_1565) with
| (c, g_branch) -> begin
(
# 1087 "FStar.TypeChecker.Tc.fst"
let _72_1590 = (match ((eqs, when_condition)) with
| (None, None) -> begin
(c, g_when)
end
| (Some (f), None) -> begin
(
# 1093 "FStar.TypeChecker.Tc.fst"
let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1094 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _151_681 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _151_680 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_151_681, _151_680)))))
end
| (Some (f), Some (w)) -> begin
(
# 1099 "FStar.TypeChecker.Tc.fst"
let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1100 "FStar.TypeChecker.Tc.fst"
let g_fw = (let _151_682 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_151_682))
in (let _151_685 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _151_684 = (let _151_683 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _151_683 g_when))
in (_151_685, _151_684)))))
end
| (None, Some (w)) -> begin
(
# 1105 "FStar.TypeChecker.Tc.fst"
let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (
# 1106 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _151_686 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_151_686, g_when))))
end)
in (match (_72_1590) with
| (c_weak, g_when_weak) -> begin
(
# 1111 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _151_688 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _151_687 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_151_688, _151_687, g_branch))))
end))
end)))
in (match (_72_1595) with
| (c, g_when, g_branch) -> begin
(
# 1129 "FStar.TypeChecker.Tc.fst"
let branch_guard = (
# 1131 "FStar.TypeChecker.Tc.fst"
let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (
# 1132 "FStar.TypeChecker.Tc.fst"
let discriminate = (fun scrutinee_tm f -> if ((let _151_698 = (let _151_697 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _151_697))
in (FStar_List.length _151_698)) > 1) then begin
(
# 1135 "FStar.TypeChecker.Tc.fst"
let disc = (let _151_699 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar None _151_699 (FStar_Ident.range_of_lid f.FStar_Syntax_Syntax.v)))
in (
# 1136 "FStar.TypeChecker.Tc.fst"
let disc = (let _151_701 = (let _151_700 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_151_700)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _151_701 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _151_702 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_151_702)::[])))
end else begin
[]
end)
in (
# 1140 "FStar.TypeChecker.Tc.fst"
let fail = (fun _72_1605 -> (match (()) with
| () -> begin
(let _151_708 = (let _151_707 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _151_706 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _151_705 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _151_707 _151_706 _151_705))))
in (FStar_All.failwith _151_708))
end))
in (
# 1146 "FStar.TypeChecker.Tc.fst"
let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (f, _72_1610) -> begin
f
end
| FStar_Syntax_Syntax.Tm_uinst (t, _72_1615) -> begin
(head_constructor t)
end
| _72_1619 -> begin
(fail ())
end))
in (
# 1151 "FStar.TypeChecker.Tc.fst"
let pat_exp = (let _151_711 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _151_711 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_72_1644) -> begin
(let _151_716 = (let _151_715 = (let _151_714 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _151_713 = (let _151_712 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_151_712)::[])
in (_151_714)::_151_713))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _151_715 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_151_716)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 1160 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _151_717 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _151_717))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 1165 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(
# 1168 "FStar.TypeChecker.Tc.fst"
let sub_term_guards = (let _151_723 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _72_1662 -> (match (_72_1662) with
| (ei, _72_1661) -> begin
(
# 1169 "FStar.TypeChecker.Tc.fst"
let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (
# 1170 "FStar.TypeChecker.Tc.fst"
let sub_term = (let _151_722 = (FStar_Syntax_Syntax.fvar None projector f.FStar_Syntax_Syntax.p)
in (let _151_721 = (let _151_720 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_151_720)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _151_722 _151_721 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei)))
end))))
in (FStar_All.pipe_right _151_723 FStar_List.flatten))
in (let _151_724 = (discriminate scrutinee_tm f)
in (FStar_List.append _151_724 sub_term_guards)))
end)
end
| _72_1667 -> begin
[]
end))))))
in (
# 1176 "FStar.TypeChecker.Tc.fst"
let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid scrutinee_tm.FStar_Syntax_Syntax.pos)
end else begin
(
# 1179 "FStar.TypeChecker.Tc.fst"
let t = (let _151_729 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _151_729))
in (
# 1180 "FStar.TypeChecker.Tc.fst"
let _72_1675 = (FStar_Syntax_Util.type_u ())
in (match (_72_1675) with
| (k, _72_1674) -> begin
(
# 1181 "FStar.TypeChecker.Tc.fst"
let _72_1681 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_72_1681) with
| (t, _72_1678, _72_1680) -> begin
t
end))
end)))
end)
in (
# 1185 "FStar.TypeChecker.Tc.fst"
let branch_guard = (let _151_730 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _151_730 FStar_Syntax_Util.mk_disj_l))
in (
# 1188 "FStar.TypeChecker.Tc.fst"
let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
in (
# 1194 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (
# 1196 "FStar.TypeChecker.Tc.fst"
let _72_1689 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_731 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _151_731))
end else begin
()
end
in (let _151_732 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_151_732, branch_guard, c, guard)))))
end)))
end))
end))
end))
end)))))
end))
end)))
and check_top_level_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1210 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1213 "FStar.TypeChecker.Tc.fst"
let _72_1706 = (check_let_bound_def true env lb)
in (match (_72_1706) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(
# 1216 "FStar.TypeChecker.Tc.fst"
let _72_1718 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(
# 1219 "FStar.TypeChecker.Tc.fst"
let g1 = (let _151_735 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _151_735 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1220 "FStar.TypeChecker.Tc.fst"
let _72_1713 = (let _151_739 = (let _151_738 = (let _151_737 = (let _151_736 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _151_736))
in (_151_737)::[])
in (FStar_TypeChecker_Util.generalize env _151_738))
in (FStar_List.hd _151_739))
in (match (_72_1713) with
| (_72_1709, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_72_1718) with
| (g1, e1, univ_vars, c1) -> begin
(
# 1224 "FStar.TypeChecker.Tc.fst"
let _72_1728 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(
# 1226 "FStar.TypeChecker.Tc.fst"
let _72_1721 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_72_1721) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(
# 1229 "FStar.TypeChecker.Tc.fst"
let _72_1722 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _151_740 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _151_740 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _151_741 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_151_741, c1)))
end
end))
end else begin
(
# 1233 "FStar.TypeChecker.Tc.fst"
let _72_1724 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _151_742 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _151_742)))
end
in (match (_72_1728) with
| (e2, c1) -> begin
(
# 1238 "FStar.TypeChecker.Tc.fst"
let cres = (let _151_743 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Recheck.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_743))
in (
# 1239 "FStar.TypeChecker.Tc.fst"
let _72_1730 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Recheck.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1241 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _151_744 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Recheck.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_151_744, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _72_1734 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1258 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1261 "FStar.TypeChecker.Tc.fst"
let env = (
# 1261 "FStar.TypeChecker.Tc.fst"
let _72_1745 = env
in {FStar_TypeChecker_Env.solver = _72_1745.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _72_1745.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _72_1745.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _72_1745.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _72_1745.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _72_1745.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _72_1745.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _72_1745.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _72_1745.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _72_1745.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _72_1745.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _72_1745.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _72_1745.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _72_1745.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _72_1745.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _72_1745.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _72_1745.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _72_1745.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _72_1745.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _72_1745.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1262 "FStar.TypeChecker.Tc.fst"
let _72_1754 = (let _151_748 = (let _151_747 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _151_747 Prims.fst))
in (check_let_bound_def false _151_748 lb))
in (match (_72_1754) with
| (e1, _72_1750, c1, g1, annotated) -> begin
(
# 1263 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (
# 1264 "FStar.TypeChecker.Tc.fst"
let x = (
# 1264 "FStar.TypeChecker.Tc.fst"
let _72_1756 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _72_1756.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _72_1756.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (
# 1265 "FStar.TypeChecker.Tc.fst"
let _72_1761 = (let _151_750 = (let _151_749 = (FStar_Syntax_Syntax.mk_binder x)
in (_151_749)::[])
in (FStar_Syntax_Subst.open_term _151_750 e2))
in (match (_72_1761) with
| (xb, e2) -> begin
(
# 1266 "FStar.TypeChecker.Tc.fst"
let xbinder = (FStar_List.hd xb)
in (
# 1267 "FStar.TypeChecker.Tc.fst"
let x = (Prims.fst xbinder)
in (
# 1268 "FStar.TypeChecker.Tc.fst"
let _72_1767 = (let _151_751 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _151_751 e2))
in (match (_72_1767) with
| (e2, c2, g2) -> begin
(
# 1269 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (x), c2))
in (
# 1270 "FStar.TypeChecker.Tc.fst"
let e = (let _151_754 = (let _151_753 = (let _151_752 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _151_752))
in FStar_Syntax_Syntax.Tm_let (_151_753))
in (FStar_Syntax_Syntax.mk _151_754 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 1271 "FStar.TypeChecker.Tc.fst"
let x_eq_e1 = (let _151_757 = (let _151_756 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _151_756 e1))
in (FStar_All.pipe_left (fun _151_755 -> FStar_TypeChecker_Common.NonTrivial (_151_755)) _151_757))
in (
# 1272 "FStar.TypeChecker.Tc.fst"
let g2 = (let _151_759 = (let _151_758 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _151_758 g2))
in (FStar_TypeChecker_Rel.close_guard xb _151_759))
in (
# 1274 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if annotated then begin
(e, cres, guard)
end else begin
(
# 1278 "FStar.TypeChecker.Tc.fst"
let _72_1773 = (check_no_escape env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end)))))
end))))
end))))
end)))
end
| _72_1776 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1287 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1290 "FStar.TypeChecker.Tc.fst"
let _72_1788 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_72_1788) with
| (lbs, e2) -> begin
(
# 1292 "FStar.TypeChecker.Tc.fst"
let _72_1791 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_72_1791) with
| (env0, topt) -> begin
(
# 1293 "FStar.TypeChecker.Tc.fst"
let _72_1794 = (build_let_rec_env true env0 lbs)
in (match (_72_1794) with
| (lbs, rec_env) -> begin
(
# 1294 "FStar.TypeChecker.Tc.fst"
let _72_1797 = (check_let_recs rec_env lbs)
in (match (_72_1797) with
| (lbs, g_lbs) -> begin
(
# 1295 "FStar.TypeChecker.Tc.fst"
let g_lbs = (let _151_762 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _151_762 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1297 "FStar.TypeChecker.Tc.fst"
let all_lb_names = (let _151_765 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _151_765 (fun _151_764 -> Some (_151_764))))
in (
# 1299 "FStar.TypeChecker.Tc.fst"
let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(
# 1305 "FStar.TypeChecker.Tc.fst"
let ecs = (let _151_769 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _151_768 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _151_768)))))
in (FStar_TypeChecker_Util.generalize env _151_769))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _72_1808 -> (match (_72_1808) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (
# 1312 "FStar.TypeChecker.Tc.fst"
let cres = (let _151_771 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Recheck.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_771))
in (
# 1313 "FStar.TypeChecker.Tc.fst"
let _72_1811 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Recheck.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1315 "FStar.TypeChecker.Tc.fst"
let _72_1815 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_72_1815) with
| (lbs, e2) -> begin
(let _151_773 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Recheck.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _151_772 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_151_773, cres, _151_772)))
end)))))))
end))
end))
end))
end))
end
| _72_1817 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1326 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1329 "FStar.TypeChecker.Tc.fst"
let _72_1829 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_72_1829) with
| (lbs, e2) -> begin
(
# 1331 "FStar.TypeChecker.Tc.fst"
let _72_1832 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_72_1832) with
| (env0, topt) -> begin
(
# 1332 "FStar.TypeChecker.Tc.fst"
let _72_1835 = (build_let_rec_env false env0 lbs)
in (match (_72_1835) with
| (lbs, rec_env) -> begin
(
# 1333 "FStar.TypeChecker.Tc.fst"
let _72_1838 = (check_let_recs rec_env lbs)
in (match (_72_1838) with
| (lbs, g_lbs) -> begin
(
# 1335 "FStar.TypeChecker.Tc.fst"
let _72_1856 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _72_1841 _72_1850 -> (match ((_72_1841, _72_1850)) with
| ((bvs, env), {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _72_1848; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _72_1845; FStar_Syntax_Syntax.lbdef = _72_1843}) -> begin
(
# 1336 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env x ([], t))
in (let _151_779 = (let _151_778 = (
# 1337 "FStar.TypeChecker.Tc.fst"
let _72_1852 = (FStar_Util.left x)
in {FStar_Syntax_Syntax.ppname = _72_1852.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _72_1852.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (_151_778)::bvs)
in (_151_779, env)))
end)) ([], env)))
in (match (_72_1856) with
| (bvs, env) -> begin
(
# 1338 "FStar.TypeChecker.Tc.fst"
let bvs = (FStar_List.rev bvs)
in (
# 1340 "FStar.TypeChecker.Tc.fst"
let _72_1861 = (tc_term env e2)
in (match (_72_1861) with
| (e2, cres, g2) -> begin
(
# 1341 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (
# 1342 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (
# 1343 "FStar.TypeChecker.Tc.fst"
let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (
# 1344 "FStar.TypeChecker.Tc.fst"
let cres = (
# 1344 "FStar.TypeChecker.Tc.fst"
let _72_1865 = cres
in {FStar_Syntax_Syntax.eff_name = _72_1865.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _72_1865.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _72_1865.FStar_Syntax_Syntax.comp})
in (
# 1346 "FStar.TypeChecker.Tc.fst"
let _72_1870 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_72_1870) with
| (lbs, e2) -> begin
(
# 1347 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_72_1873) -> begin
(e, cres, guard)
end
| None -> begin
(
# 1351 "FStar.TypeChecker.Tc.fst"
let _72_1876 = (check_no_escape env bvs tres)
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
| _72_1879 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (
# 1362 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1363 "FStar.TypeChecker.Tc.fst"
let _72_1912 = (FStar_List.fold_left (fun _72_1886 lb -> (match (_72_1886) with
| (lbs, env) -> begin
(
# 1364 "FStar.TypeChecker.Tc.fst"
let _72_1891 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_72_1891) with
| (univ_vars, t, check_t) -> begin
(
# 1365 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (
# 1366 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (
# 1367 "FStar.TypeChecker.Tc.fst"
let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(
# 1372 "FStar.TypeChecker.Tc.fst"
let _72_1900 = (let _151_786 = (let _151_785 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _151_785))
in (tc_check_tot_or_gtot_term (
# 1372 "FStar.TypeChecker.Tc.fst"
let _72_1894 = env0
in {FStar_TypeChecker_Env.solver = _72_1894.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _72_1894.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _72_1894.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _72_1894.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _72_1894.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _72_1894.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _72_1894.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _72_1894.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _72_1894.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _72_1894.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _72_1894.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _72_1894.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _72_1894.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _72_1894.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _72_1894.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _72_1894.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _72_1894.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _72_1894.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _72_1894.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _72_1894.FStar_TypeChecker_Env.use_bv_sorts}) t _151_786))
in (match (_72_1900) with
| (t, _72_1898, g) -> begin
(
# 1373 "FStar.TypeChecker.Tc.fst"
let _72_1901 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (
# 1375 "FStar.TypeChecker.Tc.fst"
let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(
# 1377 "FStar.TypeChecker.Tc.fst"
let _72_1904 = env
in {FStar_TypeChecker_Env.solver = _72_1904.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _72_1904.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _72_1904.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _72_1904.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _72_1904.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _72_1904.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _72_1904.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _72_1904.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _72_1904.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _72_1904.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _72_1904.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _72_1904.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _72_1904.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _72_1904.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _72_1904.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _72_1904.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _72_1904.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _72_1904.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _72_1904.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _72_1904.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (
# 1379 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1379 "FStar.TypeChecker.Tc.fst"
let _72_1907 = lb
in {FStar_Syntax_Syntax.lbname = _72_1907.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _72_1907.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_72_1912) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (
# 1386 "FStar.TypeChecker.Tc.fst"
let _72_1925 = (let _151_791 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 1387 "FStar.TypeChecker.Tc.fst"
let _72_1919 = (let _151_790 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _151_790 lb.FStar_Syntax_Syntax.lbdef))
in (match (_72_1919) with
| (e, c, g) -> begin
(
# 1388 "FStar.TypeChecker.Tc.fst"
let _72_1920 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1390 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _151_791 FStar_List.unzip))
in (match (_72_1925) with
| (lbs, gs) -> begin
(
# 1392 "FStar.TypeChecker.Tc.fst"
let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (
# 1406 "FStar.TypeChecker.Tc.fst"
let _72_1933 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_72_1933) with
| (env1, _72_1932) -> begin
(
# 1407 "FStar.TypeChecker.Tc.fst"
let e1 = lb.FStar_Syntax_Syntax.lbdef
in (
# 1410 "FStar.TypeChecker.Tc.fst"
let _72_1939 = (check_lbtyp top_level env lb)
in (match (_72_1939) with
| (topt, wf_annot, univ_vars, env1) -> begin
(
# 1412 "FStar.TypeChecker.Tc.fst"
let _72_1940 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1416 "FStar.TypeChecker.Tc.fst"
let _72_1947 = (tc_maybe_toplevel_term (
# 1416 "FStar.TypeChecker.Tc.fst"
let _72_1942 = env1
in {FStar_TypeChecker_Env.solver = _72_1942.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _72_1942.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _72_1942.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _72_1942.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _72_1942.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _72_1942.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _72_1942.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _72_1942.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _72_1942.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _72_1942.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _72_1942.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _72_1942.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _72_1942.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _72_1942.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _72_1942.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _72_1942.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _72_1942.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _72_1942.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _72_1942.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _72_1942.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_72_1947) with
| (e1, c1, g1) -> begin
(
# 1419 "FStar.TypeChecker.Tc.fst"
let _72_1951 = (let _151_798 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _72_1948 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _151_798 e1 c1 wf_annot))
in (match (_72_1951) with
| (c1, guard_f) -> begin
(
# 1422 "FStar.TypeChecker.Tc.fst"
let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (
# 1424 "FStar.TypeChecker.Tc.fst"
let _72_1953 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _151_799 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _151_799))
end else begin
()
end
in (let _151_800 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _151_800))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (
# 1436 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 1439 "FStar.TypeChecker.Tc.fst"
let _72_1960 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _72_1963 -> begin
(
# 1443 "FStar.TypeChecker.Tc.fst"
let _72_1966 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_72_1966) with
| (univ_vars, t) -> begin
(
# 1444 "FStar.TypeChecker.Tc.fst"
let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _151_804 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _151_804))
end else begin
(
# 1451 "FStar.TypeChecker.Tc.fst"
let _72_1971 = (FStar_Syntax_Util.type_u ())
in (match (_72_1971) with
| (k, _72_1970) -> begin
(
# 1452 "FStar.TypeChecker.Tc.fst"
let _72_1976 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_72_1976) with
| (t, _72_1974, g) -> begin
(
# 1453 "FStar.TypeChecker.Tc.fst"
let _72_1977 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _151_807 = (let _151_805 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _151_805))
in (let _151_806 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _151_807 _151_806)))
end else begin
()
end
in (
# 1457 "FStar.TypeChecker.Tc.fst"
let t = (norm env1 t)
in (let _151_808 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _151_808))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _72_1983 -> (match (_72_1983) with
| (x, imp) -> begin
(
# 1462 "FStar.TypeChecker.Tc.fst"
let _72_1986 = (FStar_Syntax_Util.type_u ())
in (match (_72_1986) with
| (tu, u) -> begin
(
# 1463 "FStar.TypeChecker.Tc.fst"
let _72_1991 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_72_1991) with
| (t, _72_1989, g) -> begin
(
# 1464 "FStar.TypeChecker.Tc.fst"
let x = ((
# 1464 "FStar.TypeChecker.Tc.fst"
let _72_1992 = x
in {FStar_Syntax_Syntax.ppname = _72_1992.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _72_1992.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (
# 1465 "FStar.TypeChecker.Tc.fst"
let _72_1995 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_812 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _151_811 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _151_812 _151_811)))
end else begin
()
end
in (let _151_813 = (maybe_push_binding env x)
in (x, _151_813, g, u))))
end))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe Prims.list) = (fun env bs -> (
# 1470 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_TypeChecker_Rel.trivial_guard, [])
end
| b::bs -> begin
(
# 1473 "FStar.TypeChecker.Tc.fst"
let _72_2010 = (tc_binder env b)
in (match (_72_2010) with
| (b, env', g, u) -> begin
(
# 1474 "FStar.TypeChecker.Tc.fst"
let _72_2015 = (aux env' bs)
in (match (_72_2015) with
| (bs, env', g', us) -> begin
(let _151_821 = (let _151_820 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _151_820))
in ((b)::bs, env', _151_821, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (
# 1479 "FStar.TypeChecker.Tc.fst"
let tc_args = (fun env args -> (FStar_List.fold_right (fun _72_2023 _72_2026 -> (match ((_72_2023, _72_2026)) with
| ((t, imp), (args, g)) -> begin
(
# 1483 "FStar.TypeChecker.Tc.fst"
let _72_2031 = (tc_term env t)
in (match (_72_2031) with
| (t, _72_2029, g') -> begin
(let _151_830 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _151_830))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _72_2035 -> (match (_72_2035) with
| (pats, g) -> begin
(
# 1486 "FStar.TypeChecker.Tc.fst"
let _72_2038 = (tc_args env p)
in (match (_72_2038) with
| (args, g') -> begin
(let _151_833 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _151_833))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1491 "FStar.TypeChecker.Tc.fst"
let _72_2044 = (tc_maybe_toplevel_term env e)
in (match (_72_2044) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(
# 1494 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (
# 1495 "FStar.TypeChecker.Tc.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 1496 "FStar.TypeChecker.Tc.fst"
let _72_2047 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_836 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _151_836))
end else begin
()
end
in (
# 1497 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 1498 "FStar.TypeChecker.Tc.fst"
let _72_2052 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _151_837 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_151_837, false))
end else begin
(let _151_838 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_151_838, true))
end
in (match (_72_2052) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _151_839 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _151_839))
end
| _72_2056 -> begin
if allow_ghost then begin
(let _151_842 = (let _151_841 = (let _151_840 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_151_840, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_151_841))
in (Prims.raise _151_842))
end else begin
(let _151_845 = (let _151_844 = (let _151_843 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_151_843, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_151_844))
in (Prims.raise _151_845))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 1512 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))

# 1516 "FStar.TypeChecker.Tc.fst"
let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (
# 1517 "FStar.TypeChecker.Tc.fst"
let _72_2066 = (tc_tot_or_gtot_term env t)
in (match (_72_2066) with
| (t, c, g) -> begin
(
# 1518 "FStar.TypeChecker.Tc.fst"
let _72_2067 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))

# 1521 "FStar.TypeChecker.Tc.fst"
let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (
# 1522 "FStar.TypeChecker.Tc.fst"
let _72_2075 = (tc_check_tot_or_gtot_term env t k)
in (match (_72_2075) with
| (t, c, g) -> begin
(
# 1523 "FStar.TypeChecker.Tc.fst"
let _72_2076 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))

# 1526 "FStar.TypeChecker.Tc.fst"
let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _151_865 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _151_865)))

# 1529 "FStar.TypeChecker.Tc.fst"
let check_nogen = (fun env t k -> (
# 1530 "FStar.TypeChecker.Tc.fst"
let t = (tc_check_trivial_guard env t k)
in (let _151_869 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _151_869))))

# 1533 "FStar.TypeChecker.Tc.fst"
let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (
# 1534 "FStar.TypeChecker.Tc.fst"
let _72_2091 = (tc_binders env tps)
in (match (_72_2091) with
| (tps, env, g, us) -> begin
(
# 1535 "FStar.TypeChecker.Tc.fst"
let _72_2092 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))

# 1538 "FStar.TypeChecker.Tc.fst"
let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (
# 1539 "FStar.TypeChecker.Tc.fst"
let fail = (fun _72_2098 -> (match (()) with
| () -> begin
(let _151_884 = (let _151_883 = (let _151_882 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_151_882, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_151_883))
in (Prims.raise _151_884))
end))
in (
# 1540 "FStar.TypeChecker.Tc.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1543 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _72_2115)::(wp, _72_2111)::(_wlp, _72_2107)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _72_2119 -> begin
(fail ())
end))
end
| _72_2121 -> begin
(fail ())
end))))

# 1550 "FStar.TypeChecker.Tc.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 1553 "FStar.TypeChecker.Tc.fst"
let _72_2128 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_72_2128) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _72_2130 -> begin
(
# 1556 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow binders c)
in (
# 1557 "FStar.TypeChecker.Tc.fst"
let _72_2134 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_72_2134) with
| (uvs, t') -> begin
(match ((let _151_891 = (FStar_Syntax_Subst.compress t')
in _151_891.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _72_2140 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 1562 "FStar.TypeChecker.Tc.fst"
let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (
# 1563 "FStar.TypeChecker.Tc.fst"
let fail = (fun t -> (let _151_900 = (let _151_899 = (let _151_898 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env ed.FStar_Syntax_Syntax.mname t)
in (_151_898, (FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname)))
in FStar_Syntax_Syntax.Error (_151_899))
in (Prims.raise _151_900)))
in (
# 1564 "FStar.TypeChecker.Tc.fst"
let _72_2169 = (match ((let _151_901 = (FStar_Syntax_Subst.compress ed.FStar_Syntax_Syntax.signature)
in _151_901.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1566 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _72_2160)::(wp, _72_2156)::(_wlp, _72_2152)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _72_2164 -> begin
(fail ed.FStar_Syntax_Syntax.signature)
end))
end
| _72_2166 -> begin
(fail ed.FStar_Syntax_Syntax.signature)
end)
in (match (_72_2169) with
| (a, wp) -> begin
(
# 1572 "FStar.TypeChecker.Tc.fst"
let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _72_2172 -> begin
(
# 1576 "FStar.TypeChecker.Tc.fst"
let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (
# 1577 "FStar.TypeChecker.Tc.fst"
let op = (fun ts -> (
# 1578 "FStar.TypeChecker.Tc.fst"
let _72_2176 = ()
in (
# 1579 "FStar.TypeChecker.Tc.fst"
let t0 = (Prims.snd ts)
in (
# 1580 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (
# 1582 "FStar.TypeChecker.Tc.fst"
let _72_2180 = ed
in (let _151_916 = (op ed.FStar_Syntax_Syntax.ret)
in (let _151_915 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _151_914 = (op ed.FStar_Syntax_Syntax.bind_wlp)
in (let _151_913 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _151_912 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _151_911 = (op ed.FStar_Syntax_Syntax.ite_wlp)
in (let _151_910 = (op ed.FStar_Syntax_Syntax.wp_binop)
in (let _151_909 = (op ed.FStar_Syntax_Syntax.wp_as_type)
in (let _151_908 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _151_907 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _151_906 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _151_905 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _151_904 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _72_2180.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _72_2180.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _72_2180.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _72_2180.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _72_2180.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _151_916; FStar_Syntax_Syntax.bind_wp = _151_915; FStar_Syntax_Syntax.bind_wlp = _151_914; FStar_Syntax_Syntax.if_then_else = _151_913; FStar_Syntax_Syntax.ite_wp = _151_912; FStar_Syntax_Syntax.ite_wlp = _151_911; FStar_Syntax_Syntax.wp_binop = _151_910; FStar_Syntax_Syntax.wp_as_type = _151_909; FStar_Syntax_Syntax.close_wp = _151_908; FStar_Syntax_Syntax.assert_p = _151_907; FStar_Syntax_Syntax.assume_p = _151_906; FStar_Syntax_Syntax.null_wp = _151_905; FStar_Syntax_Syntax.trivial = _151_904}))))))))))))))))
end)
in (ed, a, wp))
end))))

# 1598 "FStar.TypeChecker.Tc.fst"
let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (
# 1599 "FStar.TypeChecker.Tc.fst"
let _72_2185 = ()
in (
# 1600 "FStar.TypeChecker.Tc.fst"
let _72_2189 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_72_2189) with
| (binders, signature) -> begin
(
# 1601 "FStar.TypeChecker.Tc.fst"
let _72_2194 = (tc_tparams env0 binders)
in (match (_72_2194) with
| (binders, env, _72_2193) -> begin
(
# 1602 "FStar.TypeChecker.Tc.fst"
let _72_2198 = (tc_trivial_guard env signature)
in (match (_72_2198) with
| (signature, _72_2197) -> begin
(
# 1603 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1603 "FStar.TypeChecker.Tc.fst"
let _72_2199 = ed
in {FStar_Syntax_Syntax.qualifiers = _72_2199.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _72_2199.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _72_2199.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _72_2199.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _72_2199.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _72_2199.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = _72_2199.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _72_2199.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _72_2199.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = _72_2199.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _72_2199.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _72_2199.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _72_2199.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _72_2199.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _72_2199.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _72_2199.FStar_Syntax_Syntax.trivial})
in (
# 1606 "FStar.TypeChecker.Tc.fst"
let _72_2205 = (open_effect_decl env ed)
in (match (_72_2205) with
| (ed, a, wp_a) -> begin
(
# 1609 "FStar.TypeChecker.Tc.fst"
let env = (let _151_921 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _151_921))
in (
# 1611 "FStar.TypeChecker.Tc.fst"
let _72_2207 = if (FStar_TypeChecker_Env.debug env0 FStar_Options.Low) then begin
(let _151_924 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _151_923 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _151_922 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checked effect signature: %s %s : %s\n" _151_924 _151_923 _151_922))))
end else begin
()
end
in (
# 1617 "FStar.TypeChecker.Tc.fst"
let check_and_gen' = (fun env _72_2214 k -> (match (_72_2214) with
| (_72_2212, t) -> begin
(check_and_gen env t k)
end))
in (
# 1619 "FStar.TypeChecker.Tc.fst"
let ret = (
# 1620 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_936 = (let _151_934 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_933 = (let _151_932 = (let _151_931 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _151_931))
in (_151_932)::[])
in (_151_934)::_151_933))
in (let _151_935 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _151_936 _151_935)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (
# 1623 "FStar.TypeChecker.Tc.fst"
let bind_wp = (
# 1624 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1625 "FStar.TypeChecker.Tc.fst"
let b = (let _151_938 = (let _151_937 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_937 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _151_938))
in (
# 1626 "FStar.TypeChecker.Tc.fst"
let wp_b = (let _151_942 = (let _151_941 = (let _151_940 = (let _151_939 = (FStar_Syntax_Syntax.bv_to_name b)
in (a, _151_939))
in FStar_Syntax_Syntax.NT (_151_940))
in (_151_941)::[])
in (FStar_Syntax_Subst.subst _151_942 wp_a))
in (
# 1627 "FStar.TypeChecker.Tc.fst"
let a_wp_b = (let _151_946 = (let _151_944 = (let _151_943 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _151_943))
in (_151_944)::[])
in (let _151_945 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _151_946 _151_945)))
in (
# 1628 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = a_wp_b
in (
# 1629 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_959 = (let _151_957 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_956 = (let _151_955 = (FStar_Syntax_Syntax.mk_binder b)
in (let _151_954 = (let _151_953 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _151_952 = (let _151_951 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _151_950 = (let _151_949 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (let _151_948 = (let _151_947 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_151_947)::[])
in (_151_949)::_151_948))
in (_151_951)::_151_950))
in (_151_953)::_151_952))
in (_151_955)::_151_954))
in (_151_957)::_151_956))
in (let _151_958 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _151_959 _151_958)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))))))
in (
# 1635 "FStar.TypeChecker.Tc.fst"
let bind_wlp = (
# 1636 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1637 "FStar.TypeChecker.Tc.fst"
let b = (let _151_961 = (let _151_960 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_960 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _151_961))
in (
# 1638 "FStar.TypeChecker.Tc.fst"
let wlp_b = (let _151_965 = (let _151_964 = (let _151_963 = (let _151_962 = (FStar_Syntax_Syntax.bv_to_name b)
in (a, _151_962))
in FStar_Syntax_Syntax.NT (_151_963))
in (_151_964)::[])
in (FStar_Syntax_Subst.subst _151_965 wlp_a))
in (
# 1639 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = (let _151_969 = (let _151_967 = (let _151_966 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _151_966))
in (_151_967)::[])
in (let _151_968 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _151_969 _151_968)))
in (
# 1640 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_978 = (let _151_976 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_975 = (let _151_974 = (FStar_Syntax_Syntax.mk_binder b)
in (let _151_973 = (let _151_972 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _151_971 = (let _151_970 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_151_970)::[])
in (_151_972)::_151_971))
in (_151_974)::_151_973))
in (_151_976)::_151_975))
in (let _151_977 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _151_978 _151_977)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wlp expected_k))))))
in (
# 1646 "FStar.TypeChecker.Tc.fst"
let if_then_else = (
# 1647 "FStar.TypeChecker.Tc.fst"
let p = (let _151_980 = (let _151_979 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_979 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _151_980))
in (
# 1648 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_989 = (let _151_987 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_986 = (let _151_985 = (FStar_Syntax_Syntax.mk_binder p)
in (let _151_984 = (let _151_983 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _151_982 = (let _151_981 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_981)::[])
in (_151_983)::_151_982))
in (_151_985)::_151_984))
in (_151_987)::_151_986))
in (let _151_988 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_989 _151_988)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (
# 1654 "FStar.TypeChecker.Tc.fst"
let ite_wp = (
# 1655 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1656 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_996 = (let _151_994 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_993 = (let _151_992 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _151_991 = (let _151_990 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_990)::[])
in (_151_992)::_151_991))
in (_151_994)::_151_993))
in (let _151_995 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_996 _151_995)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k)))
in (
# 1662 "FStar.TypeChecker.Tc.fst"
let ite_wlp = (
# 1663 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1664 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1001 = (let _151_999 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_998 = (let _151_997 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (_151_997)::[])
in (_151_999)::_151_998))
in (let _151_1000 = (FStar_Syntax_Syntax.mk_Total wlp_a)
in (FStar_Syntax_Util.arrow _151_1001 _151_1000)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wlp expected_k)))
in (
# 1669 "FStar.TypeChecker.Tc.fst"
let wp_binop = (
# 1670 "FStar.TypeChecker.Tc.fst"
let bin_op = (
# 1671 "FStar.TypeChecker.Tc.fst"
let _72_2242 = (FStar_Syntax_Util.type_u ())
in (match (_72_2242) with
| (t1, u1) -> begin
(
# 1672 "FStar.TypeChecker.Tc.fst"
let _72_2245 = (FStar_Syntax_Util.type_u ())
in (match (_72_2245) with
| (t2, u2) -> begin
(
# 1673 "FStar.TypeChecker.Tc.fst"
let t = (let _151_1002 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_max ((u1)::(u2)::[]))) None _151_1002))
in (let _151_1007 = (let _151_1005 = (FStar_Syntax_Syntax.null_binder t1)
in (let _151_1004 = (let _151_1003 = (FStar_Syntax_Syntax.null_binder t2)
in (_151_1003)::[])
in (_151_1005)::_151_1004))
in (let _151_1006 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _151_1007 _151_1006))))
end))
end))
in (
# 1675 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1016 = (let _151_1014 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1013 = (let _151_1012 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _151_1011 = (let _151_1010 = (FStar_Syntax_Syntax.null_binder bin_op)
in (let _151_1009 = (let _151_1008 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_1008)::[])
in (_151_1010)::_151_1009))
in (_151_1012)::_151_1011))
in (_151_1014)::_151_1013))
in (let _151_1015 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_1016 _151_1015)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_binop expected_k)))
in (
# 1682 "FStar.TypeChecker.Tc.fst"
let wp_as_type = (
# 1683 "FStar.TypeChecker.Tc.fst"
let _72_2253 = (FStar_Syntax_Util.type_u ())
in (match (_72_2253) with
| (t, _72_2252) -> begin
(
# 1684 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1021 = (let _151_1019 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1018 = (let _151_1017 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_1017)::[])
in (_151_1019)::_151_1018))
in (let _151_1020 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _151_1021 _151_1020)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (
# 1689 "FStar.TypeChecker.Tc.fst"
let close_wp = (
# 1690 "FStar.TypeChecker.Tc.fst"
let b = (let _151_1023 = (let _151_1022 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_1022 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _151_1023))
in (
# 1691 "FStar.TypeChecker.Tc.fst"
let b_wp_a = (let _151_1027 = (let _151_1025 = (let _151_1024 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _151_1024))
in (_151_1025)::[])
in (let _151_1026 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_1027 _151_1026)))
in (
# 1692 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1034 = (let _151_1032 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1031 = (let _151_1030 = (FStar_Syntax_Syntax.mk_binder b)
in (let _151_1029 = (let _151_1028 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_151_1028)::[])
in (_151_1030)::_151_1029))
in (_151_1032)::_151_1031))
in (let _151_1033 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_1034 _151_1033)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (
# 1696 "FStar.TypeChecker.Tc.fst"
let assert_p = (
# 1697 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1043 = (let _151_1041 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1040 = (let _151_1039 = (let _151_1036 = (let _151_1035 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_1035 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _151_1036))
in (let _151_1038 = (let _151_1037 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_1037)::[])
in (_151_1039)::_151_1038))
in (_151_1041)::_151_1040))
in (let _151_1042 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_1043 _151_1042)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (
# 1703 "FStar.TypeChecker.Tc.fst"
let assume_p = (
# 1704 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1052 = (let _151_1050 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1049 = (let _151_1048 = (let _151_1045 = (let _151_1044 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_1044 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _151_1045))
in (let _151_1047 = (let _151_1046 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_1046)::[])
in (_151_1048)::_151_1047))
in (_151_1050)::_151_1049))
in (let _151_1051 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_1052 _151_1051)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (
# 1710 "FStar.TypeChecker.Tc.fst"
let null_wp = (
# 1711 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1055 = (let _151_1053 = (FStar_Syntax_Syntax.mk_binder a)
in (_151_1053)::[])
in (let _151_1054 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_1055 _151_1054)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (
# 1715 "FStar.TypeChecker.Tc.fst"
let trivial_wp = (
# 1716 "FStar.TypeChecker.Tc.fst"
let _72_2269 = (FStar_Syntax_Util.type_u ())
in (match (_72_2269) with
| (t, _72_2268) -> begin
(
# 1717 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1060 = (let _151_1058 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1057 = (let _151_1056 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_1056)::[])
in (_151_1058)::_151_1057))
in (let _151_1059 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _151_1060 _151_1059)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (
# 1723 "FStar.TypeChecker.Tc.fst"
let t = (let _151_1061 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _151_1061))
in (
# 1724 "FStar.TypeChecker.Tc.fst"
let _72_2275 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_72_2275) with
| (univs, t) -> begin
(
# 1725 "FStar.TypeChecker.Tc.fst"
let _72_2291 = (match ((let _151_1063 = (let _151_1062 = (FStar_Syntax_Subst.compress t)
in _151_1062.FStar_Syntax_Syntax.n)
in (binders, _151_1063))) with
| ([], _72_2278) -> begin
([], t)
end
| (_72_2281, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _72_2288 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_72_2291) with
| (binders, signature) -> begin
(
# 1729 "FStar.TypeChecker.Tc.fst"
let close = (fun ts -> (let _151_1066 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _151_1066)))
in (
# 1730 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1730 "FStar.TypeChecker.Tc.fst"
let _72_2294 = ed
in (let _151_1079 = (close ret)
in (let _151_1078 = (close bind_wp)
in (let _151_1077 = (close bind_wlp)
in (let _151_1076 = (close if_then_else)
in (let _151_1075 = (close ite_wp)
in (let _151_1074 = (close ite_wlp)
in (let _151_1073 = (close wp_binop)
in (let _151_1072 = (close wp_as_type)
in (let _151_1071 = (close close_wp)
in (let _151_1070 = (close assert_p)
in (let _151_1069 = (close assume_p)
in (let _151_1068 = (close null_wp)
in (let _151_1067 = (close trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _72_2294.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _72_2294.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _151_1079; FStar_Syntax_Syntax.bind_wp = _151_1078; FStar_Syntax_Syntax.bind_wlp = _151_1077; FStar_Syntax_Syntax.if_then_else = _151_1076; FStar_Syntax_Syntax.ite_wp = _151_1075; FStar_Syntax_Syntax.ite_wlp = _151_1074; FStar_Syntax_Syntax.wp_binop = _151_1073; FStar_Syntax_Syntax.wp_as_type = _151_1072; FStar_Syntax_Syntax.close_wp = _151_1071; FStar_Syntax_Syntax.assert_p = _151_1070; FStar_Syntax_Syntax.assume_p = _151_1069; FStar_Syntax_Syntax.null_wp = _151_1068; FStar_Syntax_Syntax.trivial = _151_1067}))))))))))))))
in (
# 1748 "FStar.TypeChecker.Tc.fst"
let _72_2297 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1080 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _151_1080))
end else begin
()
end
in ed)))
end))
end)))))))))))))))))))
end)))
end))
end))
end))))

# 1752 "FStar.TypeChecker.Tc.fst"
let tc_lex_t = (fun env ses quals lids -> (
# 1759 "FStar.TypeChecker.Tc.fst"
let _72_2303 = ()
in (
# 1760 "FStar.TypeChecker.Tc.fst"
let _72_2311 = ()
in (match (ses) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _72_2340, _72_2342, [], r)::FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _72_2331, r1)::FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _72_2320, r2)::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(
# 1775 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (
# 1776 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (
# 1777 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (
# 1778 "FStar.TypeChecker.Tc.fst"
let tc = FStar_Syntax_Syntax.Sig_inductive_typ ((lex_t, (u)::[], [], t, [], (FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[], [], r))
in (
# 1780 "FStar.TypeChecker.Tc.fst"
let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (
# 1781 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (let _151_1087 = (let _151_1086 = (let _151_1085 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid r1)
in (_151_1085, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_151_1086))
in (FStar_Syntax_Syntax.mk _151_1087 None r1))
in (
# 1782 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (
# 1783 "FStar.TypeChecker.Tc.fst"
let dc_lextop = FStar_Syntax_Syntax.Sig_datacon ((lex_top, (utop)::[], lex_top_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r1))
in (
# 1785 "FStar.TypeChecker.Tc.fst"
let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1786 "FStar.TypeChecker.Tc.fst"
let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1787 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (
# 1788 "FStar.TypeChecker.Tc.fst"
let a = (let _151_1088 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _151_1088))
in (
# 1789 "FStar.TypeChecker.Tc.fst"
let hd = (let _151_1089 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _151_1089))
in (
# 1790 "FStar.TypeChecker.Tc.fst"
let tl = (let _151_1093 = (let _151_1092 = (let _151_1091 = (let _151_1090 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid r2)
in (_151_1090, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_151_1091))
in (FStar_Syntax_Syntax.mk _151_1092 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _151_1093))
in (
# 1791 "FStar.TypeChecker.Tc.fst"
let res = (let _151_1096 = (let _151_1095 = (let _151_1094 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid r2)
in (_151_1094, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_151_1095))
in (FStar_Syntax_Syntax.mk _151_1096 None r2))
in (let _151_1097 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.Implicit)))::((hd, None))::((tl, None))::[]) _151_1097))))))
in (
# 1793 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (
# 1794 "FStar.TypeChecker.Tc.fst"
let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _151_1099 = (let _151_1098 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _151_1098))
in FStar_Syntax_Syntax.Sig_bundle (_151_1099)))))))))))))))
end
| _72_2366 -> begin
(let _151_1101 = (let _151_1100 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _151_1100))
in (FStar_All.failwith _151_1101))
end))))

# 1800 "FStar.TypeChecker.Tc.fst"
let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (
# 1863 "FStar.TypeChecker.Tc.fst"
let warn_positivity = (fun l r -> (let _151_1115 = (let _151_1114 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _151_1114))
in (FStar_TypeChecker_Errors.warn r _151_1115)))
in (
# 1865 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1868 "FStar.TypeChecker.Tc.fst"
let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(
# 1873 "FStar.TypeChecker.Tc.fst"
let _72_2388 = ()
in (
# 1874 "FStar.TypeChecker.Tc.fst"
let _72_2390 = (warn_positivity tc r)
in (
# 1875 "FStar.TypeChecker.Tc.fst"
let _72_2394 = (FStar_Syntax_Subst.open_term tps k)
in (match (_72_2394) with
| (tps, k) -> begin
(
# 1876 "FStar.TypeChecker.Tc.fst"
let _72_2398 = (tc_tparams env tps)
in (match (_72_2398) with
| (tps, env_tps, us) -> begin
(
# 1877 "FStar.TypeChecker.Tc.fst"
let _72_2401 = (FStar_Syntax_Util.arrow_formals k)
in (match (_72_2401) with
| (indices, t) -> begin
(
# 1878 "FStar.TypeChecker.Tc.fst"
let _72_2405 = (tc_tparams env_tps indices)
in (match (_72_2405) with
| (indices, env', us') -> begin
(
# 1879 "FStar.TypeChecker.Tc.fst"
let _72_2409 = (tc_trivial_guard env' t)
in (match (_72_2409) with
| (t, _72_2408) -> begin
(
# 1880 "FStar.TypeChecker.Tc.fst"
let k = (let _151_1120 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _151_1120))
in (
# 1881 "FStar.TypeChecker.Tc.fst"
let _72_2413 = (FStar_Syntax_Util.type_u ())
in (match (_72_2413) with
| (t_type, u) -> begin
(
# 1882 "FStar.TypeChecker.Tc.fst"
let _72_2414 = (let _151_1121 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _151_1121))
in (
# 1884 "FStar.TypeChecker.Tc.fst"
let refined_tps = (FStar_All.pipe_right tps (FStar_List.map (fun _72_2418 -> (match (_72_2418) with
| (x, imp) -> begin
(
# 1885 "FStar.TypeChecker.Tc.fst"
let y = (FStar_Syntax_Syntax.freshen_bv x)
in (
# 1886 "FStar.TypeChecker.Tc.fst"
let refined = (let _151_1125 = (let _151_1124 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _151_1123 = (FStar_Syntax_Syntax.bv_to_name y)
in (FStar_Syntax_Util.mk_eq x.FStar_Syntax_Syntax.sort x.FStar_Syntax_Syntax.sort _151_1124 _151_1123)))
in (FStar_Syntax_Util.refine y _151_1125))
in ((
# 1887 "FStar.TypeChecker.Tc.fst"
let _72_2421 = x
in {FStar_Syntax_Syntax.ppname = _72_2421.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _72_2421.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = refined}), imp)))
end))))
in (
# 1889 "FStar.TypeChecker.Tc.fst"
let t_tc = (let _151_1126 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append refined_tps indices) _151_1126))
in (
# 1890 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 1891 "FStar.TypeChecker.Tc.fst"
let k = (FStar_Syntax_Subst.close tps k)
in (let _151_1127 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (tc)) ([], t_tc))
in (_151_1127, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u)))))))
end)))
end))
end))
end))
end))
end))))
end
| _72_2428 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1898 "FStar.TypeChecker.Tc.fst"
let positive_if_pure = (fun _72_2430 l -> ())
in (
# 1901 "FStar.TypeChecker.Tc.fst"
let tc_data = (fun env tcs _72_6 -> (match (_72_6) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(
# 1903 "FStar.TypeChecker.Tc.fst"
let _72_2447 = ()
in (
# 1905 "FStar.TypeChecker.Tc.fst"
let _72_2478 = (let _151_1142 = (FStar_Util.find_map tcs (fun _72_2451 -> (match (_72_2451) with
| (se, u_tc) -> begin
if (let _151_1140 = (let _151_1139 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _151_1139))
in (FStar_Ident.lid_equals tc_lid _151_1140)) then begin
(
# 1908 "FStar.TypeChecker.Tc.fst"
let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_72_2453, _72_2455, tps, _72_2458, _72_2460, _72_2462, _72_2464, _72_2466) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _72_2472 -> (match (_72_2472) with
| (x, _72_2471) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit))
end))))
end
| _72_2474 -> begin
(FStar_All.failwith "Impossible")
end)
in Some ((tps, u_tc)))
end else begin
None
end
end)))
in (FStar_All.pipe_right _151_1142 FStar_Util.must))
in (match (_72_2478) with
| (tps, u_tc) -> begin
(
# 1915 "FStar.TypeChecker.Tc.fst"
let _72_2498 = (match ((let _151_1143 = (FStar_Syntax_Subst.compress t)
in _151_1143.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(
# 1920 "FStar.TypeChecker.Tc.fst"
let _72_2486 = (FStar_Util.first_N ntps bs)
in (match (_72_2486) with
| (_72_2484, bs') -> begin
(
# 1921 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (
# 1922 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _72_2492 -> (match (_72_2492) with
| (x, _72_2491) -> begin
(let _151_1147 = (let _151_1146 = (FStar_Syntax_Syntax.bv_to_name x)
in ((ntps - (1 + i)), _151_1146))
in FStar_Syntax_Syntax.DB (_151_1147))
end))))
in (let _151_1148 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _151_1148))))
end))
end
| _72_2495 -> begin
([], t)
end)
in (match (_72_2498) with
| (arguments, result) -> begin
(
# 1926 "FStar.TypeChecker.Tc.fst"
let _72_2499 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1151 = (FStar_Syntax_Print.lid_to_string c)
in (let _151_1150 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _151_1149 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _151_1151 _151_1150 _151_1149))))
end else begin
()
end
in (
# 1932 "FStar.TypeChecker.Tc.fst"
let _72_2504 = (tc_tparams env arguments)
in (match (_72_2504) with
| (arguments, env', us) -> begin
(
# 1933 "FStar.TypeChecker.Tc.fst"
let _72_2508 = (tc_trivial_guard env' result)
in (match (_72_2508) with
| (result, _72_2507) -> begin
(
# 1934 "FStar.TypeChecker.Tc.fst"
let _72_2512 = (FStar_Syntax_Util.head_and_args result)
in (match (_72_2512) with
| (head, _72_2511) -> begin
(
# 1935 "FStar.TypeChecker.Tc.fst"
let _72_2520 = (match ((let _151_1152 = (FStar_Syntax_Subst.compress head)
in _151_1152.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _72_2515) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v tc_lid) -> begin
()
end
| _72_2519 -> begin
(let _151_1156 = (let _151_1155 = (let _151_1154 = (let _151_1153 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _151_1153))
in (_151_1154, r))
in FStar_Syntax_Syntax.Error (_151_1155))
in (Prims.raise _151_1156))
end)
in (
# 1938 "FStar.TypeChecker.Tc.fst"
let g = (FStar_List.fold_left2 (fun g _72_2526 u_x -> (match (_72_2526) with
| (x, _72_2525) -> begin
(
# 1939 "FStar.TypeChecker.Tc.fst"
let _72_2528 = ()
in (let _151_1160 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _151_1160)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (
# 1945 "FStar.TypeChecker.Tc.fst"
let t = (let _151_1161 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow (FStar_List.append tps arguments) _151_1161))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _72_2533 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1952 "FStar.TypeChecker.Tc.fst"
let generalize_and_recheck = (fun env g tcs datas -> (
# 1953 "FStar.TypeChecker.Tc.fst"
let _72_2539 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 1954 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _72_7 -> (match (_72_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_72_2543, _72_2545, tps, k, _72_2549, _72_2551, _72_2553, _72_2555) -> begin
(let _151_1172 = (let _151_1171 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _151_1171))
in (FStar_Syntax_Syntax.null_binder _151_1172))
end
| _72_2559 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 1957 "FStar.TypeChecker.Tc.fst"
let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _72_8 -> (match (_72_8) with
| FStar_Syntax_Syntax.Sig_datacon (_72_2563, _72_2565, t, _72_2568, _72_2570, _72_2572, _72_2574, _72_2576) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _72_2580 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 1960 "FStar.TypeChecker.Tc.fst"
let t = (let _151_1174 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Recheck.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _151_1174))
in (
# 1961 "FStar.TypeChecker.Tc.fst"
let _72_2583 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1175 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _151_1175))
end else begin
()
end
in (
# 1962 "FStar.TypeChecker.Tc.fst"
let _72_2587 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_72_2587) with
| (uvs, t) -> begin
(
# 1963 "FStar.TypeChecker.Tc.fst"
let _72_2589 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1179 = (let _151_1177 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _151_1177 (FStar_String.concat ", ")))
in (let _151_1178 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _151_1179 _151_1178)))
end else begin
()
end
in (
# 1966 "FStar.TypeChecker.Tc.fst"
let _72_2593 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_72_2593) with
| (uvs, t) -> begin
(
# 1967 "FStar.TypeChecker.Tc.fst"
let _72_2597 = (FStar_Syntax_Util.arrow_formals t)
in (match (_72_2597) with
| (args, _72_2596) -> begin
(
# 1968 "FStar.TypeChecker.Tc.fst"
let _72_2600 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_72_2600) with
| (tc_types, data_types) -> begin
(
# 1969 "FStar.TypeChecker.Tc.fst"
let tcs = (FStar_List.map2 (fun _72_2604 se -> (match (_72_2604) with
| (x, _72_2603) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _72_2608, tps, _72_2611, mutuals, datas, quals, r) -> begin
(
# 1971 "FStar.TypeChecker.Tc.fst"
let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (
# 1972 "FStar.TypeChecker.Tc.fst"
let _72_2634 = (match ((let _151_1182 = (FStar_Syntax_Subst.compress ty)
in _151_1182.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 1974 "FStar.TypeChecker.Tc.fst"
let _72_2625 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_72_2625) with
| (tps, rest) -> begin
(
# 1975 "FStar.TypeChecker.Tc.fst"
let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _72_2628 -> begin
(let _151_1183 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _151_1183 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _72_2631 -> begin
([], ty)
end)
in (match (_72_2634) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _72_2636 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (
# 1987 "FStar.TypeChecker.Tc.fst"
let env_data = (FStar_TypeChecker_Env.push_univ_vars env uvs)
in (
# 1988 "FStar.TypeChecker.Tc.fst"
let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _151_1184 -> FStar_Syntax_Syntax.U_name (_151_1184))))
in (
# 1989 "FStar.TypeChecker.Tc.fst"
let env_data = (FStar_List.fold_left (fun env tc -> (FStar_TypeChecker_Env.push_sigelt_inst env tc uvs_universes)) env_data tcs)
in (
# 1990 "FStar.TypeChecker.Tc.fst"
let datas = (FStar_List.map2 (fun _72_2646 -> (match (_72_2646) with
| (t, _72_2645) -> begin
(fun _72_9 -> (match (_72_9) with
| FStar_Syntax_Syntax.Sig_datacon (l, _72_2650, _72_2652, tc, ntps, quals, mutuals, r) -> begin
(
# 1992 "FStar.TypeChecker.Tc.fst"
let ty = (match (uvs) with
| [] -> begin
t.FStar_Syntax_Syntax.sort
end
| _72_2662 -> begin
(
# 1995 "FStar.TypeChecker.Tc.fst"
let _72_2663 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1192 = (FStar_Syntax_Print.lid_to_string l)
in (let _151_1191 = (FStar_Syntax_Print.term_to_string t.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Rechecking datacon %s : %s\n" _151_1192 _151_1191)))
end else begin
()
end
in (
# 1997 "FStar.TypeChecker.Tc.fst"
let _72_2669 = (tc_tot_or_gtot_term env_data t.FStar_Syntax_Syntax.sort)
in (match (_72_2669) with
| (ty, _72_2667, g) -> begin
(
# 1998 "FStar.TypeChecker.Tc.fst"
let g = (
# 1998 "FStar.TypeChecker.Tc.fst"
let _72_2670 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _72_2670.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _72_2670.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _72_2670.FStar_TypeChecker_Env.implicits})
in (
# 1999 "FStar.TypeChecker.Tc.fst"
let _72_2673 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Subst.close_univ_vars uvs ty)))
end)))
end)
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _72_2677 -> begin
(FStar_All.failwith "Impossible")
end))
end)) data_types datas)
in (tcs, datas))))))
end))
end))
end)))
end))))))))
in (
# 2005 "FStar.TypeChecker.Tc.fst"
let _72_2687 = (FStar_All.pipe_right ses (FStar_List.partition (fun _72_10 -> (match (_72_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_72_2681) -> begin
true
end
| _72_2684 -> begin
false
end))))
in (match (_72_2687) with
| (tys, datas) -> begin
(
# 2007 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2010 "FStar.TypeChecker.Tc.fst"
let _72_2704 = (FStar_List.fold_right (fun tc _72_2693 -> (match (_72_2693) with
| (env, all_tcs, g) -> begin
(
# 2011 "FStar.TypeChecker.Tc.fst"
let _72_2697 = (tc_tycon env tc)
in (match (_72_2697) with
| (env, tc, tc_u) -> begin
(
# 2012 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (
# 2013 "FStar.TypeChecker.Tc.fst"
let _72_2699 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1196 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _151_1196))
end else begin
()
end
in (let _151_1197 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _151_1197))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_72_2704) with
| (env, tcs, g) -> begin
(
# 2020 "FStar.TypeChecker.Tc.fst"
let _72_2714 = (FStar_List.fold_right (fun se _72_2708 -> (match (_72_2708) with
| (datas, g) -> begin
(
# 2021 "FStar.TypeChecker.Tc.fst"
let _72_2711 = (tc_data env tcs se)
in (match (_72_2711) with
| (data, g') -> begin
(let _151_1200 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _151_1200))
end))
end)) datas ([], g))
in (match (_72_2714) with
| (datas, g) -> begin
(
# 2026 "FStar.TypeChecker.Tc.fst"
let _72_2717 = (let _151_1201 = (FStar_List.map Prims.fst tcs)
in (generalize_and_recheck env0 g _151_1201 datas))
in (match (_72_2717) with
| (tcs, datas) -> begin
(let _151_1203 = (let _151_1202 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _151_1202))
in FStar_Syntax_Syntax.Sig_bundle (_151_1203))
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
in (let _151_1208 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _151_1208))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(
# 2047 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2048 "FStar.TypeChecker.Tc.fst"
let se = (tc_inductive env ses quals lids)
in (let _151_1209 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _151_1209))))
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
let _72_2753 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (
# 2061 "FStar.TypeChecker.Tc.fst"
let _72_2755 = (let _151_1210 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _151_1210 Prims.ignore))
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
let _72_2770 = (let _151_1211 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _151_1211))
in (match (_72_2770) with
| (a, wp_a_src) -> begin
(
# 2073 "FStar.TypeChecker.Tc.fst"
let _72_2773 = (let _151_1212 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _151_1212))
in (match (_72_2773) with
| (b, wp_b_tgt) -> begin
(
# 2074 "FStar.TypeChecker.Tc.fst"
let wp_a_tgt = (let _151_1216 = (let _151_1215 = (let _151_1214 = (let _151_1213 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _151_1213))
in FStar_Syntax_Syntax.NT (_151_1214))
in (_151_1215)::[])
in (FStar_Syntax_Subst.subst _151_1216 wp_b_tgt))
in (
# 2075 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1221 = (let _151_1219 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1218 = (let _151_1217 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_151_1217)::[])
in (_151_1219)::_151_1218))
in (let _151_1220 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _151_1221 _151_1220)))
in (
# 2076 "FStar.TypeChecker.Tc.fst"
let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (
# 2077 "FStar.TypeChecker.Tc.fst"
let sub = (
# 2077 "FStar.TypeChecker.Tc.fst"
let _72_2777 = sub
in {FStar_Syntax_Syntax.source = _72_2777.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _72_2777.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
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
let _72_2790 = ()
in (
# 2084 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2085 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2086 "FStar.TypeChecker.Tc.fst"
let _72_2796 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_72_2796) with
| (tps, c) -> begin
(
# 2087 "FStar.TypeChecker.Tc.fst"
let _72_2800 = (tc_tparams env tps)
in (match (_72_2800) with
| (tps, env, us) -> begin
(
# 2088 "FStar.TypeChecker.Tc.fst"
let _72_2804 = (tc_comp env c)
in (match (_72_2804) with
| (c, g, u) -> begin
(
# 2089 "FStar.TypeChecker.Tc.fst"
let tags = (FStar_All.pipe_right tags (FStar_List.map (fun _72_11 -> (match (_72_11) with
| FStar_Syntax_Syntax.DefaultEffect (None) -> begin
(
# 2091 "FStar.TypeChecker.Tc.fst"
let c' = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let _151_1224 = (FStar_All.pipe_right c'.FStar_Syntax_Syntax.effect_name (fun _151_1223 -> Some (_151_1223)))
in FStar_Syntax_Syntax.DefaultEffect (_151_1224)))
end
| t -> begin
t
end))))
in (
# 2094 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 2095 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.close_comp tps c)
in (
# 2096 "FStar.TypeChecker.Tc.fst"
let _72_2815 = (let _151_1225 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _151_1225))
in (match (_72_2815) with
| (uvs, t) -> begin
(
# 2097 "FStar.TypeChecker.Tc.fst"
let _72_2834 = (match ((let _151_1227 = (let _151_1226 = (FStar_Syntax_Subst.compress t)
in _151_1226.FStar_Syntax_Syntax.n)
in (tps, _151_1227))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_72_2818, c)) -> begin
([], c)
end
| (_72_2824, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _72_2831 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_72_2834) with
| (tps, c) -> begin
(
# 2101 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_effect_abbrev ((lid, uvs, tps, c, tags, r))
in (
# 2102 "FStar.TypeChecker.Tc.fst"
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
# 2106 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2107 "FStar.TypeChecker.Tc.fst"
let _72_2845 = ()
in (
# 2108 "FStar.TypeChecker.Tc.fst"
let k = (let _151_1228 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _151_1228))
in (
# 2109 "FStar.TypeChecker.Tc.fst"
let _72_2850 = (check_and_gen env t k)
in (match (_72_2850) with
| (uvs, t) -> begin
(
# 2110 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (
# 2111 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(
# 2115 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2116 "FStar.TypeChecker.Tc.fst"
let _72_2863 = (FStar_Syntax_Util.type_u ())
in (match (_72_2863) with
| (k, _72_2862) -> begin
(
# 2117 "FStar.TypeChecker.Tc.fst"
let phi = (let _151_1229 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _151_1229 (norm env)))
in (
# 2118 "FStar.TypeChecker.Tc.fst"
let _72_2865 = (FStar_TypeChecker_Util.check_uvars r phi)
in (
# 2119 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))
in (
# 2120 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(
# 2124 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2125 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Recheck.t_unit)
in (
# 2126 "FStar.TypeChecker.Tc.fst"
let _72_2878 = (tc_term env e)
in (match (_72_2878) with
| (e, c, g1) -> begin
(
# 2127 "FStar.TypeChecker.Tc.fst"
let _72_2883 = (let _151_1233 = (let _151_1230 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Recheck.t_unit r)
in Some (_151_1230))
in (let _151_1232 = (let _151_1231 = (c.FStar_Syntax_Syntax.comp ())
in (e, _151_1231))
in (check_expected_effect env _151_1233 _151_1232)))
in (match (_72_2883) with
| (e, _72_2881, g) -> begin
(
# 2128 "FStar.TypeChecker.Tc.fst"
let _72_2884 = (let _151_1234 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _151_1234))
in (
# 2129 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, r))
in (
# 2130 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(
# 2134 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2135 "FStar.TypeChecker.Tc.fst"
let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
if (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q')) then begin
Some (q)
end else begin
(let _151_1244 = (let _151_1243 = (let _151_1242 = (let _151_1241 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Inconsistent qualifier annotations on %s" _151_1241))
in (_151_1242, r))
in FStar_Syntax_Syntax.Error (_151_1243))
in (Prims.raise _151_1244))
end
end))
in (
# 2146 "FStar.TypeChecker.Tc.fst"
let _72_2928 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _72_2905 lb -> (match (_72_2905) with
| (gen, lbs, quals_opt) -> begin
(
# 2147 "FStar.TypeChecker.Tc.fst"
let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2148 "FStar.TypeChecker.Tc.fst"
let _72_2924 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(
# 2152 "FStar.TypeChecker.Tc.fst"
let quals_opt = (check_quals_eq lbname quals_opt quals)
in (
# 2153 "FStar.TypeChecker.Tc.fst"
let _72_2919 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _72_2918 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _151_1247 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _151_1247, quals_opt))))
end)
in (match (_72_2924) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_72_2928) with
| (should_generalize, lbs', quals_opt) -> begin
(
# 2162 "FStar.TypeChecker.Tc.fst"
let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _72_12 -> (match (_72_12) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _72_2937 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (
# 2169 "FStar.TypeChecker.Tc.fst"
let lbs' = (FStar_List.rev lbs')
in (
# 2172 "FStar.TypeChecker.Tc.fst"
let e = (let _151_1251 = (let _151_1250 = (let _151_1249 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _151_1249))
in FStar_Syntax_Syntax.Tm_let (_151_1250))
in (FStar_Syntax_Syntax.mk _151_1251 None r))
in (
# 2175 "FStar.TypeChecker.Tc.fst"
let _72_2971 = (match ((tc_maybe_toplevel_term (
# 2175 "FStar.TypeChecker.Tc.fst"
let _72_2941 = env
in {FStar_TypeChecker_Env.solver = _72_2941.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _72_2941.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _72_2941.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _72_2941.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _72_2941.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _72_2941.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _72_2941.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _72_2941.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _72_2941.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _72_2941.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _72_2941.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _72_2941.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _72_2941.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _72_2941.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _72_2941.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _72_2941.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _72_2941.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _72_2941.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _72_2941.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _72_2948; FStar_Syntax_Syntax.pos = _72_2946; FStar_Syntax_Syntax.vars = _72_2944}, _72_2955, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(
# 2178 "FStar.TypeChecker.Tc.fst"
let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_72_2959, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _72_2965 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _72_2968 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_72_2971) with
| (se, lbs) -> begin
(
# 2185 "FStar.TypeChecker.Tc.fst"
let _72_2977 = if (log env) then begin
(let _151_1257 = (let _151_1256 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 2187 "FStar.TypeChecker.Tc.fst"
let should_log = (match ((let _151_1253 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _151_1253))) with
| None -> begin
true
end
| _72_2975 -> begin
false
end)
in if should_log then begin
(let _151_1255 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _151_1254 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _151_1255 _151_1254)))
end else begin
""
end))))
in (FStar_All.pipe_right _151_1256 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _151_1257))
end else begin
()
end
in (
# 2194 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end))))
end))

# 2198 "FStar.TypeChecker.Tc.fst"
let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (
# 2223 "FStar.TypeChecker.Tc.fst"
let private_or_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun x -> ((x = FStar_Syntax_Syntax.Private) || (x = FStar_Syntax_Syntax.Abstract))))))
in (
# 2224 "FStar.TypeChecker.Tc.fst"
let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _72_2994 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_72_2996) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _72_3007, _72_3009) -> begin
if (private_or_abstract quals) then begin
(FStar_List.fold_right (fun se _72_3015 -> (match (_72_3015) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _72_3021, _72_3023, quals, r) -> begin
(
# 2238 "FStar.TypeChecker.Tc.fst"
let dec = (let _151_1273 = (let _151_1272 = (let _151_1271 = (let _151_1270 = (let _151_1269 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _151_1269))
in FStar_Syntax_Syntax.Tm_arrow (_151_1270))
in (FStar_Syntax_Syntax.mk _151_1271 None r))
in (l, us, _151_1272, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_151_1273))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _72_3033, _72_3035, _72_3037, _72_3039, r) -> begin
(
# 2241 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _72_3045 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_72_3047, _72_3049, quals, _72_3052) -> begin
if (private_or_abstract quals) then begin
([], hidden)
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, us, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) then begin
((FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r)))::[], (l)::hidden)
end else begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _72_13 -> (match (_72_13) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _72_3071 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_72_3073) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _72_3089, _72_3091, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
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
if (private_or_abstract quals) then begin
(let _151_1278 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _151_1277 = (let _151_1276 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (_151_1276, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_151_1277)))))
in (_151_1278, hidden))
end else begin
((se)::[], hidden)
end
end))))

# 2283 "FStar.TypeChecker.Tc.fst"
let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (
# 2284 "FStar.TypeChecker.Tc.fst"
let _72_3129 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _72_3110 se -> (match (_72_3110) with
| (ses, exports, env, hidden) -> begin
(
# 2286 "FStar.TypeChecker.Tc.fst"
let _72_3112 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1285 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _151_1285))
end else begin
()
end
in (
# 2289 "FStar.TypeChecker.Tc.fst"
let _72_3116 = (tc_decl env se)
in (match (_72_3116) with
| (se, env) -> begin
(
# 2291 "FStar.TypeChecker.Tc.fst"
let _72_3117 = if ((FStar_ST.read FStar_Options.log_types) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _151_1286 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _151_1286))
end else begin
()
end
in (
# 2294 "FStar.TypeChecker.Tc.fst"
let _72_3119 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (
# 2296 "FStar.TypeChecker.Tc.fst"
let _72_3123 = (for_export hidden se)
in (match (_72_3123) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_72_3129) with
| (ses, exports, env, _72_3128) -> begin
(let _151_1287 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _151_1287, env))
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
let _72_3134 = env
in (let _151_1292 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _72_3134.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _72_3134.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _72_3134.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _72_3134.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _72_3134.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _72_3134.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _72_3134.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _72_3134.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _72_3134.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _72_3134.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _72_3134.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _72_3134.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _72_3134.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _72_3134.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _72_3134.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _72_3134.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _151_1292; FStar_TypeChecker_Env.default_effects = _72_3134.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _72_3134.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _72_3134.FStar_TypeChecker_Env.use_bv_sorts}))
in (
# 2305 "FStar.TypeChecker.Tc.fst"
let _72_3137 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (
# 2306 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (
# 2307 "FStar.TypeChecker.Tc.fst"
let _72_3143 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_72_3143) with
| (ses, exports, env) -> begin
((
# 2308 "FStar.TypeChecker.Tc.fst"
let _72_3144 = modul
in {FStar_Syntax_Syntax.name = _72_3144.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _72_3144.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _72_3144.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))

# 2310 "FStar.TypeChecker.Tc.fst"
let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (
# 2311 "FStar.TypeChecker.Tc.fst"
let _72_3152 = (tc_decls env decls)
in (match (_72_3152) with
| (ses, exports, env) -> begin
(
# 2312 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2312 "FStar.TypeChecker.Tc.fst"
let _72_3153 = modul
in {FStar_Syntax_Syntax.name = _72_3153.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _72_3153.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _72_3153.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))

# 2315 "FStar.TypeChecker.Tc.fst"
let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (
# 2316 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2316 "FStar.TypeChecker.Tc.fst"
let _72_3159 = modul
in {FStar_Syntax_Syntax.name = _72_3159.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _72_3159.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (
# 2317 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.finish_module env modul)
in (
# 2318 "FStar.TypeChecker.Tc.fst"
let _72_3169 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(
# 2320 "FStar.TypeChecker.Tc.fst"
let _72_3163 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (
# 2321 "FStar.TypeChecker.Tc.fst"
let _72_3165 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (
# 2322 "FStar.TypeChecker.Tc.fst"
let _72_3167 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _151_1305 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _151_1305 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))

# 2327 "FStar.TypeChecker.Tc.fst"
let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2328 "FStar.TypeChecker.Tc.fst"
let _72_3176 = (tc_partial_modul env modul)
in (match (_72_3176) with
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
let _72_3183 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env elt)
in env)))
in (
# 2337 "FStar.TypeChecker.Tc.fst"
let en = (FStar_TypeChecker_Env.set_current_module en m.FStar_Syntax_Syntax.name)
in (let _151_1318 = (FStar_List.fold_left do_sigelt en m.FStar_Syntax_Syntax.exports)
in (FStar_TypeChecker_Env.finish_module _151_1318 m)))))

# 2340 "FStar.TypeChecker.Tc.fst"
let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 2341 "FStar.TypeChecker.Tc.fst"
let _72_3188 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _151_1323 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _151_1323))
end else begin
()
end
in (
# 2343 "FStar.TypeChecker.Tc.fst"
let env = (
# 2343 "FStar.TypeChecker.Tc.fst"
let _72_3190 = env
in {FStar_TypeChecker_Env.solver = _72_3190.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _72_3190.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _72_3190.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _72_3190.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _72_3190.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _72_3190.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _72_3190.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _72_3190.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _72_3190.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _72_3190.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _72_3190.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _72_3190.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _72_3190.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _72_3190.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _72_3190.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _72_3190.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _72_3190.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _72_3190.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _72_3190.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _72_3190.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 2344 "FStar.TypeChecker.Tc.fst"
let _72_3196 = (tc_tot_or_gtot_term env e)
in (match (_72_3196) with
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
let _72_3199 = if ((let _151_1328 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _151_1328)) <> 0) then begin
(let _151_1329 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _151_1329))
end else begin
()
end
in (
# 2352 "FStar.TypeChecker.Tc.fst"
let _72_3203 = (tc_modul env m)
in (match (_72_3203) with
| (m, env) -> begin
(
# 2353 "FStar.TypeChecker.Tc.fst"
let _72_3204 = if (FStar_Options.should_dump m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _151_1330 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _151_1330))
end else begin
()
end
in (m, env))
end))))




