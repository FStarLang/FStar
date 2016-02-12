
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
let _72_1593 = (
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
let _72_1588 = (match ((eqs, when_condition)) with
| (None, None) -> begin
(c, g_when, g_branch)
end
| (Some (f), None) -> begin
(
# 1089 "FStar.TypeChecker.Tc.fst"
let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1090 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _151_681 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _151_680 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (let _151_679 = (FStar_TypeChecker_Rel.imp_guard g g_branch)
in (_151_681, _151_680, _151_679))))))
end
| (Some (f), Some (w)) -> begin
(
# 1096 "FStar.TypeChecker.Tc.fst"
let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1097 "FStar.TypeChecker.Tc.fst"
let g_fw = (let _151_682 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_151_682))
in (let _151_687 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _151_686 = (let _151_683 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _151_683 g_when))
in (let _151_685 = (let _151_684 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_fw)
in (FStar_TypeChecker_Rel.imp_guard _151_684 g_branch))
in (_151_687, _151_686, _151_685))))))
end
| (None, Some (w)) -> begin
(
# 1103 "FStar.TypeChecker.Tc.fst"
let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (
# 1104 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _151_689 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (let _151_688 = (FStar_TypeChecker_Rel.imp_guard g g_branch)
in (_151_689, g_when, _151_688)))))
end)
in (match (_72_1588) with
| (c_weak, g_when_weak, g_branch_weak) -> begin
(
# 1110 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _151_692 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _151_691 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (let _151_690 = (FStar_TypeChecker_Rel.close_guard binders g_branch_weak)
in (_151_692, _151_691, _151_690)))))
end)))
in (match (_72_1593) with
| (c, g_when, g_branch) -> begin
(
# 1128 "FStar.TypeChecker.Tc.fst"
let branch_guard = (
# 1130 "FStar.TypeChecker.Tc.fst"
let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (
# 1131 "FStar.TypeChecker.Tc.fst"
let discriminate = (fun scrutinee_tm f -> if ((let _151_702 = (let _151_701 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _151_701))
in (FStar_List.length _151_702)) > 1) then begin
(
# 1134 "FStar.TypeChecker.Tc.fst"
let disc = (let _151_703 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar None _151_703 (FStar_Ident.range_of_lid f.FStar_Syntax_Syntax.v)))
in (
# 1135 "FStar.TypeChecker.Tc.fst"
let disc = (let _151_705 = (let _151_704 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_151_704)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _151_705 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _151_706 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_151_706)::[])))
end else begin
[]
end)
in (
# 1139 "FStar.TypeChecker.Tc.fst"
let fail = (fun _72_1603 -> (match (()) with
| () -> begin
(let _151_712 = (let _151_711 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _151_710 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _151_709 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _151_711 _151_710 _151_709))))
in (FStar_All.failwith _151_712))
end))
in (
# 1145 "FStar.TypeChecker.Tc.fst"
let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (f, _72_1608) -> begin
f
end
| FStar_Syntax_Syntax.Tm_uinst (t, _72_1613) -> begin
(head_constructor t)
end
| _72_1617 -> begin
(fail ())
end))
in (
# 1150 "FStar.TypeChecker.Tc.fst"
let pat_exp = (let _151_715 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _151_715 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_72_1642) -> begin
(let _151_720 = (let _151_719 = (let _151_718 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _151_717 = (let _151_716 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_151_716)::[])
in (_151_718)::_151_717))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _151_719 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_151_720)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 1159 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _151_721 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _151_721))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 1164 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(
# 1167 "FStar.TypeChecker.Tc.fst"
let sub_term_guards = (let _151_727 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _72_1660 -> (match (_72_1660) with
| (ei, _72_1659) -> begin
(
# 1168 "FStar.TypeChecker.Tc.fst"
let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (
# 1169 "FStar.TypeChecker.Tc.fst"
let sub_term = (let _151_726 = (FStar_Syntax_Syntax.fvar None projector f.FStar_Syntax_Syntax.p)
in (let _151_725 = (let _151_724 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_151_724)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _151_726 _151_725 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei)))
end))))
in (FStar_All.pipe_right _151_727 FStar_List.flatten))
in (let _151_728 = (discriminate scrutinee_tm f)
in (FStar_List.append _151_728 sub_term_guards)))
end)
end
| _72_1665 -> begin
[]
end))))))
in (
# 1175 "FStar.TypeChecker.Tc.fst"
let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid scrutinee_tm.FStar_Syntax_Syntax.pos)
end else begin
(
# 1178 "FStar.TypeChecker.Tc.fst"
let t = (let _151_733 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _151_733))
in (
# 1179 "FStar.TypeChecker.Tc.fst"
let _72_1673 = (FStar_Syntax_Util.type_u ())
in (match (_72_1673) with
| (k, _72_1672) -> begin
(
# 1180 "FStar.TypeChecker.Tc.fst"
let _72_1679 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_72_1679) with
| (t, _72_1676, _72_1678) -> begin
t
end))
end)))
end)
in (
# 1184 "FStar.TypeChecker.Tc.fst"
let branch_guard = (let _151_734 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _151_734 FStar_Syntax_Util.mk_disj_l))
in (
# 1187 "FStar.TypeChecker.Tc.fst"
let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
in (
# 1193 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (
# 1195 "FStar.TypeChecker.Tc.fst"
let _72_1687 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_735 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _151_735))
end else begin
()
end
in (let _151_736 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_151_736, branch_guard, c, guard)))))
end)))
end))
end))
end))
end)))))
end))
end)))
and check_top_level_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1209 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1212 "FStar.TypeChecker.Tc.fst"
let _72_1704 = (check_let_bound_def true env lb)
in (match (_72_1704) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(
# 1215 "FStar.TypeChecker.Tc.fst"
let _72_1716 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(
# 1218 "FStar.TypeChecker.Tc.fst"
let g1 = (let _151_739 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _151_739 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1219 "FStar.TypeChecker.Tc.fst"
let _72_1711 = (let _151_743 = (let _151_742 = (let _151_741 = (let _151_740 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _151_740))
in (_151_741)::[])
in (FStar_TypeChecker_Util.generalize env _151_742))
in (FStar_List.hd _151_743))
in (match (_72_1711) with
| (_72_1707, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_72_1716) with
| (g1, e1, univ_vars, c1) -> begin
(
# 1223 "FStar.TypeChecker.Tc.fst"
let _72_1726 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(
# 1225 "FStar.TypeChecker.Tc.fst"
let _72_1719 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_72_1719) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(
# 1228 "FStar.TypeChecker.Tc.fst"
let _72_1720 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _151_744 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _151_744 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _151_745 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_151_745, c1)))
end
end))
end else begin
(
# 1232 "FStar.TypeChecker.Tc.fst"
let _72_1722 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _151_746 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _151_746)))
end
in (match (_72_1726) with
| (e2, c1) -> begin
(
# 1237 "FStar.TypeChecker.Tc.fst"
let cres = (let _151_747 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Recheck.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_747))
in (
# 1238 "FStar.TypeChecker.Tc.fst"
let _72_1728 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Recheck.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1240 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _151_748 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Recheck.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_151_748, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _72_1732 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1257 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1260 "FStar.TypeChecker.Tc.fst"
let env = (
# 1260 "FStar.TypeChecker.Tc.fst"
let _72_1743 = env
in {FStar_TypeChecker_Env.solver = _72_1743.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _72_1743.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _72_1743.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _72_1743.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _72_1743.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _72_1743.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _72_1743.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _72_1743.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _72_1743.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _72_1743.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _72_1743.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _72_1743.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _72_1743.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _72_1743.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _72_1743.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _72_1743.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _72_1743.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _72_1743.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _72_1743.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _72_1743.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1261 "FStar.TypeChecker.Tc.fst"
let _72_1752 = (let _151_752 = (let _151_751 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _151_751 Prims.fst))
in (check_let_bound_def false _151_752 lb))
in (match (_72_1752) with
| (e1, _72_1748, c1, g1, annotated) -> begin
(
# 1262 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (
# 1263 "FStar.TypeChecker.Tc.fst"
let x = (
# 1263 "FStar.TypeChecker.Tc.fst"
let _72_1754 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _72_1754.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _72_1754.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (
# 1264 "FStar.TypeChecker.Tc.fst"
let _72_1759 = (let _151_754 = (let _151_753 = (FStar_Syntax_Syntax.mk_binder x)
in (_151_753)::[])
in (FStar_Syntax_Subst.open_term _151_754 e2))
in (match (_72_1759) with
| (xb, e2) -> begin
(
# 1265 "FStar.TypeChecker.Tc.fst"
let xbinder = (FStar_List.hd xb)
in (
# 1266 "FStar.TypeChecker.Tc.fst"
let x = (Prims.fst xbinder)
in (
# 1267 "FStar.TypeChecker.Tc.fst"
let _72_1765 = (let _151_755 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _151_755 e2))
in (match (_72_1765) with
| (e2, c2, g2) -> begin
(
# 1268 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (x), c2))
in (
# 1269 "FStar.TypeChecker.Tc.fst"
let e = (let _151_758 = (let _151_757 = (let _151_756 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _151_756))
in FStar_Syntax_Syntax.Tm_let (_151_757))
in (FStar_Syntax_Syntax.mk _151_758 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 1270 "FStar.TypeChecker.Tc.fst"
let x_eq_e1 = (let _151_761 = (let _151_760 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _151_760 e1))
in (FStar_All.pipe_left (fun _151_759 -> FStar_TypeChecker_Common.NonTrivial (_151_759)) _151_761))
in (
# 1271 "FStar.TypeChecker.Tc.fst"
let g2 = (let _151_763 = (let _151_762 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _151_762 g2))
in (FStar_TypeChecker_Rel.close_guard xb _151_763))
in (
# 1273 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if annotated then begin
(e, cres, guard)
end else begin
(
# 1277 "FStar.TypeChecker.Tc.fst"
let _72_1771 = (check_no_escape env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end)))))
end))))
end))))
end)))
end
| _72_1774 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1286 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1289 "FStar.TypeChecker.Tc.fst"
let _72_1786 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_72_1786) with
| (lbs, e2) -> begin
(
# 1291 "FStar.TypeChecker.Tc.fst"
let _72_1789 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_72_1789) with
| (env0, topt) -> begin
(
# 1292 "FStar.TypeChecker.Tc.fst"
let _72_1792 = (build_let_rec_env true env0 lbs)
in (match (_72_1792) with
| (lbs, rec_env) -> begin
(
# 1293 "FStar.TypeChecker.Tc.fst"
let _72_1795 = (check_let_recs rec_env lbs)
in (match (_72_1795) with
| (lbs, g_lbs) -> begin
(
# 1294 "FStar.TypeChecker.Tc.fst"
let g_lbs = (let _151_766 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _151_766 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1296 "FStar.TypeChecker.Tc.fst"
let all_lb_names = (let _151_769 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _151_769 (fun _151_768 -> Some (_151_768))))
in (
# 1298 "FStar.TypeChecker.Tc.fst"
let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(
# 1304 "FStar.TypeChecker.Tc.fst"
let ecs = (let _151_773 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _151_772 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _151_772)))))
in (FStar_TypeChecker_Util.generalize env _151_773))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _72_1806 -> (match (_72_1806) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (
# 1311 "FStar.TypeChecker.Tc.fst"
let cres = (let _151_775 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Recheck.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_775))
in (
# 1312 "FStar.TypeChecker.Tc.fst"
let _72_1809 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Recheck.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1314 "FStar.TypeChecker.Tc.fst"
let _72_1813 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_72_1813) with
| (lbs, e2) -> begin
(let _151_777 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Recheck.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _151_776 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_151_777, cres, _151_776)))
end)))))))
end))
end))
end))
end))
end
| _72_1815 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1325 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1328 "FStar.TypeChecker.Tc.fst"
let _72_1827 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_72_1827) with
| (lbs, e2) -> begin
(
# 1330 "FStar.TypeChecker.Tc.fst"
let _72_1830 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_72_1830) with
| (env0, topt) -> begin
(
# 1331 "FStar.TypeChecker.Tc.fst"
let _72_1833 = (build_let_rec_env false env0 lbs)
in (match (_72_1833) with
| (lbs, rec_env) -> begin
(
# 1332 "FStar.TypeChecker.Tc.fst"
let _72_1836 = (check_let_recs rec_env lbs)
in (match (_72_1836) with
| (lbs, g_lbs) -> begin
(
# 1334 "FStar.TypeChecker.Tc.fst"
let _72_1854 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _72_1839 _72_1848 -> (match ((_72_1839, _72_1848)) with
| ((bvs, env), {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _72_1846; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _72_1843; FStar_Syntax_Syntax.lbdef = _72_1841}) -> begin
(
# 1335 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env x ([], t))
in (let _151_783 = (let _151_782 = (
# 1336 "FStar.TypeChecker.Tc.fst"
let _72_1850 = (FStar_Util.left x)
in {FStar_Syntax_Syntax.ppname = _72_1850.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _72_1850.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (_151_782)::bvs)
in (_151_783, env)))
end)) ([], env)))
in (match (_72_1854) with
| (bvs, env) -> begin
(
# 1337 "FStar.TypeChecker.Tc.fst"
let bvs = (FStar_List.rev bvs)
in (
# 1339 "FStar.TypeChecker.Tc.fst"
let _72_1859 = (tc_term env e2)
in (match (_72_1859) with
| (e2, cres, g2) -> begin
(
# 1340 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (
# 1341 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (
# 1342 "FStar.TypeChecker.Tc.fst"
let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (
# 1343 "FStar.TypeChecker.Tc.fst"
let cres = (
# 1343 "FStar.TypeChecker.Tc.fst"
let _72_1863 = cres
in {FStar_Syntax_Syntax.eff_name = _72_1863.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _72_1863.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _72_1863.FStar_Syntax_Syntax.comp})
in (
# 1345 "FStar.TypeChecker.Tc.fst"
let _72_1868 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_72_1868) with
| (lbs, e2) -> begin
(
# 1346 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_72_1871) -> begin
(e, cres, guard)
end
| None -> begin
(
# 1350 "FStar.TypeChecker.Tc.fst"
let _72_1874 = (check_no_escape env bvs tres)
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
| _72_1877 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (
# 1361 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1362 "FStar.TypeChecker.Tc.fst"
let _72_1910 = (FStar_List.fold_left (fun _72_1884 lb -> (match (_72_1884) with
| (lbs, env) -> begin
(
# 1363 "FStar.TypeChecker.Tc.fst"
let _72_1889 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_72_1889) with
| (univ_vars, t, check_t) -> begin
(
# 1364 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (
# 1365 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (
# 1366 "FStar.TypeChecker.Tc.fst"
let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(
# 1371 "FStar.TypeChecker.Tc.fst"
let _72_1898 = (let _151_790 = (let _151_789 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _151_789))
in (tc_check_tot_or_gtot_term (
# 1371 "FStar.TypeChecker.Tc.fst"
let _72_1892 = env0
in {FStar_TypeChecker_Env.solver = _72_1892.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _72_1892.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _72_1892.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _72_1892.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _72_1892.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _72_1892.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _72_1892.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _72_1892.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _72_1892.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _72_1892.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _72_1892.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _72_1892.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _72_1892.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _72_1892.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _72_1892.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _72_1892.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _72_1892.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _72_1892.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _72_1892.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _72_1892.FStar_TypeChecker_Env.use_bv_sorts}) t _151_790))
in (match (_72_1898) with
| (t, _72_1896, g) -> begin
(
# 1372 "FStar.TypeChecker.Tc.fst"
let _72_1899 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (
# 1374 "FStar.TypeChecker.Tc.fst"
let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(
# 1376 "FStar.TypeChecker.Tc.fst"
let _72_1902 = env
in {FStar_TypeChecker_Env.solver = _72_1902.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _72_1902.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _72_1902.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _72_1902.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _72_1902.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _72_1902.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _72_1902.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _72_1902.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _72_1902.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _72_1902.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _72_1902.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _72_1902.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _72_1902.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _72_1902.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _72_1902.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _72_1902.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _72_1902.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _72_1902.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _72_1902.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _72_1902.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (
# 1378 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1378 "FStar.TypeChecker.Tc.fst"
let _72_1905 = lb
in {FStar_Syntax_Syntax.lbname = _72_1905.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _72_1905.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_72_1910) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (
# 1385 "FStar.TypeChecker.Tc.fst"
let _72_1923 = (let _151_795 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 1386 "FStar.TypeChecker.Tc.fst"
let _72_1917 = (let _151_794 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _151_794 lb.FStar_Syntax_Syntax.lbdef))
in (match (_72_1917) with
| (e, c, g) -> begin
(
# 1387 "FStar.TypeChecker.Tc.fst"
let _72_1918 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1389 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _151_795 FStar_List.unzip))
in (match (_72_1923) with
| (lbs, gs) -> begin
(
# 1391 "FStar.TypeChecker.Tc.fst"
let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (
# 1405 "FStar.TypeChecker.Tc.fst"
let _72_1931 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_72_1931) with
| (env1, _72_1930) -> begin
(
# 1406 "FStar.TypeChecker.Tc.fst"
let e1 = lb.FStar_Syntax_Syntax.lbdef
in (
# 1409 "FStar.TypeChecker.Tc.fst"
let _72_1937 = (check_lbtyp top_level env lb)
in (match (_72_1937) with
| (topt, wf_annot, univ_vars, env1) -> begin
(
# 1411 "FStar.TypeChecker.Tc.fst"
let _72_1938 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1415 "FStar.TypeChecker.Tc.fst"
let _72_1945 = (tc_maybe_toplevel_term (
# 1415 "FStar.TypeChecker.Tc.fst"
let _72_1940 = env1
in {FStar_TypeChecker_Env.solver = _72_1940.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _72_1940.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _72_1940.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _72_1940.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _72_1940.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _72_1940.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _72_1940.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _72_1940.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _72_1940.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _72_1940.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _72_1940.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _72_1940.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _72_1940.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _72_1940.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _72_1940.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _72_1940.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _72_1940.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _72_1940.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _72_1940.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _72_1940.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_72_1945) with
| (e1, c1, g1) -> begin
(
# 1418 "FStar.TypeChecker.Tc.fst"
let _72_1949 = (let _151_802 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _72_1946 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _151_802 e1 c1 wf_annot))
in (match (_72_1949) with
| (c1, guard_f) -> begin
(
# 1421 "FStar.TypeChecker.Tc.fst"
let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (
# 1423 "FStar.TypeChecker.Tc.fst"
let _72_1951 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _151_803 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _151_803))
end else begin
()
end
in (let _151_804 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _151_804))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (
# 1435 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 1438 "FStar.TypeChecker.Tc.fst"
let _72_1958 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _72_1961 -> begin
(
# 1442 "FStar.TypeChecker.Tc.fst"
let _72_1964 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_72_1964) with
| (univ_vars, t) -> begin
(
# 1443 "FStar.TypeChecker.Tc.fst"
let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _151_808 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _151_808))
end else begin
(
# 1450 "FStar.TypeChecker.Tc.fst"
let _72_1969 = (FStar_Syntax_Util.type_u ())
in (match (_72_1969) with
| (k, _72_1968) -> begin
(
# 1451 "FStar.TypeChecker.Tc.fst"
let _72_1974 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_72_1974) with
| (t, _72_1972, g) -> begin
(
# 1452 "FStar.TypeChecker.Tc.fst"
let _72_1975 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _151_811 = (let _151_809 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _151_809))
in (let _151_810 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _151_811 _151_810)))
end else begin
()
end
in (
# 1456 "FStar.TypeChecker.Tc.fst"
let t = (norm env1 t)
in (let _151_812 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _151_812))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _72_1981 -> (match (_72_1981) with
| (x, imp) -> begin
(
# 1461 "FStar.TypeChecker.Tc.fst"
let _72_1984 = (FStar_Syntax_Util.type_u ())
in (match (_72_1984) with
| (tu, u) -> begin
(
# 1462 "FStar.TypeChecker.Tc.fst"
let _72_1989 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_72_1989) with
| (t, _72_1987, g) -> begin
(
# 1463 "FStar.TypeChecker.Tc.fst"
let x = ((
# 1463 "FStar.TypeChecker.Tc.fst"
let _72_1990 = x
in {FStar_Syntax_Syntax.ppname = _72_1990.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _72_1990.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (
# 1464 "FStar.TypeChecker.Tc.fst"
let _72_1993 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_816 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _151_815 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _151_816 _151_815)))
end else begin
()
end
in (let _151_817 = (maybe_push_binding env x)
in (x, _151_817, g, u))))
end))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe Prims.list) = (fun env bs -> (
# 1469 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_TypeChecker_Rel.trivial_guard, [])
end
| b::bs -> begin
(
# 1472 "FStar.TypeChecker.Tc.fst"
let _72_2008 = (tc_binder env b)
in (match (_72_2008) with
| (b, env', g, u) -> begin
(
# 1473 "FStar.TypeChecker.Tc.fst"
let _72_2013 = (aux env' bs)
in (match (_72_2013) with
| (bs, env', g', us) -> begin
(let _151_825 = (let _151_824 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _151_824))
in ((b)::bs, env', _151_825, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (
# 1478 "FStar.TypeChecker.Tc.fst"
let tc_args = (fun env args -> (FStar_List.fold_right (fun _72_2021 _72_2024 -> (match ((_72_2021, _72_2024)) with
| ((t, imp), (args, g)) -> begin
(
# 1482 "FStar.TypeChecker.Tc.fst"
let _72_2029 = (tc_term env t)
in (match (_72_2029) with
| (t, _72_2027, g') -> begin
(let _151_834 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _151_834))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _72_2033 -> (match (_72_2033) with
| (pats, g) -> begin
(
# 1485 "FStar.TypeChecker.Tc.fst"
let _72_2036 = (tc_args env p)
in (match (_72_2036) with
| (args, g') -> begin
(let _151_837 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _151_837))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1490 "FStar.TypeChecker.Tc.fst"
let _72_2042 = (tc_maybe_toplevel_term env e)
in (match (_72_2042) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(
# 1493 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (
# 1494 "FStar.TypeChecker.Tc.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 1495 "FStar.TypeChecker.Tc.fst"
let _72_2045 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_840 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _151_840))
end else begin
()
end
in (
# 1496 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 1497 "FStar.TypeChecker.Tc.fst"
let _72_2050 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _151_841 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_151_841, false))
end else begin
(let _151_842 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_151_842, true))
end
in (match (_72_2050) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _151_843 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _151_843))
end
| _72_2054 -> begin
if allow_ghost then begin
(let _151_846 = (let _151_845 = (let _151_844 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_151_844, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_151_845))
in (Prims.raise _151_846))
end else begin
(let _151_849 = (let _151_848 = (let _151_847 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_151_847, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_151_848))
in (Prims.raise _151_849))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 1511 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))

# 1515 "FStar.TypeChecker.Tc.fst"
let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (
# 1516 "FStar.TypeChecker.Tc.fst"
let _72_2064 = (tc_tot_or_gtot_term env t)
in (match (_72_2064) with
| (t, c, g) -> begin
(
# 1517 "FStar.TypeChecker.Tc.fst"
let _72_2065 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))

# 1520 "FStar.TypeChecker.Tc.fst"
let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (
# 1521 "FStar.TypeChecker.Tc.fst"
let _72_2073 = (tc_check_tot_or_gtot_term env t k)
in (match (_72_2073) with
| (t, c, g) -> begin
(
# 1522 "FStar.TypeChecker.Tc.fst"
let _72_2074 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))

# 1525 "FStar.TypeChecker.Tc.fst"
let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _151_869 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _151_869)))

# 1528 "FStar.TypeChecker.Tc.fst"
let check_nogen = (fun env t k -> (
# 1529 "FStar.TypeChecker.Tc.fst"
let t = (tc_check_trivial_guard env t k)
in (let _151_873 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _151_873))))

# 1532 "FStar.TypeChecker.Tc.fst"
let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (
# 1533 "FStar.TypeChecker.Tc.fst"
let _72_2089 = (tc_binders env tps)
in (match (_72_2089) with
| (tps, env, g, us) -> begin
(
# 1534 "FStar.TypeChecker.Tc.fst"
let _72_2090 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))

# 1537 "FStar.TypeChecker.Tc.fst"
let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (
# 1538 "FStar.TypeChecker.Tc.fst"
let fail = (fun _72_2096 -> (match (()) with
| () -> begin
(let _151_888 = (let _151_887 = (let _151_886 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_151_886, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_151_887))
in (Prims.raise _151_888))
end))
in (
# 1539 "FStar.TypeChecker.Tc.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1542 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _72_2113)::(wp, _72_2109)::(_wlp, _72_2105)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _72_2117 -> begin
(fail ())
end))
end
| _72_2119 -> begin
(fail ())
end))))

# 1549 "FStar.TypeChecker.Tc.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 1552 "FStar.TypeChecker.Tc.fst"
let _72_2126 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_72_2126) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _72_2128 -> begin
(
# 1555 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow binders c)
in (
# 1556 "FStar.TypeChecker.Tc.fst"
let _72_2132 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_72_2132) with
| (uvs, t') -> begin
(match ((let _151_895 = (FStar_Syntax_Subst.compress t')
in _151_895.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _72_2138 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 1561 "FStar.TypeChecker.Tc.fst"
let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (
# 1562 "FStar.TypeChecker.Tc.fst"
let fail = (fun t -> (let _151_904 = (let _151_903 = (let _151_902 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env ed.FStar_Syntax_Syntax.mname t)
in (_151_902, (FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname)))
in FStar_Syntax_Syntax.Error (_151_903))
in (Prims.raise _151_904)))
in (
# 1563 "FStar.TypeChecker.Tc.fst"
let _72_2167 = (match ((let _151_905 = (FStar_Syntax_Subst.compress ed.FStar_Syntax_Syntax.signature)
in _151_905.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1565 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _72_2158)::(wp, _72_2154)::(_wlp, _72_2150)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _72_2162 -> begin
(fail ed.FStar_Syntax_Syntax.signature)
end))
end
| _72_2164 -> begin
(fail ed.FStar_Syntax_Syntax.signature)
end)
in (match (_72_2167) with
| (a, wp) -> begin
(
# 1571 "FStar.TypeChecker.Tc.fst"
let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _72_2170 -> begin
(
# 1575 "FStar.TypeChecker.Tc.fst"
let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (
# 1576 "FStar.TypeChecker.Tc.fst"
let op = (fun ts -> (
# 1577 "FStar.TypeChecker.Tc.fst"
let _72_2174 = ()
in (
# 1578 "FStar.TypeChecker.Tc.fst"
let t0 = (Prims.snd ts)
in (
# 1579 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (
# 1581 "FStar.TypeChecker.Tc.fst"
let _72_2178 = ed
in (let _151_920 = (op ed.FStar_Syntax_Syntax.ret)
in (let _151_919 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _151_918 = (op ed.FStar_Syntax_Syntax.bind_wlp)
in (let _151_917 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _151_916 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _151_915 = (op ed.FStar_Syntax_Syntax.ite_wlp)
in (let _151_914 = (op ed.FStar_Syntax_Syntax.wp_binop)
in (let _151_913 = (op ed.FStar_Syntax_Syntax.wp_as_type)
in (let _151_912 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _151_911 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _151_910 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _151_909 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _151_908 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _72_2178.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _72_2178.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _72_2178.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _72_2178.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _72_2178.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _151_920; FStar_Syntax_Syntax.bind_wp = _151_919; FStar_Syntax_Syntax.bind_wlp = _151_918; FStar_Syntax_Syntax.if_then_else = _151_917; FStar_Syntax_Syntax.ite_wp = _151_916; FStar_Syntax_Syntax.ite_wlp = _151_915; FStar_Syntax_Syntax.wp_binop = _151_914; FStar_Syntax_Syntax.wp_as_type = _151_913; FStar_Syntax_Syntax.close_wp = _151_912; FStar_Syntax_Syntax.assert_p = _151_911; FStar_Syntax_Syntax.assume_p = _151_910; FStar_Syntax_Syntax.null_wp = _151_909; FStar_Syntax_Syntax.trivial = _151_908}))))))))))))))))
end)
in (ed, a, wp))
end))))

# 1597 "FStar.TypeChecker.Tc.fst"
let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (
# 1598 "FStar.TypeChecker.Tc.fst"
let _72_2183 = ()
in (
# 1599 "FStar.TypeChecker.Tc.fst"
let _72_2187 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_72_2187) with
| (binders, signature) -> begin
(
# 1600 "FStar.TypeChecker.Tc.fst"
let _72_2192 = (tc_tparams env0 binders)
in (match (_72_2192) with
| (binders, env, _72_2191) -> begin
(
# 1601 "FStar.TypeChecker.Tc.fst"
let _72_2196 = (tc_trivial_guard env signature)
in (match (_72_2196) with
| (signature, _72_2195) -> begin
(
# 1602 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1602 "FStar.TypeChecker.Tc.fst"
let _72_2197 = ed
in {FStar_Syntax_Syntax.qualifiers = _72_2197.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _72_2197.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _72_2197.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _72_2197.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _72_2197.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _72_2197.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = _72_2197.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _72_2197.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _72_2197.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = _72_2197.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _72_2197.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _72_2197.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _72_2197.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _72_2197.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _72_2197.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _72_2197.FStar_Syntax_Syntax.trivial})
in (
# 1605 "FStar.TypeChecker.Tc.fst"
let _72_2203 = (open_effect_decl env ed)
in (match (_72_2203) with
| (ed, a, wp_a) -> begin
(
# 1608 "FStar.TypeChecker.Tc.fst"
let env = (let _151_925 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _151_925))
in (
# 1610 "FStar.TypeChecker.Tc.fst"
let _72_2205 = if (FStar_TypeChecker_Env.debug env0 FStar_Options.Low) then begin
(let _151_928 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _151_927 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _151_926 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checked effect signature: %s %s : %s\n" _151_928 _151_927 _151_926))))
end else begin
()
end
in (
# 1616 "FStar.TypeChecker.Tc.fst"
let check_and_gen' = (fun env _72_2212 k -> (match (_72_2212) with
| (_72_2210, t) -> begin
(check_and_gen env t k)
end))
in (
# 1618 "FStar.TypeChecker.Tc.fst"
let ret = (
# 1619 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_940 = (let _151_938 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_937 = (let _151_936 = (let _151_935 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _151_935))
in (_151_936)::[])
in (_151_938)::_151_937))
in (let _151_939 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _151_940 _151_939)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (
# 1622 "FStar.TypeChecker.Tc.fst"
let bind_wp = (
# 1623 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1624 "FStar.TypeChecker.Tc.fst"
let b = (let _151_942 = (let _151_941 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_941 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _151_942))
in (
# 1625 "FStar.TypeChecker.Tc.fst"
let wp_b = (let _151_946 = (let _151_945 = (let _151_944 = (let _151_943 = (FStar_Syntax_Syntax.bv_to_name b)
in (a, _151_943))
in FStar_Syntax_Syntax.NT (_151_944))
in (_151_945)::[])
in (FStar_Syntax_Subst.subst _151_946 wp_a))
in (
# 1626 "FStar.TypeChecker.Tc.fst"
let a_wp_b = (let _151_950 = (let _151_948 = (let _151_947 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _151_947))
in (_151_948)::[])
in (let _151_949 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _151_950 _151_949)))
in (
# 1627 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = a_wp_b
in (
# 1628 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_963 = (let _151_961 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_960 = (let _151_959 = (FStar_Syntax_Syntax.mk_binder b)
in (let _151_958 = (let _151_957 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _151_956 = (let _151_955 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _151_954 = (let _151_953 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (let _151_952 = (let _151_951 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_151_951)::[])
in (_151_953)::_151_952))
in (_151_955)::_151_954))
in (_151_957)::_151_956))
in (_151_959)::_151_958))
in (_151_961)::_151_960))
in (let _151_962 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _151_963 _151_962)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))))))
in (
# 1634 "FStar.TypeChecker.Tc.fst"
let bind_wlp = (
# 1635 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1636 "FStar.TypeChecker.Tc.fst"
let b = (let _151_965 = (let _151_964 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_964 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _151_965))
in (
# 1637 "FStar.TypeChecker.Tc.fst"
let wlp_b = (let _151_969 = (let _151_968 = (let _151_967 = (let _151_966 = (FStar_Syntax_Syntax.bv_to_name b)
in (a, _151_966))
in FStar_Syntax_Syntax.NT (_151_967))
in (_151_968)::[])
in (FStar_Syntax_Subst.subst _151_969 wlp_a))
in (
# 1638 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = (let _151_973 = (let _151_971 = (let _151_970 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _151_970))
in (_151_971)::[])
in (let _151_972 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _151_973 _151_972)))
in (
# 1639 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_982 = (let _151_980 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_979 = (let _151_978 = (FStar_Syntax_Syntax.mk_binder b)
in (let _151_977 = (let _151_976 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _151_975 = (let _151_974 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_151_974)::[])
in (_151_976)::_151_975))
in (_151_978)::_151_977))
in (_151_980)::_151_979))
in (let _151_981 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _151_982 _151_981)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wlp expected_k))))))
in (
# 1645 "FStar.TypeChecker.Tc.fst"
let if_then_else = (
# 1646 "FStar.TypeChecker.Tc.fst"
let p = (let _151_984 = (let _151_983 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_983 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _151_984))
in (
# 1647 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_993 = (let _151_991 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_990 = (let _151_989 = (FStar_Syntax_Syntax.mk_binder p)
in (let _151_988 = (let _151_987 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _151_986 = (let _151_985 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_985)::[])
in (_151_987)::_151_986))
in (_151_989)::_151_988))
in (_151_991)::_151_990))
in (let _151_992 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_993 _151_992)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (
# 1653 "FStar.TypeChecker.Tc.fst"
let ite_wp = (
# 1654 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1655 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1000 = (let _151_998 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_997 = (let _151_996 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _151_995 = (let _151_994 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_994)::[])
in (_151_996)::_151_995))
in (_151_998)::_151_997))
in (let _151_999 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_1000 _151_999)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k)))
in (
# 1661 "FStar.TypeChecker.Tc.fst"
let ite_wlp = (
# 1662 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1663 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1005 = (let _151_1003 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1002 = (let _151_1001 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (_151_1001)::[])
in (_151_1003)::_151_1002))
in (let _151_1004 = (FStar_Syntax_Syntax.mk_Total wlp_a)
in (FStar_Syntax_Util.arrow _151_1005 _151_1004)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wlp expected_k)))
in (
# 1668 "FStar.TypeChecker.Tc.fst"
let wp_binop = (
# 1669 "FStar.TypeChecker.Tc.fst"
let bin_op = (
# 1670 "FStar.TypeChecker.Tc.fst"
let _72_2240 = (FStar_Syntax_Util.type_u ())
in (match (_72_2240) with
| (t1, u1) -> begin
(
# 1671 "FStar.TypeChecker.Tc.fst"
let _72_2243 = (FStar_Syntax_Util.type_u ())
in (match (_72_2243) with
| (t2, u2) -> begin
(
# 1672 "FStar.TypeChecker.Tc.fst"
let t = (let _151_1006 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_max ((u1)::(u2)::[]))) None _151_1006))
in (let _151_1011 = (let _151_1009 = (FStar_Syntax_Syntax.null_binder t1)
in (let _151_1008 = (let _151_1007 = (FStar_Syntax_Syntax.null_binder t2)
in (_151_1007)::[])
in (_151_1009)::_151_1008))
in (let _151_1010 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _151_1011 _151_1010))))
end))
end))
in (
# 1674 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1020 = (let _151_1018 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1017 = (let _151_1016 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _151_1015 = (let _151_1014 = (FStar_Syntax_Syntax.null_binder bin_op)
in (let _151_1013 = (let _151_1012 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_1012)::[])
in (_151_1014)::_151_1013))
in (_151_1016)::_151_1015))
in (_151_1018)::_151_1017))
in (let _151_1019 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_1020 _151_1019)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_binop expected_k)))
in (
# 1681 "FStar.TypeChecker.Tc.fst"
let wp_as_type = (
# 1682 "FStar.TypeChecker.Tc.fst"
let _72_2251 = (FStar_Syntax_Util.type_u ())
in (match (_72_2251) with
| (t, _72_2250) -> begin
(
# 1683 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1025 = (let _151_1023 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1022 = (let _151_1021 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_1021)::[])
in (_151_1023)::_151_1022))
in (let _151_1024 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _151_1025 _151_1024)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (
# 1688 "FStar.TypeChecker.Tc.fst"
let close_wp = (
# 1689 "FStar.TypeChecker.Tc.fst"
let b = (let _151_1027 = (let _151_1026 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_1026 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _151_1027))
in (
# 1690 "FStar.TypeChecker.Tc.fst"
let b_wp_a = (let _151_1031 = (let _151_1029 = (let _151_1028 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _151_1028))
in (_151_1029)::[])
in (let _151_1030 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_1031 _151_1030)))
in (
# 1691 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1038 = (let _151_1036 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1035 = (let _151_1034 = (FStar_Syntax_Syntax.mk_binder b)
in (let _151_1033 = (let _151_1032 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_151_1032)::[])
in (_151_1034)::_151_1033))
in (_151_1036)::_151_1035))
in (let _151_1037 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_1038 _151_1037)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (
# 1695 "FStar.TypeChecker.Tc.fst"
let assert_p = (
# 1696 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1047 = (let _151_1045 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1044 = (let _151_1043 = (let _151_1040 = (let _151_1039 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_1039 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _151_1040))
in (let _151_1042 = (let _151_1041 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_1041)::[])
in (_151_1043)::_151_1042))
in (_151_1045)::_151_1044))
in (let _151_1046 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_1047 _151_1046)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (
# 1702 "FStar.TypeChecker.Tc.fst"
let assume_p = (
# 1703 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1056 = (let _151_1054 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1053 = (let _151_1052 = (let _151_1049 = (let _151_1048 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_1048 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _151_1049))
in (let _151_1051 = (let _151_1050 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_1050)::[])
in (_151_1052)::_151_1051))
in (_151_1054)::_151_1053))
in (let _151_1055 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_1056 _151_1055)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (
# 1709 "FStar.TypeChecker.Tc.fst"
let null_wp = (
# 1710 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1059 = (let _151_1057 = (FStar_Syntax_Syntax.mk_binder a)
in (_151_1057)::[])
in (let _151_1058 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_1059 _151_1058)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (
# 1714 "FStar.TypeChecker.Tc.fst"
let trivial_wp = (
# 1715 "FStar.TypeChecker.Tc.fst"
let _72_2267 = (FStar_Syntax_Util.type_u ())
in (match (_72_2267) with
| (t, _72_2266) -> begin
(
# 1716 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1064 = (let _151_1062 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1061 = (let _151_1060 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_1060)::[])
in (_151_1062)::_151_1061))
in (let _151_1063 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _151_1064 _151_1063)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (
# 1722 "FStar.TypeChecker.Tc.fst"
let t = (let _151_1065 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _151_1065))
in (
# 1723 "FStar.TypeChecker.Tc.fst"
let _72_2273 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_72_2273) with
| (univs, t) -> begin
(
# 1724 "FStar.TypeChecker.Tc.fst"
let _72_2289 = (match ((let _151_1067 = (let _151_1066 = (FStar_Syntax_Subst.compress t)
in _151_1066.FStar_Syntax_Syntax.n)
in (binders, _151_1067))) with
| ([], _72_2276) -> begin
([], t)
end
| (_72_2279, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _72_2286 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_72_2289) with
| (binders, signature) -> begin
(
# 1728 "FStar.TypeChecker.Tc.fst"
let close = (fun ts -> (let _151_1070 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _151_1070)))
in (
# 1729 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1729 "FStar.TypeChecker.Tc.fst"
let _72_2292 = ed
in (let _151_1083 = (close ret)
in (let _151_1082 = (close bind_wp)
in (let _151_1081 = (close bind_wlp)
in (let _151_1080 = (close if_then_else)
in (let _151_1079 = (close ite_wp)
in (let _151_1078 = (close ite_wlp)
in (let _151_1077 = (close wp_binop)
in (let _151_1076 = (close wp_as_type)
in (let _151_1075 = (close close_wp)
in (let _151_1074 = (close assert_p)
in (let _151_1073 = (close assume_p)
in (let _151_1072 = (close null_wp)
in (let _151_1071 = (close trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _72_2292.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _72_2292.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _151_1083; FStar_Syntax_Syntax.bind_wp = _151_1082; FStar_Syntax_Syntax.bind_wlp = _151_1081; FStar_Syntax_Syntax.if_then_else = _151_1080; FStar_Syntax_Syntax.ite_wp = _151_1079; FStar_Syntax_Syntax.ite_wlp = _151_1078; FStar_Syntax_Syntax.wp_binop = _151_1077; FStar_Syntax_Syntax.wp_as_type = _151_1076; FStar_Syntax_Syntax.close_wp = _151_1075; FStar_Syntax_Syntax.assert_p = _151_1074; FStar_Syntax_Syntax.assume_p = _151_1073; FStar_Syntax_Syntax.null_wp = _151_1072; FStar_Syntax_Syntax.trivial = _151_1071}))))))))))))))
in (
# 1747 "FStar.TypeChecker.Tc.fst"
let _72_2295 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1084 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _151_1084))
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

# 1751 "FStar.TypeChecker.Tc.fst"
let tc_lex_t = (fun env ses quals lids -> (
# 1758 "FStar.TypeChecker.Tc.fst"
let _72_2301 = ()
in (
# 1759 "FStar.TypeChecker.Tc.fst"
let _72_2309 = ()
in (match (ses) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _72_2338, _72_2340, [], r)::FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _72_2329, r1)::FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _72_2318, r2)::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(
# 1774 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (
# 1775 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (
# 1776 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (
# 1777 "FStar.TypeChecker.Tc.fst"
let tc = FStar_Syntax_Syntax.Sig_inductive_typ ((lex_t, (u)::[], [], t, [], (FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[], [], r))
in (
# 1779 "FStar.TypeChecker.Tc.fst"
let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (
# 1780 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (let _151_1091 = (let _151_1090 = (let _151_1089 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid r1)
in (_151_1089, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_151_1090))
in (FStar_Syntax_Syntax.mk _151_1091 None r1))
in (
# 1781 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (
# 1782 "FStar.TypeChecker.Tc.fst"
let dc_lextop = FStar_Syntax_Syntax.Sig_datacon ((lex_top, (utop)::[], lex_top_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r1))
in (
# 1784 "FStar.TypeChecker.Tc.fst"
let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1785 "FStar.TypeChecker.Tc.fst"
let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1786 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (
# 1787 "FStar.TypeChecker.Tc.fst"
let a = (let _151_1092 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _151_1092))
in (
# 1788 "FStar.TypeChecker.Tc.fst"
let hd = (let _151_1093 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _151_1093))
in (
# 1789 "FStar.TypeChecker.Tc.fst"
let tl = (let _151_1097 = (let _151_1096 = (let _151_1095 = (let _151_1094 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid r2)
in (_151_1094, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_151_1095))
in (FStar_Syntax_Syntax.mk _151_1096 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _151_1097))
in (
# 1790 "FStar.TypeChecker.Tc.fst"
let res = (let _151_1100 = (let _151_1099 = (let _151_1098 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid r2)
in (_151_1098, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_151_1099))
in (FStar_Syntax_Syntax.mk _151_1100 None r2))
in (let _151_1101 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.Implicit)))::((hd, None))::((tl, None))::[]) _151_1101))))))
in (
# 1792 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (
# 1793 "FStar.TypeChecker.Tc.fst"
let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _151_1103 = (let _151_1102 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _151_1102))
in FStar_Syntax_Syntax.Sig_bundle (_151_1103)))))))))))))))
end
| _72_2364 -> begin
(let _151_1105 = (let _151_1104 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _151_1104))
in (FStar_All.failwith _151_1105))
end))))

# 1799 "FStar.TypeChecker.Tc.fst"
let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (
# 1862 "FStar.TypeChecker.Tc.fst"
let warn_positivity = (fun l r -> (let _151_1119 = (let _151_1118 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _151_1118))
in (FStar_TypeChecker_Errors.warn r _151_1119)))
in (
# 1864 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1867 "FStar.TypeChecker.Tc.fst"
let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(
# 1872 "FStar.TypeChecker.Tc.fst"
let _72_2386 = ()
in (
# 1873 "FStar.TypeChecker.Tc.fst"
let _72_2388 = (warn_positivity tc r)
in (
# 1874 "FStar.TypeChecker.Tc.fst"
let _72_2392 = (FStar_Syntax_Subst.open_term tps k)
in (match (_72_2392) with
| (tps, k) -> begin
(
# 1875 "FStar.TypeChecker.Tc.fst"
let _72_2396 = (tc_tparams env tps)
in (match (_72_2396) with
| (tps, env_tps, us) -> begin
(
# 1876 "FStar.TypeChecker.Tc.fst"
let _72_2399 = (FStar_Syntax_Util.arrow_formals k)
in (match (_72_2399) with
| (indices, t) -> begin
(
# 1877 "FStar.TypeChecker.Tc.fst"
let _72_2403 = (tc_tparams env_tps indices)
in (match (_72_2403) with
| (indices, env', us') -> begin
(
# 1878 "FStar.TypeChecker.Tc.fst"
let _72_2407 = (tc_trivial_guard env' t)
in (match (_72_2407) with
| (t, _72_2406) -> begin
(
# 1879 "FStar.TypeChecker.Tc.fst"
let k = (let _151_1124 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _151_1124))
in (
# 1880 "FStar.TypeChecker.Tc.fst"
let _72_2411 = (FStar_Syntax_Util.type_u ())
in (match (_72_2411) with
| (t_type, u) -> begin
(
# 1881 "FStar.TypeChecker.Tc.fst"
let _72_2412 = (let _151_1125 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _151_1125))
in (
# 1883 "FStar.TypeChecker.Tc.fst"
let refined_tps = (FStar_All.pipe_right tps (FStar_List.map (fun _72_2416 -> (match (_72_2416) with
| (x, imp) -> begin
(
# 1884 "FStar.TypeChecker.Tc.fst"
let y = (FStar_Syntax_Syntax.freshen_bv x)
in (
# 1885 "FStar.TypeChecker.Tc.fst"
let refined = (let _151_1129 = (let _151_1128 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _151_1127 = (FStar_Syntax_Syntax.bv_to_name y)
in (FStar_Syntax_Util.mk_eq x.FStar_Syntax_Syntax.sort x.FStar_Syntax_Syntax.sort _151_1128 _151_1127)))
in (FStar_Syntax_Util.refine y _151_1129))
in ((
# 1886 "FStar.TypeChecker.Tc.fst"
let _72_2419 = x
in {FStar_Syntax_Syntax.ppname = _72_2419.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _72_2419.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = refined}), imp)))
end))))
in (
# 1888 "FStar.TypeChecker.Tc.fst"
let t_tc = (let _151_1130 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append refined_tps indices) _151_1130))
in (
# 1889 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 1890 "FStar.TypeChecker.Tc.fst"
let k = (FStar_Syntax_Subst.close tps k)
in (let _151_1131 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (tc)) ([], t_tc))
in (_151_1131, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u)))))))
end)))
end))
end))
end))
end))
end))))
end
| _72_2426 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1897 "FStar.TypeChecker.Tc.fst"
let positive_if_pure = (fun _72_2428 l -> ())
in (
# 1900 "FStar.TypeChecker.Tc.fst"
let tc_data = (fun env tcs _72_6 -> (match (_72_6) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(
# 1902 "FStar.TypeChecker.Tc.fst"
let _72_2445 = ()
in (
# 1904 "FStar.TypeChecker.Tc.fst"
let _72_2476 = (let _151_1146 = (FStar_Util.find_map tcs (fun _72_2449 -> (match (_72_2449) with
| (se, u_tc) -> begin
if (let _151_1144 = (let _151_1143 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _151_1143))
in (FStar_Ident.lid_equals tc_lid _151_1144)) then begin
(
# 1907 "FStar.TypeChecker.Tc.fst"
let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_72_2451, _72_2453, tps, _72_2456, _72_2458, _72_2460, _72_2462, _72_2464) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _72_2470 -> (match (_72_2470) with
| (x, _72_2469) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit))
end))))
end
| _72_2472 -> begin
(FStar_All.failwith "Impossible")
end)
in Some ((tps, u_tc)))
end else begin
None
end
end)))
in (FStar_All.pipe_right _151_1146 FStar_Util.must))
in (match (_72_2476) with
| (tps, u_tc) -> begin
(
# 1914 "FStar.TypeChecker.Tc.fst"
let _72_2496 = (match ((let _151_1147 = (FStar_Syntax_Subst.compress t)
in _151_1147.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(
# 1919 "FStar.TypeChecker.Tc.fst"
let _72_2484 = (FStar_Util.first_N ntps bs)
in (match (_72_2484) with
| (_72_2482, bs') -> begin
(
# 1920 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (
# 1921 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _72_2490 -> (match (_72_2490) with
| (x, _72_2489) -> begin
(let _151_1151 = (let _151_1150 = (FStar_Syntax_Syntax.bv_to_name x)
in ((ntps - (1 + i)), _151_1150))
in FStar_Syntax_Syntax.DB (_151_1151))
end))))
in (let _151_1152 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _151_1152))))
end))
end
| _72_2493 -> begin
([], t)
end)
in (match (_72_2496) with
| (arguments, result) -> begin
(
# 1925 "FStar.TypeChecker.Tc.fst"
let _72_2497 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1155 = (FStar_Syntax_Print.lid_to_string c)
in (let _151_1154 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _151_1153 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _151_1155 _151_1154 _151_1153))))
end else begin
()
end
in (
# 1931 "FStar.TypeChecker.Tc.fst"
let _72_2502 = (tc_tparams env arguments)
in (match (_72_2502) with
| (arguments, env', us) -> begin
(
# 1932 "FStar.TypeChecker.Tc.fst"
let _72_2506 = (tc_trivial_guard env' result)
in (match (_72_2506) with
| (result, _72_2505) -> begin
(
# 1933 "FStar.TypeChecker.Tc.fst"
let _72_2510 = (FStar_Syntax_Util.head_and_args result)
in (match (_72_2510) with
| (head, _72_2509) -> begin
(
# 1934 "FStar.TypeChecker.Tc.fst"
let _72_2518 = (match ((let _151_1156 = (FStar_Syntax_Subst.compress head)
in _151_1156.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _72_2513) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v tc_lid) -> begin
()
end
| _72_2517 -> begin
(let _151_1160 = (let _151_1159 = (let _151_1158 = (let _151_1157 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _151_1157))
in (_151_1158, r))
in FStar_Syntax_Syntax.Error (_151_1159))
in (Prims.raise _151_1160))
end)
in (
# 1937 "FStar.TypeChecker.Tc.fst"
let g = (FStar_List.fold_left2 (fun g _72_2524 u_x -> (match (_72_2524) with
| (x, _72_2523) -> begin
(
# 1938 "FStar.TypeChecker.Tc.fst"
let _72_2526 = ()
in (let _151_1164 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _151_1164)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (
# 1944 "FStar.TypeChecker.Tc.fst"
let t = (let _151_1165 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow (FStar_List.append tps arguments) _151_1165))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _72_2531 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1951 "FStar.TypeChecker.Tc.fst"
let generalize_and_recheck = (fun env g tcs datas -> (
# 1952 "FStar.TypeChecker.Tc.fst"
let _72_2537 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 1953 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _72_7 -> (match (_72_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_72_2541, _72_2543, tps, k, _72_2547, _72_2549, _72_2551, _72_2553) -> begin
(let _151_1176 = (let _151_1175 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _151_1175))
in (FStar_Syntax_Syntax.null_binder _151_1176))
end
| _72_2557 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 1956 "FStar.TypeChecker.Tc.fst"
let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _72_8 -> (match (_72_8) with
| FStar_Syntax_Syntax.Sig_datacon (_72_2561, _72_2563, t, _72_2566, _72_2568, _72_2570, _72_2572, _72_2574) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _72_2578 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 1959 "FStar.TypeChecker.Tc.fst"
let t = (let _151_1178 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Recheck.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _151_1178))
in (
# 1960 "FStar.TypeChecker.Tc.fst"
let _72_2581 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1179 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _151_1179))
end else begin
()
end
in (
# 1961 "FStar.TypeChecker.Tc.fst"
let _72_2585 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_72_2585) with
| (uvs, t) -> begin
(
# 1962 "FStar.TypeChecker.Tc.fst"
let _72_2587 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1183 = (let _151_1181 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _151_1181 (FStar_String.concat ", ")))
in (let _151_1182 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _151_1183 _151_1182)))
end else begin
()
end
in (
# 1965 "FStar.TypeChecker.Tc.fst"
let _72_2591 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_72_2591) with
| (uvs, t) -> begin
(
# 1966 "FStar.TypeChecker.Tc.fst"
let _72_2595 = (FStar_Syntax_Util.arrow_formals t)
in (match (_72_2595) with
| (args, _72_2594) -> begin
(
# 1967 "FStar.TypeChecker.Tc.fst"
let _72_2598 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_72_2598) with
| (tc_types, data_types) -> begin
(
# 1968 "FStar.TypeChecker.Tc.fst"
let tcs = (FStar_List.map2 (fun _72_2602 se -> (match (_72_2602) with
| (x, _72_2601) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _72_2606, tps, _72_2609, mutuals, datas, quals, r) -> begin
(
# 1970 "FStar.TypeChecker.Tc.fst"
let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (
# 1971 "FStar.TypeChecker.Tc.fst"
let _72_2632 = (match ((let _151_1186 = (FStar_Syntax_Subst.compress ty)
in _151_1186.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 1973 "FStar.TypeChecker.Tc.fst"
let _72_2623 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_72_2623) with
| (tps, rest) -> begin
(
# 1974 "FStar.TypeChecker.Tc.fst"
let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _72_2626 -> begin
(let _151_1187 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _151_1187 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _72_2629 -> begin
([], ty)
end)
in (match (_72_2632) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _72_2634 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (
# 1986 "FStar.TypeChecker.Tc.fst"
let env_data = (FStar_TypeChecker_Env.push_univ_vars env uvs)
in (
# 1987 "FStar.TypeChecker.Tc.fst"
let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _151_1188 -> FStar_Syntax_Syntax.U_name (_151_1188))))
in (
# 1988 "FStar.TypeChecker.Tc.fst"
let env_data = (FStar_List.fold_left (fun env tc -> (FStar_TypeChecker_Env.push_sigelt_inst env tc uvs_universes)) env_data tcs)
in (
# 1989 "FStar.TypeChecker.Tc.fst"
let datas = (FStar_List.map2 (fun _72_2644 -> (match (_72_2644) with
| (t, _72_2643) -> begin
(fun _72_9 -> (match (_72_9) with
| FStar_Syntax_Syntax.Sig_datacon (l, _72_2648, _72_2650, tc, ntps, quals, mutuals, r) -> begin
(
# 1991 "FStar.TypeChecker.Tc.fst"
let ty = (match (uvs) with
| [] -> begin
t.FStar_Syntax_Syntax.sort
end
| _72_2660 -> begin
(
# 1994 "FStar.TypeChecker.Tc.fst"
let _72_2661 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1196 = (FStar_Syntax_Print.lid_to_string l)
in (let _151_1195 = (FStar_Syntax_Print.term_to_string t.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Rechecking datacon %s : %s\n" _151_1196 _151_1195)))
end else begin
()
end
in (
# 1996 "FStar.TypeChecker.Tc.fst"
let _72_2667 = (tc_tot_or_gtot_term env_data t.FStar_Syntax_Syntax.sort)
in (match (_72_2667) with
| (ty, _72_2665, g) -> begin
(
# 1997 "FStar.TypeChecker.Tc.fst"
let g = (
# 1997 "FStar.TypeChecker.Tc.fst"
let _72_2668 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _72_2668.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _72_2668.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _72_2668.FStar_TypeChecker_Env.implicits})
in (
# 1998 "FStar.TypeChecker.Tc.fst"
let _72_2671 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Subst.close_univ_vars uvs ty)))
end)))
end)
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _72_2675 -> begin
(FStar_All.failwith "Impossible")
end))
end)) data_types datas)
in (tcs, datas))))))
end))
end))
end)))
end))))))))
in (
# 2004 "FStar.TypeChecker.Tc.fst"
let _72_2685 = (FStar_All.pipe_right ses (FStar_List.partition (fun _72_10 -> (match (_72_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_72_2679) -> begin
true
end
| _72_2682 -> begin
false
end))))
in (match (_72_2685) with
| (tys, datas) -> begin
(
# 2006 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2009 "FStar.TypeChecker.Tc.fst"
let _72_2702 = (FStar_List.fold_right (fun tc _72_2691 -> (match (_72_2691) with
| (env, all_tcs, g) -> begin
(
# 2010 "FStar.TypeChecker.Tc.fst"
let _72_2695 = (tc_tycon env tc)
in (match (_72_2695) with
| (env, tc, tc_u) -> begin
(
# 2011 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (
# 2012 "FStar.TypeChecker.Tc.fst"
let _72_2697 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1200 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _151_1200))
end else begin
()
end
in (let _151_1201 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _151_1201))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_72_2702) with
| (env, tcs, g) -> begin
(
# 2019 "FStar.TypeChecker.Tc.fst"
let _72_2712 = (FStar_List.fold_right (fun se _72_2706 -> (match (_72_2706) with
| (datas, g) -> begin
(
# 2020 "FStar.TypeChecker.Tc.fst"
let _72_2709 = (tc_data env tcs se)
in (match (_72_2709) with
| (data, g') -> begin
(let _151_1204 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _151_1204))
end))
end)) datas ([], g))
in (match (_72_2712) with
| (datas, g) -> begin
(
# 2025 "FStar.TypeChecker.Tc.fst"
let _72_2715 = (let _151_1205 = (FStar_List.map Prims.fst tcs)
in (generalize_and_recheck env0 g _151_1205 datas))
in (match (_72_2715) with
| (tcs, datas) -> begin
(let _151_1207 = (let _151_1206 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _151_1206))
in FStar_Syntax_Syntax.Sig_bundle (_151_1207))
end))
end))
end)))
end)))))))))

# 2028 "FStar.TypeChecker.Tc.fst"
let rec tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.env) = (fun env se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(
# 2041 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2042 "FStar.TypeChecker.Tc.fst"
let se = (tc_lex_t env ses quals lids)
in (let _151_1212 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _151_1212))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(
# 2046 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2047 "FStar.TypeChecker.Tc.fst"
let se = (tc_inductive env ses quals lids)
in (let _151_1213 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _151_1213))))
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
# 2059 "FStar.TypeChecker.Tc.fst"
let _72_2751 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (
# 2060 "FStar.TypeChecker.Tc.fst"
let _72_2753 = (let _151_1214 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _151_1214 Prims.ignore))
in (se, env)))
end)
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(
# 2065 "FStar.TypeChecker.Tc.fst"
let ne = (tc_eff_decl env ne)
in (
# 2066 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (
# 2067 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(
# 2071 "FStar.TypeChecker.Tc.fst"
let _72_2768 = (let _151_1215 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _151_1215))
in (match (_72_2768) with
| (a, wp_a_src) -> begin
(
# 2072 "FStar.TypeChecker.Tc.fst"
let _72_2771 = (let _151_1216 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _151_1216))
in (match (_72_2771) with
| (b, wp_b_tgt) -> begin
(
# 2073 "FStar.TypeChecker.Tc.fst"
let wp_a_tgt = (let _151_1220 = (let _151_1219 = (let _151_1218 = (let _151_1217 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _151_1217))
in FStar_Syntax_Syntax.NT (_151_1218))
in (_151_1219)::[])
in (FStar_Syntax_Subst.subst _151_1220 wp_b_tgt))
in (
# 2074 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _151_1225 = (let _151_1223 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1222 = (let _151_1221 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_151_1221)::[])
in (_151_1223)::_151_1222))
in (let _151_1224 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _151_1225 _151_1224)))
in (
# 2075 "FStar.TypeChecker.Tc.fst"
let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (
# 2076 "FStar.TypeChecker.Tc.fst"
let sub = (
# 2076 "FStar.TypeChecker.Tc.fst"
let _72_2775 = sub
in {FStar_Syntax_Syntax.source = _72_2775.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _72_2775.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
in (
# 2077 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect ((sub, r))
in (
# 2078 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(
# 2082 "FStar.TypeChecker.Tc.fst"
let _72_2788 = ()
in (
# 2083 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2084 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2085 "FStar.TypeChecker.Tc.fst"
let _72_2794 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_72_2794) with
| (tps, c) -> begin
(
# 2086 "FStar.TypeChecker.Tc.fst"
let _72_2798 = (tc_tparams env tps)
in (match (_72_2798) with
| (tps, env, us) -> begin
(
# 2087 "FStar.TypeChecker.Tc.fst"
let _72_2802 = (tc_comp env c)
in (match (_72_2802) with
| (c, g, u) -> begin
(
# 2088 "FStar.TypeChecker.Tc.fst"
let tags = (FStar_All.pipe_right tags (FStar_List.map (fun _72_11 -> (match (_72_11) with
| FStar_Syntax_Syntax.DefaultEffect (None) -> begin
(
# 2090 "FStar.TypeChecker.Tc.fst"
let c' = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let _151_1228 = (FStar_All.pipe_right c'.FStar_Syntax_Syntax.effect_name (fun _151_1227 -> Some (_151_1227)))
in FStar_Syntax_Syntax.DefaultEffect (_151_1228)))
end
| t -> begin
t
end))))
in (
# 2093 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 2094 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.close_comp tps c)
in (
# 2095 "FStar.TypeChecker.Tc.fst"
let _72_2813 = (let _151_1229 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _151_1229))
in (match (_72_2813) with
| (uvs, t) -> begin
(
# 2096 "FStar.TypeChecker.Tc.fst"
let _72_2832 = (match ((let _151_1231 = (let _151_1230 = (FStar_Syntax_Subst.compress t)
in _151_1230.FStar_Syntax_Syntax.n)
in (tps, _151_1231))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_72_2816, c)) -> begin
([], c)
end
| (_72_2822, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _72_2829 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_72_2832) with
| (tps, c) -> begin
(
# 2100 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_effect_abbrev ((lid, uvs, tps, c, tags, r))
in (
# 2101 "FStar.TypeChecker.Tc.fst"
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
# 2105 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2106 "FStar.TypeChecker.Tc.fst"
let _72_2843 = ()
in (
# 2107 "FStar.TypeChecker.Tc.fst"
let k = (let _151_1232 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _151_1232))
in (
# 2108 "FStar.TypeChecker.Tc.fst"
let _72_2848 = (check_and_gen env t k)
in (match (_72_2848) with
| (uvs, t) -> begin
(
# 2109 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (
# 2110 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(
# 2114 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2115 "FStar.TypeChecker.Tc.fst"
let _72_2861 = (FStar_Syntax_Util.type_u ())
in (match (_72_2861) with
| (k, _72_2860) -> begin
(
# 2116 "FStar.TypeChecker.Tc.fst"
let phi = (let _151_1233 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _151_1233 (norm env)))
in (
# 2117 "FStar.TypeChecker.Tc.fst"
let _72_2863 = (FStar_TypeChecker_Util.check_uvars r phi)
in (
# 2118 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))
in (
# 2119 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(
# 2123 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2124 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Recheck.t_unit)
in (
# 2125 "FStar.TypeChecker.Tc.fst"
let _72_2876 = (tc_term env e)
in (match (_72_2876) with
| (e, c, g1) -> begin
(
# 2126 "FStar.TypeChecker.Tc.fst"
let _72_2881 = (let _151_1237 = (let _151_1234 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Recheck.t_unit r)
in Some (_151_1234))
in (let _151_1236 = (let _151_1235 = (c.FStar_Syntax_Syntax.comp ())
in (e, _151_1235))
in (check_expected_effect env _151_1237 _151_1236)))
in (match (_72_2881) with
| (e, _72_2879, g) -> begin
(
# 2127 "FStar.TypeChecker.Tc.fst"
let _72_2882 = (let _151_1238 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _151_1238))
in (
# 2128 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, r))
in (
# 2129 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(
# 2133 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2134 "FStar.TypeChecker.Tc.fst"
let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
if (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q')) then begin
Some (q)
end else begin
(let _151_1248 = (let _151_1247 = (let _151_1246 = (let _151_1245 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Inconsistent qualifier annotations on %s" _151_1245))
in (_151_1246, r))
in FStar_Syntax_Syntax.Error (_151_1247))
in (Prims.raise _151_1248))
end
end))
in (
# 2145 "FStar.TypeChecker.Tc.fst"
let _72_2926 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _72_2903 lb -> (match (_72_2903) with
| (gen, lbs, quals_opt) -> begin
(
# 2146 "FStar.TypeChecker.Tc.fst"
let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2147 "FStar.TypeChecker.Tc.fst"
let _72_2922 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(
# 2151 "FStar.TypeChecker.Tc.fst"
let quals_opt = (check_quals_eq lbname quals_opt quals)
in (
# 2152 "FStar.TypeChecker.Tc.fst"
let _72_2917 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _72_2916 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _151_1251 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _151_1251, quals_opt))))
end)
in (match (_72_2922) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_72_2926) with
| (should_generalize, lbs', quals_opt) -> begin
(
# 2161 "FStar.TypeChecker.Tc.fst"
let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _72_12 -> (match (_72_12) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _72_2935 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (
# 2168 "FStar.TypeChecker.Tc.fst"
let lbs' = (FStar_List.rev lbs')
in (
# 2171 "FStar.TypeChecker.Tc.fst"
let e = (let _151_1255 = (let _151_1254 = (let _151_1253 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _151_1253))
in FStar_Syntax_Syntax.Tm_let (_151_1254))
in (FStar_Syntax_Syntax.mk _151_1255 None r))
in (
# 2174 "FStar.TypeChecker.Tc.fst"
let _72_2969 = (match ((tc_maybe_toplevel_term (
# 2174 "FStar.TypeChecker.Tc.fst"
let _72_2939 = env
in {FStar_TypeChecker_Env.solver = _72_2939.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _72_2939.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _72_2939.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _72_2939.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _72_2939.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _72_2939.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _72_2939.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _72_2939.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _72_2939.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _72_2939.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _72_2939.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _72_2939.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _72_2939.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _72_2939.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _72_2939.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _72_2939.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _72_2939.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _72_2939.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _72_2939.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _72_2946; FStar_Syntax_Syntax.pos = _72_2944; FStar_Syntax_Syntax.vars = _72_2942}, _72_2953, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(
# 2177 "FStar.TypeChecker.Tc.fst"
let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_72_2957, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _72_2963 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _72_2966 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_72_2969) with
| (se, lbs) -> begin
(
# 2184 "FStar.TypeChecker.Tc.fst"
let _72_2975 = if (log env) then begin
(let _151_1261 = (let _151_1260 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 2186 "FStar.TypeChecker.Tc.fst"
let should_log = (match ((let _151_1257 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _151_1257))) with
| None -> begin
true
end
| _72_2973 -> begin
false
end)
in if should_log then begin
(let _151_1259 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _151_1258 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _151_1259 _151_1258)))
end else begin
""
end))))
in (FStar_All.pipe_right _151_1260 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _151_1261))
end else begin
()
end
in (
# 2193 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end))))
end))

# 2197 "FStar.TypeChecker.Tc.fst"
let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (
# 2222 "FStar.TypeChecker.Tc.fst"
let private_or_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun x -> ((x = FStar_Syntax_Syntax.Private) || (x = FStar_Syntax_Syntax.Abstract))))))
in (
# 2223 "FStar.TypeChecker.Tc.fst"
let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _72_2992 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_72_2994) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _72_3005, _72_3007) -> begin
if (private_or_abstract quals) then begin
(FStar_List.fold_right (fun se _72_3013 -> (match (_72_3013) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _72_3019, _72_3021, quals, r) -> begin
(
# 2237 "FStar.TypeChecker.Tc.fst"
let dec = (let _151_1277 = (let _151_1276 = (let _151_1275 = (let _151_1274 = (let _151_1273 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _151_1273))
in FStar_Syntax_Syntax.Tm_arrow (_151_1274))
in (FStar_Syntax_Syntax.mk _151_1275 None r))
in (l, us, _151_1276, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_151_1277))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _72_3031, _72_3033, _72_3035, _72_3037, r) -> begin
(
# 2240 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _72_3043 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_72_3045, _72_3047, quals, _72_3050) -> begin
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
| _72_3069 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_72_3071) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _72_3087, _72_3089, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(
# 2270 "FStar.TypeChecker.Tc.fst"
let lid = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals lid))) then begin
([], hidden)
end else begin
(
# 2273 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((lid, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::[], (FStar_Ident.range_of_lid lid)))
in ((dec)::[], (lid)::hidden))
end)
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (private_or_abstract quals) then begin
(let _151_1282 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _151_1281 = (let _151_1280 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (_151_1280, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_151_1281)))))
in (_151_1282, hidden))
end else begin
((se)::[], hidden)
end
end))))

# 2282 "FStar.TypeChecker.Tc.fst"
let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (
# 2283 "FStar.TypeChecker.Tc.fst"
let _72_3127 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _72_3108 se -> (match (_72_3108) with
| (ses, exports, env, hidden) -> begin
(
# 2285 "FStar.TypeChecker.Tc.fst"
let _72_3110 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1289 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _151_1289))
end else begin
()
end
in (
# 2288 "FStar.TypeChecker.Tc.fst"
let _72_3114 = (tc_decl env se)
in (match (_72_3114) with
| (se, env) -> begin
(
# 2290 "FStar.TypeChecker.Tc.fst"
let _72_3115 = if ((FStar_ST.read FStar_Options.log_types) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _151_1290 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _151_1290))
end else begin
()
end
in (
# 2293 "FStar.TypeChecker.Tc.fst"
let _72_3117 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (
# 2295 "FStar.TypeChecker.Tc.fst"
let _72_3121 = (for_export hidden se)
in (match (_72_3121) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_72_3127) with
| (ses, exports, env, _72_3126) -> begin
(let _151_1291 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _151_1291, env))
end)))

# 2300 "FStar.TypeChecker.Tc.fst"
let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2301 "FStar.TypeChecker.Tc.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 2302 "FStar.TypeChecker.Tc.fst"
let msg = (Prims.strcat "Internals for " name)
in (
# 2303 "FStar.TypeChecker.Tc.fst"
let env = (
# 2303 "FStar.TypeChecker.Tc.fst"
let _72_3132 = env
in (let _151_1296 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _72_3132.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _72_3132.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _72_3132.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _72_3132.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _72_3132.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _72_3132.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _72_3132.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _72_3132.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _72_3132.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _72_3132.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _72_3132.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _72_3132.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _72_3132.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _72_3132.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _72_3132.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _72_3132.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _151_1296; FStar_TypeChecker_Env.default_effects = _72_3132.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _72_3132.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _72_3132.FStar_TypeChecker_Env.use_bv_sorts}))
in (
# 2304 "FStar.TypeChecker.Tc.fst"
let _72_3135 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (
# 2305 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (
# 2306 "FStar.TypeChecker.Tc.fst"
let _72_3141 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_72_3141) with
| (ses, exports, env) -> begin
((
# 2307 "FStar.TypeChecker.Tc.fst"
let _72_3142 = modul
in {FStar_Syntax_Syntax.name = _72_3142.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _72_3142.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _72_3142.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))

# 2309 "FStar.TypeChecker.Tc.fst"
let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (
# 2310 "FStar.TypeChecker.Tc.fst"
let _72_3150 = (tc_decls env decls)
in (match (_72_3150) with
| (ses, exports, env) -> begin
(
# 2311 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2311 "FStar.TypeChecker.Tc.fst"
let _72_3151 = modul
in {FStar_Syntax_Syntax.name = _72_3151.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _72_3151.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _72_3151.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))

# 2314 "FStar.TypeChecker.Tc.fst"
let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (
# 2315 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2315 "FStar.TypeChecker.Tc.fst"
let _72_3157 = modul
in {FStar_Syntax_Syntax.name = _72_3157.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _72_3157.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (
# 2316 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.finish_module env modul)
in (
# 2317 "FStar.TypeChecker.Tc.fst"
let _72_3167 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(
# 2319 "FStar.TypeChecker.Tc.fst"
let _72_3161 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (
# 2320 "FStar.TypeChecker.Tc.fst"
let _72_3163 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (
# 2321 "FStar.TypeChecker.Tc.fst"
let _72_3165 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _151_1309 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _151_1309 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))

# 2326 "FStar.TypeChecker.Tc.fst"
let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2327 "FStar.TypeChecker.Tc.fst"
let _72_3174 = (tc_partial_modul env modul)
in (match (_72_3174) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

# 2330 "FStar.TypeChecker.Tc.fst"
let add_modul_to_tcenv : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_TypeChecker_Env.env = (fun en m -> (
# 2331 "FStar.TypeChecker.Tc.fst"
let do_sigelt = (fun en elt -> (
# 2332 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt en elt)
in (
# 2333 "FStar.TypeChecker.Tc.fst"
let _72_3181 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env elt)
in env)))
in (
# 2336 "FStar.TypeChecker.Tc.fst"
let en = (FStar_TypeChecker_Env.set_current_module en m.FStar_Syntax_Syntax.name)
in (let _151_1322 = (FStar_List.fold_left do_sigelt en m.FStar_Syntax_Syntax.exports)
in (FStar_TypeChecker_Env.finish_module _151_1322 m)))))

# 2339 "FStar.TypeChecker.Tc.fst"
let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 2340 "FStar.TypeChecker.Tc.fst"
let _72_3186 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _151_1327 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _151_1327))
end else begin
()
end
in (
# 2342 "FStar.TypeChecker.Tc.fst"
let env = (
# 2342 "FStar.TypeChecker.Tc.fst"
let _72_3188 = env
in {FStar_TypeChecker_Env.solver = _72_3188.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _72_3188.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _72_3188.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _72_3188.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _72_3188.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _72_3188.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _72_3188.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _72_3188.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _72_3188.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _72_3188.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _72_3188.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _72_3188.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _72_3188.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _72_3188.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _72_3188.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _72_3188.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _72_3188.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _72_3188.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _72_3188.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _72_3188.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 2343 "FStar.TypeChecker.Tc.fst"
let _72_3194 = (tc_tot_or_gtot_term env e)
in (match (_72_3194) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected a total term; got a ghost term", e.FStar_Syntax_Syntax.pos))))
end
end)))))

# 2348 "FStar.TypeChecker.Tc.fst"
let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (
# 2349 "FStar.TypeChecker.Tc.fst"
let _72_3197 = if ((let _151_1332 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _151_1332)) <> 0) then begin
(let _151_1333 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _151_1333))
end else begin
()
end
in (
# 2351 "FStar.TypeChecker.Tc.fst"
let _72_3201 = (tc_modul env m)
in (match (_72_3201) with
| (m, env) -> begin
(
# 2352 "FStar.TypeChecker.Tc.fst"
let _72_3202 = if (FStar_Options.should_dump m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _151_1334 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _151_1334))
end else begin
()
end
in (m, env))
end))))




