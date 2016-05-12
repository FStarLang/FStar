
open Prims
# 43 "FStar.TypeChecker.Tc.fst"
type effect_cost =
| ForFree
| NotForFree

# 43 "FStar.TypeChecker.Tc.fst"
let is_ForFree = (fun _discr_ -> (match (_discr_) with
| ForFree (_) -> begin
true
end
| _ -> begin
false
end))

# 43 "FStar.TypeChecker.Tc.fst"
let is_NotForFree = (fun _discr_ -> (match (_discr_) with
| NotForFree (_) -> begin
true
end
| _ -> begin
false
end))

# 45 "FStar.TypeChecker.Tc.fst"
let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_ST.read FStar_Options.log_types) && (not ((let _146_5 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _146_5))))))

# 46 "FStar.TypeChecker.Tc.fst"
let rng : FStar_TypeChecker_Env.env  ->  FStar_Range.range = (fun env -> (FStar_TypeChecker_Env.get_range env))

# 47 "FStar.TypeChecker.Tc.fst"
let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (
# 47 "FStar.TypeChecker.Tc.fst"
let _57_17 = env
in {FStar_TypeChecker_Env.solver = _57_17.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_17.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_17.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_17.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_17.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_17.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_17.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_17.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_17.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _57_17.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_17.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_17.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_17.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_17.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_17.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_17.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_17.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_17.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_17.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_17.FStar_TypeChecker_Env.use_bv_sorts}))

# 48 "FStar.TypeChecker.Tc.fst"
let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (
# 48 "FStar.TypeChecker.Tc.fst"
let _57_20 = env
in {FStar_TypeChecker_Env.solver = _57_20.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_20.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_20.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_20.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_20.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_20.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_20.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_20.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_20.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _57_20.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_20.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_20.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_20.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_20.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_20.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_20.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_20.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_20.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_20.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_20.FStar_TypeChecker_Env.use_bv_sorts}))

# 49 "FStar.TypeChecker.Tc.fst"
let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (
# 51 "FStar.TypeChecker.Tc.fst"
let r = if (tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
v.FStar_Syntax_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos tl.FStar_Syntax_Syntax.pos)
end
in (let _146_19 = (let _146_18 = (FStar_Syntax_Syntax.as_arg v)
in (let _146_17 = (let _146_16 = (FStar_Syntax_Syntax.as_arg tl)
in (_146_16)::[])
in (_146_18)::_146_17))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _146_19 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))

# 54 "FStar.TypeChecker.Tc.fst"
let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _57_1 -> (match (_57_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _57_30 -> begin
false
end))

# 57 "FStar.TypeChecker.Tc.fst"
let steps : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Normalize.step Prims.list = (fun env -> if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::[]
end else begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]
end)

# 61 "FStar.TypeChecker.Tc.fst"
let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Beta)::[]) env t))

# 62 "FStar.TypeChecker.Tc.fst"
let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _146_32 = (steps env)
in (FStar_TypeChecker_Normalize.normalize _146_32 env t)))

# 63 "FStar.TypeChecker.Tc.fst"
let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _146_37 = (steps env)
in (FStar_TypeChecker_Normalize.normalize_comp _146_37 env c)))

# 64 "FStar.TypeChecker.Tc.fst"
let check_no_escape : FStar_Syntax_Syntax.term Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun head_opt env fvs kt -> (
# 65 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
()
end
| _57_47 -> begin
(
# 68 "FStar.TypeChecker.Tc.fst"
let fvs' = (let _146_50 = if try_norm then begin
(norm env t)
end else begin
t
end
in (FStar_Syntax_Free.names _146_50))
in (match ((FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)) with
| None -> begin
()
end
| Some (x) -> begin
if (not (try_norm)) then begin
(aux true t)
end else begin
(
# 74 "FStar.TypeChecker.Tc.fst"
let fail = (fun _57_54 -> (match (()) with
| () -> begin
(
# 75 "FStar.TypeChecker.Tc.fst"
let msg = (match (head_opt) with
| None -> begin
(let _146_54 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _146_54))
end
| Some (head) -> begin
(let _146_56 = (FStar_Syntax_Print.bv_to_string x)
in (let _146_55 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _146_56 _146_55)))
end)
in (let _146_59 = (let _146_58 = (let _146_57 = (FStar_TypeChecker_Env.get_range env)
in (msg, _146_57))
in FStar_Syntax_Syntax.Error (_146_58))
in (Prims.raise _146_59)))
end))
in (
# 80 "FStar.TypeChecker.Tc.fst"
let s = (let _146_61 = (let _146_60 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _146_60))
in (FStar_TypeChecker_Util.new_uvar env _146_61))
in (match ((FStar_TypeChecker_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g)
end
| _57_63 -> begin
(fail ())
end)))
end
end))
end))
in (aux false kt)))

# 87 "FStar.TypeChecker.Tc.fst"
let maybe_push_binding : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder  ->  FStar_TypeChecker_Env.env = (fun env b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
env
end else begin
(
# 89 "FStar.TypeChecker.Tc.fst"
let _57_66 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_67 = (FStar_Syntax_Print.bv_to_string (Prims.fst b))
in (let _146_66 = (FStar_Syntax_Print.term_to_string (Prims.fst b).FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _146_67 _146_66)))
end else begin
()
end
in (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))
end)

# 93 "FStar.TypeChecker.Tc.fst"
let maybe_make_subst = (fun _57_2 -> (match (_57_2) with
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Syntax_Syntax.NT ((x, e)))::[]
end
| _57_75 -> begin
[]
end))

# 97 "FStar.TypeChecker.Tc.fst"
let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.subst_t = (fun s b v -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
s
end else begin
(FStar_Syntax_Syntax.NT (((Prims.fst b), v)))::s
end)

# 101 "FStar.TypeChecker.Tc.fst"
let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (
# 102 "FStar.TypeChecker.Tc.fst"
let _57_81 = lc
in {FStar_Syntax_Syntax.eff_name = _57_81.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _57_81.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _57_83 -> (match (()) with
| () -> begin
(let _146_80 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _146_80 t))
end))}))

# 104 "FStar.TypeChecker.Tc.fst"
let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (
# 105 "FStar.TypeChecker.Tc.fst"
let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _146_89 = if (not ((FStar_Syntax_Util.is_pure_or_ghost_function t))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _146_89))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (
# 110 "FStar.TypeChecker.Tc.fst"
let t = lc.FStar_Syntax_Syntax.res_typ
in (
# 111 "FStar.TypeChecker.Tc.fst"
let _57_115 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, guard)
end
| Some (t') -> begin
(
# 114 "FStar.TypeChecker.Tc.fst"
let _57_97 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_91 = (FStar_Syntax_Print.term_to_string t)
in (let _146_90 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _146_91 _146_90)))
end else begin
()
end
in (
# 116 "FStar.TypeChecker.Tc.fst"
let _57_101 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_57_101) with
| (e, lc) -> begin
(
# 117 "FStar.TypeChecker.Tc.fst"
let t = lc.FStar_Syntax_Syntax.res_typ
in (
# 118 "FStar.TypeChecker.Tc.fst"
let _57_105 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_57_105) with
| (e, g) -> begin
(
# 119 "FStar.TypeChecker.Tc.fst"
let _57_106 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_93 = (FStar_Syntax_Print.term_to_string t)
in (let _146_92 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _146_93 _146_92)))
end else begin
()
end
in (
# 121 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (
# 122 "FStar.TypeChecker.Tc.fst"
let _57_111 = (let _146_99 = (FStar_All.pipe_left (fun _146_98 -> Some (_146_98)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _146_99 env e lc g))
in (match (_57_111) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))))
end)))
end)))
end)
in (match (_57_115) with
| (e, lc, g) -> begin
(
# 124 "FStar.TypeChecker.Tc.fst"
let _57_116 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_100 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _146_100))
end else begin
()
end
in (e, lc, g))
end)))))

# 128 "FStar.TypeChecker.Tc.fst"
let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (t) -> begin
(
# 132 "FStar.TypeChecker.Tc.fst"
let _57_126 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_57_126) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))

# 135 "FStar.TypeChecker.Tc.fst"
let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _57_131 -> (match (_57_131) with
| (e, c) -> begin
(
# 136 "FStar.TypeChecker.Tc.fst"
let expected_c_opt = (match (copt) with
| Some (_57_133) -> begin
copt
end
| None -> begin
if ((FStar_ST.read FStar_Options.ml_ish) && (FStar_Ident.lid_equals FStar_Syntax_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) then begin
(let _146_113 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (_146_113))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
if (FStar_Syntax_Util.is_pure_comp c) then begin
(let _146_114 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (_146_114))
end else begin
if (FStar_Syntax_Util.is_pure_or_ghost_comp c) then begin
(let _146_115 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (_146_115))
end else begin
None
end
end
end
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _146_116 = (norm_c env c)
in (e, _146_116, FStar_TypeChecker_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(
# 152 "FStar.TypeChecker.Tc.fst"
let _57_140 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_119 = (FStar_Syntax_Print.term_to_string e)
in (let _146_118 = (FStar_Syntax_Print.comp_to_string c)
in (let _146_117 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _146_119 _146_118 _146_117))))
end else begin
()
end
in (
# 155 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 156 "FStar.TypeChecker.Tc.fst"
let _57_143 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_122 = (FStar_Syntax_Print.term_to_string e)
in (let _146_121 = (FStar_Syntax_Print.comp_to_string c)
in (let _146_120 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _146_122 _146_121 _146_120))))
end else begin
()
end
in (
# 161 "FStar.TypeChecker.Tc.fst"
let _57_149 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_57_149) with
| (e, _57_147, g) -> begin
(
# 162 "FStar.TypeChecker.Tc.fst"
let g = (let _146_123 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _146_123 "could not prove post-condition" g))
in (
# 163 "FStar.TypeChecker.Tc.fst"
let _57_151 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_125 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _146_124 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _146_125 _146_124)))
end else begin
()
end
in (e, expected_c, g)))
end)))))
end))
end))

# 166 "FStar.TypeChecker.Tc.fst"
let no_logical_guard = (fun env _57_157 -> (match (_57_157) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
(te, kt, f)
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _146_131 = (let _146_130 = (let _146_129 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _146_128 = (FStar_TypeChecker_Env.get_range env)
in (_146_129, _146_128)))
in FStar_Syntax_Syntax.Error (_146_130))
in (Prims.raise _146_131))
end)
end))

# 171 "FStar.TypeChecker.Tc.fst"
let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _146_134 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _146_134))
end))

# 178 "FStar.TypeChecker.Tc.fst"
let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _57_181; FStar_Syntax_Syntax.result_typ = _57_179; FStar_Syntax_Syntax.effect_args = _pre::_post::(pats, _57_173)::[]; FStar_Syntax_Syntax.flags = _57_170}) -> begin
(
# 182 "FStar.TypeChecker.Tc.fst"
let pat_vars = (FStar_Syntax_Free.names pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _57_188 -> (match (_57_188) with
| (b, _57_187) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _57_192) -> begin
(let _146_141 = (let _146_140 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _146_140))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _146_141))
end))
end
| _57_196 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end)

# 193 "FStar.TypeChecker.Tc.fst"
let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun env actuals expected_c -> (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(
# 197 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 198 "FStar.TypeChecker.Tc.fst"
let env = (
# 198 "FStar.TypeChecker.Tc.fst"
let _57_203 = env
in {FStar_TypeChecker_Env.solver = _57_203.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_203.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_203.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_203.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_203.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_203.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_203.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_203.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_203.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_203.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_203.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_203.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_203.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_203.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_203.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_203.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_203.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_203.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_203.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_203.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 199 "FStar.TypeChecker.Tc.fst"
let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (
# 201 "FStar.TypeChecker.Tc.fst"
let decreases_clause = (fun bs c -> (
# 203 "FStar.TypeChecker.Tc.fst"
let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _57_215 -> (match (_57_215) with
| (b, _57_214) -> begin
(
# 205 "FStar.TypeChecker.Tc.fst"
let t = (let _146_155 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _146_155))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _57_224 -> begin
(let _146_156 = (FStar_Syntax_Syntax.bv_to_name b)
in (_146_156)::[])
end))
end)))))
in (
# 210 "FStar.TypeChecker.Tc.fst"
let as_lex_list = (fun dec -> (
# 211 "FStar.TypeChecker.Tc.fst"
let _57_230 = (FStar_Syntax_Util.head_and_args dec)
in (match (_57_230) with
| (head, _57_229) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _57_234 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (
# 215 "FStar.TypeChecker.Tc.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _57_3 -> (match (_57_3) with
| FStar_Syntax_Syntax.DECREASES (_57_238) -> begin
true
end
| _57_241 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _57_246 -> begin
(
# 219 "FStar.TypeChecker.Tc.fst"
let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| x::[] -> begin
x
end
| _57_251 -> begin
(mk_lex_list xs)
end))
end)))))
in (
# 224 "FStar.TypeChecker.Tc.fst"
let previous_dec = (decreases_clause actuals expected_c)
in (
# 225 "FStar.TypeChecker.Tc.fst"
let guard_one_letrec = (fun _57_256 -> (match (_57_256) with
| (l, t) -> begin
(match ((let _146_162 = (FStar_Syntax_Subst.compress t)
in _146_162.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 229 "FStar.TypeChecker.Tc.fst"
let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _57_263 -> (match (_57_263) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _146_166 = (let _146_165 = (let _146_164 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_146_164))
in (FStar_Syntax_Syntax.new_bv _146_165 x.FStar_Syntax_Syntax.sort))
in (_146_166, imp))
end else begin
(x, imp)
end
end))))
in (
# 230 "FStar.TypeChecker.Tc.fst"
let _57_267 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_57_267) with
| (formals, c) -> begin
(
# 231 "FStar.TypeChecker.Tc.fst"
let dec = (decreases_clause formals c)
in (
# 232 "FStar.TypeChecker.Tc.fst"
let precedes = (let _146_170 = (let _146_169 = (FStar_Syntax_Syntax.as_arg dec)
in (let _146_168 = (let _146_167 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_146_167)::[])
in (_146_169)::_146_168))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _146_170 None r))
in (
# 233 "FStar.TypeChecker.Tc.fst"
let _57_274 = (FStar_Util.prefix formals)
in (match (_57_274) with
| (bs, (last, imp)) -> begin
(
# 234 "FStar.TypeChecker.Tc.fst"
let last = (
# 234 "FStar.TypeChecker.Tc.fst"
let _57_275 = last
in (let _146_171 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _57_275.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_275.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_171}))
in (
# 235 "FStar.TypeChecker.Tc.fst"
let refined_formals = (FStar_List.append bs (((last, imp))::[]))
in (
# 236 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (
# 237 "FStar.TypeChecker.Tc.fst"
let _57_280 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_174 = (FStar_Syntax_Print.lbname_to_string l)
in (let _146_173 = (FStar_Syntax_Print.term_to_string t)
in (let _146_172 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _146_174 _146_173 _146_172))))
end else begin
()
end
in (l, t')))))
end))))
end)))
end
| _57_283 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end))

# 249 "FStar.TypeChecker.Tc.fst"
let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (
# 249 "FStar.TypeChecker.Tc.fst"
let _57_286 = env
in {FStar_TypeChecker_Env.solver = _57_286.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_286.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_286.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_286.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_286.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_286.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_286.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_286.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_286.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_286.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_286.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_286.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_286.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_286.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_286.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_286.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_286.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_286.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_286.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_286.FStar_TypeChecker_Env.use_bv_sorts}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 254 "FStar.TypeChecker.Tc.fst"
let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (
# 255 "FStar.TypeChecker.Tc.fst"
let _57_291 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_242 = (let _146_240 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _146_240))
in (let _146_241 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _146_242 _146_241)))
end else begin
()
end
in (
# 256 "FStar.TypeChecker.Tc.fst"
let top = e
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_57_295) -> begin
(let _146_246 = (FStar_Syntax_Subst.compress e)
in (tc_term env _146_246))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(
# 273 "FStar.TypeChecker.Tc.fst"
let _57_336 = (tc_tot_or_gtot_term env e)
in (match (_57_336) with
| (e, c, g) -> begin
(
# 274 "FStar.TypeChecker.Tc.fst"
let g = (
# 274 "FStar.TypeChecker.Tc.fst"
let _57_337 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_337.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_337.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_337.FStar_TypeChecker_Env.implicits})
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(
# 278 "FStar.TypeChecker.Tc.fst"
let _57_347 = (FStar_Syntax_Util.type_u ())
in (match (_57_347) with
| (t, u) -> begin
(
# 279 "FStar.TypeChecker.Tc.fst"
let _57_351 = (tc_check_tot_or_gtot_term env e t)
in (match (_57_351) with
| (e, c, g) -> begin
(
# 280 "FStar.TypeChecker.Tc.fst"
let _57_358 = (
# 281 "FStar.TypeChecker.Tc.fst"
let _57_355 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_355) with
| (env, _57_354) -> begin
(tc_pats env pats)
end))
in (match (_57_358) with
| (pats, g') -> begin
(
# 283 "FStar.TypeChecker.Tc.fst"
let g' = (
# 283 "FStar.TypeChecker.Tc.fst"
let _57_359 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_359.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_359.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_359.FStar_TypeChecker_Env.implicits})
in (let _146_248 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_pattern (pats)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_247 = (FStar_TypeChecker_Rel.conj_guard g g')
in (_146_248, c, _146_247))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _146_249 = (FStar_Syntax_Subst.compress e)
in _146_249.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_57_368, {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _57_375; FStar_Syntax_Syntax.lbtyp = _57_373; FStar_Syntax_Syntax.lbeff = _57_371; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 291 "FStar.TypeChecker.Tc.fst"
let _57_386 = (let _146_250 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _146_250 e1))
in (match (_57_386) with
| (e1, c1, g1) -> begin
(
# 292 "FStar.TypeChecker.Tc.fst"
let _57_390 = (tc_term env e2)
in (match (_57_390) with
| (e2, c2, g2) -> begin
(
# 293 "FStar.TypeChecker.Tc.fst"
let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (None, c2))
in (
# 294 "FStar.TypeChecker.Tc.fst"
let e = (let _146_255 = (let _146_254 = (let _146_253 = (let _146_252 = (let _146_251 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Common.t_unit, e1))
in (_146_251)::[])
in (false, _146_252))
in (_146_253, e2))
in FStar_Syntax_Syntax.Tm_let (_146_254))
in (FStar_Syntax_Syntax.mk _146_255 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 295 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_256 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _146_256)))))
end))
end))
end
| _57_395 -> begin
(
# 298 "FStar.TypeChecker.Tc.fst"
let _57_399 = (tc_term env e)
in (match (_57_399) with
| (e, c, g) -> begin
(
# 299 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(
# 304 "FStar.TypeChecker.Tc.fst"
let _57_408 = (tc_term env e)
in (match (_57_408) with
| (e, c, g) -> begin
(
# 305 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, m))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _57_414) -> begin
(
# 309 "FStar.TypeChecker.Tc.fst"
let _57_421 = (tc_comp env expected_c)
in (match (_57_421) with
| (expected_c, _57_419, g) -> begin
(
# 310 "FStar.TypeChecker.Tc.fst"
let _57_425 = (tc_term env e)
in (match (_57_425) with
| (e, c', g') -> begin
(
# 311 "FStar.TypeChecker.Tc.fst"
let _57_429 = (let _146_258 = (let _146_257 = (c'.FStar_Syntax_Syntax.comp ())
in (e, _146_257))
in (check_expected_effect env (Some (expected_c)) _146_258))
in (match (_57_429) with
| (e, expected_c, g'') -> begin
(
# 312 "FStar.TypeChecker.Tc.fst"
let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (let _146_261 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t_res), Some ((FStar_Syntax_Util.comp_effect_name expected_c))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_260 = (let _146_259 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _146_259))
in (_146_261, (FStar_Syntax_Util.lcomp_of_comp expected_c), _146_260))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _57_435) -> begin
(
# 318 "FStar.TypeChecker.Tc.fst"
let _57_440 = (FStar_Syntax_Util.type_u ())
in (match (_57_440) with
| (k, u) -> begin
(
# 319 "FStar.TypeChecker.Tc.fst"
let _57_445 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_445) with
| (t, _57_443, f) -> begin
(
# 320 "FStar.TypeChecker.Tc.fst"
let _57_449 = (let _146_262 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _146_262 e))
in (match (_57_449) with
| (e, c, g) -> begin
(
# 321 "FStar.TypeChecker.Tc.fst"
let _57_453 = (let _146_266 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_450 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _146_266 e c f))
in (match (_57_453) with
| (c, f) -> begin
(
# 322 "FStar.TypeChecker.Tc.fst"
let _57_457 = (let _146_267 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t), Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _146_267 c))
in (match (_57_457) with
| (e, c, f2) -> begin
(let _146_269 = (let _146_268 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _146_268))
in (e, c, _146_269))
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
let env = (let _146_271 = (let _146_270 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_270 Prims.fst))
in (FStar_All.pipe_right _146_271 instantiate_both))
in (
# 328 "FStar.TypeChecker.Tc.fst"
let _57_464 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_273 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _146_272 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _146_273 _146_272)))
end else begin
()
end
in (
# 332 "FStar.TypeChecker.Tc.fst"
let _57_469 = (tc_term (no_inst env) head)
in (match (_57_469) with
| (head, chead, g_head) -> begin
(
# 333 "FStar.TypeChecker.Tc.fst"
let _57_473 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _146_274 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _146_274))
end else begin
(let _146_275 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _146_275))
end
in (match (_57_473) with
| (e, c, g) -> begin
(
# 336 "FStar.TypeChecker.Tc.fst"
let _57_474 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_276 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _146_276))
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
let _57_480 = (comp_check_expected_typ env0 e c)
in (match (_57_480) with
| (e, c, g') -> begin
(
# 344 "FStar.TypeChecker.Tc.fst"
let gimp = (match ((let _146_277 = (FStar_Syntax_Subst.compress head)
in _146_277.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _57_483) -> begin
(
# 347 "FStar.TypeChecker.Tc.fst"
let imp = ("head of application is a uvar", env0, u, e, c.FStar_Syntax_Syntax.res_typ, head.FStar_Syntax_Syntax.pos)
in (
# 348 "FStar.TypeChecker.Tc.fst"
let _57_487 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_487.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_487.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_487.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _57_490 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (
# 350 "FStar.TypeChecker.Tc.fst"
let gres = (let _146_278 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _146_278))
in (
# 351 "FStar.TypeChecker.Tc.fst"
let _57_493 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_279 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print1 "Guard from application node is %s\n" _146_279))
end else begin
()
end
in (e, c, gres))))
end))))
end))
end)))))
end
| FStar_Syntax_Syntax.Tm_match (e1, eqns) -> begin
(
# 356 "FStar.TypeChecker.Tc.fst"
let _57_501 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_501) with
| (env1, topt) -> begin
(
# 357 "FStar.TypeChecker.Tc.fst"
let env1 = (instantiate_both env1)
in (
# 358 "FStar.TypeChecker.Tc.fst"
let _57_506 = (tc_term env1 e1)
in (match (_57_506) with
| (e1, c1, g1) -> begin
(
# 359 "FStar.TypeChecker.Tc.fst"
let _57_517 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(
# 362 "FStar.TypeChecker.Tc.fst"
let _57_513 = (FStar_Syntax_Util.type_u ())
in (match (_57_513) with
| (k, _57_512) -> begin
(
# 363 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _146_280 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_146_280, res_t)))
end))
end)
in (match (_57_517) with
| (env_branches, res_t) -> begin
(
# 366 "FStar.TypeChecker.Tc.fst"
let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (
# 367 "FStar.TypeChecker.Tc.fst"
let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (
# 368 "FStar.TypeChecker.Tc.fst"
let _57_534 = (
# 369 "FStar.TypeChecker.Tc.fst"
let _57_531 = (FStar_List.fold_right (fun _57_525 _57_528 -> (match ((_57_525, _57_528)) with
| ((_57_521, f, c, g), (caccum, gaccum)) -> begin
(let _146_283 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _146_283))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_531) with
| (cases, g) -> begin
(let _146_284 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_146_284, g))
end))
in (match (_57_534) with
| (c_branches, g_branches) -> begin
(
# 373 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (Some (guard_x), c_branches))
in (
# 374 "FStar.TypeChecker.Tc.fst"
let e = (let _146_288 = (let _146_287 = (let _146_286 = (FStar_List.map (fun _57_543 -> (match (_57_543) with
| (f, _57_538, _57_540, _57_542) -> begin
f
end)) t_eqns)
in (e1, _146_286))
in FStar_Syntax_Syntax.Tm_match (_146_287))
in (FStar_Syntax_Syntax.mk _146_288 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (
# 376 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ), Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (
# 377 "FStar.TypeChecker.Tc.fst"
let _57_546 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_291 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _146_290 = (let _146_289 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _146_289))
in (FStar_Util.print2 "(%s) comp type = %s\n" _146_291 _146_290)))
end else begin
()
end
in (let _146_292 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _146_292))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_558); FStar_Syntax_Syntax.lbunivs = _57_556; FStar_Syntax_Syntax.lbtyp = _57_554; FStar_Syntax_Syntax.lbeff = _57_552; FStar_Syntax_Syntax.lbdef = _57_550}::[]), _57_564) -> begin
(
# 384 "FStar.TypeChecker.Tc.fst"
let _57_567 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_293 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _146_293))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _57_571), _57_574) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_589); FStar_Syntax_Syntax.lbunivs = _57_587; FStar_Syntax_Syntax.lbtyp = _57_585; FStar_Syntax_Syntax.lbeff = _57_583; FStar_Syntax_Syntax.lbdef = _57_581}::_57_579), _57_595) -> begin
(
# 391 "FStar.TypeChecker.Tc.fst"
let _57_598 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_294 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _146_294))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _57_602), _57_605) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 404 "FStar.TypeChecker.Tc.fst"
let check_instantiated_fvar = (fun env v dc e t -> (
# 405 "FStar.TypeChecker.Tc.fst"
let _57_619 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_619) with
| (e, t, implicits) -> begin
(
# 407 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _146_308 = (let _146_307 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_307))
in FStar_Util.Inr (_146_308))
end
in (
# 408 "FStar.TypeChecker.Tc.fst"
let is_data_ctor = (fun _57_4 -> (match (_57_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _57_629 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _146_314 = (let _146_313 = (let _146_312 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _146_311 = (FStar_TypeChecker_Env.get_range env)
in (_146_312, _146_311)))
in FStar_Syntax_Syntax.Error (_146_313))
in (Prims.raise _146_314))
end else begin
(value_check_expected_typ env e tc implicits)
end))
end)))
in (
# 418 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (
# 419 "FStar.TypeChecker.Tc.fst"
let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(FStar_All.failwith "Impossible: Violation of locally nameless convention")
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(
# 425 "FStar.TypeChecker.Tc.fst"
let g = (match ((let _146_315 = (FStar_Syntax_Subst.compress t1)
in _146_315.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_640) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _57_643 -> begin
(
# 427 "FStar.TypeChecker.Tc.fst"
let imp = ("uvar in term", env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (
# 428 "FStar.TypeChecker.Tc.fst"
let _57_645 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_645.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_645.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_645.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 433 "FStar.TypeChecker.Tc.fst"
let _57_651 = (FStar_Syntax_Util.type_u ())
in (match (_57_651) with
| (k, u) -> begin
(
# 434 "FStar.TypeChecker.Tc.fst"
let t = (FStar_TypeChecker_Util.new_uvar env k)
in (
# 435 "FStar.TypeChecker.Tc.fst"
let e = (FStar_TypeChecker_Util.new_uvar env t)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
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
let _57_657 = x
in {FStar_Syntax_Syntax.ppname = _57_657.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_657.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (
# 441 "FStar.TypeChecker.Tc.fst"
let _57_663 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_663) with
| (e, t, implicits) -> begin
(
# 442 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _146_317 = (let _146_316 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_316))
in FStar_Util.Inr (_146_317))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _57_670; FStar_Syntax_Syntax.pos = _57_668; FStar_Syntax_Syntax.vars = _57_666}, us) -> begin
(
# 446 "FStar.TypeChecker.Tc.fst"
let us = (FStar_List.map (tc_universe env) us)
in (
# 447 "FStar.TypeChecker.Tc.fst"
let _57_680 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_680) with
| (us', t) -> begin
(
# 448 "FStar.TypeChecker.Tc.fst"
let _57_687 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _146_320 = (let _146_319 = (let _146_318 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _146_318))
in FStar_Syntax_Syntax.Error (_146_319))
in (Prims.raise _146_320))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _57_686 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (
# 453 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 453 "FStar.TypeChecker.Tc.fst"
let _57_689 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 453 "FStar.TypeChecker.Tc.fst"
let _57_691 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_691.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_691.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_689.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_689.FStar_Syntax_Syntax.fv_qual})
in (
# 454 "FStar.TypeChecker.Tc.fst"
let e = (let _146_323 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_323 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(
# 458 "FStar.TypeChecker.Tc.fst"
let _57_699 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_699) with
| (us, t) -> begin
(
# 459 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 459 "FStar.TypeChecker.Tc.fst"
let _57_700 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 459 "FStar.TypeChecker.Tc.fst"
let _57_702 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_702.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_702.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_700.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_700.FStar_Syntax_Syntax.fv_qual})
in (
# 460 "FStar.TypeChecker.Tc.fst"
let e = (let _146_324 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_324 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t)))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(
# 464 "FStar.TypeChecker.Tc.fst"
let t = (tc_constant top.FStar_Syntax_Syntax.pos c)
in (
# 465 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 469 "FStar.TypeChecker.Tc.fst"
let _57_716 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_716) with
| (bs, c) -> begin
(
# 470 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 471 "FStar.TypeChecker.Tc.fst"
let _57_721 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_721) with
| (env, _57_720) -> begin
(
# 472 "FStar.TypeChecker.Tc.fst"
let _57_726 = (tc_binders env bs)
in (match (_57_726) with
| (bs, env, g, us) -> begin
(
# 473 "FStar.TypeChecker.Tc.fst"
let _57_730 = (tc_comp env c)
in (match (_57_730) with
| (c, uc, f) -> begin
(
# 474 "FStar.TypeChecker.Tc.fst"
let e = (
# 474 "FStar.TypeChecker.Tc.fst"
let _57_731 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _57_731.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_731.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_731.FStar_Syntax_Syntax.vars})
in (
# 475 "FStar.TypeChecker.Tc.fst"
let _57_734 = (check_smt_pat env e bs c)
in (
# 476 "FStar.TypeChecker.Tc.fst"
let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (
# 477 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 478 "FStar.TypeChecker.Tc.fst"
let g = (let _146_325 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _146_325))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(
# 482 "FStar.TypeChecker.Tc.fst"
let u = (tc_universe env u)
in (
# 483 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) None top.FStar_Syntax_Syntax.pos)
in (
# 484 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 488 "FStar.TypeChecker.Tc.fst"
let _57_750 = (let _146_327 = (let _146_326 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_326)::[])
in (FStar_Syntax_Subst.open_term _146_327 phi))
in (match (_57_750) with
| (x, phi) -> begin
(
# 489 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 490 "FStar.TypeChecker.Tc.fst"
let _57_755 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_755) with
| (env, _57_754) -> begin
(
# 491 "FStar.TypeChecker.Tc.fst"
let _57_760 = (let _146_328 = (FStar_List.hd x)
in (tc_binder env _146_328))
in (match (_57_760) with
| (x, env, f1, u) -> begin
(
# 492 "FStar.TypeChecker.Tc.fst"
let _57_761 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_331 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _146_330 = (FStar_Syntax_Print.term_to_string phi)
in (let _146_329 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _146_331 _146_330 _146_329))))
end else begin
()
end
in (
# 495 "FStar.TypeChecker.Tc.fst"
let _57_766 = (FStar_Syntax_Util.type_u ())
in (match (_57_766) with
| (t_phi, _57_765) -> begin
(
# 496 "FStar.TypeChecker.Tc.fst"
let _57_771 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_57_771) with
| (phi, _57_769, f2) -> begin
(
# 497 "FStar.TypeChecker.Tc.fst"
let e = (
# 497 "FStar.TypeChecker.Tc.fst"
let _57_772 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _57_772.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_772.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_772.FStar_Syntax_Syntax.vars})
in (
# 498 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 499 "FStar.TypeChecker.Tc.fst"
let g = (let _146_332 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _146_332))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _57_780) -> begin
(
# 503 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (
# 504 "FStar.TypeChecker.Tc.fst"
let _57_786 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_333 = (FStar_Syntax_Print.term_to_string (
# 505 "FStar.TypeChecker.Tc.fst"
let _57_784 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _57_784.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_784.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_784.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _146_333))
end else begin
()
end
in (
# 506 "FStar.TypeChecker.Tc.fst"
let _57_790 = (FStar_Syntax_Subst.open_term bs body)
in (match (_57_790) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _57_792 -> begin
(let _146_335 = (let _146_334 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _146_334))
in (FStar_All.failwith _146_335))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_57_797) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_57_800, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_57_805, Some (FStar_Const.Unsigned, FStar_Const.Int8)) -> begin
FStar_TypeChecker_Common.t_uint8
end
| FStar_Const.Const_int (_57_813, Some (FStar_Const.Signed, FStar_Const.Int8)) -> begin
FStar_TypeChecker_Common.t_int8
end
| FStar_Const.Const_int (_57_821, Some (FStar_Const.Unsigned, FStar_Const.Int16)) -> begin
FStar_TypeChecker_Common.t_uint16
end
| FStar_Const.Const_int (_57_829, Some (FStar_Const.Signed, FStar_Const.Int16)) -> begin
FStar_TypeChecker_Common.t_int16
end
| FStar_Const.Const_int (_57_837, Some (FStar_Const.Unsigned, FStar_Const.Int32)) -> begin
FStar_TypeChecker_Common.t_uint32
end
| FStar_Const.Const_int (_57_845, Some (FStar_Const.Signed, FStar_Const.Int32)) -> begin
FStar_TypeChecker_Common.t_int32
end
| FStar_Const.Const_int (_57_853, Some (FStar_Const.Unsigned, FStar_Const.Int64)) -> begin
FStar_TypeChecker_Common.t_uint64
end
| FStar_Const.Const_int (_57_861, Some (FStar_Const.Signed, FStar_Const.Int64)) -> begin
FStar_TypeChecker_Common.t_int64
end
| FStar_Const.Const_string (_57_869) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_57_872) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_57_875) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_57_879) -> begin
FStar_TypeChecker_Common.t_range
end
| _57_882 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 542 "FStar.TypeChecker.Tc.fst"
let _57_889 = (FStar_Syntax_Util.type_u ())
in (match (_57_889) with
| (k, u) -> begin
(
# 543 "FStar.TypeChecker.Tc.fst"
let _57_894 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_894) with
| (t, _57_892, g) -> begin
(let _146_340 = (FStar_Syntax_Syntax.mk_Total t)
in (_146_340, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 547 "FStar.TypeChecker.Tc.fst"
let _57_899 = (FStar_Syntax_Util.type_u ())
in (match (_57_899) with
| (k, u) -> begin
(
# 548 "FStar.TypeChecker.Tc.fst"
let _57_904 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_904) with
| (t, _57_902, g) -> begin
(let _146_341 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_146_341, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 552 "FStar.TypeChecker.Tc.fst"
let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (
# 553 "FStar.TypeChecker.Tc.fst"
let tc = (let _146_343 = (let _146_342 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_146_342)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _146_343 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 554 "FStar.TypeChecker.Tc.fst"
let _57_913 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_57_913) with
| (tc, _57_911, f) -> begin
(
# 555 "FStar.TypeChecker.Tc.fst"
let _57_917 = (FStar_Syntax_Util.head_and_args tc)
in (match (_57_917) with
| (_57_915, args) -> begin
(
# 556 "FStar.TypeChecker.Tc.fst"
let _57_920 = (let _146_345 = (FStar_List.hd args)
in (let _146_344 = (FStar_List.tl args)
in (_146_345, _146_344)))
in (match (_57_920) with
| (res, args) -> begin
(
# 557 "FStar.TypeChecker.Tc.fst"
let _57_936 = (let _146_347 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _57_5 -> (match (_57_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(
# 559 "FStar.TypeChecker.Tc.fst"
let _57_927 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_927) with
| (env, _57_926) -> begin
(
# 560 "FStar.TypeChecker.Tc.fst"
let _57_932 = (tc_tot_or_gtot_term env e)
in (match (_57_932) with
| (e, _57_930, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _146_347 FStar_List.unzip))
in (match (_57_936) with
| (flags, guards) -> begin
(
# 563 "FStar.TypeChecker.Tc.fst"
let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| _57_941 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _146_349 = (FStar_Syntax_Syntax.mk_Comp (
# 566 "FStar.TypeChecker.Tc.fst"
let _57_943 = c
in {FStar_Syntax_Syntax.effect_name = _57_943.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _57_943.FStar_Syntax_Syntax.flags}))
in (let _146_348 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_146_349, u, _146_348))))
end))
end))
end))
end))))
end))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (
# 573 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun u -> (
# 574 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_57_951) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _146_354 = (aux u)
in FStar_Syntax_Syntax.U_succ (_146_354))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _146_355 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_146_355))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _146_359 = (let _146_358 = (let _146_357 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _146_356 = (FStar_TypeChecker_Env.get_range env)
in (_146_357, _146_356)))
in FStar_Syntax_Syntax.Error (_146_358))
in (Prims.raise _146_359))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _146_360 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_360 Prims.snd))
end
| _57_966 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (
# 596 "FStar.TypeChecker.Tc.fst"
let fail = (fun msg t -> (let _146_369 = (let _146_368 = (let _146_367 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_146_367, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_368))
in (Prims.raise _146_369)))
in (
# 605 "FStar.TypeChecker.Tc.fst"
let check_binders = (fun env bs bs_expected -> (
# 610 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun _57_984 bs bs_expected -> (match (_57_984) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| ((hd, imp)::bs, (hd_expected, imp')::bs_expected) -> begin
(
# 614 "FStar.TypeChecker.Tc.fst"
let _57_1015 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _146_386 = (let _146_385 = (let _146_384 = (let _146_382 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _146_382))
in (let _146_383 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_146_384, _146_383)))
in FStar_Syntax_Syntax.Error (_146_385))
in (Prims.raise _146_386))
end
| _57_1014 -> begin
()
end)
in (
# 621 "FStar.TypeChecker.Tc.fst"
let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (
# 622 "FStar.TypeChecker.Tc.fst"
let _57_1032 = (match ((let _146_387 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _146_387.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _57_1020 -> begin
(
# 625 "FStar.TypeChecker.Tc.fst"
let _57_1021 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_388 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _146_388))
end else begin
()
end
in (
# 626 "FStar.TypeChecker.Tc.fst"
let _57_1027 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_57_1027) with
| (t, _57_1025, g1) -> begin
(
# 627 "FStar.TypeChecker.Tc.fst"
let g2 = (let _146_390 = (FStar_TypeChecker_Env.get_range env)
in (let _146_389 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _146_390 "Type annotation on parameter incompatible with the expected type" _146_389)))
in (
# 631 "FStar.TypeChecker.Tc.fst"
let g = (let _146_391 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _146_391))
in (t, g)))
end)))
end)
in (match (_57_1032) with
| (t, g) -> begin
(
# 633 "FStar.TypeChecker.Tc.fst"
let hd = (
# 633 "FStar.TypeChecker.Tc.fst"
let _57_1033 = hd
in {FStar_Syntax_Syntax.ppname = _57_1033.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1033.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 634 "FStar.TypeChecker.Tc.fst"
let b = (hd, imp)
in (
# 635 "FStar.TypeChecker.Tc.fst"
let b_expected = (hd_expected, imp')
in (
# 636 "FStar.TypeChecker.Tc.fst"
let env = (maybe_push_binding env b)
in (
# 637 "FStar.TypeChecker.Tc.fst"
let subst = (let _146_392 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _146_392))
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
# 647 "FStar.TypeChecker.Tc.fst"
let rec expected_function_typ = (fun env t0 body -> (match (t0) with
| None -> begin
(
# 658 "FStar.TypeChecker.Tc.fst"
let _57_1054 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1053 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (
# 661 "FStar.TypeChecker.Tc.fst"
let _57_1061 = (tc_binders env bs)
in (match (_57_1061) with
| (bs, envbody, g, _57_1060) -> begin
(
# 662 "FStar.TypeChecker.Tc.fst"
let _57_1079 = (match ((let _146_399 = (FStar_Syntax_Subst.compress body)
in _146_399.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _57_1066) -> begin
(
# 664 "FStar.TypeChecker.Tc.fst"
let _57_1073 = (tc_comp envbody c)
in (match (_57_1073) with
| (c, _57_1071, g') -> begin
(let _146_400 = (FStar_TypeChecker_Rel.conj_guard g g')
in (Some (c), body, _146_400))
end))
end
| _57_1075 -> begin
(None, body, g)
end)
in (match (_57_1079) with
| (copt, body, g) -> begin
(None, bs, [], copt, envbody, body, g)
end))
end)))
end
| Some (t) -> begin
(
# 670 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 671 "FStar.TypeChecker.Tc.fst"
let rec as_function_typ = (fun norm t -> (match ((let _146_405 = (FStar_Syntax_Subst.compress t)
in _146_405.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 675 "FStar.TypeChecker.Tc.fst"
let _57_1106 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1105 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 676 "FStar.TypeChecker.Tc.fst"
let _57_1113 = (tc_binders env bs)
in (match (_57_1113) with
| (bs, envbody, g, _57_1112) -> begin
(
# 677 "FStar.TypeChecker.Tc.fst"
let _57_1117 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_57_1117) with
| (envbody, _57_1116) -> begin
(Some ((t, true)), bs, [], None, envbody, body, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _57_1120) -> begin
(
# 683 "FStar.TypeChecker.Tc.fst"
let _57_1131 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_57_1131) with
| (_57_1124, bs, bs', copt, env, body, g) -> begin
(Some ((t, false)), bs, bs', copt, env, body, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 687 "FStar.TypeChecker.Tc.fst"
let _57_1138 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_57_1138) with
| (bs_expected, c_expected) -> begin
(
# 694 "FStar.TypeChecker.Tc.fst"
let check_actuals_against_formals = (fun env bs bs_expected -> (
# 695 "FStar.TypeChecker.Tc.fst"
let rec handle_more = (fun _57_1149 c_expected -> (match (_57_1149) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _146_416 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _146_416))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(
# 700 "FStar.TypeChecker.Tc.fst"
let c = (let _146_417 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _146_417))
in (let _146_418 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _146_418)))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(
# 704 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.subst_comp subst c_expected)
in if (FStar_Syntax_Util.is_total_comp c) then begin
(
# 707 "FStar.TypeChecker.Tc.fst"
let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 710 "FStar.TypeChecker.Tc.fst"
let _57_1170 = (check_binders env more_bs bs_expected)
in (match (_57_1170) with
| (env, bs', more, guard', subst) -> begin
(let _146_420 = (let _146_419 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _146_419, subst))
in (handle_more _146_420 c_expected))
end))
end
| _57_1172 -> begin
(let _146_422 = (let _146_421 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _146_421))
in (fail _146_422 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _146_423 = (check_binders env bs bs_expected)
in (handle_more _146_423 c_expected))))
in (
# 717 "FStar.TypeChecker.Tc.fst"
let mk_letrec_env = (fun envbody bs c -> (
# 718 "FStar.TypeChecker.Tc.fst"
let letrecs = (guard_letrecs envbody bs c)
in (
# 719 "FStar.TypeChecker.Tc.fst"
let envbody = (
# 719 "FStar.TypeChecker.Tc.fst"
let _57_1178 = envbody
in {FStar_TypeChecker_Env.solver = _57_1178.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1178.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1178.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1178.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1178.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1178.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1178.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1178.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1178.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1178.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1178.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1178.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_1178.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1178.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1178.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1178.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1178.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1178.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1178.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1178.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _57_1183 _57_1186 -> (match ((_57_1183, _57_1186)) with
| ((env, letrec_binders), (l, t)) -> begin
(
# 723 "FStar.TypeChecker.Tc.fst"
let _57_1192 = (let _146_433 = (let _146_432 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_432 Prims.fst))
in (tc_term _146_433 t))
in (match (_57_1192) with
| (t, _57_1189, _57_1191) -> begin
(
# 724 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (
# 725 "FStar.TypeChecker.Tc.fst"
let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _146_434 = (FStar_Syntax_Syntax.mk_binder (
# 726 "FStar.TypeChecker.Tc.fst"
let _57_1196 = x
in {FStar_Syntax_Syntax.ppname = _57_1196.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1196.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_146_434)::letrec_binders)
end
| _57_1199 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (
# 731 "FStar.TypeChecker.Tc.fst"
let _57_1205 = (check_actuals_against_formals env bs bs_expected)
in (match (_57_1205) with
| (envbody, bs, g, c) -> begin
(
# 732 "FStar.TypeChecker.Tc.fst"
let _57_1208 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_57_1208) with
| (envbody, letrecs) -> begin
(
# 733 "FStar.TypeChecker.Tc.fst"
let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, body, g))
end))
end))))
end))
end
| _57_1211 -> begin
if (not (norm)) then begin
(let _146_435 = (unfold_whnf env t)
in (as_function_typ true _146_435))
end else begin
(
# 741 "FStar.TypeChecker.Tc.fst"
let _57_1221 = (expected_function_typ env None body)
in (match (_57_1221) with
| (_57_1213, bs, _57_1216, c_opt, envbody, body, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, body, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (
# 745 "FStar.TypeChecker.Tc.fst"
let use_eq = env.FStar_TypeChecker_Env.use_eq
in (
# 746 "FStar.TypeChecker.Tc.fst"
let _57_1225 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1225) with
| (env, topt) -> begin
(
# 748 "FStar.TypeChecker.Tc.fst"
let _57_1229 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_436 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _146_436 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (
# 753 "FStar.TypeChecker.Tc.fst"
let _57_1238 = (expected_function_typ env topt body)
in (match (_57_1238) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(
# 754 "FStar.TypeChecker.Tc.fst"
let _57_1244 = (tc_term (
# 754 "FStar.TypeChecker.Tc.fst"
let _57_1239 = envbody
in {FStar_TypeChecker_Env.solver = _57_1239.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1239.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1239.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1239.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1239.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1239.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1239.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1239.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1239.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1239.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1239.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1239.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1239.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1239.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1239.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1239.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1239.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1239.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1239.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_57_1244) with
| (body, cbody, guard_body) -> begin
(
# 756 "FStar.TypeChecker.Tc.fst"
let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (
# 759 "FStar.TypeChecker.Tc.fst"
let _57_1246 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _146_439 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _146_438 = (let _146_437 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _146_437))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _146_439 _146_438)))
end else begin
()
end
in (
# 764 "FStar.TypeChecker.Tc.fst"
let _57_1253 = (let _146_441 = (let _146_440 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _146_440))
in (check_expected_effect (
# 764 "FStar.TypeChecker.Tc.fst"
let _57_1248 = envbody
in {FStar_TypeChecker_Env.solver = _57_1248.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1248.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1248.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1248.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1248.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1248.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1248.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1248.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1248.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1248.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1248.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1248.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1248.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1248.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1248.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1248.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1248.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1248.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1248.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1248.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _146_441))
in (match (_57_1253) with
| (body, cbody, guard) -> begin
(
# 765 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (
# 766 "FStar.TypeChecker.Tc.fst"
let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _146_442 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _146_442))
end else begin
(
# 768 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (
# 771 "FStar.TypeChecker.Tc.fst"
let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (
# 772 "FStar.TypeChecker.Tc.fst"
let e = (let _146_445 = (let _146_444 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _146_443 -> FStar_Util.Inl (_146_443)))
in Some (_146_444))
in (FStar_Syntax_Util.abs bs body _146_445))
in (
# 773 "FStar.TypeChecker.Tc.fst"
let _57_1276 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(
# 775 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_1265) -> begin
(e, t, guard)
end
| _57_1268 -> begin
(
# 782 "FStar.TypeChecker.Tc.fst"
let _57_1271 = if use_teq then begin
(let _146_446 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _146_446))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_57_1271) with
| (e, guard') -> begin
(let _146_447 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _146_447))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_57_1276) with
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
let _57_1280 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_57_1280) with
| (c, g) -> begin
(e, c, g)
end)))
end))))))
end))))
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
let _57_1290 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_456 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _146_455 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _146_456 _146_455)))
end else begin
()
end
in (
# 804 "FStar.TypeChecker.Tc.fst"
let rec check_function_app = (fun norm tf -> (match ((let _146_461 = (FStar_Syntax_Util.unrefine tf)
in _146_461.FStar_Syntax_Syntax.n)) with
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
let _57_1324 = (tc_term env e)
in (match (_57_1324) with
| (e, c, g_e) -> begin
(
# 812 "FStar.TypeChecker.Tc.fst"
let _57_1328 = (tc_args env tl)
in (match (_57_1328) with
| (args, comps, g_rest) -> begin
(let _146_466 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, ((e.FStar_Syntax_Syntax.pos, c))::comps, _146_466))
end))
end))
end))
in (
# 820 "FStar.TypeChecker.Tc.fst"
let _57_1332 = (tc_args env args)
in (match (_57_1332) with
| (args, comps, g_args) -> begin
(
# 821 "FStar.TypeChecker.Tc.fst"
let bs = (let _146_468 = (FStar_All.pipe_right comps (FStar_List.map (fun _57_1336 -> (match (_57_1336) with
| (_57_1334, c) -> begin
(c.FStar_Syntax_Syntax.res_typ, None)
end))))
in (FStar_Syntax_Util.null_binders_of_tks _146_468))
in (
# 822 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _57_1342 -> begin
FStar_Syntax_Util.ml_comp
end)
in (
# 825 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _146_483 = (FStar_Syntax_Subst.compress t)
in _146_483.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_1348) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _57_1353 -> begin
ml_or_tot
end)
end)
in (
# 832 "FStar.TypeChecker.Tc.fst"
let cres = (let _146_488 = (let _146_487 = (let _146_486 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_486 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _146_487))
in (ml_or_tot _146_488 r))
in (
# 833 "FStar.TypeChecker.Tc.fst"
let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (
# 834 "FStar.TypeChecker.Tc.fst"
let _57_1357 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_491 = (FStar_Syntax_Print.term_to_string head)
in (let _146_490 = (FStar_Syntax_Print.term_to_string tf)
in (let _146_489 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _146_491 _146_490 _146_489))))
end else begin
()
end
in (
# 839 "FStar.TypeChecker.Tc.fst"
let _57_1359 = (let _146_492 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _146_492))
in (
# 840 "FStar.TypeChecker.Tc.fst"
let comp = (let _146_495 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _57_1363 out -> (match (_57_1363) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c (None, out))
end)) (((head.FStar_Syntax_Syntax.pos, chead))::comps) _146_495))
in (let _146_497 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _146_496 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_146_497, comp, _146_496)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 848 "FStar.TypeChecker.Tc.fst"
let _57_1372 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_1372) with
| (bs, c) -> begin
(
# 850 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun _57_1380 bs cres args -> (match (_57_1380) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (_57_1387)))::rest, (_57_1395, None)::_57_1393) -> begin
(
# 861 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 862 "FStar.TypeChecker.Tc.fst"
let _57_1401 = (check_no_escape (Some (head)) env fvs t)
in (
# 863 "FStar.TypeChecker.Tc.fst"
let _57_1407 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_57_1407) with
| (varg, _57_1405, implicits) -> begin
(
# 864 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (
# 865 "FStar.TypeChecker.Tc.fst"
let arg = (let _146_506 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _146_506))
in (let _146_508 = (let _146_507 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _146_507, fvs))
in (tc_args _146_508 rest cres args))))
end))))
end
| ((x, aqual)::rest, (e, aq)::rest') -> begin
(
# 869 "FStar.TypeChecker.Tc.fst"
let _57_1439 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _57_1438 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (
# 874 "FStar.TypeChecker.Tc.fst"
let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 875 "FStar.TypeChecker.Tc.fst"
let x = (
# 875 "FStar.TypeChecker.Tc.fst"
let _57_1442 = x
in {FStar_Syntax_Syntax.ppname = _57_1442.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1442.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (
# 876 "FStar.TypeChecker.Tc.fst"
let _57_1445 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_509 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _146_509))
end else begin
()
end
in (
# 877 "FStar.TypeChecker.Tc.fst"
let _57_1447 = (check_no_escape (Some (head)) env fvs targ)
in (
# 878 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (
# 879 "FStar.TypeChecker.Tc.fst"
let env = (
# 879 "FStar.TypeChecker.Tc.fst"
let _57_1450 = env
in {FStar_TypeChecker_Env.solver = _57_1450.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1450.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1450.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1450.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1450.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1450.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1450.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1450.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1450.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1450.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1450.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1450.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1450.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1450.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1450.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _57_1450.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1450.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1450.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1450.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1450.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 880 "FStar.TypeChecker.Tc.fst"
let _57_1453 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_512 = (FStar_Syntax_Print.tag_of_term e)
in (let _146_511 = (FStar_Syntax_Print.term_to_string e)
in (let _146_510 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _146_512 _146_511 _146_510))))
end else begin
()
end
in (
# 881 "FStar.TypeChecker.Tc.fst"
let _57_1458 = (tc_term env e)
in (match (_57_1458) with
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
let subst = (let _146_513 = (FStar_List.hd bs)
in (maybe_extend_subst subst _146_513 e))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(
# 889 "FStar.TypeChecker.Tc.fst"
let subst = (let _146_514 = (FStar_List.hd bs)
in (maybe_extend_subst subst _146_514 e))
in (
# 890 "FStar.TypeChecker.Tc.fst"
let _57_1465 = (((e.FStar_Syntax_Syntax.pos, Some (x), c))::comps, g)
in (match (_57_1465) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _146_515 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _146_515)) then begin
(
# 894 "FStar.TypeChecker.Tc.fst"
let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (
# 895 "FStar.TypeChecker.Tc.fst"
let arg' = (let _146_516 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _146_516))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((e.FStar_Syntax_Syntax.pos, Some (newx), c))::comps, g, fvs) rest cres rest')))
end else begin
(let _146_520 = (let _146_519 = (let _146_518 = (let _146_517 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _146_517))
in (_146_518)::arg_rets)
in (subst, (arg)::outargs, _146_519, ((e.FStar_Syntax_Syntax.pos, Some (x), c))::comps, g, (x)::fvs))
in (tc_args _146_520 rest cres rest'))
end
end
end))
end))))))))))
end
| (_57_1469, []) -> begin
(
# 904 "FStar.TypeChecker.Tc.fst"
let _57_1472 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (
# 905 "FStar.TypeChecker.Tc.fst"
let _57_1492 = (match (bs) with
| [] -> begin
(
# 908 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (
# 914 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (
# 916 "FStar.TypeChecker.Tc.fst"
let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _57_1482 -> (match (_57_1482) with
| (_57_1478, _57_1480, c) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (
# 923 "FStar.TypeChecker.Tc.fst"
let cres = if refine_with_equality then begin
(let _146_522 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _146_522 cres))
end else begin
(
# 929 "FStar.TypeChecker.Tc.fst"
let _57_1484 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_525 = (FStar_Syntax_Print.term_to_string head)
in (let _146_524 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _146_523 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _146_525 _146_524 _146_523))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _57_1488 -> begin
(
# 938 "FStar.TypeChecker.Tc.fst"
let g = (let _146_526 = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (FStar_All.pipe_right _146_526 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _146_531 = (let _146_530 = (let _146_529 = (let _146_528 = (let _146_527 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _146_527))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _146_528))
in (FStar_Syntax_Syntax.mk_Total _146_529))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_530))
in (_146_531, g)))
end)
in (match (_57_1492) with
| (cres, g) -> begin
(
# 941 "FStar.TypeChecker.Tc.fst"
let _57_1493 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_532 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _146_532))
end else begin
()
end
in (
# 942 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_List.fold_left (fun out _57_1499 -> (match (_57_1499) with
| (r1, x, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c (x, out))
end)) cres comps)
in (
# 943 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.bind head.FStar_Syntax_Syntax.pos env None chead (None, comp))
in (
# 944 "FStar.TypeChecker.Tc.fst"
let app = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev outargs) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (
# 945 "FStar.TypeChecker.Tc.fst"
let _57_1505 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp g)
in (match (_57_1505) with
| (comp, g) -> begin
(app, comp, g)
end))))))
end)))
end
| ([], arg::_57_1508) -> begin
(
# 950 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun norm tres -> (
# 951 "FStar.TypeChecker.Tc.fst"
let tres = (let _146_540 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _146_540 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(
# 954 "FStar.TypeChecker.Tc.fst"
let _57_1520 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_541 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _146_541))
end else begin
()
end
in (let _146_545 = (let _146_544 = (let _146_543 = (let _146_542 = (FStar_TypeChecker_Env.get_range env)
in (_146_542, None, cres))
in (_146_543)::comps)
in (subst, outargs, arg_rets, _146_544, g, fvs))
in (tc_args _146_545 bs (FStar_Syntax_Util.lcomp_of_comp cres') args)))
end
| _57_1523 when (not (norm)) -> begin
(let _146_546 = (unfold_whnf env tres)
in (aux true _146_546))
end
| _57_1525 -> begin
(let _146_552 = (let _146_551 = (let _146_550 = (let _146_548 = (FStar_TypeChecker_Normalize.term_to_string env tf)
in (let _146_547 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _146_548 _146_547)))
in (let _146_549 = (FStar_Syntax_Syntax.argpos arg)
in (_146_550, _146_549)))
in FStar_Syntax_Syntax.Error (_146_551))
in (Prims.raise _146_552))
end)))
in (aux false cres.FStar_Syntax_Syntax.res_typ))
end)
end))
in (tc_args ([], [], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs (FStar_Syntax_Util.lcomp_of_comp c) args))
end))
end
| _57_1527 -> begin
if (not (norm)) then begin
(let _146_553 = (unfold_whnf env tf)
in (check_function_app true _146_553))
end else begin
(let _146_556 = (let _146_555 = (let _146_554 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_146_554, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_555))
in (Prims.raise _146_556))
end
end))
in (let _146_558 = (let _146_557 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _146_557))
in (check_function_app false _146_558))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (
# 980 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 981 "FStar.TypeChecker.Tc.fst"
let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(
# 984 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in (
# 985 "FStar.TypeChecker.Tc.fst"
let _57_1563 = (FStar_List.fold_left2 (fun _57_1544 _57_1547 _57_1550 -> (match ((_57_1544, _57_1547, _57_1550)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(
# 986 "FStar.TypeChecker.Tc.fst"
let _57_1551 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 987 "FStar.TypeChecker.Tc.fst"
let _57_1556 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_57_1556) with
| (e, c, g) -> begin
(
# 988 "FStar.TypeChecker.Tc.fst"
let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (
# 989 "FStar.TypeChecker.Tc.fst"
let g = (let _146_568 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _146_568 g))
in (
# 990 "FStar.TypeChecker.Tc.fst"
let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _146_572 = (let _146_570 = (let _146_569 = (FStar_Syntax_Syntax.as_arg e)
in (_146_569)::[])
in (FStar_List.append seen _146_570))
in (let _146_571 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_146_572, _146_571, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_57_1563) with
| (args, guard, ghost) -> begin
(
# 994 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (
# 995 "FStar.TypeChecker.Tc.fst"
let c = if ghost then begin
(let _146_573 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _146_573 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (
# 996 "FStar.TypeChecker.Tc.fst"
let _57_1568 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_57_1568) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _57_1570 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (
# 1016 "FStar.TypeChecker.Tc.fst"
let _57_1577 = (FStar_Syntax_Subst.open_branch branch)
in (match (_57_1577) with
| (pattern, when_clause, branch_exp) -> begin
(
# 1017 "FStar.TypeChecker.Tc.fst"
let _57_1582 = branch
in (match (_57_1582) with
| (cpat, _57_1580, cbr) -> begin
(
# 1020 "FStar.TypeChecker.Tc.fst"
let tc_pat = (fun allow_implicits pat_t p0 -> (
# 1027 "FStar.TypeChecker.Tc.fst"
let _57_1590 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_57_1590) with
| (pat_bvs, exps, p) -> begin
(
# 1028 "FStar.TypeChecker.Tc.fst"
let _57_1591 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_585 = (FStar_Syntax_Print.pat_to_string p0)
in (let _146_584 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _146_585 _146_584)))
end else begin
()
end
in (
# 1030 "FStar.TypeChecker.Tc.fst"
let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (
# 1031 "FStar.TypeChecker.Tc.fst"
let _57_1597 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_57_1597) with
| (env1, _57_1596) -> begin
(
# 1032 "FStar.TypeChecker.Tc.fst"
let env1 = (
# 1032 "FStar.TypeChecker.Tc.fst"
let _57_1598 = env1
in {FStar_TypeChecker_Env.solver = _57_1598.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1598.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1598.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1598.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1598.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1598.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1598.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1598.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _57_1598.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1598.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1598.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1598.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1598.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1598.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1598.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1598.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1598.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1598.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1598.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1598.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1033 "FStar.TypeChecker.Tc.fst"
let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (
# 1034 "FStar.TypeChecker.Tc.fst"
let _57_1637 = (let _146_608 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (
# 1035 "FStar.TypeChecker.Tc.fst"
let _57_1603 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_588 = (FStar_Syntax_Print.term_to_string e)
in (let _146_587 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _146_588 _146_587)))
end else begin
()
end
in (
# 1038 "FStar.TypeChecker.Tc.fst"
let _57_1608 = (tc_term env1 e)
in (match (_57_1608) with
| (e, lc, g) -> begin
(
# 1040 "FStar.TypeChecker.Tc.fst"
let _57_1609 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_590 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _146_589 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _146_590 _146_589)))
end else begin
()
end
in (
# 1043 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (
# 1044 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (
# 1045 "FStar.TypeChecker.Tc.fst"
let _57_1615 = (let _146_591 = (FStar_TypeChecker_Rel.discharge_guard env (
# 1045 "FStar.TypeChecker.Tc.fst"
let _57_1613 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_1613.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_1613.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_1613.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _146_591 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1046 "FStar.TypeChecker.Tc.fst"
let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (
# 1047 "FStar.TypeChecker.Tc.fst"
let uvars_to_string = (fun uvs -> (let _146_596 = (let _146_595 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _146_595 (FStar_List.map (fun _57_1623 -> (match (_57_1623) with
| (u, _57_1622) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _146_596 (FStar_String.concat ", "))))
in (
# 1048 "FStar.TypeChecker.Tc.fst"
let uvs1 = (FStar_Syntax_Free.uvars e')
in (
# 1049 "FStar.TypeChecker.Tc.fst"
let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (
# 1050 "FStar.TypeChecker.Tc.fst"
let _57_1631 = if (let _146_597 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _146_597)) then begin
(
# 1051 "FStar.TypeChecker.Tc.fst"
let unresolved = (let _146_598 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _146_598 FStar_Util.set_elements))
in (let _146_606 = (let _146_605 = (let _146_604 = (let _146_603 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _146_602 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _146_601 = (let _146_600 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _57_1630 -> (match (_57_1630) with
| (u, _57_1629) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _146_600 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _146_603 _146_602 _146_601))))
in (_146_604, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_146_605))
in (Prims.raise _146_606)))
end else begin
()
end
in (
# 1058 "FStar.TypeChecker.Tc.fst"
let _57_1633 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_607 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _146_607))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _146_608 FStar_List.unzip))
in (match (_57_1637) with
| (exps, norm_exps) -> begin
(
# 1063 "FStar.TypeChecker.Tc.fst"
let p = (FStar_TypeChecker_Util.decorate_pattern env p exps)
in (p, pat_bvs, pat_env, exps, norm_exps))
end))))
end))))
end)))
in (
# 1067 "FStar.TypeChecker.Tc.fst"
let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (
# 1068 "FStar.TypeChecker.Tc.fst"
let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (
# 1069 "FStar.TypeChecker.Tc.fst"
let _57_1644 = (let _146_609 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _146_609 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_57_1644) with
| (scrutinee_env, _57_1643) -> begin
(
# 1072 "FStar.TypeChecker.Tc.fst"
let _57_1650 = (tc_pat true pat_t pattern)
in (match (_57_1650) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(
# 1075 "FStar.TypeChecker.Tc.fst"
let _57_1660 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(
# 1082 "FStar.TypeChecker.Tc.fst"
let _57_1657 = (let _146_610 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _146_610 e))
in (match (_57_1657) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_57_1660) with
| (when_clause, g_when) -> begin
(
# 1086 "FStar.TypeChecker.Tc.fst"
let _57_1664 = (tc_term pat_env branch_exp)
in (match (_57_1664) with
| (branch_exp, c, g_branch) -> begin
(
# 1090 "FStar.TypeChecker.Tc.fst"
let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _146_612 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _146_611 -> Some (_146_611)) _146_612))
end)
in (
# 1097 "FStar.TypeChecker.Tc.fst"
let _57_1720 = (
# 1100 "FStar.TypeChecker.Tc.fst"
let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (
# 1101 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _57_1682 -> begin
(
# 1107 "FStar.TypeChecker.Tc.fst"
let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _146_616 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _146_615 -> Some (_146_615)) _146_616))
end))
end))) None))
in (
# 1112 "FStar.TypeChecker.Tc.fst"
let _57_1690 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_57_1690) with
| (c, g_branch) -> begin
(
# 1116 "FStar.TypeChecker.Tc.fst"
let _57_1715 = (match ((eqs, when_condition)) with
| (None, None) -> begin
(c, g_when)
end
| (Some (f), None) -> begin
(
# 1122 "FStar.TypeChecker.Tc.fst"
let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1123 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _146_619 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _146_618 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_146_619, _146_618)))))
end
| (Some (f), Some (w)) -> begin
(
# 1128 "FStar.TypeChecker.Tc.fst"
let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1129 "FStar.TypeChecker.Tc.fst"
let g_fw = (let _146_620 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_146_620))
in (let _146_623 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _146_622 = (let _146_621 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _146_621 g_when))
in (_146_623, _146_622)))))
end
| (None, Some (w)) -> begin
(
# 1134 "FStar.TypeChecker.Tc.fst"
let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (
# 1135 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _146_624 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_146_624, g_when))))
end)
in (match (_57_1715) with
| (c_weak, g_when_weak) -> begin
(
# 1140 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _146_626 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _146_625 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_146_626, _146_625, g_branch))))
end))
end)))
in (match (_57_1720) with
| (c, g_when, g_branch) -> begin
(
# 1158 "FStar.TypeChecker.Tc.fst"
let branch_guard = (
# 1160 "FStar.TypeChecker.Tc.fst"
let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (
# 1161 "FStar.TypeChecker.Tc.fst"
let discriminate = (fun scrutinee_tm f -> if ((let _146_636 = (let _146_635 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _146_635))
in (FStar_List.length _146_636)) > 1) then begin
(
# 1164 "FStar.TypeChecker.Tc.fst"
let disc = (let _146_637 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _146_637 FStar_Syntax_Syntax.Delta_equational None))
in (
# 1165 "FStar.TypeChecker.Tc.fst"
let disc = (let _146_639 = (let _146_638 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_146_638)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _146_639 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _146_640 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_146_640)::[])))
end else begin
[]
end)
in (
# 1169 "FStar.TypeChecker.Tc.fst"
let fail = (fun _57_1730 -> (match (()) with
| () -> begin
(let _146_646 = (let _146_645 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _146_644 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _146_643 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _146_645 _146_644 _146_643))))
in (FStar_All.failwith _146_646))
end))
in (
# 1175 "FStar.TypeChecker.Tc.fst"
let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _57_1737) -> begin
(head_constructor t)
end
| _57_1741 -> begin
(fail ())
end))
in (
# 1180 "FStar.TypeChecker.Tc.fst"
let pat_exp = (let _146_649 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _146_649 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_57_1766) -> begin
(let _146_654 = (let _146_653 = (let _146_652 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _146_651 = (let _146_650 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_146_650)::[])
in (_146_652)::_146_651))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _146_653 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_146_654)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 1189 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _146_655 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _146_655))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 1194 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(
# 1197 "FStar.TypeChecker.Tc.fst"
let sub_term_guards = (let _146_662 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _57_1784 -> (match (_57_1784) with
| (ei, _57_1783) -> begin
(
# 1198 "FStar.TypeChecker.Tc.fst"
let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _57_1788 -> begin
(
# 1202 "FStar.TypeChecker.Tc.fst"
let sub_term = (let _146_661 = (let _146_658 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _146_658 FStar_Syntax_Syntax.Delta_equational None))
in (let _146_660 = (let _146_659 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_146_659)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _146_661 _146_660 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _146_662 FStar_List.flatten))
in (let _146_663 = (discriminate scrutinee_tm f)
in (FStar_List.append _146_663 sub_term_guards)))
end)
end
| _57_1792 -> begin
[]
end))))))
in (
# 1208 "FStar.TypeChecker.Tc.fst"
let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(
# 1211 "FStar.TypeChecker.Tc.fst"
let t = (let _146_668 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _146_668))
in (
# 1212 "FStar.TypeChecker.Tc.fst"
let _57_1800 = (FStar_Syntax_Util.type_u ())
in (match (_57_1800) with
| (k, _57_1799) -> begin
(
# 1213 "FStar.TypeChecker.Tc.fst"
let _57_1806 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_57_1806) with
| (t, _57_1803, _57_1805) -> begin
t
end))
end)))
end)
in (
# 1217 "FStar.TypeChecker.Tc.fst"
let branch_guard = (let _146_669 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _146_669 FStar_Syntax_Util.mk_disj_l))
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
let _57_1814 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_670 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _146_670))
end else begin
()
end
in (let _146_671 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_146_671, branch_guard, c, guard)))))
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
let _57_1831 = (check_let_bound_def true env lb)
in (match (_57_1831) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(
# 1247 "FStar.TypeChecker.Tc.fst"
let _57_1843 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(
# 1250 "FStar.TypeChecker.Tc.fst"
let g1 = (let _146_674 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _146_674 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1251 "FStar.TypeChecker.Tc.fst"
let _57_1838 = (let _146_678 = (let _146_677 = (let _146_676 = (let _146_675 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _146_675))
in (_146_676)::[])
in (FStar_TypeChecker_Util.generalize env _146_677))
in (FStar_List.hd _146_678))
in (match (_57_1838) with
| (_57_1834, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_57_1843) with
| (g1, e1, univ_vars, c1) -> begin
(
# 1255 "FStar.TypeChecker.Tc.fst"
let _57_1853 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(
# 1257 "FStar.TypeChecker.Tc.fst"
let _57_1846 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_57_1846) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(
# 1260 "FStar.TypeChecker.Tc.fst"
let _57_1847 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _146_679 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _146_679 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _146_680 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_146_680, c1)))
end
end))
end else begin
(
# 1264 "FStar.TypeChecker.Tc.fst"
let _57_1849 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _146_681 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _146_681)))
end
in (match (_57_1853) with
| (e2, c1) -> begin
(
# 1269 "FStar.TypeChecker.Tc.fst"
let cres = (let _146_682 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_682))
in (
# 1270 "FStar.TypeChecker.Tc.fst"
let _57_1855 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1272 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _146_683 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_146_683, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _57_1859 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1289 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1292 "FStar.TypeChecker.Tc.fst"
let env = (
# 1292 "FStar.TypeChecker.Tc.fst"
let _57_1870 = env
in {FStar_TypeChecker_Env.solver = _57_1870.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1870.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1870.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1870.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1870.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1870.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1870.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1870.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1870.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1870.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1870.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1870.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1870.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1870.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1870.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1870.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1870.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1870.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1870.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1870.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1293 "FStar.TypeChecker.Tc.fst"
let _57_1879 = (let _146_687 = (let _146_686 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_686 Prims.fst))
in (check_let_bound_def false _146_687 lb))
in (match (_57_1879) with
| (e1, _57_1875, c1, g1, annotated) -> begin
(
# 1294 "FStar.TypeChecker.Tc.fst"
let x = (
# 1294 "FStar.TypeChecker.Tc.fst"
let _57_1880 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1880.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1880.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (
# 1295 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (
# 1296 "FStar.TypeChecker.Tc.fst"
let _57_1886 = (let _146_689 = (let _146_688 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_688)::[])
in (FStar_Syntax_Subst.open_term _146_689 e2))
in (match (_57_1886) with
| (xb, e2) -> begin
(
# 1297 "FStar.TypeChecker.Tc.fst"
let xbinder = (FStar_List.hd xb)
in (
# 1298 "FStar.TypeChecker.Tc.fst"
let x = (Prims.fst xbinder)
in (
# 1299 "FStar.TypeChecker.Tc.fst"
let _57_1892 = (let _146_690 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _146_690 e2))
in (match (_57_1892) with
| (e2, c2, g2) -> begin
(
# 1300 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (Some (x), c2))
in (
# 1301 "FStar.TypeChecker.Tc.fst"
let e = (let _146_693 = (let _146_692 = (let _146_691 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _146_691))
in FStar_Syntax_Syntax.Tm_let (_146_692))
in (FStar_Syntax_Syntax.mk _146_693 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 1302 "FStar.TypeChecker.Tc.fst"
let x_eq_e1 = (let _146_696 = (let _146_695 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _146_695 e1))
in (FStar_All.pipe_left (fun _146_694 -> FStar_TypeChecker_Common.NonTrivial (_146_694)) _146_696))
in (
# 1303 "FStar.TypeChecker.Tc.fst"
let g2 = (let _146_698 = (let _146_697 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _146_697 g2))
in (FStar_TypeChecker_Rel.close_guard xb _146_698))
in (
# 1305 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if annotated then begin
(e, cres, guard)
end else begin
(
# 1309 "FStar.TypeChecker.Tc.fst"
let _57_1898 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end)))))
end))))
end))))
end)))
end
| _57_1901 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1318 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1321 "FStar.TypeChecker.Tc.fst"
let _57_1913 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1913) with
| (lbs, e2) -> begin
(
# 1323 "FStar.TypeChecker.Tc.fst"
let _57_1916 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1916) with
| (env0, topt) -> begin
(
# 1324 "FStar.TypeChecker.Tc.fst"
let _57_1919 = (build_let_rec_env true env0 lbs)
in (match (_57_1919) with
| (lbs, rec_env) -> begin
(
# 1325 "FStar.TypeChecker.Tc.fst"
let _57_1922 = (check_let_recs rec_env lbs)
in (match (_57_1922) with
| (lbs, g_lbs) -> begin
(
# 1326 "FStar.TypeChecker.Tc.fst"
let g_lbs = (let _146_701 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _146_701 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1328 "FStar.TypeChecker.Tc.fst"
let all_lb_names = (let _146_704 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _146_704 (fun _146_703 -> Some (_146_703))))
in (
# 1330 "FStar.TypeChecker.Tc.fst"
let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(
# 1336 "FStar.TypeChecker.Tc.fst"
let ecs = (let _146_708 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _146_707 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _146_707)))))
in (FStar_TypeChecker_Util.generalize env _146_708))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _57_1933 -> (match (_57_1933) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (
# 1343 "FStar.TypeChecker.Tc.fst"
let cres = (let _146_710 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_710))
in (
# 1344 "FStar.TypeChecker.Tc.fst"
let _57_1936 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1346 "FStar.TypeChecker.Tc.fst"
let _57_1940 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1940) with
| (lbs, e2) -> begin
(let _146_712 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_711 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_146_712, cres, _146_711)))
end)))))))
end))
end))
end))
end))
end
| _57_1942 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1357 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1360 "FStar.TypeChecker.Tc.fst"
let _57_1954 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1954) with
| (lbs, e2) -> begin
(
# 1362 "FStar.TypeChecker.Tc.fst"
let _57_1957 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1957) with
| (env0, topt) -> begin
(
# 1363 "FStar.TypeChecker.Tc.fst"
let _57_1960 = (build_let_rec_env false env0 lbs)
in (match (_57_1960) with
| (lbs, rec_env) -> begin
(
# 1364 "FStar.TypeChecker.Tc.fst"
let _57_1963 = (check_let_recs rec_env lbs)
in (match (_57_1963) with
| (lbs, g_lbs) -> begin
(
# 1366 "FStar.TypeChecker.Tc.fst"
let _57_1975 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (
# 1367 "FStar.TypeChecker.Tc.fst"
let x = (
# 1367 "FStar.TypeChecker.Tc.fst"
let _57_1966 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1966.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1966.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (
# 1368 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1368 "FStar.TypeChecker.Tc.fst"
let _57_1969 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _57_1969.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1969.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1969.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _57_1969.FStar_Syntax_Syntax.lbdef})
in (
# 1369 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], lb.FStar_Syntax_Syntax.lbtyp))
in (env, lb))))) env))
in (match (_57_1975) with
| (env, lbs) -> begin
(
# 1372 "FStar.TypeChecker.Tc.fst"
let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (
# 1374 "FStar.TypeChecker.Tc.fst"
let _57_1981 = (tc_term env e2)
in (match (_57_1981) with
| (e2, cres, g2) -> begin
(
# 1375 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (
# 1376 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (
# 1377 "FStar.TypeChecker.Tc.fst"
let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (
# 1378 "FStar.TypeChecker.Tc.fst"
let cres = (
# 1378 "FStar.TypeChecker.Tc.fst"
let _57_1985 = cres
in {FStar_Syntax_Syntax.eff_name = _57_1985.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _57_1985.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_1985.FStar_Syntax_Syntax.comp})
in (
# 1380 "FStar.TypeChecker.Tc.fst"
let _57_1990 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1990) with
| (lbs, e2) -> begin
(
# 1381 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_57_1993) -> begin
(e, cres, guard)
end
| None -> begin
(
# 1385 "FStar.TypeChecker.Tc.fst"
let _57_1996 = (check_no_escape None env bvs tres)
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
| _57_1999 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (
# 1396 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1397 "FStar.TypeChecker.Tc.fst"
let _57_2032 = (FStar_List.fold_left (fun _57_2006 lb -> (match (_57_2006) with
| (lbs, env) -> begin
(
# 1398 "FStar.TypeChecker.Tc.fst"
let _57_2011 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_57_2011) with
| (univ_vars, t, check_t) -> begin
(
# 1399 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (
# 1400 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (
# 1401 "FStar.TypeChecker.Tc.fst"
let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(
# 1406 "FStar.TypeChecker.Tc.fst"
let _57_2020 = (let _146_724 = (let _146_723 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _146_723))
in (tc_check_tot_or_gtot_term (
# 1406 "FStar.TypeChecker.Tc.fst"
let _57_2014 = env0
in {FStar_TypeChecker_Env.solver = _57_2014.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2014.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2014.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2014.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2014.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2014.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2014.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2014.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2014.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2014.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2014.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2014.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2014.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2014.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _57_2014.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2014.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2014.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2014.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2014.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2014.FStar_TypeChecker_Env.use_bv_sorts}) t _146_724))
in (match (_57_2020) with
| (t, _57_2018, g) -> begin
(
# 1407 "FStar.TypeChecker.Tc.fst"
let _57_2021 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (
# 1409 "FStar.TypeChecker.Tc.fst"
let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(
# 1411 "FStar.TypeChecker.Tc.fst"
let _57_2024 = env
in {FStar_TypeChecker_Env.solver = _57_2024.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2024.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2024.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2024.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2024.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2024.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2024.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2024.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2024.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2024.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2024.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2024.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2024.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_2024.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2024.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2024.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2024.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2024.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2024.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2024.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (
# 1413 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1413 "FStar.TypeChecker.Tc.fst"
let _57_2027 = lb
in {FStar_Syntax_Syntax.lbname = _57_2027.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _57_2027.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_57_2032) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (
# 1420 "FStar.TypeChecker.Tc.fst"
let _57_2045 = (let _146_729 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 1421 "FStar.TypeChecker.Tc.fst"
let _57_2039 = (let _146_728 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _146_728 lb.FStar_Syntax_Syntax.lbdef))
in (match (_57_2039) with
| (e, c, g) -> begin
(
# 1422 "FStar.TypeChecker.Tc.fst"
let _57_2040 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1424 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _146_729 FStar_List.unzip))
in (match (_57_2045) with
| (lbs, gs) -> begin
(
# 1426 "FStar.TypeChecker.Tc.fst"
let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (
# 1440 "FStar.TypeChecker.Tc.fst"
let _57_2053 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_2053) with
| (env1, _57_2052) -> begin
(
# 1441 "FStar.TypeChecker.Tc.fst"
let e1 = lb.FStar_Syntax_Syntax.lbdef
in (
# 1444 "FStar.TypeChecker.Tc.fst"
let _57_2059 = (check_lbtyp top_level env lb)
in (match (_57_2059) with
| (topt, wf_annot, univ_vars, env1) -> begin
(
# 1446 "FStar.TypeChecker.Tc.fst"
let _57_2060 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1450 "FStar.TypeChecker.Tc.fst"
let _57_2067 = (tc_maybe_toplevel_term (
# 1450 "FStar.TypeChecker.Tc.fst"
let _57_2062 = env1
in {FStar_TypeChecker_Env.solver = _57_2062.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2062.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2062.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2062.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2062.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2062.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2062.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2062.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2062.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2062.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2062.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2062.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2062.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _57_2062.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2062.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2062.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2062.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2062.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2062.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2062.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_57_2067) with
| (e1, c1, g1) -> begin
(
# 1453 "FStar.TypeChecker.Tc.fst"
let _57_2071 = (let _146_736 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_2068 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _146_736 e1 c1 wf_annot))
in (match (_57_2071) with
| (c1, guard_f) -> begin
(
# 1456 "FStar.TypeChecker.Tc.fst"
let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (
# 1458 "FStar.TypeChecker.Tc.fst"
let _57_2073 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_737 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _146_737))
end else begin
()
end
in (let _146_738 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _146_738))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (
# 1470 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 1473 "FStar.TypeChecker.Tc.fst"
let _57_2080 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _57_2083 -> begin
(
# 1477 "FStar.TypeChecker.Tc.fst"
let _57_2086 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_57_2086) with
| (univ_vars, t) -> begin
(
# 1478 "FStar.TypeChecker.Tc.fst"
let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _146_742 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _146_742))
end else begin
(
# 1485 "FStar.TypeChecker.Tc.fst"
let _57_2091 = (FStar_Syntax_Util.type_u ())
in (match (_57_2091) with
| (k, _57_2090) -> begin
(
# 1486 "FStar.TypeChecker.Tc.fst"
let _57_2096 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_57_2096) with
| (t, _57_2094, g) -> begin
(
# 1487 "FStar.TypeChecker.Tc.fst"
let _57_2097 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _146_745 = (let _146_743 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _146_743))
in (let _146_744 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _146_745 _146_744)))
end else begin
()
end
in (
# 1491 "FStar.TypeChecker.Tc.fst"
let t = (norm env1 t)
in (let _146_746 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _146_746))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _57_2103 -> (match (_57_2103) with
| (x, imp) -> begin
(
# 1496 "FStar.TypeChecker.Tc.fst"
let _57_2106 = (FStar_Syntax_Util.type_u ())
in (match (_57_2106) with
| (tu, u) -> begin
(
# 1497 "FStar.TypeChecker.Tc.fst"
let _57_2111 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_57_2111) with
| (t, _57_2109, g) -> begin
(
# 1498 "FStar.TypeChecker.Tc.fst"
let x = ((
# 1498 "FStar.TypeChecker.Tc.fst"
let _57_2112 = x
in {FStar_Syntax_Syntax.ppname = _57_2112.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2112.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (
# 1499 "FStar.TypeChecker.Tc.fst"
let _57_2115 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_750 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _146_749 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _146_750 _146_749)))
end else begin
()
end
in (let _146_751 = (maybe_push_binding env x)
in (x, _146_751, g, u))))
end))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe Prims.list) = (fun env bs -> (
# 1504 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_TypeChecker_Rel.trivial_guard, [])
end
| b::bs -> begin
(
# 1507 "FStar.TypeChecker.Tc.fst"
let _57_2130 = (tc_binder env b)
in (match (_57_2130) with
| (b, env', g, u) -> begin
(
# 1508 "FStar.TypeChecker.Tc.fst"
let _57_2135 = (aux env' bs)
in (match (_57_2135) with
| (bs, env', g', us) -> begin
(let _146_759 = (let _146_758 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _146_758))
in ((b)::bs, env', _146_759, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (
# 1513 "FStar.TypeChecker.Tc.fst"
let tc_args = (fun env args -> (FStar_List.fold_right (fun _57_2143 _57_2146 -> (match ((_57_2143, _57_2146)) with
| ((t, imp), (args, g)) -> begin
(
# 1517 "FStar.TypeChecker.Tc.fst"
let _57_2151 = (tc_term env t)
in (match (_57_2151) with
| (t, _57_2149, g') -> begin
(let _146_768 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _146_768))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _57_2155 -> (match (_57_2155) with
| (pats, g) -> begin
(
# 1520 "FStar.TypeChecker.Tc.fst"
let _57_2158 = (tc_args env p)
in (match (_57_2158) with
| (args, g') -> begin
(let _146_771 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _146_771))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1525 "FStar.TypeChecker.Tc.fst"
let _57_2164 = (tc_maybe_toplevel_term env e)
in (match (_57_2164) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(
# 1528 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (
# 1529 "FStar.TypeChecker.Tc.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 1530 "FStar.TypeChecker.Tc.fst"
let _57_2167 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_774 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _146_774))
end else begin
()
end
in (
# 1531 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 1532 "FStar.TypeChecker.Tc.fst"
let _57_2172 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _146_775 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_146_775, false))
end else begin
(let _146_776 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_146_776, true))
end
in (match (_57_2172) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _146_777 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _146_777))
end
| _57_2176 -> begin
if allow_ghost then begin
(let _146_780 = (let _146_779 = (let _146_778 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_146_778, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_779))
in (Prims.raise _146_780))
end else begin
(let _146_783 = (let _146_782 = (let _146_781 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_146_781, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_782))
in (Prims.raise _146_783))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 1546 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))

# 1550 "FStar.TypeChecker.Tc.fst"
let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (
# 1551 "FStar.TypeChecker.Tc.fst"
let _57_2186 = (tc_tot_or_gtot_term env t)
in (match (_57_2186) with
| (t, c, g) -> begin
(
# 1552 "FStar.TypeChecker.Tc.fst"
let _57_2187 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))

# 1555 "FStar.TypeChecker.Tc.fst"
let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (
# 1556 "FStar.TypeChecker.Tc.fst"
let _57_2195 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_2195) with
| (t, c, g) -> begin
(
# 1557 "FStar.TypeChecker.Tc.fst"
let _57_2196 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))

# 1560 "FStar.TypeChecker.Tc.fst"
let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _146_803 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _146_803)))

# 1565 "FStar.TypeChecker.Tc.fst"
let check_nogen = (fun env t k -> (
# 1566 "FStar.TypeChecker.Tc.fst"
let t = (tc_check_trivial_guard env t k)
in (let _146_807 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _146_807))))

# 1569 "FStar.TypeChecker.Tc.fst"
let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (
# 1570 "FStar.TypeChecker.Tc.fst"
let _57_2211 = (tc_binders env tps)
in (match (_57_2211) with
| (tps, env, g, us) -> begin
(
# 1571 "FStar.TypeChecker.Tc.fst"
let _57_2212 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))

# 1574 "FStar.TypeChecker.Tc.fst"
let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (
# 1575 "FStar.TypeChecker.Tc.fst"
let fail = (fun _57_2218 -> (match (()) with
| () -> begin
(let _146_822 = (let _146_821 = (let _146_820 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_146_820, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_146_821))
in (Prims.raise _146_822))
end))
in (
# 1576 "FStar.TypeChecker.Tc.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1579 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _57_2235)::(wp, _57_2231)::(_wlp, _57_2227)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2239 -> begin
(fail ())
end))
end
| _57_2241 -> begin
(fail ())
end))))

# 1586 "FStar.TypeChecker.Tc.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 1589 "FStar.TypeChecker.Tc.fst"
let _57_2248 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_57_2248) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _57_2250 -> begin
(
# 1592 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow binders c)
in (
# 1593 "FStar.TypeChecker.Tc.fst"
let _57_2254 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_57_2254) with
| (uvs, t') -> begin
(match ((let _146_829 = (FStar_Syntax_Subst.compress t')
in _146_829.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _57_2260 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 1598 "FStar.TypeChecker.Tc.fst"
let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (
# 1599 "FStar.TypeChecker.Tc.fst"
let fail = (fun t -> (let _146_840 = (let _146_839 = (let _146_838 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_146_838, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_146_839))
in (Prims.raise _146_840)))
in (match ((let _146_841 = (FStar_Syntax_Subst.compress signature)
in _146_841.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1602 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _57_2281)::(wp, _57_2277)::(_wlp, _57_2273)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2285 -> begin
(fail signature)
end))
end
| _57_2287 -> begin
(fail signature)
end)))

# 1609 "FStar.TypeChecker.Tc.fst"
let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (
# 1610 "FStar.TypeChecker.Tc.fst"
let _57_2292 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_57_2292) with
| (a, wp) -> begin
(
# 1611 "FStar.TypeChecker.Tc.fst"
let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _57_2295 -> begin
(
# 1615 "FStar.TypeChecker.Tc.fst"
let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (
# 1616 "FStar.TypeChecker.Tc.fst"
let op = (fun ts -> (
# 1617 "FStar.TypeChecker.Tc.fst"
let _57_2299 = ()
in (
# 1618 "FStar.TypeChecker.Tc.fst"
let t0 = (Prims.snd ts)
in (
# 1619 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (
# 1621 "FStar.TypeChecker.Tc.fst"
let _57_2303 = ed
in (let _146_860 = (op ed.FStar_Syntax_Syntax.ret)
in (let _146_859 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _146_858 = (op ed.FStar_Syntax_Syntax.bind_wlp)
in (let _146_857 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _146_856 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _146_855 = (op ed.FStar_Syntax_Syntax.ite_wlp)
in (let _146_854 = (op ed.FStar_Syntax_Syntax.wp_binop)
in (let _146_853 = (op ed.FStar_Syntax_Syntax.wp_as_type)
in (let _146_852 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _146_851 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _146_850 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _146_849 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _146_848 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _57_2303.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2303.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2303.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2303.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2303.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _146_860; FStar_Syntax_Syntax.bind_wp = _146_859; FStar_Syntax_Syntax.bind_wlp = _146_858; FStar_Syntax_Syntax.if_then_else = _146_857; FStar_Syntax_Syntax.ite_wp = _146_856; FStar_Syntax_Syntax.ite_wlp = _146_855; FStar_Syntax_Syntax.wp_binop = _146_854; FStar_Syntax_Syntax.wp_as_type = _146_853; FStar_Syntax_Syntax.close_wp = _146_852; FStar_Syntax_Syntax.assert_p = _146_851; FStar_Syntax_Syntax.assume_p = _146_850; FStar_Syntax_Syntax.null_wp = _146_849; FStar_Syntax_Syntax.trivial = _146_848}))))))))))))))))
end)
in (ed, a, wp))
end)))

# 1637 "FStar.TypeChecker.Tc.fst"
let gen_wps_for_free : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env binders a wp_a ed -> (
# 1642 "FStar.TypeChecker.Tc.fst"
let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env)
in (
# 1644 "FStar.TypeChecker.Tc.fst"
let d = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))
in (
# 1645 "FStar.TypeChecker.Tc.fst"
let normalize_and_make_binders_explicit = (fun tm -> (
# 1646 "FStar.TypeChecker.Tc.fst"
let tm = (normalize tm)
in (
# 1647 "FStar.TypeChecker.Tc.fst"
let rec visit_term = (fun tm -> (
# 1648 "FStar.TypeChecker.Tc.fst"
let n = (match ((let _146_882 = (FStar_Syntax_Subst.compress tm)
in _146_882.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(
# 1650 "FStar.TypeChecker.Tc.fst"
let comp = (visit_comp comp)
in (
# 1651 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map visit_binder binders)
in FStar_Syntax_Syntax.Tm_arrow ((binders, comp))))
end
| FStar_Syntax_Syntax.Tm_abs (binders, term, comp) -> begin
(
# 1654 "FStar.TypeChecker.Tc.fst"
let comp = (visit_maybe_lcomp comp)
in (
# 1655 "FStar.TypeChecker.Tc.fst"
let term = (visit_term term)
in (
# 1656 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map visit_binder binders)
in FStar_Syntax_Syntax.Tm_abs ((binders, term, comp)))))
end
| _57_2338 -> begin
tm.FStar_Syntax_Syntax.n
end)
in (
# 1661 "FStar.TypeChecker.Tc.fst"
let _57_2340 = tm
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2340.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2340.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2340.FStar_Syntax_Syntax.vars})))
and visit_binder = (fun _57_2344 -> (match (_57_2344) with
| (bv, a) -> begin
(let _146_886 = (
# 1663 "FStar.TypeChecker.Tc.fst"
let _57_2345 = bv
in (let _146_884 = (visit_term bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_2345.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2345.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_884}))
in (let _146_885 = (FStar_Syntax_Syntax.as_implicit false)
in (_146_886, _146_885)))
end))
and visit_maybe_lcomp = (fun lcomp -> (match (lcomp) with
| Some (FStar_Util.Inl (lcomp)) -> begin
(let _146_891 = (let _146_890 = (let _146_889 = (let _146_888 = (lcomp.FStar_Syntax_Syntax.comp ())
in (visit_comp _146_888))
in (FStar_Syntax_Util.lcomp_of_comp _146_889))
in FStar_Util.Inl (_146_890))
in Some (_146_891))
end
| comp -> begin
comp
end))
and visit_comp = (fun comp -> (
# 1671 "FStar.TypeChecker.Tc.fst"
let n = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tm) -> begin
(let _146_893 = (visit_term tm)
in FStar_Syntax_Syntax.Total (_146_893))
end
| FStar_Syntax_Syntax.GTotal (tm) -> begin
(let _146_894 = (visit_term tm)
in FStar_Syntax_Syntax.GTotal (_146_894))
end
| comp -> begin
comp
end)
in (
# 1679 "FStar.TypeChecker.Tc.fst"
let _57_2359 = comp
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2359.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2359.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2359.FStar_Syntax_Syntax.vars})))
and visit_args = (fun args -> (FStar_List.map (fun _57_2364 -> (match (_57_2364) with
| (tm, q) -> begin
(let _146_897 = (visit_term tm)
in (_146_897, q))
end)) args))
in (visit_term tm))))
in (
# 1687 "FStar.TypeChecker.Tc.fst"
let check = (fun str t -> if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(
# 1689 "FStar.TypeChecker.Tc.fst"
let _57_2368 = (let _146_902 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Generated term for %s: %s\n" str _146_902))
in (
# 1690 "FStar.TypeChecker.Tc.fst"
let t = (normalize t)
in (
# 1691 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 1692 "FStar.TypeChecker.Tc.fst"
let _57_2383 = (tc_term env t)
in (match (_57_2383) with
| (e, {FStar_Syntax_Syntax.eff_name = _57_2379; FStar_Syntax_Syntax.res_typ = res_typ; FStar_Syntax_Syntax.cflags = _57_2376; FStar_Syntax_Syntax.comp = _57_2374}, _57_2382) -> begin
(
# 1693 "FStar.TypeChecker.Tc.fst"
let _57_2384 = (let _146_905 = (let _146_904 = (normalize res_typ)
in (FStar_Syntax_Print.term_to_string _146_904))
in (FStar_Util.print2 "Inferred type for %s: %s\n" str _146_905))
in (let _146_907 = (let _146_906 = (normalize e)
in (FStar_Syntax_Print.term_to_string _146_906))
in (FStar_Util.print2 "Elaborated term for %s: %s\n" str _146_907)))
end)))))
end else begin
()
end)
in (
# 1709 "FStar.TypeChecker.Tc.fst"
let rec collect_binders = (fun t -> (match ((let _146_910 = (FStar_Syntax_Subst.compress t)
in _146_910.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(
# 1712 "FStar.TypeChecker.Tc.fst"
let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
t
end
| _57_2395 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _146_911 = (collect_binders rest)
in (FStar_List.append bs _146_911)))
end
| FStar_Syntax_Syntax.Tm_type (_57_2398) -> begin
[]
end
| _57_2401 -> begin
(FStar_All.failwith "wp_a doesn\'t end in Type0")
end))
in (
# 1721 "FStar.TypeChecker.Tc.fst"
let _57_2416 = (
# 1722 "FStar.TypeChecker.Tc.fst"
let i = (FStar_ST.alloc 0)
in (
# 1723 "FStar.TypeChecker.Tc.fst"
let wp_binders = (let _146_918 = (normalize wp_a)
in (collect_binders _146_918))
in ((fun t -> (let _146_924 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow wp_binders _146_924))), (fun t -> (let _146_927 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow wp_binders _146_927))), (fun _57_2406 -> (match (()) with
| () -> begin
(FStar_List.map (fun _57_2410 -> (match (_57_2410) with
| (bv, _57_2409) -> begin
(
# 1732 "FStar.TypeChecker.Tc.fst"
let _57_2411 = (let _146_931 = ((FStar_ST.read i) + 1)
in (FStar_ST.op_Colon_Equals i _146_931))
in (let _146_934 = (let _146_933 = (let _146_932 = (FStar_ST.read i)
in (FStar_Util.string_of_int _146_932))
in (Prims.strcat "g" _146_933))
in (FStar_Syntax_Syntax.gen_bv _146_934 None bv.FStar_Syntax_Syntax.sort)))
end)) wp_binders)
end)))))
in (match (_57_2416) with
| (mk_ctx, mk_gctx, mk_gamma) -> begin
(
# 1738 "FStar.TypeChecker.Tc.fst"
let binders_of_list = (FStar_List.map (fun _57_2419 -> (match (_57_2419) with
| (t, b) -> begin
(let _146_940 = (FStar_Syntax_Syntax.as_implicit b)
in (t, _146_940))
end)))
in (
# 1740 "FStar.TypeChecker.Tc.fst"
let implicit_binders_of_list = (FStar_List.map (fun t -> (let _146_943 = (FStar_Syntax_Syntax.as_implicit true)
in (t, _146_943))))
in (
# 1742 "FStar.TypeChecker.Tc.fst"
let args_of_bv = (FStar_List.map (fun bv -> (let _146_946 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_Syntax_Syntax.as_arg _146_946))))
in (
# 1747 "FStar.TypeChecker.Tc.fst"
let c_pure = (
# 1748 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (
# 1749 "FStar.TypeChecker.Tc.fst"
let x = (let _146_947 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _146_947))
in (
# 1750 "FStar.TypeChecker.Tc.fst"
let ret = (let _146_952 = (let _146_951 = (let _146_950 = (let _146_949 = (let _146_948 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx _146_948))
in (FStar_Syntax_Syntax.mk_Total _146_949))
in (FStar_Syntax_Util.lcomp_of_comp _146_950))
in FStar_Util.Inl (_146_951))
in Some (_146_952))
in (
# 1751 "FStar.TypeChecker.Tc.fst"
let gamma = (mk_gamma ())
in (
# 1752 "FStar.TypeChecker.Tc.fst"
let body = (let _146_954 = (implicit_binders_of_list gamma)
in (let _146_953 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs _146_954 _146_953 ret)))
in (let _146_955 = (binders_of_list (((t, true))::((x, false))::[]))
in (FStar_Syntax_Util.abs _146_955 body ret)))))))
in (
# 1755 "FStar.TypeChecker.Tc.fst"
let _57_2431 = (let _146_959 = (let _146_958 = (let _146_957 = (let _146_956 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_956)::[])
in (FStar_List.append binders _146_957))
in (FStar_Syntax_Util.abs _146_958 c_pure None))
in (check "pure" _146_959))
in (
# 1762 "FStar.TypeChecker.Tc.fst"
let c_app = (
# 1763 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (
# 1764 "FStar.TypeChecker.Tc.fst"
let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (
# 1765 "FStar.TypeChecker.Tc.fst"
let l = (let _146_967 = (let _146_966 = (let _146_965 = (let _146_962 = (let _146_961 = (let _146_960 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _146_960))
in (FStar_Syntax_Syntax.mk_binder _146_961))
in (_146_962)::[])
in (let _146_964 = (let _146_963 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _146_963))
in (FStar_Syntax_Util.arrow _146_965 _146_964)))
in (mk_gctx _146_966))
in (FStar_Syntax_Syntax.gen_bv "l" None _146_967))
in (
# 1768 "FStar.TypeChecker.Tc.fst"
let r = (let _146_969 = (let _146_968 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _146_968))
in (FStar_Syntax_Syntax.gen_bv "r" None _146_969))
in (
# 1769 "FStar.TypeChecker.Tc.fst"
let ret = (let _146_974 = (let _146_973 = (let _146_972 = (let _146_971 = (let _146_970 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_970))
in (FStar_Syntax_Syntax.mk_Total _146_971))
in (FStar_Syntax_Util.lcomp_of_comp _146_972))
in FStar_Util.Inl (_146_973))
in Some (_146_974))
in (
# 1770 "FStar.TypeChecker.Tc.fst"
let outer_body = (
# 1771 "FStar.TypeChecker.Tc.fst"
let gamma = (mk_gamma ())
in (
# 1772 "FStar.TypeChecker.Tc.fst"
let gamma_as_args = (args_of_bv gamma)
in (
# 1773 "FStar.TypeChecker.Tc.fst"
let inner_body = (let _146_980 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _146_979 = (let _146_978 = (let _146_977 = (let _146_976 = (let _146_975 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _146_975 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg _146_976))
in (_146_977)::[])
in (FStar_List.append gamma_as_args _146_978))
in (FStar_Syntax_Util.mk_app _146_980 _146_979)))
in (let _146_981 = (implicit_binders_of_list gamma)
in (FStar_Syntax_Util.abs _146_981 inner_body ret)))))
in (let _146_982 = (binders_of_list (((t1, true))::((t2, true))::((l, false))::((r, false))::[]))
in (FStar_Syntax_Util.abs _146_982 outer_body ret))))))))
in (
# 1782 "FStar.TypeChecker.Tc.fst"
let _57_2443 = (let _146_986 = (let _146_985 = (let _146_984 = (let _146_983 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_983)::[])
in (FStar_List.append binders _146_984))
in (FStar_Syntax_Util.abs _146_985 c_app None))
in (check "app" _146_986))
in (
# 1791 "FStar.TypeChecker.Tc.fst"
let unknown = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (
# 1792 "FStar.TypeChecker.Tc.fst"
let c_lift1 = (
# 1793 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (
# 1794 "FStar.TypeChecker.Tc.fst"
let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (
# 1795 "FStar.TypeChecker.Tc.fst"
let t_f = (let _146_991 = (let _146_988 = (let _146_987 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_987))
in (_146_988)::[])
in (let _146_990 = (let _146_989 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _146_989))
in (FStar_Syntax_Util.arrow _146_991 _146_990)))
in (
# 1796 "FStar.TypeChecker.Tc.fst"
let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (
# 1797 "FStar.TypeChecker.Tc.fst"
let a1 = (let _146_993 = (let _146_992 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _146_992))
in (FStar_Syntax_Syntax.gen_bv "a1" None _146_993))
in (
# 1798 "FStar.TypeChecker.Tc.fst"
let ret = (let _146_998 = (let _146_997 = (let _146_996 = (let _146_995 = (let _146_994 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_994))
in (FStar_Syntax_Syntax.mk_Total _146_995))
in (FStar_Syntax_Util.lcomp_of_comp _146_996))
in FStar_Util.Inl (_146_997))
in Some (_146_998))
in (let _146_1011 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::((a1, false))::[]))
in (let _146_1010 = (let _146_1009 = (let _146_1008 = (let _146_1007 = (let _146_1006 = (let _146_1005 = (let _146_1002 = (let _146_1001 = (let _146_1000 = (let _146_999 = (FStar_Syntax_Syntax.bv_to_name f)
in (_146_999)::[])
in (unknown)::_146_1000)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1001))
in (FStar_Syntax_Util.mk_app c_pure _146_1002))
in (let _146_1004 = (let _146_1003 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_146_1003)::[])
in (_146_1005)::_146_1004))
in (unknown)::_146_1006)
in (unknown)::_146_1007)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1008))
in (FStar_Syntax_Util.mk_app c_app _146_1009))
in (FStar_Syntax_Util.abs _146_1011 _146_1010 ret)))))))))
in (
# 1806 "FStar.TypeChecker.Tc.fst"
let _57_2453 = (let _146_1015 = (let _146_1014 = (let _146_1013 = (let _146_1012 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1012)::[])
in (FStar_List.append binders _146_1013))
in (FStar_Syntax_Util.abs _146_1014 c_lift1 None))
in (check "lift1" _146_1015))
in (
# 1817 "FStar.TypeChecker.Tc.fst"
let c_lift2 = (
# 1818 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (
# 1819 "FStar.TypeChecker.Tc.fst"
let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (
# 1820 "FStar.TypeChecker.Tc.fst"
let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (
# 1821 "FStar.TypeChecker.Tc.fst"
let t_f = (let _146_1023 = (let _146_1020 = (let _146_1016 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_1016))
in (let _146_1019 = (let _146_1018 = (let _146_1017 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder _146_1017))
in (_146_1018)::[])
in (_146_1020)::_146_1019))
in (let _146_1022 = (let _146_1021 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal _146_1021))
in (FStar_Syntax_Util.arrow _146_1023 _146_1022)))
in (
# 1825 "FStar.TypeChecker.Tc.fst"
let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (
# 1826 "FStar.TypeChecker.Tc.fst"
let a1 = (let _146_1025 = (let _146_1024 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _146_1024))
in (FStar_Syntax_Syntax.gen_bv "a1" None _146_1025))
in (
# 1827 "FStar.TypeChecker.Tc.fst"
let a2 = (let _146_1027 = (let _146_1026 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_1026))
in (FStar_Syntax_Syntax.gen_bv "a2" None _146_1027))
in (
# 1828 "FStar.TypeChecker.Tc.fst"
let ret = (let _146_1032 = (let _146_1031 = (let _146_1030 = (let _146_1029 = (let _146_1028 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx _146_1028))
in (FStar_Syntax_Syntax.mk_Total _146_1029))
in (FStar_Syntax_Util.lcomp_of_comp _146_1030))
in FStar_Util.Inl (_146_1031))
in Some (_146_1032))
in (let _146_1052 = (binders_of_list (((t1, true))::((t2, true))::((t3, true))::((f, false))::((a1, false))::((a2, false))::[]))
in (let _146_1051 = (let _146_1050 = (let _146_1049 = (let _146_1048 = (let _146_1047 = (let _146_1046 = (let _146_1043 = (let _146_1042 = (let _146_1041 = (let _146_1040 = (let _146_1039 = (let _146_1036 = (let _146_1035 = (let _146_1034 = (let _146_1033 = (FStar_Syntax_Syntax.bv_to_name f)
in (_146_1033)::[])
in (unknown)::_146_1034)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1035))
in (FStar_Syntax_Util.mk_app c_pure _146_1036))
in (let _146_1038 = (let _146_1037 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_146_1037)::[])
in (_146_1039)::_146_1038))
in (unknown)::_146_1040)
in (unknown)::_146_1041)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1042))
in (FStar_Syntax_Util.mk_app c_app _146_1043))
in (let _146_1045 = (let _146_1044 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_146_1044)::[])
in (_146_1046)::_146_1045))
in (unknown)::_146_1047)
in (unknown)::_146_1048)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1049))
in (FStar_Syntax_Util.mk_app c_app _146_1050))
in (FStar_Syntax_Util.abs _146_1052 _146_1051 ret)))))))))))
in (
# 1839 "FStar.TypeChecker.Tc.fst"
let _57_2464 = (let _146_1056 = (let _146_1055 = (let _146_1054 = (let _146_1053 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1053)::[])
in (FStar_List.append binders _146_1054))
in (FStar_Syntax_Util.abs _146_1055 c_lift2 None))
in (check "lift2" _146_1056))
in (
# 1845 "FStar.TypeChecker.Tc.fst"
let c_push = (
# 1846 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (
# 1847 "FStar.TypeChecker.Tc.fst"
let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (
# 1848 "FStar.TypeChecker.Tc.fst"
let t_f = (let _146_1062 = (let _146_1058 = (let _146_1057 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_1057))
in (_146_1058)::[])
in (let _146_1061 = (let _146_1060 = (let _146_1059 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_1059))
in (FStar_Syntax_Syntax.mk_Total _146_1060))
in (FStar_Syntax_Util.arrow _146_1062 _146_1061)))
in (
# 1852 "FStar.TypeChecker.Tc.fst"
let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (
# 1853 "FStar.TypeChecker.Tc.fst"
let ret = (let _146_1072 = (let _146_1071 = (let _146_1070 = (let _146_1069 = (let _146_1068 = (let _146_1067 = (let _146_1064 = (let _146_1063 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_1063))
in (_146_1064)::[])
in (let _146_1066 = (let _146_1065 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _146_1065))
in (FStar_Syntax_Util.arrow _146_1067 _146_1066)))
in (mk_ctx _146_1068))
in (FStar_Syntax_Syntax.mk_Total _146_1069))
in (FStar_Syntax_Util.lcomp_of_comp _146_1070))
in FStar_Util.Inl (_146_1071))
in Some (_146_1072))
in (
# 1856 "FStar.TypeChecker.Tc.fst"
let e1 = (let _146_1073 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _146_1073))
in (
# 1857 "FStar.TypeChecker.Tc.fst"
let gamma = (mk_gamma ())
in (
# 1858 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1083 = (let _146_1076 = (FStar_Syntax_Syntax.binders_of_list gamma)
in (let _146_1075 = (let _146_1074 = (FStar_Syntax_Syntax.mk_binder e1)
in (_146_1074)::[])
in (FStar_List.append _146_1076 _146_1075)))
in (let _146_1082 = (let _146_1081 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _146_1080 = (let _146_1079 = (let _146_1077 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _146_1077))
in (let _146_1078 = (args_of_bv gamma)
in (_146_1079)::_146_1078))
in (FStar_Syntax_Util.mk_app _146_1081 _146_1080)))
in (FStar_Syntax_Util.abs _146_1083 _146_1082 ret)))
in (let _146_1084 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::[]))
in (FStar_Syntax_Util.abs _146_1084 body ret))))))))))
in (
# 1863 "FStar.TypeChecker.Tc.fst"
let _57_2475 = (let _146_1088 = (let _146_1087 = (let _146_1086 = (let _146_1085 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1085)::[])
in (FStar_List.append binders _146_1086))
in (FStar_Syntax_Util.abs _146_1087 c_push None))
in (check "push" _146_1088))
in (
# 1865 "FStar.TypeChecker.Tc.fst"
let ret_tot_wp_a = (let _146_1091 = (let _146_1090 = (let _146_1089 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _146_1089))
in FStar_Util.Inl (_146_1090))
in Some (_146_1091))
in (
# 1871 "FStar.TypeChecker.Tc.fst"
let wp_if_then_else = (
# 1872 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _146_1102 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (let _146_1101 = (
# 1877 "FStar.TypeChecker.Tc.fst"
let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_unfoldable (2)) None)
in (let _146_1100 = (let _146_1099 = (let _146_1098 = (let _146_1097 = (let _146_1096 = (let _146_1095 = (let _146_1094 = (let _146_1093 = (let _146_1092 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _146_1092))
in (_146_1093)::[])
in (FStar_Syntax_Util.mk_app l_ite _146_1094))
in (_146_1095)::[])
in (unknown)::_146_1096)
in (unknown)::_146_1097)
in (unknown)::_146_1098)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1099))
in (FStar_Syntax_Util.mk_app c_lift2 _146_1100)))
in (FStar_Syntax_Util.abs _146_1102 _146_1101 ret_tot_wp_a))))
in (
# 1885 "FStar.TypeChecker.Tc.fst"
let wp_if_then_else = (normalize_and_make_binders_explicit wp_if_then_else)
in (
# 1886 "FStar.TypeChecker.Tc.fst"
let _57_2482 = (let _146_1103 = (FStar_Syntax_Util.abs binders wp_if_then_else None)
in (check "wp_if_then_else" _146_1103))
in (
# 1892 "FStar.TypeChecker.Tc.fst"
let wp_binop = (
# 1893 "FStar.TypeChecker.Tc.fst"
let l = (FStar_Syntax_Syntax.gen_bv "l" None wp_a)
in (
# 1894 "FStar.TypeChecker.Tc.fst"
let op = (let _146_1109 = (let _146_1108 = (let _146_1106 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Util.ktype0)
in (let _146_1105 = (let _146_1104 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Util.ktype0)
in (_146_1104)::[])
in (_146_1106)::_146_1105))
in (let _146_1107 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _146_1108 _146_1107)))
in (FStar_Syntax_Syntax.gen_bv "op" None _146_1109))
in (
# 1897 "FStar.TypeChecker.Tc.fst"
let r = (FStar_Syntax_Syntax.gen_bv "r" None wp_a)
in (let _146_1121 = (FStar_Syntax_Syntax.binders_of_list ((a)::(l)::(op)::(r)::[]))
in (let _146_1120 = (let _146_1119 = (let _146_1118 = (let _146_1117 = (let _146_1116 = (let _146_1115 = (let _146_1114 = (FStar_Syntax_Syntax.bv_to_name op)
in (let _146_1113 = (let _146_1112 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _146_1111 = (let _146_1110 = (FStar_Syntax_Syntax.bv_to_name r)
in (_146_1110)::[])
in (_146_1112)::_146_1111))
in (_146_1114)::_146_1113))
in (unknown)::_146_1115)
in (unknown)::_146_1116)
in (unknown)::_146_1117)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1118))
in (FStar_Syntax_Util.mk_app c_lift2 _146_1119))
in (FStar_Syntax_Util.abs _146_1121 _146_1120 ret_tot_wp_a))))))
in (
# 1905 "FStar.TypeChecker.Tc.fst"
let wp_binop = (normalize_and_make_binders_explicit wp_binop)
in (
# 1906 "FStar.TypeChecker.Tc.fst"
let _57_2489 = (let _146_1122 = (FStar_Syntax_Util.abs binders wp_binop None)
in (check "wp_binop" _146_1122))
in (
# 1911 "FStar.TypeChecker.Tc.fst"
let wp_assert = (
# 1912 "FStar.TypeChecker.Tc.fst"
let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (
# 1913 "FStar.TypeChecker.Tc.fst"
let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (
# 1914 "FStar.TypeChecker.Tc.fst"
let l_and = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (
# 1915 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1136 = (let _146_1135 = (let _146_1134 = (let _146_1133 = (let _146_1132 = (let _146_1129 = (let _146_1128 = (let _146_1127 = (let _146_1126 = (let _146_1125 = (let _146_1124 = (let _146_1123 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _146_1123))
in (_146_1124)::[])
in (FStar_Syntax_Util.mk_app l_and _146_1125))
in (_146_1126)::[])
in (unknown)::_146_1127)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1128))
in (FStar_Syntax_Util.mk_app c_pure _146_1129))
in (let _146_1131 = (let _146_1130 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_146_1130)::[])
in (_146_1132)::_146_1131))
in (unknown)::_146_1133)
in (unknown)::_146_1134)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1135))
in (FStar_Syntax_Util.mk_app c_app _146_1136))
in (let _146_1137 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _146_1137 body ret_tot_wp_a))))))
in (
# 1925 "FStar.TypeChecker.Tc.fst"
let wp_assert = (normalize_and_make_binders_explicit wp_assert)
in (
# 1926 "FStar.TypeChecker.Tc.fst"
let _57_2497 = (let _146_1138 = (FStar_Syntax_Util.abs binders wp_assert None)
in (check "wp_assert" _146_1138))
in (
# 1931 "FStar.TypeChecker.Tc.fst"
let wp_assume = (
# 1932 "FStar.TypeChecker.Tc.fst"
let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (
# 1933 "FStar.TypeChecker.Tc.fst"
let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (
# 1934 "FStar.TypeChecker.Tc.fst"
let l_imp = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (
# 1935 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1152 = (let _146_1151 = (let _146_1150 = (let _146_1149 = (let _146_1148 = (let _146_1145 = (let _146_1144 = (let _146_1143 = (let _146_1142 = (let _146_1141 = (let _146_1140 = (let _146_1139 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _146_1139))
in (_146_1140)::[])
in (FStar_Syntax_Util.mk_app l_imp _146_1141))
in (_146_1142)::[])
in (unknown)::_146_1143)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1144))
in (FStar_Syntax_Util.mk_app c_pure _146_1145))
in (let _146_1147 = (let _146_1146 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_146_1146)::[])
in (_146_1148)::_146_1147))
in (unknown)::_146_1149)
in (unknown)::_146_1150)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1151))
in (FStar_Syntax_Util.mk_app c_app _146_1152))
in (let _146_1153 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _146_1153 body ret_tot_wp_a))))))
in (
# 1945 "FStar.TypeChecker.Tc.fst"
let wp_assume = (normalize_and_make_binders_explicit wp_assume)
in (
# 1946 "FStar.TypeChecker.Tc.fst"
let _57_2505 = (let _146_1154 = (FStar_Syntax_Util.abs binders wp_assume None)
in (check "wp_assume" _146_1154))
in (
# 1948 "FStar.TypeChecker.Tc.fst"
let tforall = (let _146_1157 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _146_1156 = (let _146_1155 = (FStar_Syntax_Syntax.as_arg unknown)
in (_146_1155)::[])
in (FStar_Syntax_Util.mk_app _146_1157 _146_1156)))
in (
# 1954 "FStar.TypeChecker.Tc.fst"
let wp_close = (
# 1955 "FStar.TypeChecker.Tc.fst"
let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (
# 1956 "FStar.TypeChecker.Tc.fst"
let t_f = (let _146_1161 = (let _146_1159 = (let _146_1158 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _146_1158))
in (_146_1159)::[])
in (let _146_1160 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1161 _146_1160)))
in (
# 1957 "FStar.TypeChecker.Tc.fst"
let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (
# 1958 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1174 = (let _146_1173 = (let _146_1172 = (let _146_1171 = (let _146_1170 = (let _146_1162 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((unknown)::(tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _146_1162))
in (let _146_1169 = (let _146_1168 = (let _146_1167 = (let _146_1166 = (let _146_1165 = (let _146_1164 = (let _146_1163 = (FStar_Syntax_Syntax.bv_to_name f)
in (_146_1163)::[])
in (unknown)::_146_1164)
in (unknown)::_146_1165)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1166))
in (FStar_Syntax_Util.mk_app c_push _146_1167))
in (_146_1168)::[])
in (_146_1170)::_146_1169))
in (unknown)::_146_1171)
in (unknown)::_146_1172)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1173))
in (FStar_Syntax_Util.mk_app c_app _146_1174))
in (let _146_1175 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_Syntax_Util.abs _146_1175 body ret_tot_wp_a))))))
in (
# 1970 "FStar.TypeChecker.Tc.fst"
let wp_close = (normalize_and_make_binders_explicit wp_close)
in (
# 1971 "FStar.TypeChecker.Tc.fst"
let _57_2514 = (let _146_1176 = (FStar_Syntax_Util.abs binders wp_close None)
in (check "wp_close" _146_1176))
in (
# 1973 "FStar.TypeChecker.Tc.fst"
let ret_tot_type0 = (let _146_1179 = (let _146_1178 = (let _146_1177 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_1177))
in FStar_Util.Inl (_146_1178))
in Some (_146_1179))
in (
# 1974 "FStar.TypeChecker.Tc.fst"
let mk_forall = (fun x body -> (
# 1975 "FStar.TypeChecker.Tc.fst"
let tforall = (let _146_1186 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _146_1185 = (let _146_1184 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (_146_1184)::[])
in (FStar_Syntax_Util.mk_app _146_1186 _146_1185)))
in (let _146_1193 = (let _146_1192 = (let _146_1191 = (let _146_1190 = (let _146_1189 = (let _146_1188 = (let _146_1187 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_1187)::[])
in (FStar_Syntax_Util.abs _146_1188 body ret_tot_type0))
in (FStar_Syntax_Syntax.as_arg _146_1189))
in (_146_1190)::[])
in (tforall, _146_1191))
in FStar_Syntax_Syntax.Tm_app (_146_1192))
in (FStar_Syntax_Syntax.mk _146_1193 None FStar_Range.dummyRange))))
in (
# 1986 "FStar.TypeChecker.Tc.fst"
let rec mk_leq = (fun t x y -> (match ((let _146_1201 = (let _146_1200 = (FStar_Syntax_Subst.compress t)
in (normalize _146_1200))
in _146_1201.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_2526) -> begin
(FStar_Syntax_Util.mk_imp x y)
end
| (FStar_Syntax_Syntax.Tm_arrow (binder::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow (binder::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) when (FStar_Syntax_Syntax.is_null_binder binder) -> begin
(
# 1993 "FStar.TypeChecker.Tc.fst"
let a = (Prims.fst binder).FStar_Syntax_Syntax.sort
in (
# 1995 "FStar.TypeChecker.Tc.fst"
let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (
# 1996 "FStar.TypeChecker.Tc.fst"
let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (
# 1997 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1213 = (let _146_1203 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _146_1202 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_leq a _146_1203 _146_1202)))
in (let _146_1212 = (let _146_1211 = (let _146_1206 = (let _146_1205 = (let _146_1204 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _146_1204))
in (_146_1205)::[])
in (FStar_Syntax_Util.mk_app x _146_1206))
in (let _146_1210 = (let _146_1209 = (let _146_1208 = (let _146_1207 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _146_1207))
in (_146_1208)::[])
in (FStar_Syntax_Util.mk_app y _146_1209))
in (mk_leq b _146_1211 _146_1210)))
in (FStar_Syntax_Util.mk_imp _146_1213 _146_1212)))
in (let _146_1214 = (mk_forall a2 body)
in (mk_forall a1 _146_1214))))))
end
| FStar_Syntax_Syntax.Tm_arrow (binder::binders, comp) -> begin
(
# 2005 "FStar.TypeChecker.Tc.fst"
let t = (
# 2005 "FStar.TypeChecker.Tc.fst"
let _57_2562 = t
in (let _146_1218 = (let _146_1217 = (let _146_1216 = (let _146_1215 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _146_1215))
in ((binder)::[], _146_1216))
in FStar_Syntax_Syntax.Tm_arrow (_146_1217))
in {FStar_Syntax_Syntax.n = _146_1218; FStar_Syntax_Syntax.tk = _57_2562.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2562.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2562.FStar_Syntax_Syntax.vars}))
in (mk_leq t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_57_2566) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _57_2569 -> begin
(FStar_Syntax_Util.mk_eq t t x y)
end))
in (
# 2014 "FStar.TypeChecker.Tc.fst"
let stronger = (
# 2015 "FStar.TypeChecker.Tc.fst"
let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (
# 2016 "FStar.TypeChecker.Tc.fst"
let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (
# 2017 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1220 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _146_1219 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_leq wp_a _146_1220 _146_1219)))
in (let _146_1221 = (FStar_Syntax_Syntax.binders_of_list ((wp1)::(wp2)::[]))
in (FStar_Syntax_Util.abs _146_1221 body ret_tot_type0)))))
in (
# 2020 "FStar.TypeChecker.Tc.fst"
let _57_2574 = (let _146_1225 = (let _146_1224 = (let _146_1223 = (let _146_1222 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1222)::[])
in (FStar_List.append binders _146_1223))
in (FStar_Syntax_Util.abs _146_1224 stronger None))
in (check "stronger" _146_1225))
in (
# 2022 "FStar.TypeChecker.Tc.fst"
let null_wp = (Prims.snd ed.FStar_Syntax_Syntax.null_wp)
in (
# 2026 "FStar.TypeChecker.Tc.fst"
let wp_trivial = (
# 2027 "FStar.TypeChecker.Tc.fst"
let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (
# 2028 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1233 = (let _146_1232 = (let _146_1231 = (let _146_1228 = (let _146_1227 = (let _146_1226 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _146_1226))
in (_146_1227)::[])
in (FStar_Syntax_Util.mk_app null_wp _146_1228))
in (let _146_1230 = (let _146_1229 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_146_1229)::[])
in (_146_1231)::_146_1230))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1232))
in (FStar_Syntax_Util.mk_app stronger _146_1233))
in (let _146_1234 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_Syntax_Util.abs _146_1234 body ret_tot_type0))))
in (
# 2034 "FStar.TypeChecker.Tc.fst"
let wp_trivial = (normalize_and_make_binders_explicit wp_trivial)
in (
# 2035 "FStar.TypeChecker.Tc.fst"
let _57_2581 = (let _146_1235 = (FStar_Syntax_Util.abs binders wp_trivial None)
in (check "wp_trivial" _146_1235))
in (
# 2037 "FStar.TypeChecker.Tc.fst"
let _57_2583 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2583.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2583.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2583.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2583.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2583.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _57_2583.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2583.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _57_2583.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = ([], wp_if_then_else); FStar_Syntax_Syntax.ite_wp = _57_2583.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _57_2583.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = ([], wp_binop); FStar_Syntax_Syntax.wp_as_type = _57_2583.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = ([], wp_close); FStar_Syntax_Syntax.assert_p = ([], wp_assert); FStar_Syntax_Syntax.assume_p = ([], wp_assume); FStar_Syntax_Syntax.null_wp = _57_2583.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = ([], wp_trivial)})))))))))))))))))))))))))))))))))))))))))
end))))))))

# 2047 "FStar.TypeChecker.Tc.fst"
let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  effect_cost  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed is_for_free -> (
# 2048 "FStar.TypeChecker.Tc.fst"
let _57_2588 = ()
in (
# 2049 "FStar.TypeChecker.Tc.fst"
let _57_2592 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_57_2592) with
| (binders_un, signature_un) -> begin
(
# 2050 "FStar.TypeChecker.Tc.fst"
let _57_2597 = (tc_tparams env0 binders_un)
in (match (_57_2597) with
| (binders, env, _57_2596) -> begin
(
# 2051 "FStar.TypeChecker.Tc.fst"
let _57_2601 = (tc_trivial_guard env signature_un)
in (match (_57_2601) with
| (signature, _57_2600) -> begin
(
# 2052 "FStar.TypeChecker.Tc.fst"
let ed = (
# 2052 "FStar.TypeChecker.Tc.fst"
let _57_2602 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2602.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2602.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2602.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _57_2602.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2602.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _57_2602.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = _57_2602.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _57_2602.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _57_2602.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = _57_2602.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _57_2602.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _57_2602.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _57_2602.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _57_2602.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _57_2602.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _57_2602.FStar_Syntax_Syntax.trivial})
in (
# 2055 "FStar.TypeChecker.Tc.fst"
let _57_2608 = (open_effect_decl env ed)
in (match (_57_2608) with
| (ed, a, wp_a) -> begin
(
# 2056 "FStar.TypeChecker.Tc.fst"
let get_effect_signature = (fun _57_2610 -> (match (()) with
| () -> begin
(
# 2057 "FStar.TypeChecker.Tc.fst"
let _57_2614 = (tc_trivial_guard env signature_un)
in (match (_57_2614) with
| (signature, _57_2613) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (
# 2061 "FStar.TypeChecker.Tc.fst"
let env = (let _146_1244 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _146_1244))
in (
# 2063 "FStar.TypeChecker.Tc.fst"
let _57_2616 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _146_1247 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _146_1246 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _146_1245 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checking effect signature: %s %s : %s\n" _146_1247 _146_1246 _146_1245))))
end else begin
()
end
in (
# 2069 "FStar.TypeChecker.Tc.fst"
let check_and_gen' = (fun env _57_2623 k -> (match (_57_2623) with
| (_57_2621, t) -> begin
(check_and_gen env t k)
end))
in (
# 2073 "FStar.TypeChecker.Tc.fst"
let ed = (match (is_for_free) with
| NotForFree -> begin
ed
end
| ForFree -> begin
(gen_wps_for_free env binders a wp_a ed)
end)
in (
# 2078 "FStar.TypeChecker.Tc.fst"
let ret = (
# 2079 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1259 = (let _146_1257 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1256 = (let _146_1255 = (let _146_1254 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_1254))
in (_146_1255)::[])
in (_146_1257)::_146_1256))
in (let _146_1258 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _146_1259 _146_1258)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (
# 2082 "FStar.TypeChecker.Tc.fst"
let bind_wp = (
# 2083 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 2084 "FStar.TypeChecker.Tc.fst"
let _57_2633 = (get_effect_signature ())
in (match (_57_2633) with
| (b, wp_b) -> begin
(
# 2085 "FStar.TypeChecker.Tc.fst"
let a_wp_b = (let _146_1263 = (let _146_1261 = (let _146_1260 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_1260))
in (_146_1261)::[])
in (let _146_1262 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _146_1263 _146_1262)))
in (
# 2086 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = a_wp_b
in (
# 2087 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1278 = (let _146_1276 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _146_1275 = (let _146_1274 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1273 = (let _146_1272 = (FStar_Syntax_Syntax.mk_binder b)
in (let _146_1271 = (let _146_1270 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_1269 = (let _146_1268 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _146_1267 = (let _146_1266 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (let _146_1265 = (let _146_1264 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_146_1264)::[])
in (_146_1266)::_146_1265))
in (_146_1268)::_146_1267))
in (_146_1270)::_146_1269))
in (_146_1272)::_146_1271))
in (_146_1274)::_146_1273))
in (_146_1276)::_146_1275))
in (let _146_1277 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _146_1278 _146_1277)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k))))
end)))
in (
# 2094 "FStar.TypeChecker.Tc.fst"
let bind_wlp = (
# 2095 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 2096 "FStar.TypeChecker.Tc.fst"
let _57_2641 = (get_effect_signature ())
in (match (_57_2641) with
| (b, wlp_b) -> begin
(
# 2097 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = (let _146_1282 = (let _146_1280 = (let _146_1279 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_1279))
in (_146_1280)::[])
in (let _146_1281 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _146_1282 _146_1281)))
in (
# 2098 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1293 = (let _146_1291 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _146_1290 = (let _146_1289 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1288 = (let _146_1287 = (FStar_Syntax_Syntax.mk_binder b)
in (let _146_1286 = (let _146_1285 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _146_1284 = (let _146_1283 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_146_1283)::[])
in (_146_1285)::_146_1284))
in (_146_1287)::_146_1286))
in (_146_1289)::_146_1288))
in (_146_1291)::_146_1290))
in (let _146_1292 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _146_1293 _146_1292)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wlp expected_k)))
end)))
in (
# 2105 "FStar.TypeChecker.Tc.fst"
let if_then_else = (
# 2106 "FStar.TypeChecker.Tc.fst"
let p = (let _146_1295 = (let _146_1294 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1294 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _146_1295))
in (
# 2107 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1304 = (let _146_1302 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1301 = (let _146_1300 = (FStar_Syntax_Syntax.mk_binder p)
in (let _146_1299 = (let _146_1298 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_1297 = (let _146_1296 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1296)::[])
in (_146_1298)::_146_1297))
in (_146_1300)::_146_1299))
in (_146_1302)::_146_1301))
in (let _146_1303 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1304 _146_1303)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (
# 2113 "FStar.TypeChecker.Tc.fst"
let ite_wp = (
# 2114 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 2115 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1311 = (let _146_1309 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1308 = (let _146_1307 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _146_1306 = (let _146_1305 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1305)::[])
in (_146_1307)::_146_1306))
in (_146_1309)::_146_1308))
in (let _146_1310 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1311 _146_1310)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k)))
in (
# 2121 "FStar.TypeChecker.Tc.fst"
let ite_wlp = (
# 2122 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 2123 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1316 = (let _146_1314 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1313 = (let _146_1312 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (_146_1312)::[])
in (_146_1314)::_146_1313))
in (let _146_1315 = (FStar_Syntax_Syntax.mk_Total wlp_a)
in (FStar_Syntax_Util.arrow _146_1316 _146_1315)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wlp expected_k)))
in (
# 2128 "FStar.TypeChecker.Tc.fst"
let wp_binop = (
# 2129 "FStar.TypeChecker.Tc.fst"
let bin_op = (
# 2130 "FStar.TypeChecker.Tc.fst"
let _57_2656 = (FStar_Syntax_Util.type_u ())
in (match (_57_2656) with
| (t1, u1) -> begin
(
# 2131 "FStar.TypeChecker.Tc.fst"
let _57_2659 = (FStar_Syntax_Util.type_u ())
in (match (_57_2659) with
| (t2, u2) -> begin
(
# 2132 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1317 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_max ((u1)::(u2)::[]))) None _146_1317))
in (let _146_1322 = (let _146_1320 = (FStar_Syntax_Syntax.null_binder t1)
in (let _146_1319 = (let _146_1318 = (FStar_Syntax_Syntax.null_binder t2)
in (_146_1318)::[])
in (_146_1320)::_146_1319))
in (let _146_1321 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _146_1322 _146_1321))))
end))
end))
in (
# 2134 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1331 = (let _146_1329 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1328 = (let _146_1327 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_1326 = (let _146_1325 = (FStar_Syntax_Syntax.null_binder bin_op)
in (let _146_1324 = (let _146_1323 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1323)::[])
in (_146_1325)::_146_1324))
in (_146_1327)::_146_1326))
in (_146_1329)::_146_1328))
in (let _146_1330 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1331 _146_1330)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_binop expected_k)))
in (
# 2141 "FStar.TypeChecker.Tc.fst"
let wp_as_type = (
# 2142 "FStar.TypeChecker.Tc.fst"
let _57_2667 = (FStar_Syntax_Util.type_u ())
in (match (_57_2667) with
| (t, _57_2666) -> begin
(
# 2143 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1336 = (let _146_1334 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1333 = (let _146_1332 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1332)::[])
in (_146_1334)::_146_1333))
in (let _146_1335 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _146_1336 _146_1335)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (
# 2148 "FStar.TypeChecker.Tc.fst"
let close_wp = (
# 2149 "FStar.TypeChecker.Tc.fst"
let b = (let _146_1338 = (let _146_1337 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1337 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _146_1338))
in (
# 2150 "FStar.TypeChecker.Tc.fst"
let b_wp_a = (let _146_1342 = (let _146_1340 = (let _146_1339 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _146_1339))
in (_146_1340)::[])
in (let _146_1341 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1342 _146_1341)))
in (
# 2151 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1349 = (let _146_1347 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1346 = (let _146_1345 = (FStar_Syntax_Syntax.mk_binder b)
in (let _146_1344 = (let _146_1343 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_146_1343)::[])
in (_146_1345)::_146_1344))
in (_146_1347)::_146_1346))
in (let _146_1348 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1349 _146_1348)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (
# 2155 "FStar.TypeChecker.Tc.fst"
let assert_p = (
# 2156 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1358 = (let _146_1356 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1355 = (let _146_1354 = (let _146_1351 = (let _146_1350 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1350 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _146_1351))
in (let _146_1353 = (let _146_1352 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1352)::[])
in (_146_1354)::_146_1353))
in (_146_1356)::_146_1355))
in (let _146_1357 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1358 _146_1357)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (
# 2162 "FStar.TypeChecker.Tc.fst"
let assume_p = (
# 2163 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1367 = (let _146_1365 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1364 = (let _146_1363 = (let _146_1360 = (let _146_1359 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1359 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _146_1360))
in (let _146_1362 = (let _146_1361 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1361)::[])
in (_146_1363)::_146_1362))
in (_146_1365)::_146_1364))
in (let _146_1366 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1367 _146_1366)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (
# 2169 "FStar.TypeChecker.Tc.fst"
let null_wp = (
# 2170 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1370 = (let _146_1368 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1368)::[])
in (let _146_1369 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1370 _146_1369)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (
# 2174 "FStar.TypeChecker.Tc.fst"
let trivial_wp = (
# 2175 "FStar.TypeChecker.Tc.fst"
let _57_2683 = (FStar_Syntax_Util.type_u ())
in (match (_57_2683) with
| (t, _57_2682) -> begin
(
# 2176 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1375 = (let _146_1373 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1372 = (let _146_1371 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1371)::[])
in (_146_1373)::_146_1372))
in (let _146_1374 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _146_1375 _146_1374)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (
# 2182 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1376 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _146_1376))
in (
# 2183 "FStar.TypeChecker.Tc.fst"
let _57_2689 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_57_2689) with
| (univs, t) -> begin
(
# 2184 "FStar.TypeChecker.Tc.fst"
let _57_2705 = (match ((let _146_1378 = (let _146_1377 = (FStar_Syntax_Subst.compress t)
in _146_1377.FStar_Syntax_Syntax.n)
in (binders, _146_1378))) with
| ([], _57_2692) -> begin
([], t)
end
| (_57_2695, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _57_2702 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_2705) with
| (binders, signature) -> begin
(
# 2188 "FStar.TypeChecker.Tc.fst"
let close = (fun n ts -> (
# 2189 "FStar.TypeChecker.Tc.fst"
let ts = (let _146_1383 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _146_1383))
in (
# 2190 "FStar.TypeChecker.Tc.fst"
let _57_2710 = ()
in ts)))
in (
# 2192 "FStar.TypeChecker.Tc.fst"
let ed = (
# 2192 "FStar.TypeChecker.Tc.fst"
let _57_2712 = ed
in (let _146_1396 = (close 0 ret)
in (let _146_1395 = (close 1 bind_wp)
in (let _146_1394 = (close 1 bind_wlp)
in (let _146_1393 = (close 0 if_then_else)
in (let _146_1392 = (close 0 ite_wp)
in (let _146_1391 = (close 0 ite_wlp)
in (let _146_1390 = (close 0 wp_binop)
in (let _146_1389 = (close 0 wp_as_type)
in (let _146_1388 = (close 1 close_wp)
in (let _146_1387 = (close 0 assert_p)
in (let _146_1386 = (close 0 assume_p)
in (let _146_1385 = (close 0 null_wp)
in (let _146_1384 = (close 0 trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _57_2712.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2712.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _146_1396; FStar_Syntax_Syntax.bind_wp = _146_1395; FStar_Syntax_Syntax.bind_wlp = _146_1394; FStar_Syntax_Syntax.if_then_else = _146_1393; FStar_Syntax_Syntax.ite_wp = _146_1392; FStar_Syntax_Syntax.ite_wlp = _146_1391; FStar_Syntax_Syntax.wp_binop = _146_1390; FStar_Syntax_Syntax.wp_as_type = _146_1389; FStar_Syntax_Syntax.close_wp = _146_1388; FStar_Syntax_Syntax.assert_p = _146_1387; FStar_Syntax_Syntax.assume_p = _146_1386; FStar_Syntax_Syntax.null_wp = _146_1385; FStar_Syntax_Syntax.trivial = _146_1384}))))))))))))))
in (
# 2210 "FStar.TypeChecker.Tc.fst"
let _57_2715 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1397 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _146_1397))
end else begin
()
end
in ed)))
end))
end)))))))))))))))))))))
end)))
end))
end))
end))))

# 2214 "FStar.TypeChecker.Tc.fst"
let tc_lex_t = (fun env ses quals lids -> (
# 2221 "FStar.TypeChecker.Tc.fst"
let _57_2721 = ()
in (
# 2222 "FStar.TypeChecker.Tc.fst"
let _57_2729 = ()
in (match (ses) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _57_2758, _57_2760, [], r)::FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _57_2749, r1)::FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _57_2738, r2)::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(
# 2237 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (
# 2238 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (
# 2239 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (
# 2240 "FStar.TypeChecker.Tc.fst"
let tc = FStar_Syntax_Syntax.Sig_inductive_typ ((lex_t, (u)::[], [], t, [], (FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[], [], r))
in (
# 2242 "FStar.TypeChecker.Tc.fst"
let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (
# 2243 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (let _146_1405 = (let _146_1404 = (let _146_1403 = (let _146_1402 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _146_1402 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1403, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1404))
in (FStar_Syntax_Syntax.mk _146_1405 None r1))
in (
# 2244 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (
# 2245 "FStar.TypeChecker.Tc.fst"
let dc_lextop = FStar_Syntax_Syntax.Sig_datacon ((lex_top, (utop)::[], lex_top_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r1))
in (
# 2247 "FStar.TypeChecker.Tc.fst"
let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 2248 "FStar.TypeChecker.Tc.fst"
let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 2249 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (
# 2250 "FStar.TypeChecker.Tc.fst"
let a = (let _146_1406 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1406))
in (
# 2251 "FStar.TypeChecker.Tc.fst"
let hd = (let _146_1407 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1407))
in (
# 2252 "FStar.TypeChecker.Tc.fst"
let tl = (let _146_1412 = (let _146_1411 = (let _146_1410 = (let _146_1409 = (let _146_1408 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _146_1408 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1409, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1410))
in (FStar_Syntax_Syntax.mk _146_1411 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1412))
in (
# 2253 "FStar.TypeChecker.Tc.fst"
let res = (let _146_1416 = (let _146_1415 = (let _146_1414 = (let _146_1413 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _146_1413 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1414, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1415))
in (FStar_Syntax_Syntax.mk _146_1416 None r2))
in (let _146_1417 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _146_1417))))))
in (
# 2255 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (
# 2256 "FStar.TypeChecker.Tc.fst"
let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _146_1419 = (let _146_1418 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _146_1418))
in FStar_Syntax_Syntax.Sig_bundle (_146_1419)))))))))))))))
end
| _57_2784 -> begin
(let _146_1421 = (let _146_1420 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _146_1420))
in (FStar_All.failwith _146_1421))
end))))

# 2262 "FStar.TypeChecker.Tc.fst"
let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (
# 2325 "FStar.TypeChecker.Tc.fst"
let warn_positivity = (fun l r -> (let _146_1435 = (let _146_1434 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _146_1434))
in (FStar_TypeChecker_Errors.diag r _146_1435)))
in (
# 2327 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2330 "FStar.TypeChecker.Tc.fst"
let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(
# 2335 "FStar.TypeChecker.Tc.fst"
let _57_2806 = ()
in (
# 2336 "FStar.TypeChecker.Tc.fst"
let _57_2808 = (warn_positivity tc r)
in (
# 2337 "FStar.TypeChecker.Tc.fst"
let _57_2812 = (FStar_Syntax_Subst.open_term tps k)
in (match (_57_2812) with
| (tps, k) -> begin
(
# 2338 "FStar.TypeChecker.Tc.fst"
let _57_2816 = (tc_tparams env tps)
in (match (_57_2816) with
| (tps, env_tps, us) -> begin
(
# 2339 "FStar.TypeChecker.Tc.fst"
let _57_2819 = (FStar_Syntax_Util.arrow_formals k)
in (match (_57_2819) with
| (indices, t) -> begin
(
# 2340 "FStar.TypeChecker.Tc.fst"
let _57_2823 = (tc_tparams env_tps indices)
in (match (_57_2823) with
| (indices, env', us') -> begin
(
# 2341 "FStar.TypeChecker.Tc.fst"
let _57_2827 = (tc_trivial_guard env' t)
in (match (_57_2827) with
| (t, _57_2826) -> begin
(
# 2342 "FStar.TypeChecker.Tc.fst"
let k = (let _146_1440 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _146_1440))
in (
# 2343 "FStar.TypeChecker.Tc.fst"
let _57_2831 = (FStar_Syntax_Util.type_u ())
in (match (_57_2831) with
| (t_type, u) -> begin
(
# 2344 "FStar.TypeChecker.Tc.fst"
let _57_2832 = (let _146_1441 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _146_1441))
in (
# 2346 "FStar.TypeChecker.Tc.fst"
let t_tc = (let _146_1442 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _146_1442))
in (
# 2347 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 2348 "FStar.TypeChecker.Tc.fst"
let k = (FStar_Syntax_Subst.close tps k)
in (
# 2349 "FStar.TypeChecker.Tc.fst"
let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _146_1443 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) ([], t_tc))
in (_146_1443, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u)))))))
end)))
end))
end))
end))
end))
end))))
end
| _57_2839 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 2356 "FStar.TypeChecker.Tc.fst"
let positive_if_pure = (fun _57_2841 l -> ())
in (
# 2359 "FStar.TypeChecker.Tc.fst"
let tc_data = (fun env tcs _57_6 -> (match (_57_6) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(
# 2361 "FStar.TypeChecker.Tc.fst"
let _57_2858 = ()
in (
# 2363 "FStar.TypeChecker.Tc.fst"
let _57_2893 = (
# 2364 "FStar.TypeChecker.Tc.fst"
let tps_u_opt = (FStar_Util.find_map tcs (fun _57_2862 -> (match (_57_2862) with
| (se, u_tc) -> begin
if (let _146_1456 = (let _146_1455 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _146_1455))
in (FStar_Ident.lid_equals tc_lid _146_1456)) then begin
(
# 2366 "FStar.TypeChecker.Tc.fst"
let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2864, _57_2866, tps, _57_2869, _57_2871, _57_2873, _57_2875, _57_2877) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _57_2883 -> (match (_57_2883) with
| (x, _57_2882) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _57_2885 -> begin
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
in (match (_57_2893) with
| (tps, u_tc) -> begin
(
# 2379 "FStar.TypeChecker.Tc.fst"
let _57_2913 = (match ((let _146_1458 = (FStar_Syntax_Subst.compress t)
in _146_1458.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(
# 2384 "FStar.TypeChecker.Tc.fst"
let _57_2901 = (FStar_Util.first_N ntps bs)
in (match (_57_2901) with
| (_57_2899, bs') -> begin
(
# 2385 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (
# 2386 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _57_2907 -> (match (_57_2907) with
| (x, _57_2906) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _146_1461 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _146_1461))))
end))
end
| _57_2910 -> begin
([], t)
end)
in (match (_57_2913) with
| (arguments, result) -> begin
(
# 2390 "FStar.TypeChecker.Tc.fst"
let _57_2914 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1464 = (FStar_Syntax_Print.lid_to_string c)
in (let _146_1463 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _146_1462 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _146_1464 _146_1463 _146_1462))))
end else begin
()
end
in (
# 2396 "FStar.TypeChecker.Tc.fst"
let _57_2919 = (tc_tparams env arguments)
in (match (_57_2919) with
| (arguments, env', us) -> begin
(
# 2397 "FStar.TypeChecker.Tc.fst"
let _57_2923 = (tc_trivial_guard env' result)
in (match (_57_2923) with
| (result, _57_2922) -> begin
(
# 2398 "FStar.TypeChecker.Tc.fst"
let _57_2927 = (FStar_Syntax_Util.head_and_args result)
in (match (_57_2927) with
| (head, _57_2926) -> begin
(
# 2399 "FStar.TypeChecker.Tc.fst"
let _57_2932 = (match ((let _146_1465 = (FStar_Syntax_Subst.compress head)
in _146_1465.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _57_2931 -> begin
(let _146_1469 = (let _146_1468 = (let _146_1467 = (let _146_1466 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _146_1466))
in (_146_1467, r))
in FStar_Syntax_Syntax.Error (_146_1468))
in (Prims.raise _146_1469))
end)
in (
# 2402 "FStar.TypeChecker.Tc.fst"
let g = (FStar_List.fold_left2 (fun g _57_2938 u_x -> (match (_57_2938) with
| (x, _57_2937) -> begin
(
# 2403 "FStar.TypeChecker.Tc.fst"
let _57_2940 = ()
in (let _146_1473 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _146_1473)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (
# 2409 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1477 = (let _146_1475 = (FStar_All.pipe_right tps (FStar_List.map (fun _57_2946 -> (match (_57_2946) with
| (x, _57_2945) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _146_1475 arguments))
in (let _146_1476 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _146_1477 _146_1476)))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _57_2949 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 2417 "FStar.TypeChecker.Tc.fst"
let generalize_and_inst_within = (fun env g tcs datas -> (
# 2418 "FStar.TypeChecker.Tc.fst"
let _57_2955 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2419 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_7 -> (match (_57_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2959, _57_2961, tps, k, _57_2965, _57_2967, _57_2969, _57_2971) -> begin
(let _146_1488 = (let _146_1487 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _146_1487))
in (FStar_Syntax_Syntax.null_binder _146_1488))
end
| _57_2975 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2422 "FStar.TypeChecker.Tc.fst"
let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _57_8 -> (match (_57_8) with
| FStar_Syntax_Syntax.Sig_datacon (_57_2979, _57_2981, t, _57_2984, _57_2986, _57_2988, _57_2990, _57_2992) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _57_2996 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2425 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1490 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _146_1490))
in (
# 2426 "FStar.TypeChecker.Tc.fst"
let _57_2999 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1491 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _146_1491))
end else begin
()
end
in (
# 2427 "FStar.TypeChecker.Tc.fst"
let _57_3003 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_57_3003) with
| (uvs, t) -> begin
(
# 2428 "FStar.TypeChecker.Tc.fst"
let _57_3005 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1495 = (let _146_1493 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _146_1493 (FStar_String.concat ", ")))
in (let _146_1494 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _146_1495 _146_1494)))
end else begin
()
end
in (
# 2431 "FStar.TypeChecker.Tc.fst"
let _57_3009 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_57_3009) with
| (uvs, t) -> begin
(
# 2432 "FStar.TypeChecker.Tc.fst"
let _57_3013 = (FStar_Syntax_Util.arrow_formals t)
in (match (_57_3013) with
| (args, _57_3012) -> begin
(
# 2433 "FStar.TypeChecker.Tc.fst"
let _57_3016 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_57_3016) with
| (tc_types, data_types) -> begin
(
# 2434 "FStar.TypeChecker.Tc.fst"
let tcs = (FStar_List.map2 (fun _57_3020 se -> (match (_57_3020) with
| (x, _57_3019) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3024, tps, _57_3027, mutuals, datas, quals, r) -> begin
(
# 2436 "FStar.TypeChecker.Tc.fst"
let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (
# 2437 "FStar.TypeChecker.Tc.fst"
let _57_3050 = (match ((let _146_1498 = (FStar_Syntax_Subst.compress ty)
in _146_1498.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 2439 "FStar.TypeChecker.Tc.fst"
let _57_3041 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_57_3041) with
| (tps, rest) -> begin
(
# 2440 "FStar.TypeChecker.Tc.fst"
let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _57_3044 -> begin
(let _146_1499 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _146_1499 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _57_3047 -> begin
([], ty)
end)
in (match (_57_3050) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _57_3052 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (
# 2450 "FStar.TypeChecker.Tc.fst"
let datas = (match (uvs) with
| [] -> begin
datas
end
| _57_3056 -> begin
(
# 2453 "FStar.TypeChecker.Tc.fst"
let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _146_1500 -> FStar_Syntax_Syntax.U_name (_146_1500))))
in (
# 2454 "FStar.TypeChecker.Tc.fst"
let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_9 -> (match (_57_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3061, _57_3063, _57_3065, _57_3067, _57_3069, _57_3071, _57_3073) -> begin
(tc, uvs_universes)
end
| _57_3077 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _57_3082 d -> (match (_57_3082) with
| (t, _57_3081) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _57_3086, _57_3088, tc, ntps, quals, mutuals, r) -> begin
(
# 2458 "FStar.TypeChecker.Tc.fst"
let ty = (let _146_1504 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _146_1504 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _57_3098 -> begin
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
# 2464 "FStar.TypeChecker.Tc.fst"
let _57_3108 = (FStar_All.pipe_right ses (FStar_List.partition (fun _57_10 -> (match (_57_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_3102) -> begin
true
end
| _57_3105 -> begin
false
end))))
in (match (_57_3108) with
| (tys, datas) -> begin
(
# 2466 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2469 "FStar.TypeChecker.Tc.fst"
let _57_3125 = (FStar_List.fold_right (fun tc _57_3114 -> (match (_57_3114) with
| (env, all_tcs, g) -> begin
(
# 2470 "FStar.TypeChecker.Tc.fst"
let _57_3118 = (tc_tycon env tc)
in (match (_57_3118) with
| (env, tc, tc_u) -> begin
(
# 2471 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (
# 2472 "FStar.TypeChecker.Tc.fst"
let _57_3120 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1508 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _146_1508))
end else begin
()
end
in (let _146_1509 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _146_1509))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_3125) with
| (env, tcs, g) -> begin
(
# 2479 "FStar.TypeChecker.Tc.fst"
let _57_3135 = (FStar_List.fold_right (fun se _57_3129 -> (match (_57_3129) with
| (datas, g) -> begin
(
# 2480 "FStar.TypeChecker.Tc.fst"
let _57_3132 = (tc_data env tcs se)
in (match (_57_3132) with
| (data, g') -> begin
(let _146_1512 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _146_1512))
end))
end)) datas ([], g))
in (match (_57_3135) with
| (datas, g) -> begin
(
# 2485 "FStar.TypeChecker.Tc.fst"
let _57_3138 = (let _146_1513 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _146_1513 datas))
in (match (_57_3138) with
| (tcs, datas) -> begin
(let _146_1515 = (let _146_1514 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _146_1514))
in FStar_Syntax_Syntax.Sig_bundle (_146_1515))
end))
end))
end)))
end)))))))))

# 2488 "FStar.TypeChecker.Tc.fst"
let rec tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.env) = (fun env se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(
# 2501 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2502 "FStar.TypeChecker.Tc.fst"
let se = (tc_lex_t env ses quals lids)
in (let _146_1520 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _146_1520))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(
# 2506 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2507 "FStar.TypeChecker.Tc.fst"
let se = (tc_inductive env ses quals lids)
in (let _146_1521 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _146_1521))))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(
# 2511 "FStar.TypeChecker.Tc.fst"
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
# 2517 "FStar.TypeChecker.Tc.fst"
let _57_3176 = (set_options FStar_Options.Set o)
in (se, env))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(
# 2520 "FStar.TypeChecker.Tc.fst"
let _57_3180 = (let _146_1526 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _146_1526 Prims.ignore))
in (
# 2521 "FStar.TypeChecker.Tc.fst"
let _57_3185 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (
# 2524 "FStar.TypeChecker.Tc.fst"
let _57_3187 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (se, env))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(
# 2529 "FStar.TypeChecker.Tc.fst"
let ne = (tc_eff_decl env ne ForFree)
in (
# 2531 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (
# 2532 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(
# 2536 "FStar.TypeChecker.Tc.fst"
let ne = (tc_eff_decl env ne NotForFree)
in (
# 2537 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (
# 2538 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(
# 2542 "FStar.TypeChecker.Tc.fst"
let _57_3209 = (let _146_1527 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _146_1527))
in (match (_57_3209) with
| (a, wp_a_src) -> begin
(
# 2543 "FStar.TypeChecker.Tc.fst"
let _57_3212 = (let _146_1528 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _146_1528))
in (match (_57_3212) with
| (b, wp_b_tgt) -> begin
(
# 2544 "FStar.TypeChecker.Tc.fst"
let wp_a_tgt = (let _146_1532 = (let _146_1531 = (let _146_1530 = (let _146_1529 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _146_1529))
in FStar_Syntax_Syntax.NT (_146_1530))
in (_146_1531)::[])
in (FStar_Syntax_Subst.subst _146_1532 wp_b_tgt))
in (
# 2545 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1537 = (let _146_1535 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1534 = (let _146_1533 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_146_1533)::[])
in (_146_1535)::_146_1534))
in (let _146_1536 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _146_1537 _146_1536)))
in (
# 2546 "FStar.TypeChecker.Tc.fst"
let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (
# 2547 "FStar.TypeChecker.Tc.fst"
let sub = (
# 2547 "FStar.TypeChecker.Tc.fst"
let _57_3216 = sub
in {FStar_Syntax_Syntax.source = _57_3216.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _57_3216.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
in (
# 2548 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect ((sub, r))
in (
# 2549 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(
# 2553 "FStar.TypeChecker.Tc.fst"
let _57_3229 = ()
in (
# 2554 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2555 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2556 "FStar.TypeChecker.Tc.fst"
let _57_3235 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_57_3235) with
| (tps, c) -> begin
(
# 2557 "FStar.TypeChecker.Tc.fst"
let _57_3239 = (tc_tparams env tps)
in (match (_57_3239) with
| (tps, env, us) -> begin
(
# 2558 "FStar.TypeChecker.Tc.fst"
let _57_3243 = (tc_comp env c)
in (match (_57_3243) with
| (c, u, g) -> begin
(
# 2559 "FStar.TypeChecker.Tc.fst"
let _57_3244 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2560 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 2561 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.close_comp tps c)
in (
# 2562 "FStar.TypeChecker.Tc.fst"
let _57_3250 = (let _146_1538 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _146_1538))
in (match (_57_3250) with
| (uvs, t) -> begin
(
# 2563 "FStar.TypeChecker.Tc.fst"
let _57_3269 = (match ((let _146_1540 = (let _146_1539 = (FStar_Syntax_Subst.compress t)
in _146_1539.FStar_Syntax_Syntax.n)
in (tps, _146_1540))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_57_3253, c)) -> begin
([], c)
end
| (_57_3259, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _57_3266 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_3269) with
| (tps, c) -> begin
(
# 2567 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_effect_abbrev ((lid, uvs, tps, c, tags, r))
in (
# 2568 "FStar.TypeChecker.Tc.fst"
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
# 2572 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2573 "FStar.TypeChecker.Tc.fst"
let _57_3280 = ()
in (
# 2574 "FStar.TypeChecker.Tc.fst"
let _57_3284 = (let _146_1542 = (let _146_1541 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _146_1541))
in (check_and_gen env t _146_1542))
in (match (_57_3284) with
| (uvs, t) -> begin
(
# 2575 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (
# 2576 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(
# 2580 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2581 "FStar.TypeChecker.Tc.fst"
let _57_3297 = (FStar_Syntax_Util.type_u ())
in (match (_57_3297) with
| (k, _57_3296) -> begin
(
# 2582 "FStar.TypeChecker.Tc.fst"
let phi = (let _146_1543 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _146_1543 (norm env)))
in (
# 2583 "FStar.TypeChecker.Tc.fst"
let _57_3299 = (FStar_TypeChecker_Util.check_uvars r phi)
in (
# 2584 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))
in (
# 2585 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(
# 2589 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2590 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (
# 2591 "FStar.TypeChecker.Tc.fst"
let _57_3312 = (tc_term env e)
in (match (_57_3312) with
| (e, c, g1) -> begin
(
# 2592 "FStar.TypeChecker.Tc.fst"
let _57_3317 = (let _146_1547 = (let _146_1544 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_146_1544))
in (let _146_1546 = (let _146_1545 = (c.FStar_Syntax_Syntax.comp ())
in (e, _146_1545))
in (check_expected_effect env _146_1547 _146_1546)))
in (match (_57_3317) with
| (e, _57_3315, g) -> begin
(
# 2593 "FStar.TypeChecker.Tc.fst"
let _57_3318 = (let _146_1548 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _146_1548))
in (
# 2594 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, r))
in (
# 2595 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(
# 2599 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2600 "FStar.TypeChecker.Tc.fst"
let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
if (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q')) then begin
Some (q)
end else begin
(let _146_1560 = (let _146_1559 = (let _146_1558 = (let _146_1557 = (FStar_Syntax_Print.lid_to_string l)
in (let _146_1556 = (FStar_Syntax_Print.quals_to_string q)
in (let _146_1555 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _146_1557 _146_1556 _146_1555))))
in (_146_1558, r))
in FStar_Syntax_Syntax.Error (_146_1559))
in (Prims.raise _146_1560))
end
end))
in (
# 2614 "FStar.TypeChecker.Tc.fst"
let _57_3362 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _57_3339 lb -> (match (_57_3339) with
| (gen, lbs, quals_opt) -> begin
(
# 2615 "FStar.TypeChecker.Tc.fst"
let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2616 "FStar.TypeChecker.Tc.fst"
let _57_3358 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(
# 2620 "FStar.TypeChecker.Tc.fst"
let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (
# 2621 "FStar.TypeChecker.Tc.fst"
let _57_3353 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _57_3352 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _146_1563 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _146_1563, quals_opt))))
end)
in (match (_57_3358) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_57_3362) with
| (should_generalize, lbs', quals_opt) -> begin
(
# 2630 "FStar.TypeChecker.Tc.fst"
let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _57_11 -> (match (_57_11) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _57_3371 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (
# 2637 "FStar.TypeChecker.Tc.fst"
let lbs' = (FStar_List.rev lbs')
in (
# 2640 "FStar.TypeChecker.Tc.fst"
let e = (let _146_1567 = (let _146_1566 = (let _146_1565 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _146_1565))
in FStar_Syntax_Syntax.Tm_let (_146_1566))
in (FStar_Syntax_Syntax.mk _146_1567 None r))
in (
# 2643 "FStar.TypeChecker.Tc.fst"
let _57_3405 = (match ((tc_maybe_toplevel_term (
# 2643 "FStar.TypeChecker.Tc.fst"
let _57_3375 = env
in {FStar_TypeChecker_Env.solver = _57_3375.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3375.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3375.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3375.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3375.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3375.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3375.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3375.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3375.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3375.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3375.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _57_3375.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _57_3375.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3375.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3375.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3375.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3375.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3375.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3375.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _57_3382; FStar_Syntax_Syntax.pos = _57_3380; FStar_Syntax_Syntax.vars = _57_3378}, _57_3389, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(
# 2646 "FStar.TypeChecker.Tc.fst"
let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_57_3393, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _57_3399 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _57_3402 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_57_3405) with
| (se, lbs) -> begin
(
# 2653 "FStar.TypeChecker.Tc.fst"
let _57_3411 = if (log env) then begin
(let _146_1575 = (let _146_1574 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 2655 "FStar.TypeChecker.Tc.fst"
let should_log = (match ((let _146_1571 = (let _146_1570 = (let _146_1569 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _146_1569.FStar_Syntax_Syntax.fv_name)
in _146_1570.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _146_1571))) with
| None -> begin
true
end
| _57_3409 -> begin
false
end)
in if should_log then begin
(let _146_1573 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _146_1572 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _146_1573 _146_1572)))
end else begin
""
end))))
in (FStar_All.pipe_right _146_1574 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _146_1575))
end else begin
()
end
in (
# 2662 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end))))
end))

# 2666 "FStar.TypeChecker.Tc.fst"
let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (
# 2690 "FStar.TypeChecker.Tc.fst"
let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _57_12 -> (match (_57_12) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _57_3421 -> begin
false
end)))))
in (
# 2691 "FStar.TypeChecker.Tc.fst"
let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _57_3431 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_57_3433) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _57_3444, _57_3446) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _57_3452 -> (match (_57_3452) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _57_3458, _57_3460, quals, r) -> begin
(
# 2705 "FStar.TypeChecker.Tc.fst"
let dec = (let _146_1591 = (let _146_1590 = (let _146_1589 = (let _146_1588 = (let _146_1587 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _146_1587))
in FStar_Syntax_Syntax.Tm_arrow (_146_1588))
in (FStar_Syntax_Syntax.mk _146_1589 None r))
in (l, us, _146_1590, (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_146_1591))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _57_3470, _57_3472, _57_3474, _57_3476, r) -> begin
(
# 2708 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _57_3482 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_57_3484, _57_3486, quals, _57_3489) -> begin
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
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _57_13 -> (match (_57_13) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _57_3508 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_57_3510) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _57_3529, _57_3531, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(
# 2739 "FStar.TypeChecker.Tc.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2740 "FStar.TypeChecker.Tc.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))) then begin
([], hidden)
end else begin
(
# 2743 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::[], (FStar_Ident.range_of_lid lid)))
in ((dec)::[], (lid)::hidden))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (is_abstract quals) then begin
(let _146_1598 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _146_1597 = (let _146_1596 = (let _146_1595 = (let _146_1594 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _146_1594.FStar_Syntax_Syntax.fv_name)
in _146_1595.FStar_Syntax_Syntax.v)
in (_146_1596, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_146_1597)))))
in (_146_1598, hidden))
end else begin
((se)::[], hidden)
end
end))))

# 2752 "FStar.TypeChecker.Tc.fst"
let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (
# 2753 "FStar.TypeChecker.Tc.fst"
let _57_3570 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _57_3551 se -> (match (_57_3551) with
| (ses, exports, env, hidden) -> begin
(
# 2755 "FStar.TypeChecker.Tc.fst"
let _57_3553 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1605 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _146_1605))
end else begin
()
end
in (
# 2758 "FStar.TypeChecker.Tc.fst"
let _57_3557 = (tc_decl env se)
in (match (_57_3557) with
| (se, env) -> begin
(
# 2760 "FStar.TypeChecker.Tc.fst"
let _57_3558 = if ((FStar_ST.read FStar_Options.log_types) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _146_1606 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _146_1606))
end else begin
()
end
in (
# 2763 "FStar.TypeChecker.Tc.fst"
let _57_3560 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (
# 2765 "FStar.TypeChecker.Tc.fst"
let _57_3564 = (for_export hidden se)
in (match (_57_3564) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_57_3570) with
| (ses, exports, env, _57_3569) -> begin
(let _146_1607 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _146_1607, env))
end)))

# 2770 "FStar.TypeChecker.Tc.fst"
let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2771 "FStar.TypeChecker.Tc.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 2772 "FStar.TypeChecker.Tc.fst"
let msg = (Prims.strcat "Internals for " name)
in (
# 2773 "FStar.TypeChecker.Tc.fst"
let env = (
# 2773 "FStar.TypeChecker.Tc.fst"
let _57_3575 = env
in (let _146_1612 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _57_3575.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3575.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3575.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3575.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3575.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3575.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3575.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3575.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3575.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3575.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3575.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3575.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3575.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_3575.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_3575.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3575.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _146_1612; FStar_TypeChecker_Env.type_of = _57_3575.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3575.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3575.FStar_TypeChecker_Env.use_bv_sorts}))
in (
# 2774 "FStar.TypeChecker.Tc.fst"
let _57_3578 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (
# 2775 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (
# 2776 "FStar.TypeChecker.Tc.fst"
let _57_3584 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_57_3584) with
| (ses, exports, env) -> begin
((
# 2777 "FStar.TypeChecker.Tc.fst"
let _57_3585 = modul
in {FStar_Syntax_Syntax.name = _57_3585.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _57_3585.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3585.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))

# 2779 "FStar.TypeChecker.Tc.fst"
let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (
# 2780 "FStar.TypeChecker.Tc.fst"
let _57_3593 = (tc_decls env decls)
in (match (_57_3593) with
| (ses, exports, env) -> begin
(
# 2781 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2781 "FStar.TypeChecker.Tc.fst"
let _57_3594 = modul
in {FStar_Syntax_Syntax.name = _57_3594.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _57_3594.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3594.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))

# 2784 "FStar.TypeChecker.Tc.fst"
let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (
# 2785 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2785 "FStar.TypeChecker.Tc.fst"
let _57_3600 = modul
in {FStar_Syntax_Syntax.name = _57_3600.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _57_3600.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (
# 2786 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.finish_module env modul)
in (
# 2787 "FStar.TypeChecker.Tc.fst"
let _57_3610 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(
# 2789 "FStar.TypeChecker.Tc.fst"
let _57_3604 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (
# 2790 "FStar.TypeChecker.Tc.fst"
let _57_3606 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (
# 2791 "FStar.TypeChecker.Tc.fst"
let _57_3608 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _146_1625 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _146_1625 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))

# 2796 "FStar.TypeChecker.Tc.fst"
let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2797 "FStar.TypeChecker.Tc.fst"
let _57_3617 = (tc_partial_modul env modul)
in (match (_57_3617) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

# 2800 "FStar.TypeChecker.Tc.fst"
let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 2801 "FStar.TypeChecker.Tc.fst"
let _57_3620 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _146_1634 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _146_1634))
end else begin
()
end
in (
# 2803 "FStar.TypeChecker.Tc.fst"
let env = (
# 2803 "FStar.TypeChecker.Tc.fst"
let _57_3622 = env
in {FStar_TypeChecker_Env.solver = _57_3622.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3622.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3622.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3622.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3622.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3622.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3622.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3622.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3622.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3622.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3622.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3622.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3622.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_3622.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3622.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3622.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3622.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3622.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3622.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3622.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 2804 "FStar.TypeChecker.Tc.fst"
let _57_3638 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _57_3630) -> begin
(let _146_1639 = (let _146_1638 = (let _146_1637 = (FStar_TypeChecker_Env.get_range env)
in ((Prims.strcat "Implicit argument: " msg), _146_1637))
in FStar_Syntax_Syntax.Error (_146_1638))
in (Prims.raise _146_1639))
end
in (match (_57_3638) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(t, c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(let _146_1644 = (let _146_1643 = (let _146_1642 = (let _146_1640 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _146_1640))
in (let _146_1641 = (FStar_TypeChecker_Env.get_range env)
in (_146_1642, _146_1641)))
in FStar_Syntax_Syntax.Error (_146_1643))
in (Prims.raise _146_1644))
end
end)))))

# 2811 "FStar.TypeChecker.Tc.fst"
let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (
# 2812 "FStar.TypeChecker.Tc.fst"
let _57_3641 = if ((let _146_1649 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _146_1649)) <> 0) then begin
(let _146_1650 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _146_1650))
end else begin
()
end
in (
# 2814 "FStar.TypeChecker.Tc.fst"
let _57_3645 = (tc_modul env m)
in (match (_57_3645) with
| (m, env) -> begin
(
# 2815 "FStar.TypeChecker.Tc.fst"
let _57_3646 = if (FStar_Options.should_dump m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _146_1651 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _146_1651))
end else begin
()
end
in (m, env))
end))))




