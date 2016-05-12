
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
(let _146_243 = (let _146_241 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _146_241))
in (let _146_242 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _146_243 _146_242)))
end else begin
()
end
in (
# 256 "FStar.TypeChecker.Tc.fst"
let top = e
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_57_295) -> begin
(let _146_247 = (FStar_Syntax_Subst.compress e)
in (tc_term env _146_247))
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
in (let _146_249 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_pattern (pats)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_248 = (FStar_TypeChecker_Rel.conj_guard g g')
in (_146_249, c, _146_248))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _146_250 = (FStar_Syntax_Subst.compress e)
in _146_250.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_57_368, {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _57_375; FStar_Syntax_Syntax.lbtyp = _57_373; FStar_Syntax_Syntax.lbeff = _57_371; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 291 "FStar.TypeChecker.Tc.fst"
let _57_386 = (let _146_251 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _146_251 e1))
in (match (_57_386) with
| (e1, c1, g1) -> begin
(
# 292 "FStar.TypeChecker.Tc.fst"
let _57_390 = (tc_term env e2)
in (match (_57_390) with
| (e2, c2, g2) -> begin
(
# 293 "FStar.TypeChecker.Tc.fst"
let c = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (None, c2))
in (
# 294 "FStar.TypeChecker.Tc.fst"
let e = (let _146_256 = (let _146_255 = (let _146_254 = (let _146_253 = (let _146_252 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Common.t_unit, e1))
in (_146_252)::[])
in (false, _146_253))
in (_146_254, e2))
in FStar_Syntax_Syntax.Tm_let (_146_255))
in (FStar_Syntax_Syntax.mk _146_256 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 295 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_257 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _146_257)))))
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
let _57_429 = (let _146_259 = (let _146_258 = (c'.FStar_Syntax_Syntax.comp ())
in (e, _146_258))
in (check_expected_effect env (Some (expected_c)) _146_259))
in (match (_57_429) with
| (e, expected_c, g'') -> begin
(
# 312 "FStar.TypeChecker.Tc.fst"
let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (let _146_262 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t_res), Some ((FStar_Syntax_Util.comp_effect_name expected_c))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_261 = (let _146_260 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _146_260))
in (_146_262, (FStar_Syntax_Util.lcomp_of_comp expected_c), _146_261))))
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
let _57_449 = (let _146_263 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _146_263 e))
in (match (_57_449) with
| (e, c, g) -> begin
(
# 321 "FStar.TypeChecker.Tc.fst"
let _57_453 = (let _146_267 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_450 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _146_267 e c f))
in (match (_57_453) with
| (c, f) -> begin
(
# 322 "FStar.TypeChecker.Tc.fst"
let _57_457 = (let _146_268 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t), Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _146_268 c))
in (match (_57_457) with
| (e, c, f2) -> begin
(let _146_270 = (let _146_269 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _146_269))
in (e, c, _146_270))
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
let env = (let _146_272 = (let _146_271 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_271 Prims.fst))
in (FStar_All.pipe_right _146_272 instantiate_both))
in (
# 328 "FStar.TypeChecker.Tc.fst"
let _57_464 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_274 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _146_273 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _146_274 _146_273)))
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
(let _146_275 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _146_275))
end else begin
(let _146_276 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _146_276))
end
in (match (_57_473) with
| (e, c, g) -> begin
(
# 336 "FStar.TypeChecker.Tc.fst"
let _57_474 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_277 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _146_277))
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
let _57_481 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_283 = (FStar_Syntax_Print.term_to_string e)
in (let _146_282 = (let _146_278 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _146_278))
in (let _146_281 = (let _146_280 = (FStar_TypeChecker_Env.expected_typ env0)
in (FStar_All.pipe_right _146_280 (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end))))
in (FStar_Util.print3 "(%s) About to check %s against expected typ %s\n" _146_283 _146_282 _146_281))))
end else begin
()
end
in (
# 348 "FStar.TypeChecker.Tc.fst"
let _57_486 = (comp_check_expected_typ env0 e c)
in (match (_57_486) with
| (e, c, g') -> begin
(
# 349 "FStar.TypeChecker.Tc.fst"
let _57_487 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_286 = (FStar_Syntax_Print.term_to_string e)
in (let _146_285 = (let _146_284 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _146_284))
in (FStar_Util.print2 "(%s) checked ... got %s\n" _146_286 _146_285)))
end else begin
()
end
in (
# 353 "FStar.TypeChecker.Tc.fst"
let gimp = (match ((let _146_287 = (FStar_Syntax_Subst.compress head)
in _146_287.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _57_491) -> begin
(
# 356 "FStar.TypeChecker.Tc.fst"
let imp = ("head of application is a uvar", env0, u, e, c.FStar_Syntax_Syntax.res_typ, head.FStar_Syntax_Syntax.pos)
in (
# 357 "FStar.TypeChecker.Tc.fst"
let _57_495 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_495.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_495.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_495.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _57_498 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (
# 359 "FStar.TypeChecker.Tc.fst"
let gres = (let _146_288 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _146_288))
in (
# 360 "FStar.TypeChecker.Tc.fst"
let _57_501 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_289 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print1 "Guard from application node is %s\n" _146_289))
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
let _57_509 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_509) with
| (env1, topt) -> begin
(
# 366 "FStar.TypeChecker.Tc.fst"
let env1 = (instantiate_both env1)
in (
# 367 "FStar.TypeChecker.Tc.fst"
let _57_514 = (tc_term env1 e1)
in (match (_57_514) with
| (e1, c1, g1) -> begin
(
# 368 "FStar.TypeChecker.Tc.fst"
let _57_525 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(
# 371 "FStar.TypeChecker.Tc.fst"
let _57_521 = (FStar_Syntax_Util.type_u ())
in (match (_57_521) with
| (k, _57_520) -> begin
(
# 372 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _146_290 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_146_290, res_t)))
end))
end)
in (match (_57_525) with
| (env_branches, res_t) -> begin
(
# 375 "FStar.TypeChecker.Tc.fst"
let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (
# 376 "FStar.TypeChecker.Tc.fst"
let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (
# 377 "FStar.TypeChecker.Tc.fst"
let _57_542 = (
# 378 "FStar.TypeChecker.Tc.fst"
let _57_539 = (FStar_List.fold_right (fun _57_533 _57_536 -> (match ((_57_533, _57_536)) with
| ((_57_529, f, c, g), (caccum, gaccum)) -> begin
(let _146_293 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _146_293))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_539) with
| (cases, g) -> begin
(let _146_294 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_146_294, g))
end))
in (match (_57_542) with
| (c_branches, g_branches) -> begin
(
# 382 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (guard_x), c_branches))
in (
# 383 "FStar.TypeChecker.Tc.fst"
let e = (let _146_298 = (let _146_297 = (let _146_296 = (FStar_List.map (fun _57_551 -> (match (_57_551) with
| (f, _57_546, _57_548, _57_550) -> begin
f
end)) t_eqns)
in (e1, _146_296))
in FStar_Syntax_Syntax.Tm_match (_146_297))
in (FStar_Syntax_Syntax.mk _146_298 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (
# 385 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ), Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (
# 386 "FStar.TypeChecker.Tc.fst"
let _57_554 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_301 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _146_300 = (let _146_299 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _146_299))
in (FStar_Util.print2 "(%s) comp type = %s\n" _146_301 _146_300)))
end else begin
()
end
in (let _146_302 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _146_302))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_566); FStar_Syntax_Syntax.lbunivs = _57_564; FStar_Syntax_Syntax.lbtyp = _57_562; FStar_Syntax_Syntax.lbeff = _57_560; FStar_Syntax_Syntax.lbdef = _57_558}::[]), _57_572) -> begin
(
# 393 "FStar.TypeChecker.Tc.fst"
let _57_575 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_303 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _146_303))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _57_579), _57_582) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_597); FStar_Syntax_Syntax.lbunivs = _57_595; FStar_Syntax_Syntax.lbtyp = _57_593; FStar_Syntax_Syntax.lbeff = _57_591; FStar_Syntax_Syntax.lbdef = _57_589}::_57_587), _57_603) -> begin
(
# 400 "FStar.TypeChecker.Tc.fst"
let _57_606 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_304 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _146_304))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _57_610), _57_613) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 413 "FStar.TypeChecker.Tc.fst"
let check_instantiated_fvar = (fun env v dc e t -> (
# 414 "FStar.TypeChecker.Tc.fst"
let _57_627 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_627) with
| (e, t, implicits) -> begin
(
# 416 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _146_318 = (let _146_317 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_317))
in FStar_Util.Inr (_146_318))
end
in (
# 417 "FStar.TypeChecker.Tc.fst"
let is_data_ctor = (fun _57_4 -> (match (_57_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _57_637 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _146_324 = (let _146_323 = (let _146_322 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _146_321 = (FStar_TypeChecker_Env.get_range env)
in (_146_322, _146_321)))
in FStar_Syntax_Syntax.Error (_146_323))
in (Prims.raise _146_324))
end else begin
(value_check_expected_typ env e tc implicits)
end))
end)))
in (
# 427 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (
# 428 "FStar.TypeChecker.Tc.fst"
let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(FStar_All.failwith "Impossible: Violation of locally nameless convention")
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(
# 434 "FStar.TypeChecker.Tc.fst"
let g = (match ((let _146_325 = (FStar_Syntax_Subst.compress t1)
in _146_325.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_648) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _57_651 -> begin
(
# 436 "FStar.TypeChecker.Tc.fst"
let imp = ("uvar in term", env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (
# 437 "FStar.TypeChecker.Tc.fst"
let _57_653 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_653.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_653.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_653.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 442 "FStar.TypeChecker.Tc.fst"
let _57_659 = (FStar_Syntax_Util.type_u ())
in (match (_57_659) with
| (k, u) -> begin
(
# 443 "FStar.TypeChecker.Tc.fst"
let t = (FStar_TypeChecker_Util.new_uvar env k)
in (
# 444 "FStar.TypeChecker.Tc.fst"
let e = (FStar_TypeChecker_Util.new_uvar env t)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 448 "FStar.TypeChecker.Tc.fst"
let t = if env.FStar_TypeChecker_Env.use_bv_sorts then begin
x.FStar_Syntax_Syntax.sort
end else begin
(FStar_TypeChecker_Env.lookup_bv env x)
end
in (
# 449 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.bv_to_name (
# 449 "FStar.TypeChecker.Tc.fst"
let _57_665 = x
in {FStar_Syntax_Syntax.ppname = _57_665.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_665.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (
# 450 "FStar.TypeChecker.Tc.fst"
let _57_671 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_671) with
| (e, t, implicits) -> begin
(
# 451 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _146_327 = (let _146_326 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_326))
in FStar_Util.Inr (_146_327))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _57_678; FStar_Syntax_Syntax.pos = _57_676; FStar_Syntax_Syntax.vars = _57_674}, us) -> begin
(
# 455 "FStar.TypeChecker.Tc.fst"
let us = (FStar_List.map (tc_universe env) us)
in (
# 456 "FStar.TypeChecker.Tc.fst"
let _57_688 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_688) with
| (us', t) -> begin
(
# 457 "FStar.TypeChecker.Tc.fst"
let _57_695 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _146_330 = (let _146_329 = (let _146_328 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _146_328))
in FStar_Syntax_Syntax.Error (_146_329))
in (Prims.raise _146_330))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _57_694 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (
# 462 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 462 "FStar.TypeChecker.Tc.fst"
let _57_697 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 462 "FStar.TypeChecker.Tc.fst"
let _57_699 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_699.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_699.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_697.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_697.FStar_Syntax_Syntax.fv_qual})
in (
# 463 "FStar.TypeChecker.Tc.fst"
let e = (let _146_333 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_333 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(
# 467 "FStar.TypeChecker.Tc.fst"
let _57_707 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_707) with
| (us, t) -> begin
(
# 468 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 468 "FStar.TypeChecker.Tc.fst"
let _57_708 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 468 "FStar.TypeChecker.Tc.fst"
let _57_710 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_710.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_710.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_708.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_708.FStar_Syntax_Syntax.fv_qual})
in (
# 469 "FStar.TypeChecker.Tc.fst"
let e = (let _146_334 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_334 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t)))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(
# 473 "FStar.TypeChecker.Tc.fst"
let t = (tc_constant env top.FStar_Syntax_Syntax.pos c)
in (
# 474 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 478 "FStar.TypeChecker.Tc.fst"
let _57_724 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_724) with
| (bs, c) -> begin
(
# 479 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 480 "FStar.TypeChecker.Tc.fst"
let _57_729 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_729) with
| (env, _57_728) -> begin
(
# 481 "FStar.TypeChecker.Tc.fst"
let _57_734 = (tc_binders env bs)
in (match (_57_734) with
| (bs, env, g, us) -> begin
(
# 482 "FStar.TypeChecker.Tc.fst"
let _57_738 = (tc_comp env c)
in (match (_57_738) with
| (c, uc, f) -> begin
(
# 483 "FStar.TypeChecker.Tc.fst"
let e = (
# 483 "FStar.TypeChecker.Tc.fst"
let _57_739 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _57_739.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_739.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_739.FStar_Syntax_Syntax.vars})
in (
# 484 "FStar.TypeChecker.Tc.fst"
let _57_742 = (check_smt_pat env e bs c)
in (
# 485 "FStar.TypeChecker.Tc.fst"
let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (
# 486 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 487 "FStar.TypeChecker.Tc.fst"
let g = (let _146_335 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _146_335))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(
# 491 "FStar.TypeChecker.Tc.fst"
let u = (tc_universe env u)
in (
# 492 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) None top.FStar_Syntax_Syntax.pos)
in (
# 493 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 497 "FStar.TypeChecker.Tc.fst"
let _57_758 = (let _146_337 = (let _146_336 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_336)::[])
in (FStar_Syntax_Subst.open_term _146_337 phi))
in (match (_57_758) with
| (x, phi) -> begin
(
# 498 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 499 "FStar.TypeChecker.Tc.fst"
let _57_763 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_763) with
| (env, _57_762) -> begin
(
# 500 "FStar.TypeChecker.Tc.fst"
let _57_768 = (let _146_338 = (FStar_List.hd x)
in (tc_binder env _146_338))
in (match (_57_768) with
| (x, env, f1, u) -> begin
(
# 501 "FStar.TypeChecker.Tc.fst"
let _57_769 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_341 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _146_340 = (FStar_Syntax_Print.term_to_string phi)
in (let _146_339 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _146_341 _146_340 _146_339))))
end else begin
()
end
in (
# 504 "FStar.TypeChecker.Tc.fst"
let _57_774 = (FStar_Syntax_Util.type_u ())
in (match (_57_774) with
| (t_phi, _57_773) -> begin
(
# 505 "FStar.TypeChecker.Tc.fst"
let _57_779 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_57_779) with
| (phi, _57_777, f2) -> begin
(
# 506 "FStar.TypeChecker.Tc.fst"
let e = (
# 506 "FStar.TypeChecker.Tc.fst"
let _57_780 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _57_780.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_780.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_780.FStar_Syntax_Syntax.vars})
in (
# 507 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 508 "FStar.TypeChecker.Tc.fst"
let g = (let _146_342 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _146_342))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _57_788) -> begin
(
# 512 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (
# 513 "FStar.TypeChecker.Tc.fst"
let _57_794 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_343 = (FStar_Syntax_Print.term_to_string (
# 514 "FStar.TypeChecker.Tc.fst"
let _57_792 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _57_792.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_792.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_792.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _146_343))
end else begin
()
end
in (
# 515 "FStar.TypeChecker.Tc.fst"
let _57_798 = (FStar_Syntax_Subst.open_term bs body)
in (match (_57_798) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _57_800 -> begin
(let _146_345 = (let _146_344 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _146_344))
in (FStar_All.failwith _146_345))
end)))))
and tc_constant : FStar_TypeChecker_Env.env  ->  FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun env r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_57_806) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_57_809, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_57_814, Some (FStar_Const.Unsigned, FStar_Const.Int8)) -> begin
FStar_TypeChecker_Common.t_uint8
end
| FStar_Const.Const_int (_57_822, Some (FStar_Const.Signed, FStar_Const.Int8)) -> begin
FStar_TypeChecker_Common.t_int8
end
| FStar_Const.Const_int (_57_830, Some (FStar_Const.Unsigned, FStar_Const.Int16)) -> begin
FStar_TypeChecker_Common.t_uint16
end
| FStar_Const.Const_int (_57_838, Some (FStar_Const.Signed, FStar_Const.Int16)) -> begin
FStar_TypeChecker_Common.t_int16
end
| FStar_Const.Const_int (_57_846, Some (FStar_Const.Unsigned, FStar_Const.Int32)) -> begin
FStar_TypeChecker_Common.t_uint32
end
| FStar_Const.Const_int (_57_854, Some (FStar_Const.Signed, FStar_Const.Int32)) -> begin
FStar_TypeChecker_Common.t_int32
end
| FStar_Const.Const_int (_57_862, Some (FStar_Const.Unsigned, FStar_Const.Int64)) -> begin
FStar_TypeChecker_Common.t_uint64
end
| FStar_Const.Const_int (_57_870, Some (FStar_Const.Signed, FStar_Const.Int64)) -> begin
FStar_TypeChecker_Common.t_int64
end
| FStar_Const.Const_string (_57_878) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_57_881) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_57_884) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_57_888) -> begin
(
# 539 "FStar.TypeChecker.Tc.fst"
let fail = (fun _57_891 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Range constant cannot be checked in this context; expected an instance of \'range_of\'", r))))
end))
in (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(fail ())
end
| Some (t) -> begin
if (let _146_351 = (FStar_Syntax_Util.destruct t FStar_Syntax_Const.range_of_lid)
in (FStar_Option.isSome _146_351)) then begin
t
end else begin
(fail ())
end
end))
end
| _57_896 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 560 "FStar.TypeChecker.Tc.fst"
let _57_903 = (FStar_Syntax_Util.type_u ())
in (match (_57_903) with
| (k, u) -> begin
(
# 561 "FStar.TypeChecker.Tc.fst"
let _57_908 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_908) with
| (t, _57_906, g) -> begin
(let _146_354 = (FStar_Syntax_Syntax.mk_Total t)
in (_146_354, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 565 "FStar.TypeChecker.Tc.fst"
let _57_913 = (FStar_Syntax_Util.type_u ())
in (match (_57_913) with
| (k, u) -> begin
(
# 566 "FStar.TypeChecker.Tc.fst"
let _57_918 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_918) with
| (t, _57_916, g) -> begin
(let _146_355 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_146_355, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 570 "FStar.TypeChecker.Tc.fst"
let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (
# 571 "FStar.TypeChecker.Tc.fst"
let tc = (let _146_357 = (let _146_356 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_146_356)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _146_357 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 572 "FStar.TypeChecker.Tc.fst"
let _57_927 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_57_927) with
| (tc, _57_925, f) -> begin
(
# 573 "FStar.TypeChecker.Tc.fst"
let _57_931 = (FStar_Syntax_Util.head_and_args tc)
in (match (_57_931) with
| (_57_929, args) -> begin
(
# 574 "FStar.TypeChecker.Tc.fst"
let _57_934 = (let _146_359 = (FStar_List.hd args)
in (let _146_358 = (FStar_List.tl args)
in (_146_359, _146_358)))
in (match (_57_934) with
| (res, args) -> begin
(
# 575 "FStar.TypeChecker.Tc.fst"
let _57_950 = (let _146_361 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _57_5 -> (match (_57_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(
# 577 "FStar.TypeChecker.Tc.fst"
let _57_941 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_941) with
| (env, _57_940) -> begin
(
# 578 "FStar.TypeChecker.Tc.fst"
let _57_946 = (tc_tot_or_gtot_term env e)
in (match (_57_946) with
| (e, _57_944, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _146_361 FStar_List.unzip))
in (match (_57_950) with
| (flags, guards) -> begin
(
# 581 "FStar.TypeChecker.Tc.fst"
let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| _57_955 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _146_363 = (FStar_Syntax_Syntax.mk_Comp (
# 584 "FStar.TypeChecker.Tc.fst"
let _57_957 = c
in {FStar_Syntax_Syntax.effect_name = _57_957.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _57_957.FStar_Syntax_Syntax.flags}))
in (let _146_362 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_146_363, u, _146_362))))
end))
end))
end))
end))))
end))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (
# 591 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun u -> (
# 592 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_57_965) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _146_368 = (aux u)
in FStar_Syntax_Syntax.U_succ (_146_368))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _146_369 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_146_369))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _146_373 = (let _146_372 = (let _146_371 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _146_370 = (FStar_TypeChecker_Env.get_range env)
in (_146_371, _146_370)))
in FStar_Syntax_Syntax.Error (_146_372))
in (Prims.raise _146_373))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _146_374 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_374 Prims.snd))
end
| _57_980 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (
# 614 "FStar.TypeChecker.Tc.fst"
let fail = (fun msg t -> (let _146_383 = (let _146_382 = (let _146_381 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_146_381, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_382))
in (Prims.raise _146_383)))
in (
# 623 "FStar.TypeChecker.Tc.fst"
let check_binders = (fun env bs bs_expected -> (
# 628 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun _57_998 bs bs_expected -> (match (_57_998) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| ((hd, imp)::bs, (hd_expected, imp')::bs_expected) -> begin
(
# 632 "FStar.TypeChecker.Tc.fst"
let _57_1029 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _146_400 = (let _146_399 = (let _146_398 = (let _146_396 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _146_396))
in (let _146_397 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_146_398, _146_397)))
in FStar_Syntax_Syntax.Error (_146_399))
in (Prims.raise _146_400))
end
| _57_1028 -> begin
()
end)
in (
# 639 "FStar.TypeChecker.Tc.fst"
let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (
# 640 "FStar.TypeChecker.Tc.fst"
let _57_1046 = (match ((let _146_401 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _146_401.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _57_1034 -> begin
(
# 643 "FStar.TypeChecker.Tc.fst"
let _57_1035 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_402 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _146_402))
end else begin
()
end
in (
# 644 "FStar.TypeChecker.Tc.fst"
let _57_1041 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_57_1041) with
| (t, _57_1039, g1) -> begin
(
# 645 "FStar.TypeChecker.Tc.fst"
let g2 = (let _146_404 = (FStar_TypeChecker_Env.get_range env)
in (let _146_403 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _146_404 "Type annotation on parameter incompatible with the expected type" _146_403)))
in (
# 649 "FStar.TypeChecker.Tc.fst"
let g = (let _146_405 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _146_405))
in (t, g)))
end)))
end)
in (match (_57_1046) with
| (t, g) -> begin
(
# 651 "FStar.TypeChecker.Tc.fst"
let hd = (
# 651 "FStar.TypeChecker.Tc.fst"
let _57_1047 = hd
in {FStar_Syntax_Syntax.ppname = _57_1047.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1047.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 652 "FStar.TypeChecker.Tc.fst"
let b = (hd, imp)
in (
# 653 "FStar.TypeChecker.Tc.fst"
let b_expected = (hd_expected, imp')
in (
# 654 "FStar.TypeChecker.Tc.fst"
let env = (maybe_push_binding env b)
in (
# 655 "FStar.TypeChecker.Tc.fst"
let subst = (let _146_406 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _146_406))
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
# 665 "FStar.TypeChecker.Tc.fst"
let rec expected_function_typ = (fun env t0 body -> (match (t0) with
| None -> begin
(
# 676 "FStar.TypeChecker.Tc.fst"
let _57_1068 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1067 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (
# 679 "FStar.TypeChecker.Tc.fst"
let _57_1075 = (tc_binders env bs)
in (match (_57_1075) with
| (bs, envbody, g, _57_1074) -> begin
(
# 680 "FStar.TypeChecker.Tc.fst"
let _57_1093 = (match ((let _146_413 = (FStar_Syntax_Subst.compress body)
in _146_413.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _57_1080) -> begin
(
# 682 "FStar.TypeChecker.Tc.fst"
let _57_1087 = (tc_comp envbody c)
in (match (_57_1087) with
| (c, _57_1085, g') -> begin
(let _146_414 = (FStar_TypeChecker_Rel.conj_guard g g')
in (Some (c), body, _146_414))
end))
end
| _57_1089 -> begin
(None, body, g)
end)
in (match (_57_1093) with
| (copt, body, g) -> begin
(None, bs, [], copt, envbody, body, g)
end))
end)))
end
| Some (t) -> begin
(
# 688 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 689 "FStar.TypeChecker.Tc.fst"
let rec as_function_typ = (fun norm t -> (match ((let _146_419 = (FStar_Syntax_Subst.compress t)
in _146_419.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 693 "FStar.TypeChecker.Tc.fst"
let _57_1120 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1119 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 694 "FStar.TypeChecker.Tc.fst"
let _57_1127 = (tc_binders env bs)
in (match (_57_1127) with
| (bs, envbody, g, _57_1126) -> begin
(
# 695 "FStar.TypeChecker.Tc.fst"
let _57_1131 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_57_1131) with
| (envbody, _57_1130) -> begin
(Some ((t, true)), bs, [], None, envbody, body, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _57_1134) -> begin
(
# 701 "FStar.TypeChecker.Tc.fst"
let _57_1145 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_57_1145) with
| (_57_1138, bs, bs', copt, env, body, g) -> begin
(Some ((t, false)), bs, bs', copt, env, body, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 705 "FStar.TypeChecker.Tc.fst"
let _57_1152 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_57_1152) with
| (bs_expected, c_expected) -> begin
(
# 712 "FStar.TypeChecker.Tc.fst"
let check_actuals_against_formals = (fun env bs bs_expected -> (
# 713 "FStar.TypeChecker.Tc.fst"
let rec handle_more = (fun _57_1163 c_expected -> (match (_57_1163) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _146_430 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _146_430))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(
# 718 "FStar.TypeChecker.Tc.fst"
let c = (let _146_431 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _146_431))
in (let _146_432 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _146_432)))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(
# 722 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.subst_comp subst c_expected)
in if (FStar_Syntax_Util.is_total_comp c) then begin
(
# 725 "FStar.TypeChecker.Tc.fst"
let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 728 "FStar.TypeChecker.Tc.fst"
let _57_1184 = (check_binders env more_bs bs_expected)
in (match (_57_1184) with
| (env, bs', more, guard', subst) -> begin
(let _146_434 = (let _146_433 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _146_433, subst))
in (handle_more _146_434 c_expected))
end))
end
| _57_1186 -> begin
(let _146_436 = (let _146_435 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _146_435))
in (fail _146_436 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _146_437 = (check_binders env bs bs_expected)
in (handle_more _146_437 c_expected))))
in (
# 735 "FStar.TypeChecker.Tc.fst"
let mk_letrec_env = (fun envbody bs c -> (
# 736 "FStar.TypeChecker.Tc.fst"
let letrecs = (guard_letrecs envbody bs c)
in (
# 737 "FStar.TypeChecker.Tc.fst"
let envbody = (
# 737 "FStar.TypeChecker.Tc.fst"
let _57_1192 = envbody
in {FStar_TypeChecker_Env.solver = _57_1192.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1192.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1192.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1192.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1192.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1192.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1192.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1192.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1192.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1192.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1192.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1192.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_1192.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1192.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1192.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1192.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1192.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1192.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1192.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1192.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _57_1197 _57_1200 -> (match ((_57_1197, _57_1200)) with
| ((env, letrec_binders), (l, t)) -> begin
(
# 741 "FStar.TypeChecker.Tc.fst"
let _57_1206 = (let _146_447 = (let _146_446 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_446 Prims.fst))
in (tc_term _146_447 t))
in (match (_57_1206) with
| (t, _57_1203, _57_1205) -> begin
(
# 742 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (
# 743 "FStar.TypeChecker.Tc.fst"
let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _146_448 = (FStar_Syntax_Syntax.mk_binder (
# 744 "FStar.TypeChecker.Tc.fst"
let _57_1210 = x
in {FStar_Syntax_Syntax.ppname = _57_1210.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1210.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_146_448)::letrec_binders)
end
| _57_1213 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (
# 749 "FStar.TypeChecker.Tc.fst"
let _57_1219 = (check_actuals_against_formals env bs bs_expected)
in (match (_57_1219) with
| (envbody, bs, g, c) -> begin
(
# 750 "FStar.TypeChecker.Tc.fst"
let _57_1222 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_57_1222) with
| (envbody, letrecs) -> begin
(
# 751 "FStar.TypeChecker.Tc.fst"
let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, body, g))
end))
end))))
end))
end
| _57_1225 -> begin
if (not (norm)) then begin
(let _146_449 = (unfold_whnf env t)
in (as_function_typ true _146_449))
end else begin
(
# 759 "FStar.TypeChecker.Tc.fst"
let _57_1235 = (expected_function_typ env None body)
in (match (_57_1235) with
| (_57_1227, bs, _57_1230, c_opt, envbody, body, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, body, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (
# 763 "FStar.TypeChecker.Tc.fst"
let use_eq = env.FStar_TypeChecker_Env.use_eq
in (
# 764 "FStar.TypeChecker.Tc.fst"
let _57_1239 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1239) with
| (env, topt) -> begin
(
# 766 "FStar.TypeChecker.Tc.fst"
let _57_1243 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_450 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _146_450 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (
# 771 "FStar.TypeChecker.Tc.fst"
let _57_1252 = (expected_function_typ env topt body)
in (match (_57_1252) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(
# 772 "FStar.TypeChecker.Tc.fst"
let _57_1258 = (tc_term (
# 772 "FStar.TypeChecker.Tc.fst"
let _57_1253 = envbody
in {FStar_TypeChecker_Env.solver = _57_1253.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1253.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1253.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1253.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1253.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1253.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1253.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1253.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1253.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1253.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1253.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1253.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1253.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1253.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1253.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1253.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1253.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1253.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1253.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_57_1258) with
| (body, cbody, guard_body) -> begin
(
# 774 "FStar.TypeChecker.Tc.fst"
let _57_1259 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_454 = (FStar_Syntax_Print.term_to_string body)
in (let _146_453 = (let _146_451 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _146_451))
in (let _146_452 = (FStar_TypeChecker_Rel.guard_to_string env guard_body)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _146_454 _146_453 _146_452))))
end else begin
()
end
in (
# 780 "FStar.TypeChecker.Tc.fst"
let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (
# 783 "FStar.TypeChecker.Tc.fst"
let _57_1262 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _146_457 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _146_456 = (let _146_455 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _146_455))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _146_457 _146_456)))
end else begin
()
end
in (
# 788 "FStar.TypeChecker.Tc.fst"
let _57_1269 = (let _146_459 = (let _146_458 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _146_458))
in (check_expected_effect (
# 788 "FStar.TypeChecker.Tc.fst"
let _57_1264 = envbody
in {FStar_TypeChecker_Env.solver = _57_1264.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1264.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1264.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1264.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1264.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1264.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1264.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1264.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1264.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1264.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1264.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1264.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1264.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1264.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1264.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1264.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1264.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1264.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1264.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1264.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _146_459))
in (match (_57_1269) with
| (body, cbody, guard) -> begin
(
# 789 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (
# 790 "FStar.TypeChecker.Tc.fst"
let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _146_460 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _146_460))
end else begin
(
# 792 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (
# 795 "FStar.TypeChecker.Tc.fst"
let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (
# 796 "FStar.TypeChecker.Tc.fst"
let e = (let _146_463 = (let _146_462 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _146_461 -> FStar_Util.Inl (_146_461)))
in Some (_146_462))
in (FStar_Syntax_Util.abs bs body _146_463))
in (
# 797 "FStar.TypeChecker.Tc.fst"
let _57_1292 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(
# 799 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_1281) -> begin
(e, t, guard)
end
| _57_1284 -> begin
(
# 806 "FStar.TypeChecker.Tc.fst"
let _57_1287 = if use_teq then begin
(let _146_464 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _146_464))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_57_1287) with
| (e, guard') -> begin
(let _146_465 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _146_465))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_57_1292) with
| (e, tfun, guard) -> begin
(
# 815 "FStar.TypeChecker.Tc.fst"
let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (
# 816 "FStar.TypeChecker.Tc.fst"
let _57_1296 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_57_1296) with
| (c, g) -> begin
(e, c, g)
end)))
end))))))
end)))))
end))
end)))
end)))))))
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead ghead args expected_topt -> (
# 824 "FStar.TypeChecker.Tc.fst"
let n_args = (FStar_List.length args)
in (
# 825 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 826 "FStar.TypeChecker.Tc.fst"
let thead = chead.FStar_Syntax_Syntax.res_typ
in (
# 827 "FStar.TypeChecker.Tc.fst"
let _57_1306 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_474 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _146_473 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _146_474 _146_473)))
end else begin
()
end
in (
# 828 "FStar.TypeChecker.Tc.fst"
let rec check_function_app = (fun norm tf -> (match ((let _146_479 = (FStar_Syntax_Util.unrefine tf)
in _146_479.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 832 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| (e, imp)::tl -> begin
(
# 835 "FStar.TypeChecker.Tc.fst"
let _57_1340 = (tc_term env e)
in (match (_57_1340) with
| (e, c, g_e) -> begin
(
# 836 "FStar.TypeChecker.Tc.fst"
let _57_1344 = (tc_args env tl)
in (match (_57_1344) with
| (args, comps, g_rest) -> begin
(let _146_484 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, (c)::comps, _146_484))
end))
end))
end))
in (
# 844 "FStar.TypeChecker.Tc.fst"
let _57_1348 = (tc_args env args)
in (match (_57_1348) with
| (args, comps, g_args) -> begin
(
# 845 "FStar.TypeChecker.Tc.fst"
let bs = (let _146_486 = (FStar_All.pipe_right comps (FStar_List.map (fun c -> (c.FStar_Syntax_Syntax.res_typ, None))))
in (FStar_Syntax_Util.null_binders_of_tks _146_486))
in (
# 846 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _57_1355 -> begin
FStar_Syntax_Util.ml_comp
end)
in (
# 849 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _146_501 = (FStar_Syntax_Subst.compress t)
in _146_501.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_1361) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _57_1366 -> begin
ml_or_tot
end)
end)
in (
# 856 "FStar.TypeChecker.Tc.fst"
let cres = (let _146_506 = (let _146_505 = (let _146_504 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_504 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _146_505))
in (ml_or_tot _146_506 r))
in (
# 857 "FStar.TypeChecker.Tc.fst"
let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (
# 858 "FStar.TypeChecker.Tc.fst"
let _57_1370 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_509 = (FStar_Syntax_Print.term_to_string head)
in (let _146_508 = (FStar_Syntax_Print.term_to_string tf)
in (let _146_507 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _146_509 _146_508 _146_507))))
end else begin
()
end
in (
# 863 "FStar.TypeChecker.Tc.fst"
let _57_1372 = (let _146_510 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _146_510))
in (
# 864 "FStar.TypeChecker.Tc.fst"
let comp = (let _146_513 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_TypeChecker_Util.bind env None c (None, out))) ((chead)::comps) _146_513))
in (let _146_515 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _146_514 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_146_515, comp, _146_514)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 868 "FStar.TypeChecker.Tc.fst"
let _57_1383 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_1383) with
| (bs, c) -> begin
(
# 870 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun _57_1391 bs cres args -> (match (_57_1391) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (_57_1398)))::rest, (_57_1406, None)::_57_1404) -> begin
(
# 881 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 882 "FStar.TypeChecker.Tc.fst"
let _57_1412 = (check_no_escape (Some (head)) env fvs t)
in (
# 883 "FStar.TypeChecker.Tc.fst"
let _57_1418 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_57_1418) with
| (varg, _57_1416, implicits) -> begin
(
# 884 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (
# 885 "FStar.TypeChecker.Tc.fst"
let arg = (let _146_524 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _146_524))
in (let _146_526 = (let _146_525 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _146_525, fvs))
in (tc_args _146_526 rest cres args))))
end))))
end
| ((x, aqual)::rest, (e, aq)::rest') -> begin
(
# 889 "FStar.TypeChecker.Tc.fst"
let _57_1450 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _57_1449 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (
# 894 "FStar.TypeChecker.Tc.fst"
let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 895 "FStar.TypeChecker.Tc.fst"
let x = (
# 895 "FStar.TypeChecker.Tc.fst"
let _57_1453 = x
in {FStar_Syntax_Syntax.ppname = _57_1453.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1453.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (
# 896 "FStar.TypeChecker.Tc.fst"
let _57_1456 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_527 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _146_527))
end else begin
()
end
in (
# 897 "FStar.TypeChecker.Tc.fst"
let _57_1458 = (check_no_escape (Some (head)) env fvs targ)
in (
# 898 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (
# 899 "FStar.TypeChecker.Tc.fst"
let env = (
# 899 "FStar.TypeChecker.Tc.fst"
let _57_1461 = env
in {FStar_TypeChecker_Env.solver = _57_1461.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1461.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1461.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1461.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1461.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1461.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1461.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1461.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1461.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1461.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1461.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1461.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1461.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1461.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1461.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _57_1461.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1461.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1461.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1461.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1461.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 900 "FStar.TypeChecker.Tc.fst"
let _57_1464 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_530 = (FStar_Syntax_Print.tag_of_term e)
in (let _146_529 = (FStar_Syntax_Print.term_to_string e)
in (let _146_528 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _146_530 _146_529 _146_528))))
end else begin
()
end
in (
# 901 "FStar.TypeChecker.Tc.fst"
let _57_1469 = (tc_term env e)
in (match (_57_1469) with
| (e, c, g_e) -> begin
(
# 902 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (
# 904 "FStar.TypeChecker.Tc.fst"
let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(
# 906 "FStar.TypeChecker.Tc.fst"
let subst = (let _146_531 = (FStar_List.hd bs)
in (maybe_extend_subst subst _146_531 e))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(
# 909 "FStar.TypeChecker.Tc.fst"
let subst = (let _146_532 = (FStar_List.hd bs)
in (maybe_extend_subst subst _146_532 e))
in (
# 910 "FStar.TypeChecker.Tc.fst"
let _57_1476 = (((Some (x), c))::comps, g)
in (match (_57_1476) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _146_533 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _146_533)) then begin
(
# 914 "FStar.TypeChecker.Tc.fst"
let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (
# 915 "FStar.TypeChecker.Tc.fst"
let arg' = (let _146_534 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _146_534))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (newx), c))::comps, g, fvs) rest cres rest')))
end else begin
(let _146_538 = (let _146_537 = (let _146_536 = (let _146_535 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _146_535))
in (_146_536)::arg_rets)
in (subst, (arg)::outargs, _146_537, ((Some (x), c))::comps, g, (x)::fvs))
in (tc_args _146_538 rest cres rest'))
end
end
end))
end))))))))))
end
| (_57_1480, []) -> begin
(
# 924 "FStar.TypeChecker.Tc.fst"
let _57_1483 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (
# 925 "FStar.TypeChecker.Tc.fst"
let _57_1501 = (match (bs) with
| [] -> begin
(
# 928 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (
# 934 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (
# 936 "FStar.TypeChecker.Tc.fst"
let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _57_1491 -> (match (_57_1491) with
| (_57_1489, c) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (
# 943 "FStar.TypeChecker.Tc.fst"
let cres = if refine_with_equality then begin
(let _146_540 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _146_540 cres))
end else begin
(
# 949 "FStar.TypeChecker.Tc.fst"
let _57_1493 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_543 = (FStar_Syntax_Print.term_to_string head)
in (let _146_542 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _146_541 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _146_543 _146_542 _146_541))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _57_1497 -> begin
(
# 958 "FStar.TypeChecker.Tc.fst"
let g = (let _146_544 = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (FStar_All.pipe_right _146_544 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _146_549 = (let _146_548 = (let _146_547 = (let _146_546 = (let _146_545 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _146_545))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _146_546))
in (FStar_Syntax_Syntax.mk_Total _146_547))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_548))
in (_146_549, g)))
end)
in (match (_57_1501) with
| (cres, g) -> begin
(
# 961 "FStar.TypeChecker.Tc.fst"
let _57_1502 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_550 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _146_550))
end else begin
()
end
in (
# 962 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_List.fold_left (fun out c -> (FStar_TypeChecker_Util.bind env None (Prims.snd c) ((Prims.fst c), out))) cres comps)
in (
# 963 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.bind env None chead (None, comp))
in (
# 964 "FStar.TypeChecker.Tc.fst"
let app = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev outargs) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (
# 965 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.record_application_site env app comp)
in (
# 966 "FStar.TypeChecker.Tc.fst"
let _57_1512 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp g)
in (match (_57_1512) with
| (comp, g) -> begin
(
# 967 "FStar.TypeChecker.Tc.fst"
let _57_1513 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_556 = (FStar_TypeChecker_Normalize.term_to_string env app)
in (let _146_555 = (let _146_554 = (comp.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Print.comp_to_string _146_554))
in (FStar_Util.print2 "\t Type of app term %s is %s\n" _146_556 _146_555)))
end else begin
()
end
in (app, comp, g))
end)))))))
end)))
end
| ([], arg::_57_1517) -> begin
(
# 973 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun norm tres -> (
# 974 "FStar.TypeChecker.Tc.fst"
let tres = (let _146_561 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _146_561 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(
# 977 "FStar.TypeChecker.Tc.fst"
let _57_1529 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_562 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _146_562))
end else begin
()
end
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs (FStar_Syntax_Util.lcomp_of_comp cres') args))
end
| _57_1532 when (not (norm)) -> begin
(let _146_563 = (unfold_whnf env tres)
in (aux true _146_563))
end
| _57_1534 -> begin
(let _146_569 = (let _146_568 = (let _146_567 = (let _146_565 = (FStar_TypeChecker_Normalize.term_to_string env tf)
in (let _146_564 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _146_565 _146_564)))
in (let _146_566 = (FStar_Syntax_Syntax.argpos arg)
in (_146_567, _146_566)))
in FStar_Syntax_Syntax.Error (_146_568))
in (Prims.raise _146_569))
end)))
in (aux false cres.FStar_Syntax_Syntax.res_typ))
end)
end))
in (tc_args ([], [], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs (FStar_Syntax_Util.lcomp_of_comp c) args))
end))
end
| _57_1536 -> begin
if (not (norm)) then begin
(let _146_570 = (unfold_whnf env tf)
in (check_function_app true _146_570))
end else begin
(let _146_573 = (let _146_572 = (let _146_571 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_146_571, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_572))
in (Prims.raise _146_573))
end
end))
in (let _146_575 = (let _146_574 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _146_574))
in (check_function_app false _146_575))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (
# 1003 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1004 "FStar.TypeChecker.Tc.fst"
let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(
# 1007 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in (
# 1008 "FStar.TypeChecker.Tc.fst"
let _57_1572 = (FStar_List.fold_left2 (fun _57_1553 _57_1556 _57_1559 -> (match ((_57_1553, _57_1556, _57_1559)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(
# 1009 "FStar.TypeChecker.Tc.fst"
let _57_1560 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1010 "FStar.TypeChecker.Tc.fst"
let _57_1565 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_57_1565) with
| (e, c, g) -> begin
(
# 1011 "FStar.TypeChecker.Tc.fst"
let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (
# 1012 "FStar.TypeChecker.Tc.fst"
let g = (let _146_585 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _146_585 g))
in (
# 1013 "FStar.TypeChecker.Tc.fst"
let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _146_589 = (let _146_587 = (let _146_586 = (FStar_Syntax_Syntax.as_arg e)
in (_146_586)::[])
in (FStar_List.append seen _146_587))
in (let _146_588 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_146_589, _146_588, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_57_1572) with
| (args, guard, ghost) -> begin
(
# 1017 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (
# 1018 "FStar.TypeChecker.Tc.fst"
let c = if ghost then begin
(let _146_590 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _146_590 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (
# 1019 "FStar.TypeChecker.Tc.fst"
let _57_1577 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_57_1577) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _57_1579 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (
# 1039 "FStar.TypeChecker.Tc.fst"
let _57_1586 = (FStar_Syntax_Subst.open_branch branch)
in (match (_57_1586) with
| (pattern, when_clause, branch_exp) -> begin
(
# 1040 "FStar.TypeChecker.Tc.fst"
let _57_1591 = branch
in (match (_57_1591) with
| (cpat, _57_1589, cbr) -> begin
(
# 1043 "FStar.TypeChecker.Tc.fst"
let tc_pat = (fun allow_implicits pat_t p0 -> (
# 1050 "FStar.TypeChecker.Tc.fst"
let _57_1599 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_57_1599) with
| (pat_bvs, exps, p) -> begin
(
# 1051 "FStar.TypeChecker.Tc.fst"
let _57_1600 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_602 = (FStar_Syntax_Print.pat_to_string p0)
in (let _146_601 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _146_602 _146_601)))
end else begin
()
end
in (
# 1053 "FStar.TypeChecker.Tc.fst"
let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (
# 1054 "FStar.TypeChecker.Tc.fst"
let _57_1606 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_57_1606) with
| (env1, _57_1605) -> begin
(
# 1055 "FStar.TypeChecker.Tc.fst"
let env1 = (
# 1055 "FStar.TypeChecker.Tc.fst"
let _57_1607 = env1
in {FStar_TypeChecker_Env.solver = _57_1607.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1607.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1607.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1607.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1607.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1607.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1607.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1607.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _57_1607.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1607.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1607.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1607.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1607.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1607.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1607.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1607.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1607.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1607.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1607.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1607.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1056 "FStar.TypeChecker.Tc.fst"
let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (
# 1057 "FStar.TypeChecker.Tc.fst"
let _57_1646 = (let _146_625 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (
# 1058 "FStar.TypeChecker.Tc.fst"
let _57_1612 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_605 = (FStar_Syntax_Print.term_to_string e)
in (let _146_604 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _146_605 _146_604)))
end else begin
()
end
in (
# 1061 "FStar.TypeChecker.Tc.fst"
let _57_1617 = (tc_term env1 e)
in (match (_57_1617) with
| (e, lc, g) -> begin
(
# 1063 "FStar.TypeChecker.Tc.fst"
let _57_1618 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_607 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _146_606 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _146_607 _146_606)))
end else begin
()
end
in (
# 1066 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (
# 1067 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (
# 1068 "FStar.TypeChecker.Tc.fst"
let _57_1624 = (let _146_608 = (FStar_TypeChecker_Rel.discharge_guard env (
# 1068 "FStar.TypeChecker.Tc.fst"
let _57_1622 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_1622.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_1622.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_1622.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _146_608 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1069 "FStar.TypeChecker.Tc.fst"
let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (
# 1070 "FStar.TypeChecker.Tc.fst"
let uvars_to_string = (fun uvs -> (let _146_613 = (let _146_612 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _146_612 (FStar_List.map (fun _57_1632 -> (match (_57_1632) with
| (u, _57_1631) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _146_613 (FStar_String.concat ", "))))
in (
# 1071 "FStar.TypeChecker.Tc.fst"
let uvs1 = (FStar_Syntax_Free.uvars e')
in (
# 1072 "FStar.TypeChecker.Tc.fst"
let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (
# 1073 "FStar.TypeChecker.Tc.fst"
let _57_1640 = if (let _146_614 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _146_614)) then begin
(
# 1074 "FStar.TypeChecker.Tc.fst"
let unresolved = (let _146_615 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _146_615 FStar_Util.set_elements))
in (let _146_623 = (let _146_622 = (let _146_621 = (let _146_620 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _146_619 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _146_618 = (let _146_617 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _57_1639 -> (match (_57_1639) with
| (u, _57_1638) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _146_617 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _146_620 _146_619 _146_618))))
in (_146_621, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_146_622))
in (Prims.raise _146_623)))
end else begin
()
end
in (
# 1081 "FStar.TypeChecker.Tc.fst"
let _57_1642 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_624 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _146_624))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _146_625 FStar_List.unzip))
in (match (_57_1646) with
| (exps, norm_exps) -> begin
(
# 1086 "FStar.TypeChecker.Tc.fst"
let p = (FStar_TypeChecker_Util.decorate_pattern env p exps)
in (p, pat_bvs, pat_env, exps, norm_exps))
end))))
end))))
end)))
in (
# 1090 "FStar.TypeChecker.Tc.fst"
let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (
# 1091 "FStar.TypeChecker.Tc.fst"
let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (
# 1092 "FStar.TypeChecker.Tc.fst"
let _57_1653 = (let _146_626 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _146_626 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_57_1653) with
| (scrutinee_env, _57_1652) -> begin
(
# 1095 "FStar.TypeChecker.Tc.fst"
let _57_1659 = (tc_pat true pat_t pattern)
in (match (_57_1659) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(
# 1098 "FStar.TypeChecker.Tc.fst"
let _57_1669 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(
# 1105 "FStar.TypeChecker.Tc.fst"
let _57_1666 = (let _146_627 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _146_627 e))
in (match (_57_1666) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_57_1669) with
| (when_clause, g_when) -> begin
(
# 1109 "FStar.TypeChecker.Tc.fst"
let _57_1673 = (tc_term pat_env branch_exp)
in (match (_57_1673) with
| (branch_exp, c, g_branch) -> begin
(
# 1113 "FStar.TypeChecker.Tc.fst"
let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _146_629 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _146_628 -> Some (_146_628)) _146_629))
end)
in (
# 1120 "FStar.TypeChecker.Tc.fst"
let _57_1729 = (
# 1123 "FStar.TypeChecker.Tc.fst"
let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (
# 1124 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _57_1691 -> begin
(
# 1130 "FStar.TypeChecker.Tc.fst"
let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _146_633 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _146_632 -> Some (_146_632)) _146_633))
end))
end))) None))
in (
# 1135 "FStar.TypeChecker.Tc.fst"
let _57_1699 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_57_1699) with
| (c, g_branch) -> begin
(
# 1139 "FStar.TypeChecker.Tc.fst"
let _57_1724 = (match ((eqs, when_condition)) with
| (None, None) -> begin
(c, g_when)
end
| (Some (f), None) -> begin
(
# 1145 "FStar.TypeChecker.Tc.fst"
let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1146 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _146_636 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _146_635 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_146_636, _146_635)))))
end
| (Some (f), Some (w)) -> begin
(
# 1151 "FStar.TypeChecker.Tc.fst"
let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1152 "FStar.TypeChecker.Tc.fst"
let g_fw = (let _146_637 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_146_637))
in (let _146_640 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _146_639 = (let _146_638 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _146_638 g_when))
in (_146_640, _146_639)))))
end
| (None, Some (w)) -> begin
(
# 1157 "FStar.TypeChecker.Tc.fst"
let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (
# 1158 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _146_641 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_146_641, g_when))))
end)
in (match (_57_1724) with
| (c_weak, g_when_weak) -> begin
(
# 1163 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _146_643 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _146_642 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_146_643, _146_642, g_branch))))
end))
end)))
in (match (_57_1729) with
| (c, g_when, g_branch) -> begin
(
# 1181 "FStar.TypeChecker.Tc.fst"
let branch_guard = (
# 1183 "FStar.TypeChecker.Tc.fst"
let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (
# 1184 "FStar.TypeChecker.Tc.fst"
let discriminate = (fun scrutinee_tm f -> if ((let _146_653 = (let _146_652 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _146_652))
in (FStar_List.length _146_653)) > 1) then begin
(
# 1187 "FStar.TypeChecker.Tc.fst"
let disc = (let _146_654 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _146_654 FStar_Syntax_Syntax.Delta_equational None))
in (
# 1188 "FStar.TypeChecker.Tc.fst"
let disc = (let _146_656 = (let _146_655 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_146_655)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _146_656 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _146_657 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_146_657)::[])))
end else begin
[]
end)
in (
# 1192 "FStar.TypeChecker.Tc.fst"
let fail = (fun _57_1739 -> (match (()) with
| () -> begin
(let _146_663 = (let _146_662 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _146_661 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _146_660 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _146_662 _146_661 _146_660))))
in (FStar_All.failwith _146_663))
end))
in (
# 1198 "FStar.TypeChecker.Tc.fst"
let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _57_1746) -> begin
(head_constructor t)
end
| _57_1750 -> begin
(fail ())
end))
in (
# 1203 "FStar.TypeChecker.Tc.fst"
let pat_exp = (let _146_666 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _146_666 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_57_1775) -> begin
(let _146_671 = (let _146_670 = (let _146_669 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _146_668 = (let _146_667 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_146_667)::[])
in (_146_669)::_146_668))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _146_670 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_146_671)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 1212 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _146_672 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _146_672))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 1217 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(
# 1220 "FStar.TypeChecker.Tc.fst"
let sub_term_guards = (let _146_679 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _57_1793 -> (match (_57_1793) with
| (ei, _57_1792) -> begin
(
# 1221 "FStar.TypeChecker.Tc.fst"
let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _57_1797 -> begin
(
# 1225 "FStar.TypeChecker.Tc.fst"
let sub_term = (let _146_678 = (let _146_675 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _146_675 FStar_Syntax_Syntax.Delta_equational None))
in (let _146_677 = (let _146_676 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_146_676)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _146_678 _146_677 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _146_679 FStar_List.flatten))
in (let _146_680 = (discriminate scrutinee_tm f)
in (FStar_List.append _146_680 sub_term_guards)))
end)
end
| _57_1801 -> begin
[]
end))))))
in (
# 1231 "FStar.TypeChecker.Tc.fst"
let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(
# 1234 "FStar.TypeChecker.Tc.fst"
let t = (let _146_685 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _146_685))
in (
# 1235 "FStar.TypeChecker.Tc.fst"
let _57_1809 = (FStar_Syntax_Util.type_u ())
in (match (_57_1809) with
| (k, _57_1808) -> begin
(
# 1236 "FStar.TypeChecker.Tc.fst"
let _57_1815 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_57_1815) with
| (t, _57_1812, _57_1814) -> begin
t
end))
end)))
end)
in (
# 1240 "FStar.TypeChecker.Tc.fst"
let branch_guard = (let _146_686 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _146_686 FStar_Syntax_Util.mk_disj_l))
in (
# 1243 "FStar.TypeChecker.Tc.fst"
let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
in (
# 1249 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (
# 1251 "FStar.TypeChecker.Tc.fst"
let _57_1823 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_687 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _146_687))
end else begin
()
end
in (let _146_688 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_146_688, branch_guard, c, guard)))))
end)))
end))
end))
end))
end)))))
end))
end)))
and check_top_level_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1265 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1268 "FStar.TypeChecker.Tc.fst"
let _57_1840 = (check_let_bound_def true env lb)
in (match (_57_1840) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(
# 1270 "FStar.TypeChecker.Tc.fst"
let _57_1852 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(
# 1273 "FStar.TypeChecker.Tc.fst"
let g1 = (let _146_691 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _146_691 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1274 "FStar.TypeChecker.Tc.fst"
let _57_1847 = (let _146_695 = (let _146_694 = (let _146_693 = (let _146_692 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _146_692))
in (_146_693)::[])
in (FStar_TypeChecker_Util.generalize env _146_694))
in (FStar_List.hd _146_695))
in (match (_57_1847) with
| (_57_1843, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_57_1852) with
| (g1, e1, univ_vars, c1) -> begin
(
# 1278 "FStar.TypeChecker.Tc.fst"
let _57_1862 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(
# 1280 "FStar.TypeChecker.Tc.fst"
let _57_1855 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_57_1855) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(
# 1283 "FStar.TypeChecker.Tc.fst"
let _57_1856 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _146_696 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _146_696 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _146_697 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_146_697, c1)))
end
end))
end else begin
(
# 1287 "FStar.TypeChecker.Tc.fst"
let _57_1858 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _146_698 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _146_698)))
end
in (match (_57_1862) with
| (e2, c1) -> begin
(
# 1292 "FStar.TypeChecker.Tc.fst"
let cres = (let _146_699 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_699))
in (
# 1293 "FStar.TypeChecker.Tc.fst"
let _57_1864 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1295 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _146_700 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_146_700, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _57_1868 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1312 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1315 "FStar.TypeChecker.Tc.fst"
let env = (
# 1315 "FStar.TypeChecker.Tc.fst"
let _57_1879 = env
in {FStar_TypeChecker_Env.solver = _57_1879.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1879.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1879.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1879.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1879.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1879.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1879.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1879.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1879.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1879.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1879.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1879.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1879.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1879.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1879.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1879.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1879.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1879.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1879.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1879.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1316 "FStar.TypeChecker.Tc.fst"
let _57_1888 = (let _146_704 = (let _146_703 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_703 Prims.fst))
in (check_let_bound_def false _146_704 lb))
in (match (_57_1888) with
| (e1, _57_1884, c1, g1, annotated) -> begin
(
# 1317 "FStar.TypeChecker.Tc.fst"
let x = (
# 1317 "FStar.TypeChecker.Tc.fst"
let _57_1889 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1889.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1889.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (
# 1318 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (
# 1319 "FStar.TypeChecker.Tc.fst"
let _57_1895 = (let _146_706 = (let _146_705 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_705)::[])
in (FStar_Syntax_Subst.open_term _146_706 e2))
in (match (_57_1895) with
| (xb, e2) -> begin
(
# 1320 "FStar.TypeChecker.Tc.fst"
let xbinder = (FStar_List.hd xb)
in (
# 1321 "FStar.TypeChecker.Tc.fst"
let x = (Prims.fst xbinder)
in (
# 1322 "FStar.TypeChecker.Tc.fst"
let _57_1901 = (let _146_707 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _146_707 e2))
in (match (_57_1901) with
| (e2, c2, g2) -> begin
(
# 1323 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (x), c2))
in (
# 1324 "FStar.TypeChecker.Tc.fst"
let e = (let _146_710 = (let _146_709 = (let _146_708 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _146_708))
in FStar_Syntax_Syntax.Tm_let (_146_709))
in (FStar_Syntax_Syntax.mk _146_710 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 1325 "FStar.TypeChecker.Tc.fst"
let x_eq_e1 = (let _146_713 = (let _146_712 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _146_712 e1))
in (FStar_All.pipe_left (fun _146_711 -> FStar_TypeChecker_Common.NonTrivial (_146_711)) _146_713))
in (
# 1326 "FStar.TypeChecker.Tc.fst"
let g2 = (let _146_715 = (let _146_714 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _146_714 g2))
in (FStar_TypeChecker_Rel.close_guard xb _146_715))
in (
# 1328 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if annotated then begin
(e, cres, guard)
end else begin
(
# 1332 "FStar.TypeChecker.Tc.fst"
let _57_1907 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end)))))
end))))
end))))
end)))
end
| _57_1910 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1341 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1344 "FStar.TypeChecker.Tc.fst"
let _57_1922 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1922) with
| (lbs, e2) -> begin
(
# 1346 "FStar.TypeChecker.Tc.fst"
let _57_1925 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1925) with
| (env0, topt) -> begin
(
# 1347 "FStar.TypeChecker.Tc.fst"
let _57_1928 = (build_let_rec_env true env0 lbs)
in (match (_57_1928) with
| (lbs, rec_env) -> begin
(
# 1348 "FStar.TypeChecker.Tc.fst"
let _57_1931 = (check_let_recs rec_env lbs)
in (match (_57_1931) with
| (lbs, g_lbs) -> begin
(
# 1349 "FStar.TypeChecker.Tc.fst"
let g_lbs = (let _146_718 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _146_718 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1351 "FStar.TypeChecker.Tc.fst"
let all_lb_names = (let _146_721 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _146_721 (fun _146_720 -> Some (_146_720))))
in (
# 1353 "FStar.TypeChecker.Tc.fst"
let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(
# 1359 "FStar.TypeChecker.Tc.fst"
let ecs = (let _146_725 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _146_724 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _146_724)))))
in (FStar_TypeChecker_Util.generalize env _146_725))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _57_1942 -> (match (_57_1942) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (
# 1366 "FStar.TypeChecker.Tc.fst"
let cres = (let _146_727 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_727))
in (
# 1367 "FStar.TypeChecker.Tc.fst"
let _57_1945 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1369 "FStar.TypeChecker.Tc.fst"
let _57_1949 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1949) with
| (lbs, e2) -> begin
(let _146_729 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_728 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_146_729, cres, _146_728)))
end)))))))
end))
end))
end))
end))
end
| _57_1951 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1380 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1383 "FStar.TypeChecker.Tc.fst"
let _57_1963 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1963) with
| (lbs, e2) -> begin
(
# 1385 "FStar.TypeChecker.Tc.fst"
let _57_1966 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1966) with
| (env0, topt) -> begin
(
# 1386 "FStar.TypeChecker.Tc.fst"
let _57_1969 = (build_let_rec_env false env0 lbs)
in (match (_57_1969) with
| (lbs, rec_env) -> begin
(
# 1387 "FStar.TypeChecker.Tc.fst"
let _57_1972 = (check_let_recs rec_env lbs)
in (match (_57_1972) with
| (lbs, g_lbs) -> begin
(
# 1389 "FStar.TypeChecker.Tc.fst"
let _57_1984 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (
# 1390 "FStar.TypeChecker.Tc.fst"
let x = (
# 1390 "FStar.TypeChecker.Tc.fst"
let _57_1975 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1975.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1975.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (
# 1391 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1391 "FStar.TypeChecker.Tc.fst"
let _57_1978 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _57_1978.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1978.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1978.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _57_1978.FStar_Syntax_Syntax.lbdef})
in (
# 1392 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], lb.FStar_Syntax_Syntax.lbtyp))
in (env, lb))))) env))
in (match (_57_1984) with
| (env, lbs) -> begin
(
# 1395 "FStar.TypeChecker.Tc.fst"
let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (
# 1397 "FStar.TypeChecker.Tc.fst"
let _57_1990 = (tc_term env e2)
in (match (_57_1990) with
| (e2, cres, g2) -> begin
(
# 1398 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (
# 1399 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (
# 1400 "FStar.TypeChecker.Tc.fst"
let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (
# 1401 "FStar.TypeChecker.Tc.fst"
let cres = (
# 1401 "FStar.TypeChecker.Tc.fst"
let _57_1994 = cres
in {FStar_Syntax_Syntax.eff_name = _57_1994.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _57_1994.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_1994.FStar_Syntax_Syntax.comp})
in (
# 1403 "FStar.TypeChecker.Tc.fst"
let _57_1999 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1999) with
| (lbs, e2) -> begin
(
# 1404 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_57_2002) -> begin
(e, cres, guard)
end
| None -> begin
(
# 1408 "FStar.TypeChecker.Tc.fst"
let _57_2005 = (check_no_escape None env bvs tres)
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
| _57_2008 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (
# 1419 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1420 "FStar.TypeChecker.Tc.fst"
let _57_2041 = (FStar_List.fold_left (fun _57_2015 lb -> (match (_57_2015) with
| (lbs, env) -> begin
(
# 1421 "FStar.TypeChecker.Tc.fst"
let _57_2020 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_57_2020) with
| (univ_vars, t, check_t) -> begin
(
# 1422 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (
# 1423 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (
# 1424 "FStar.TypeChecker.Tc.fst"
let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(
# 1429 "FStar.TypeChecker.Tc.fst"
let _57_2029 = (let _146_741 = (let _146_740 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _146_740))
in (tc_check_tot_or_gtot_term (
# 1429 "FStar.TypeChecker.Tc.fst"
let _57_2023 = env0
in {FStar_TypeChecker_Env.solver = _57_2023.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2023.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2023.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2023.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2023.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2023.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2023.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2023.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2023.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2023.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2023.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2023.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2023.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2023.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _57_2023.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2023.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2023.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2023.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2023.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2023.FStar_TypeChecker_Env.use_bv_sorts}) t _146_741))
in (match (_57_2029) with
| (t, _57_2027, g) -> begin
(
# 1430 "FStar.TypeChecker.Tc.fst"
let _57_2030 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (
# 1432 "FStar.TypeChecker.Tc.fst"
let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(
# 1434 "FStar.TypeChecker.Tc.fst"
let _57_2033 = env
in {FStar_TypeChecker_Env.solver = _57_2033.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2033.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2033.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2033.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2033.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2033.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2033.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2033.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2033.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2033.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2033.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2033.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2033.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_2033.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2033.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2033.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2033.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2033.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2033.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2033.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (
# 1436 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1436 "FStar.TypeChecker.Tc.fst"
let _57_2036 = lb
in {FStar_Syntax_Syntax.lbname = _57_2036.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _57_2036.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_57_2041) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (
# 1443 "FStar.TypeChecker.Tc.fst"
let _57_2054 = (let _146_746 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 1444 "FStar.TypeChecker.Tc.fst"
let _57_2048 = (let _146_745 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _146_745 lb.FStar_Syntax_Syntax.lbdef))
in (match (_57_2048) with
| (e, c, g) -> begin
(
# 1445 "FStar.TypeChecker.Tc.fst"
let _57_2049 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1447 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _146_746 FStar_List.unzip))
in (match (_57_2054) with
| (lbs, gs) -> begin
(
# 1449 "FStar.TypeChecker.Tc.fst"
let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (
# 1463 "FStar.TypeChecker.Tc.fst"
let _57_2062 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_2062) with
| (env1, _57_2061) -> begin
(
# 1464 "FStar.TypeChecker.Tc.fst"
let e1 = lb.FStar_Syntax_Syntax.lbdef
in (
# 1467 "FStar.TypeChecker.Tc.fst"
let _57_2068 = (check_lbtyp top_level env lb)
in (match (_57_2068) with
| (topt, wf_annot, univ_vars, env1) -> begin
(
# 1469 "FStar.TypeChecker.Tc.fst"
let _57_2069 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1473 "FStar.TypeChecker.Tc.fst"
let _57_2076 = (tc_maybe_toplevel_term (
# 1473 "FStar.TypeChecker.Tc.fst"
let _57_2071 = env1
in {FStar_TypeChecker_Env.solver = _57_2071.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2071.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2071.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2071.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2071.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2071.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2071.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2071.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2071.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2071.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2071.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2071.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2071.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _57_2071.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2071.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2071.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2071.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2071.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2071.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2071.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_57_2076) with
| (e1, c1, g1) -> begin
(
# 1476 "FStar.TypeChecker.Tc.fst"
let _57_2080 = (let _146_753 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_2077 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _146_753 e1 c1 wf_annot))
in (match (_57_2080) with
| (c1, guard_f) -> begin
(
# 1479 "FStar.TypeChecker.Tc.fst"
let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (
# 1481 "FStar.TypeChecker.Tc.fst"
let _57_2082 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_754 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _146_754))
end else begin
()
end
in (let _146_755 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _146_755))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (
# 1493 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 1496 "FStar.TypeChecker.Tc.fst"
let _57_2089 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _57_2092 -> begin
(
# 1500 "FStar.TypeChecker.Tc.fst"
let _57_2095 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_57_2095) with
| (univ_vars, t) -> begin
(
# 1501 "FStar.TypeChecker.Tc.fst"
let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _146_759 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _146_759))
end else begin
(
# 1508 "FStar.TypeChecker.Tc.fst"
let _57_2100 = (FStar_Syntax_Util.type_u ())
in (match (_57_2100) with
| (k, _57_2099) -> begin
(
# 1509 "FStar.TypeChecker.Tc.fst"
let _57_2105 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_57_2105) with
| (t, _57_2103, g) -> begin
(
# 1510 "FStar.TypeChecker.Tc.fst"
let _57_2106 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _146_762 = (let _146_760 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _146_760))
in (let _146_761 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _146_762 _146_761)))
end else begin
()
end
in (
# 1514 "FStar.TypeChecker.Tc.fst"
let t = (norm env1 t)
in (let _146_763 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _146_763))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _57_2112 -> (match (_57_2112) with
| (x, imp) -> begin
(
# 1519 "FStar.TypeChecker.Tc.fst"
let _57_2115 = (FStar_Syntax_Util.type_u ())
in (match (_57_2115) with
| (tu, u) -> begin
(
# 1520 "FStar.TypeChecker.Tc.fst"
let _57_2120 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_57_2120) with
| (t, _57_2118, g) -> begin
(
# 1521 "FStar.TypeChecker.Tc.fst"
let x = ((
# 1521 "FStar.TypeChecker.Tc.fst"
let _57_2121 = x
in {FStar_Syntax_Syntax.ppname = _57_2121.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2121.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (
# 1522 "FStar.TypeChecker.Tc.fst"
let _57_2124 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_767 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _146_766 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _146_767 _146_766)))
end else begin
()
end
in (let _146_768 = (maybe_push_binding env x)
in (x, _146_768, g, u))))
end))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe Prims.list) = (fun env bs -> (
# 1527 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_TypeChecker_Rel.trivial_guard, [])
end
| b::bs -> begin
(
# 1530 "FStar.TypeChecker.Tc.fst"
let _57_2139 = (tc_binder env b)
in (match (_57_2139) with
| (b, env', g, u) -> begin
(
# 1531 "FStar.TypeChecker.Tc.fst"
let _57_2144 = (aux env' bs)
in (match (_57_2144) with
| (bs, env', g', us) -> begin
(let _146_776 = (let _146_775 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _146_775))
in ((b)::bs, env', _146_776, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (
# 1536 "FStar.TypeChecker.Tc.fst"
let tc_args = (fun env args -> (FStar_List.fold_right (fun _57_2152 _57_2155 -> (match ((_57_2152, _57_2155)) with
| ((t, imp), (args, g)) -> begin
(
# 1540 "FStar.TypeChecker.Tc.fst"
let _57_2160 = (tc_term env t)
in (match (_57_2160) with
| (t, _57_2158, g') -> begin
(let _146_785 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _146_785))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _57_2164 -> (match (_57_2164) with
| (pats, g) -> begin
(
# 1543 "FStar.TypeChecker.Tc.fst"
let _57_2167 = (tc_args env p)
in (match (_57_2167) with
| (args, g') -> begin
(let _146_788 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _146_788))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1548 "FStar.TypeChecker.Tc.fst"
let _57_2173 = (tc_maybe_toplevel_term env e)
in (match (_57_2173) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(
# 1551 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (
# 1552 "FStar.TypeChecker.Tc.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 1553 "FStar.TypeChecker.Tc.fst"
let _57_2176 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_791 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _146_791))
end else begin
()
end
in (
# 1554 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 1555 "FStar.TypeChecker.Tc.fst"
let _57_2181 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _146_792 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_146_792, false))
end else begin
(let _146_793 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_146_793, true))
end
in (match (_57_2181) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _146_794 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _146_794))
end
| _57_2185 -> begin
if allow_ghost then begin
(let _146_797 = (let _146_796 = (let _146_795 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_146_795, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_796))
in (Prims.raise _146_797))
end else begin
(let _146_800 = (let _146_799 = (let _146_798 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_146_798, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_799))
in (Prims.raise _146_800))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 1569 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))

# 1573 "FStar.TypeChecker.Tc.fst"
let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (
# 1574 "FStar.TypeChecker.Tc.fst"
let _57_2195 = (tc_tot_or_gtot_term env t)
in (match (_57_2195) with
| (t, c, g) -> begin
(
# 1575 "FStar.TypeChecker.Tc.fst"
let _57_2196 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))

# 1578 "FStar.TypeChecker.Tc.fst"
let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (
# 1579 "FStar.TypeChecker.Tc.fst"
let _57_2204 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_2204) with
| (t, c, g) -> begin
(
# 1580 "FStar.TypeChecker.Tc.fst"
let _57_2205 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))

# 1583 "FStar.TypeChecker.Tc.fst"
let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _146_820 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _146_820)))

# 1588 "FStar.TypeChecker.Tc.fst"
let check_nogen = (fun env t k -> (
# 1589 "FStar.TypeChecker.Tc.fst"
let t = (tc_check_trivial_guard env t k)
in (let _146_824 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _146_824))))

# 1592 "FStar.TypeChecker.Tc.fst"
let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (
# 1593 "FStar.TypeChecker.Tc.fst"
let _57_2220 = (tc_binders env tps)
in (match (_57_2220) with
| (tps, env, g, us) -> begin
(
# 1594 "FStar.TypeChecker.Tc.fst"
let _57_2221 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))

# 1597 "FStar.TypeChecker.Tc.fst"
let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (
# 1598 "FStar.TypeChecker.Tc.fst"
let fail = (fun _57_2227 -> (match (()) with
| () -> begin
(let _146_839 = (let _146_838 = (let _146_837 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_146_837, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_146_838))
in (Prims.raise _146_839))
end))
in (
# 1599 "FStar.TypeChecker.Tc.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1602 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _57_2244)::(wp, _57_2240)::(_wlp, _57_2236)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2248 -> begin
(fail ())
end))
end
| _57_2250 -> begin
(fail ())
end))))

# 1609 "FStar.TypeChecker.Tc.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 1612 "FStar.TypeChecker.Tc.fst"
let _57_2257 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_57_2257) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _57_2259 -> begin
(
# 1615 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow binders c)
in (
# 1616 "FStar.TypeChecker.Tc.fst"
let _57_2263 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_57_2263) with
| (uvs, t') -> begin
(match ((let _146_846 = (FStar_Syntax_Subst.compress t')
in _146_846.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _57_2269 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 1621 "FStar.TypeChecker.Tc.fst"
let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (
# 1622 "FStar.TypeChecker.Tc.fst"
let fail = (fun t -> (let _146_857 = (let _146_856 = (let _146_855 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_146_855, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_146_856))
in (Prims.raise _146_857)))
in (match ((let _146_858 = (FStar_Syntax_Subst.compress signature)
in _146_858.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1625 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _57_2290)::(wp, _57_2286)::(_wlp, _57_2282)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2294 -> begin
(fail signature)
end))
end
| _57_2296 -> begin
(fail signature)
end)))

# 1632 "FStar.TypeChecker.Tc.fst"
let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (
# 1633 "FStar.TypeChecker.Tc.fst"
let _57_2301 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_57_2301) with
| (a, wp) -> begin
(
# 1634 "FStar.TypeChecker.Tc.fst"
let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _57_2304 -> begin
(
# 1638 "FStar.TypeChecker.Tc.fst"
let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (
# 1639 "FStar.TypeChecker.Tc.fst"
let op = (fun ts -> (
# 1640 "FStar.TypeChecker.Tc.fst"
let _57_2308 = ()
in (
# 1641 "FStar.TypeChecker.Tc.fst"
let t0 = (Prims.snd ts)
in (
# 1642 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (
# 1644 "FStar.TypeChecker.Tc.fst"
let _57_2312 = ed
in (let _146_877 = (op ed.FStar_Syntax_Syntax.ret)
in (let _146_876 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _146_875 = (op ed.FStar_Syntax_Syntax.bind_wlp)
in (let _146_874 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _146_873 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _146_872 = (op ed.FStar_Syntax_Syntax.ite_wlp)
in (let _146_871 = (op ed.FStar_Syntax_Syntax.wp_binop)
in (let _146_870 = (op ed.FStar_Syntax_Syntax.wp_as_type)
in (let _146_869 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _146_868 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _146_867 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _146_866 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _146_865 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _57_2312.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2312.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2312.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2312.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2312.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _146_877; FStar_Syntax_Syntax.bind_wp = _146_876; FStar_Syntax_Syntax.bind_wlp = _146_875; FStar_Syntax_Syntax.if_then_else = _146_874; FStar_Syntax_Syntax.ite_wp = _146_873; FStar_Syntax_Syntax.ite_wlp = _146_872; FStar_Syntax_Syntax.wp_binop = _146_871; FStar_Syntax_Syntax.wp_as_type = _146_870; FStar_Syntax_Syntax.close_wp = _146_869; FStar_Syntax_Syntax.assert_p = _146_868; FStar_Syntax_Syntax.assume_p = _146_867; FStar_Syntax_Syntax.null_wp = _146_866; FStar_Syntax_Syntax.trivial = _146_865}))))))))))))))))
end)
in (ed, a, wp))
end)))

# 1660 "FStar.TypeChecker.Tc.fst"
let gen_wps_for_free : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env binders a wp_a ed -> (
# 1665 "FStar.TypeChecker.Tc.fst"
let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env)
in (
# 1667 "FStar.TypeChecker.Tc.fst"
let d = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))
in (
# 1668 "FStar.TypeChecker.Tc.fst"
let normalize_and_make_binders_explicit = (fun tm -> (
# 1669 "FStar.TypeChecker.Tc.fst"
let tm = (normalize tm)
in (
# 1670 "FStar.TypeChecker.Tc.fst"
let rec visit_term = (fun tm -> (
# 1671 "FStar.TypeChecker.Tc.fst"
let n = (match ((let _146_899 = (FStar_Syntax_Subst.compress tm)
in _146_899.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(
# 1673 "FStar.TypeChecker.Tc.fst"
let comp = (visit_comp comp)
in (
# 1674 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map visit_binder binders)
in FStar_Syntax_Syntax.Tm_arrow ((binders, comp))))
end
| FStar_Syntax_Syntax.Tm_abs (binders, term, comp) -> begin
(
# 1677 "FStar.TypeChecker.Tc.fst"
let comp = (visit_maybe_lcomp comp)
in (
# 1678 "FStar.TypeChecker.Tc.fst"
let term = (visit_term term)
in (
# 1679 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map visit_binder binders)
in FStar_Syntax_Syntax.Tm_abs ((binders, term, comp)))))
end
| _57_2347 -> begin
tm.FStar_Syntax_Syntax.n
end)
in (
# 1684 "FStar.TypeChecker.Tc.fst"
let _57_2349 = tm
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2349.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2349.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2349.FStar_Syntax_Syntax.vars})))
and visit_binder = (fun _57_2353 -> (match (_57_2353) with
| (bv, a) -> begin
(let _146_903 = (
# 1686 "FStar.TypeChecker.Tc.fst"
let _57_2354 = bv
in (let _146_901 = (visit_term bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_2354.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2354.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_901}))
in (let _146_902 = (FStar_Syntax_Syntax.as_implicit false)
in (_146_903, _146_902)))
end))
and visit_maybe_lcomp = (fun lcomp -> (match (lcomp) with
| Some (FStar_Util.Inl (lcomp)) -> begin
(let _146_908 = (let _146_907 = (let _146_906 = (let _146_905 = (lcomp.FStar_Syntax_Syntax.comp ())
in (visit_comp _146_905))
in (FStar_Syntax_Util.lcomp_of_comp _146_906))
in FStar_Util.Inl (_146_907))
in Some (_146_908))
end
| comp -> begin
comp
end))
and visit_comp = (fun comp -> (
# 1694 "FStar.TypeChecker.Tc.fst"
let n = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tm) -> begin
(let _146_910 = (visit_term tm)
in FStar_Syntax_Syntax.Total (_146_910))
end
| FStar_Syntax_Syntax.GTotal (tm) -> begin
(let _146_911 = (visit_term tm)
in FStar_Syntax_Syntax.GTotal (_146_911))
end
| comp -> begin
comp
end)
in (
# 1702 "FStar.TypeChecker.Tc.fst"
let _57_2368 = comp
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2368.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2368.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2368.FStar_Syntax_Syntax.vars})))
and visit_args = (fun args -> (FStar_List.map (fun _57_2373 -> (match (_57_2373) with
| (tm, q) -> begin
(let _146_914 = (visit_term tm)
in (_146_914, q))
end)) args))
in (visit_term tm))))
in (
# 1710 "FStar.TypeChecker.Tc.fst"
let check = (fun str t -> if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(
# 1712 "FStar.TypeChecker.Tc.fst"
let _57_2377 = (let _146_919 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Generated term for %s: %s\n" str _146_919))
in (
# 1713 "FStar.TypeChecker.Tc.fst"
let t = (normalize t)
in (
# 1714 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 1715 "FStar.TypeChecker.Tc.fst"
let _57_2392 = (tc_term env t)
in (match (_57_2392) with
| (e, {FStar_Syntax_Syntax.eff_name = _57_2388; FStar_Syntax_Syntax.res_typ = res_typ; FStar_Syntax_Syntax.cflags = _57_2385; FStar_Syntax_Syntax.comp = _57_2383}, _57_2391) -> begin
(
# 1716 "FStar.TypeChecker.Tc.fst"
let _57_2393 = (let _146_922 = (let _146_921 = (normalize res_typ)
in (FStar_Syntax_Print.term_to_string _146_921))
in (FStar_Util.print2 "Inferred type for %s: %s\n" str _146_922))
in (let _146_924 = (let _146_923 = (normalize e)
in (FStar_Syntax_Print.term_to_string _146_923))
in (FStar_Util.print2 "Elaborated term for %s: %s\n" str _146_924)))
end)))))
end else begin
()
end)
in (
# 1732 "FStar.TypeChecker.Tc.fst"
let _57_2418 = (
# 1733 "FStar.TypeChecker.Tc.fst"
let i = (FStar_ST.alloc 0)
in (match ((let _146_937 = (normalize wp_a)
in _146_937.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, comp) -> begin
((fun t -> (FStar_Syntax_Util.arrow wp_binders (
# 1736 "FStar.TypeChecker.Tc.fst"
let _57_2401 = comp
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t); FStar_Syntax_Syntax.tk = _57_2401.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2401.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2401.FStar_Syntax_Syntax.vars}))), (fun t -> (FStar_Syntax_Util.arrow wp_binders (
# 1737 "FStar.TypeChecker.Tc.fst"
let _57_2404 = comp
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (t); FStar_Syntax_Syntax.tk = _57_2404.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2404.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2404.FStar_Syntax_Syntax.vars}))), (fun _57_2406 -> (match (()) with
| () -> begin
(FStar_List.map (fun _57_2410 -> (match (_57_2410) with
| (bv, _57_2409) -> begin
(
# 1744 "FStar.TypeChecker.Tc.fst"
let _57_2411 = (let _146_948 = ((FStar_ST.read i) + 1)
in (FStar_ST.op_Colon_Equals i _146_948))
in (let _146_951 = (let _146_950 = (let _146_949 = (FStar_ST.read i)
in (FStar_Util.string_of_int _146_949))
in (Prims.strcat "g" _146_950))
in (FStar_Syntax_Syntax.gen_bv _146_951 None bv.FStar_Syntax_Syntax.sort)))
end)) wp_binders)
end)))
end
| _57_2414 -> begin
(FStar_All.failwith "wp_a doesn\'t have the right shape")
end))
in (match (_57_2418) with
| (mk_ctx, mk_gctx, mk_gamma) -> begin
(
# 1752 "FStar.TypeChecker.Tc.fst"
let binders_of_list = (FStar_List.map (fun _57_2421 -> (match (_57_2421) with
| (t, b) -> begin
(let _146_963 = (FStar_Syntax_Syntax.as_implicit b)
in (t, _146_963))
end)))
in (
# 1754 "FStar.TypeChecker.Tc.fst"
let implicit_binders_of_list = (FStar_List.map (fun t -> (let _146_966 = (FStar_Syntax_Syntax.as_implicit true)
in (t, _146_966))))
in (
# 1756 "FStar.TypeChecker.Tc.fst"
let args_of_bv = (FStar_List.map (fun bv -> (let _146_969 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_Syntax_Syntax.as_arg _146_969))))
in (
# 1761 "FStar.TypeChecker.Tc.fst"
let c_pure = (
# 1762 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (
# 1763 "FStar.TypeChecker.Tc.fst"
let x = (let _146_970 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _146_970))
in (
# 1764 "FStar.TypeChecker.Tc.fst"
let ret = (let _146_975 = (let _146_974 = (let _146_973 = (let _146_972 = (let _146_971 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx _146_971))
in (FStar_Syntax_Syntax.mk_Total _146_972))
in (FStar_Syntax_Util.lcomp_of_comp _146_973))
in FStar_Util.Inl (_146_974))
in Some (_146_975))
in (
# 1765 "FStar.TypeChecker.Tc.fst"
let gamma = (mk_gamma ())
in (
# 1766 "FStar.TypeChecker.Tc.fst"
let body = (let _146_977 = (implicit_binders_of_list gamma)
in (let _146_976 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs _146_977 _146_976 ret)))
in (let _146_978 = (binders_of_list (((t, true))::((x, false))::[]))
in (FStar_Syntax_Util.abs _146_978 body ret)))))))
in (
# 1769 "FStar.TypeChecker.Tc.fst"
let _57_2433 = (let _146_982 = (let _146_981 = (let _146_980 = (let _146_979 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_979)::[])
in (FStar_List.append binders _146_980))
in (FStar_Syntax_Util.abs _146_981 c_pure None))
in (check "pure" _146_982))
in (
# 1776 "FStar.TypeChecker.Tc.fst"
let c_app = (
# 1777 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (
# 1778 "FStar.TypeChecker.Tc.fst"
let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (
# 1779 "FStar.TypeChecker.Tc.fst"
let l = (let _146_990 = (let _146_989 = (let _146_988 = (let _146_985 = (let _146_984 = (let _146_983 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _146_983))
in (FStar_Syntax_Syntax.mk_binder _146_984))
in (_146_985)::[])
in (let _146_987 = (let _146_986 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _146_986))
in (FStar_Syntax_Util.arrow _146_988 _146_987)))
in (mk_gctx _146_989))
in (FStar_Syntax_Syntax.gen_bv "l" None _146_990))
in (
# 1782 "FStar.TypeChecker.Tc.fst"
let r = (let _146_992 = (let _146_991 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _146_991))
in (FStar_Syntax_Syntax.gen_bv "r" None _146_992))
in (
# 1783 "FStar.TypeChecker.Tc.fst"
let ret = (let _146_997 = (let _146_996 = (let _146_995 = (let _146_994 = (let _146_993 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_993))
in (FStar_Syntax_Syntax.mk_Total _146_994))
in (FStar_Syntax_Util.lcomp_of_comp _146_995))
in FStar_Util.Inl (_146_996))
in Some (_146_997))
in (
# 1784 "FStar.TypeChecker.Tc.fst"
let outer_body = (
# 1785 "FStar.TypeChecker.Tc.fst"
let gamma = (mk_gamma ())
in (
# 1786 "FStar.TypeChecker.Tc.fst"
let gamma_as_args = (args_of_bv gamma)
in (
# 1787 "FStar.TypeChecker.Tc.fst"
let inner_body = (let _146_1003 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _146_1002 = (let _146_1001 = (let _146_1000 = (let _146_999 = (let _146_998 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _146_998 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg _146_999))
in (_146_1000)::[])
in (FStar_List.append gamma_as_args _146_1001))
in (FStar_Syntax_Util.mk_app _146_1003 _146_1002)))
in (let _146_1004 = (implicit_binders_of_list gamma)
in (FStar_Syntax_Util.abs _146_1004 inner_body ret)))))
in (let _146_1005 = (binders_of_list (((t1, true))::((t2, true))::((l, false))::((r, false))::[]))
in (FStar_Syntax_Util.abs _146_1005 outer_body ret))))))))
in (
# 1796 "FStar.TypeChecker.Tc.fst"
let _57_2445 = (let _146_1009 = (let _146_1008 = (let _146_1007 = (let _146_1006 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1006)::[])
in (FStar_List.append binders _146_1007))
in (FStar_Syntax_Util.abs _146_1008 c_app None))
in (check "app" _146_1009))
in (
# 1805 "FStar.TypeChecker.Tc.fst"
let unknown = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (
# 1806 "FStar.TypeChecker.Tc.fst"
let c_lift1 = (
# 1807 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (
# 1808 "FStar.TypeChecker.Tc.fst"
let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (
# 1809 "FStar.TypeChecker.Tc.fst"
let t_f = (let _146_1014 = (let _146_1011 = (let _146_1010 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_1010))
in (_146_1011)::[])
in (let _146_1013 = (let _146_1012 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _146_1012))
in (FStar_Syntax_Util.arrow _146_1014 _146_1013)))
in (
# 1810 "FStar.TypeChecker.Tc.fst"
let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (
# 1811 "FStar.TypeChecker.Tc.fst"
let a1 = (let _146_1016 = (let _146_1015 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _146_1015))
in (FStar_Syntax_Syntax.gen_bv "a1" None _146_1016))
in (
# 1812 "FStar.TypeChecker.Tc.fst"
let ret = (let _146_1021 = (let _146_1020 = (let _146_1019 = (let _146_1018 = (let _146_1017 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_1017))
in (FStar_Syntax_Syntax.mk_Total _146_1018))
in (FStar_Syntax_Util.lcomp_of_comp _146_1019))
in FStar_Util.Inl (_146_1020))
in Some (_146_1021))
in (let _146_1034 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::((a1, false))::[]))
in (let _146_1033 = (let _146_1032 = (let _146_1031 = (let _146_1030 = (let _146_1029 = (let _146_1028 = (let _146_1025 = (let _146_1024 = (let _146_1023 = (let _146_1022 = (FStar_Syntax_Syntax.bv_to_name f)
in (_146_1022)::[])
in (unknown)::_146_1023)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1024))
in (FStar_Syntax_Util.mk_app c_pure _146_1025))
in (let _146_1027 = (let _146_1026 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_146_1026)::[])
in (_146_1028)::_146_1027))
in (unknown)::_146_1029)
in (unknown)::_146_1030)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1031))
in (FStar_Syntax_Util.mk_app c_app _146_1032))
in (FStar_Syntax_Util.abs _146_1034 _146_1033 ret)))))))))
in (
# 1820 "FStar.TypeChecker.Tc.fst"
let _57_2455 = (let _146_1038 = (let _146_1037 = (let _146_1036 = (let _146_1035 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1035)::[])
in (FStar_List.append binders _146_1036))
in (FStar_Syntax_Util.abs _146_1037 c_lift1 None))
in (check "lift1" _146_1038))
in (
# 1831 "FStar.TypeChecker.Tc.fst"
let c_lift2 = (
# 1832 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (
# 1833 "FStar.TypeChecker.Tc.fst"
let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (
# 1834 "FStar.TypeChecker.Tc.fst"
let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (
# 1835 "FStar.TypeChecker.Tc.fst"
let t_f = (let _146_1046 = (let _146_1043 = (let _146_1039 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_1039))
in (let _146_1042 = (let _146_1041 = (let _146_1040 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder _146_1040))
in (_146_1041)::[])
in (_146_1043)::_146_1042))
in (let _146_1045 = (let _146_1044 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal _146_1044))
in (FStar_Syntax_Util.arrow _146_1046 _146_1045)))
in (
# 1839 "FStar.TypeChecker.Tc.fst"
let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (
# 1840 "FStar.TypeChecker.Tc.fst"
let a1 = (let _146_1048 = (let _146_1047 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _146_1047))
in (FStar_Syntax_Syntax.gen_bv "a1" None _146_1048))
in (
# 1841 "FStar.TypeChecker.Tc.fst"
let a2 = (let _146_1050 = (let _146_1049 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_1049))
in (FStar_Syntax_Syntax.gen_bv "a2" None _146_1050))
in (
# 1842 "FStar.TypeChecker.Tc.fst"
let ret = (let _146_1055 = (let _146_1054 = (let _146_1053 = (let _146_1052 = (let _146_1051 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx _146_1051))
in (FStar_Syntax_Syntax.mk_Total _146_1052))
in (FStar_Syntax_Util.lcomp_of_comp _146_1053))
in FStar_Util.Inl (_146_1054))
in Some (_146_1055))
in (let _146_1075 = (binders_of_list (((t1, true))::((t2, true))::((t3, true))::((f, false))::((a1, false))::((a2, false))::[]))
in (let _146_1074 = (let _146_1073 = (let _146_1072 = (let _146_1071 = (let _146_1070 = (let _146_1069 = (let _146_1066 = (let _146_1065 = (let _146_1064 = (let _146_1063 = (let _146_1062 = (let _146_1059 = (let _146_1058 = (let _146_1057 = (let _146_1056 = (FStar_Syntax_Syntax.bv_to_name f)
in (_146_1056)::[])
in (unknown)::_146_1057)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1058))
in (FStar_Syntax_Util.mk_app c_pure _146_1059))
in (let _146_1061 = (let _146_1060 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_146_1060)::[])
in (_146_1062)::_146_1061))
in (unknown)::_146_1063)
in (unknown)::_146_1064)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1065))
in (FStar_Syntax_Util.mk_app c_app _146_1066))
in (let _146_1068 = (let _146_1067 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_146_1067)::[])
in (_146_1069)::_146_1068))
in (unknown)::_146_1070)
in (unknown)::_146_1071)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1072))
in (FStar_Syntax_Util.mk_app c_app _146_1073))
in (FStar_Syntax_Util.abs _146_1075 _146_1074 ret)))))))))))
in (
# 1853 "FStar.TypeChecker.Tc.fst"
let _57_2466 = (let _146_1079 = (let _146_1078 = (let _146_1077 = (let _146_1076 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1076)::[])
in (FStar_List.append binders _146_1077))
in (FStar_Syntax_Util.abs _146_1078 c_lift2 None))
in (check "lift2" _146_1079))
in (
# 1859 "FStar.TypeChecker.Tc.fst"
let c_push = (
# 1860 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (
# 1861 "FStar.TypeChecker.Tc.fst"
let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (
# 1862 "FStar.TypeChecker.Tc.fst"
let t_f = (let _146_1085 = (let _146_1081 = (let _146_1080 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_1080))
in (_146_1081)::[])
in (let _146_1084 = (let _146_1083 = (let _146_1082 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_1082))
in (FStar_Syntax_Syntax.mk_Total _146_1083))
in (FStar_Syntax_Util.arrow _146_1085 _146_1084)))
in (
# 1866 "FStar.TypeChecker.Tc.fst"
let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (
# 1867 "FStar.TypeChecker.Tc.fst"
let ret = (let _146_1095 = (let _146_1094 = (let _146_1093 = (let _146_1092 = (let _146_1091 = (let _146_1090 = (let _146_1087 = (let _146_1086 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_1086))
in (_146_1087)::[])
in (let _146_1089 = (let _146_1088 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _146_1088))
in (FStar_Syntax_Util.arrow _146_1090 _146_1089)))
in (mk_ctx _146_1091))
in (FStar_Syntax_Syntax.mk_Total _146_1092))
in (FStar_Syntax_Util.lcomp_of_comp _146_1093))
in FStar_Util.Inl (_146_1094))
in Some (_146_1095))
in (
# 1870 "FStar.TypeChecker.Tc.fst"
let e1 = (let _146_1096 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _146_1096))
in (
# 1871 "FStar.TypeChecker.Tc.fst"
let gamma = (mk_gamma ())
in (
# 1872 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1106 = (let _146_1099 = (FStar_Syntax_Syntax.binders_of_list gamma)
in (let _146_1098 = (let _146_1097 = (FStar_Syntax_Syntax.mk_binder e1)
in (_146_1097)::[])
in (FStar_List.append _146_1099 _146_1098)))
in (let _146_1105 = (let _146_1104 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _146_1103 = (let _146_1102 = (let _146_1100 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _146_1100))
in (let _146_1101 = (args_of_bv gamma)
in (_146_1102)::_146_1101))
in (FStar_Syntax_Util.mk_app _146_1104 _146_1103)))
in (FStar_Syntax_Util.abs _146_1106 _146_1105 ret)))
in (let _146_1107 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::[]))
in (FStar_Syntax_Util.abs _146_1107 body ret))))))))))
in (
# 1877 "FStar.TypeChecker.Tc.fst"
let _57_2477 = (let _146_1111 = (let _146_1110 = (let _146_1109 = (let _146_1108 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1108)::[])
in (FStar_List.append binders _146_1109))
in (FStar_Syntax_Util.abs _146_1110 c_push None))
in (check "push" _146_1111))
in (
# 1879 "FStar.TypeChecker.Tc.fst"
let ret_tot_wp_a = (let _146_1114 = (let _146_1113 = (let _146_1112 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _146_1112))
in FStar_Util.Inl (_146_1113))
in Some (_146_1114))
in (
# 1885 "FStar.TypeChecker.Tc.fst"
let wp_if_then_else = (
# 1886 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _146_1125 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (let _146_1124 = (
# 1891 "FStar.TypeChecker.Tc.fst"
let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_unfoldable (2)) None)
in (let _146_1123 = (let _146_1122 = (let _146_1121 = (let _146_1120 = (let _146_1119 = (let _146_1118 = (let _146_1117 = (let _146_1116 = (let _146_1115 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _146_1115))
in (_146_1116)::[])
in (FStar_Syntax_Util.mk_app l_ite _146_1117))
in (_146_1118)::[])
in (unknown)::_146_1119)
in (unknown)::_146_1120)
in (unknown)::_146_1121)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1122))
in (FStar_Syntax_Util.mk_app c_lift2 _146_1123)))
in (FStar_Syntax_Util.abs _146_1125 _146_1124 ret_tot_wp_a))))
in (
# 1899 "FStar.TypeChecker.Tc.fst"
let wp_if_then_else = (normalize_and_make_binders_explicit wp_if_then_else)
in (
# 1900 "FStar.TypeChecker.Tc.fst"
let _57_2484 = (let _146_1126 = (FStar_Syntax_Util.abs binders wp_if_then_else None)
in (check "wp_if_then_else" _146_1126))
in (
# 1906 "FStar.TypeChecker.Tc.fst"
let wp_binop = (
# 1907 "FStar.TypeChecker.Tc.fst"
let l = (FStar_Syntax_Syntax.gen_bv "l" None wp_a)
in (
# 1908 "FStar.TypeChecker.Tc.fst"
let op = (let _146_1132 = (let _146_1131 = (let _146_1129 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Util.ktype0)
in (let _146_1128 = (let _146_1127 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Util.ktype0)
in (_146_1127)::[])
in (_146_1129)::_146_1128))
in (let _146_1130 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _146_1131 _146_1130)))
in (FStar_Syntax_Syntax.gen_bv "op" None _146_1132))
in (
# 1911 "FStar.TypeChecker.Tc.fst"
let r = (FStar_Syntax_Syntax.gen_bv "r" None wp_a)
in (let _146_1144 = (FStar_Syntax_Syntax.binders_of_list ((a)::(l)::(op)::(r)::[]))
in (let _146_1143 = (let _146_1142 = (let _146_1141 = (let _146_1140 = (let _146_1139 = (let _146_1138 = (let _146_1137 = (FStar_Syntax_Syntax.bv_to_name op)
in (let _146_1136 = (let _146_1135 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _146_1134 = (let _146_1133 = (FStar_Syntax_Syntax.bv_to_name r)
in (_146_1133)::[])
in (_146_1135)::_146_1134))
in (_146_1137)::_146_1136))
in (unknown)::_146_1138)
in (unknown)::_146_1139)
in (unknown)::_146_1140)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1141))
in (FStar_Syntax_Util.mk_app c_lift2 _146_1142))
in (FStar_Syntax_Util.abs _146_1144 _146_1143 ret_tot_wp_a))))))
in (
# 1919 "FStar.TypeChecker.Tc.fst"
let wp_binop = (normalize_and_make_binders_explicit wp_binop)
in (
# 1920 "FStar.TypeChecker.Tc.fst"
let _57_2491 = (let _146_1145 = (FStar_Syntax_Util.abs binders wp_binop None)
in (check "wp_binop" _146_1145))
in (
# 1925 "FStar.TypeChecker.Tc.fst"
let wp_assert = (
# 1926 "FStar.TypeChecker.Tc.fst"
let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (
# 1927 "FStar.TypeChecker.Tc.fst"
let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (
# 1928 "FStar.TypeChecker.Tc.fst"
let l_and = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (
# 1929 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1159 = (let _146_1158 = (let _146_1157 = (let _146_1156 = (let _146_1155 = (let _146_1152 = (let _146_1151 = (let _146_1150 = (let _146_1149 = (let _146_1148 = (let _146_1147 = (let _146_1146 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _146_1146))
in (_146_1147)::[])
in (FStar_Syntax_Util.mk_app l_and _146_1148))
in (_146_1149)::[])
in (unknown)::_146_1150)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1151))
in (FStar_Syntax_Util.mk_app c_pure _146_1152))
in (let _146_1154 = (let _146_1153 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_146_1153)::[])
in (_146_1155)::_146_1154))
in (unknown)::_146_1156)
in (unknown)::_146_1157)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1158))
in (FStar_Syntax_Util.mk_app c_app _146_1159))
in (let _146_1160 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _146_1160 body ret_tot_wp_a))))))
in (
# 1939 "FStar.TypeChecker.Tc.fst"
let wp_assert = (normalize_and_make_binders_explicit wp_assert)
in (
# 1940 "FStar.TypeChecker.Tc.fst"
let _57_2499 = (let _146_1161 = (FStar_Syntax_Util.abs binders wp_assert None)
in (check "wp_assert" _146_1161))
in (
# 1945 "FStar.TypeChecker.Tc.fst"
let wp_assume = (
# 1946 "FStar.TypeChecker.Tc.fst"
let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (
# 1947 "FStar.TypeChecker.Tc.fst"
let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (
# 1948 "FStar.TypeChecker.Tc.fst"
let l_imp = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (
# 1949 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1175 = (let _146_1174 = (let _146_1173 = (let _146_1172 = (let _146_1171 = (let _146_1168 = (let _146_1167 = (let _146_1166 = (let _146_1165 = (let _146_1164 = (let _146_1163 = (let _146_1162 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _146_1162))
in (_146_1163)::[])
in (FStar_Syntax_Util.mk_app l_imp _146_1164))
in (_146_1165)::[])
in (unknown)::_146_1166)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1167))
in (FStar_Syntax_Util.mk_app c_pure _146_1168))
in (let _146_1170 = (let _146_1169 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_146_1169)::[])
in (_146_1171)::_146_1170))
in (unknown)::_146_1172)
in (unknown)::_146_1173)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1174))
in (FStar_Syntax_Util.mk_app c_app _146_1175))
in (let _146_1176 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _146_1176 body ret_tot_wp_a))))))
in (
# 1959 "FStar.TypeChecker.Tc.fst"
let wp_assume = (normalize_and_make_binders_explicit wp_assume)
in (
# 1960 "FStar.TypeChecker.Tc.fst"
let _57_2507 = (let _146_1177 = (FStar_Syntax_Util.abs binders wp_assume None)
in (check "wp_assume" _146_1177))
in (
# 1962 "FStar.TypeChecker.Tc.fst"
let tforall = (let _146_1180 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _146_1179 = (let _146_1178 = (FStar_Syntax_Syntax.as_arg unknown)
in (_146_1178)::[])
in (FStar_Syntax_Util.mk_app _146_1180 _146_1179)))
in (
# 1968 "FStar.TypeChecker.Tc.fst"
let wp_close = (
# 1969 "FStar.TypeChecker.Tc.fst"
let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (
# 1970 "FStar.TypeChecker.Tc.fst"
let t_f = (let _146_1184 = (let _146_1182 = (let _146_1181 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _146_1181))
in (_146_1182)::[])
in (let _146_1183 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1184 _146_1183)))
in (
# 1971 "FStar.TypeChecker.Tc.fst"
let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (
# 1972 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1197 = (let _146_1196 = (let _146_1195 = (let _146_1194 = (let _146_1193 = (let _146_1185 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((unknown)::(tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _146_1185))
in (let _146_1192 = (let _146_1191 = (let _146_1190 = (let _146_1189 = (let _146_1188 = (let _146_1187 = (let _146_1186 = (FStar_Syntax_Syntax.bv_to_name f)
in (_146_1186)::[])
in (unknown)::_146_1187)
in (unknown)::_146_1188)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1189))
in (FStar_Syntax_Util.mk_app c_push _146_1190))
in (_146_1191)::[])
in (_146_1193)::_146_1192))
in (unknown)::_146_1194)
in (unknown)::_146_1195)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1196))
in (FStar_Syntax_Util.mk_app c_app _146_1197))
in (let _146_1198 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_Syntax_Util.abs _146_1198 body ret_tot_wp_a))))))
in (
# 1984 "FStar.TypeChecker.Tc.fst"
let wp_close = (normalize_and_make_binders_explicit wp_close)
in (
# 1985 "FStar.TypeChecker.Tc.fst"
let _57_2516 = (let _146_1199 = (FStar_Syntax_Util.abs binders wp_close None)
in (check "wp_close" _146_1199))
in (
# 1987 "FStar.TypeChecker.Tc.fst"
let ret_tot_type0 = (let _146_1202 = (let _146_1201 = (let _146_1200 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_1200))
in FStar_Util.Inl (_146_1201))
in Some (_146_1202))
in (
# 1988 "FStar.TypeChecker.Tc.fst"
let mk_forall = (fun x body -> (
# 1989 "FStar.TypeChecker.Tc.fst"
let tforall = (let _146_1209 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _146_1208 = (let _146_1207 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (_146_1207)::[])
in (FStar_Syntax_Util.mk_app _146_1209 _146_1208)))
in (let _146_1216 = (let _146_1215 = (let _146_1214 = (let _146_1213 = (let _146_1212 = (let _146_1211 = (let _146_1210 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_1210)::[])
in (FStar_Syntax_Util.abs _146_1211 body ret_tot_type0))
in (FStar_Syntax_Syntax.as_arg _146_1212))
in (_146_1213)::[])
in (tforall, _146_1214))
in FStar_Syntax_Syntax.Tm_app (_146_1215))
in (FStar_Syntax_Syntax.mk _146_1216 None FStar_Range.dummyRange))))
in (
# 2000 "FStar.TypeChecker.Tc.fst"
let rec mk_leq = (fun t x y -> (match ((let _146_1224 = (let _146_1223 = (FStar_Syntax_Subst.compress t)
in (normalize _146_1223))
in _146_1224.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_2528) -> begin
(
# 2003 "FStar.TypeChecker.Tc.fst"
let _57_2530 = (let _146_1226 = (FStar_Syntax_Print.term_to_string x)
in (let _146_1225 = (FStar_Syntax_Print.term_to_string y)
in (FStar_Util.print2 "type0, x=%s, y=%s\n" _146_1226 _146_1225)))
in (FStar_Syntax_Util.mk_imp x y))
end
| (FStar_Syntax_Syntax.Tm_arrow (binder::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow (binder::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) when (FStar_Syntax_Syntax.is_null_binder binder) -> begin
(
# 2007 "FStar.TypeChecker.Tc.fst"
let a = (Prims.fst binder).FStar_Syntax_Syntax.sort
in (
# 2008 "FStar.TypeChecker.Tc.fst"
let _57_2557 = (let _146_1228 = (FStar_Syntax_Print.term_to_string a)
in (let _146_1227 = (FStar_Syntax_Print.term_to_string b)
in (FStar_Util.print2 "arrow, a=%s, b=%s\n" _146_1228 _146_1227)))
in (
# 2009 "FStar.TypeChecker.Tc.fst"
let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (
# 2010 "FStar.TypeChecker.Tc.fst"
let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (
# 2011 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1240 = (let _146_1230 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _146_1229 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_leq a _146_1230 _146_1229)))
in (let _146_1239 = (let _146_1238 = (let _146_1233 = (let _146_1232 = (let _146_1231 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _146_1231))
in (_146_1232)::[])
in (FStar_Syntax_Util.mk_app x _146_1233))
in (let _146_1237 = (let _146_1236 = (let _146_1235 = (let _146_1234 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _146_1234))
in (_146_1235)::[])
in (FStar_Syntax_Util.mk_app y _146_1236))
in (mk_leq b _146_1238 _146_1237)))
in (FStar_Syntax_Util.mk_imp _146_1240 _146_1239)))
in (let _146_1241 = (mk_forall a2 body)
in (mk_forall a1 _146_1241)))))))
end
| FStar_Syntax_Syntax.Tm_arrow (binder::binders, comp) -> begin
(
# 2019 "FStar.TypeChecker.Tc.fst"
let t = (
# 2019 "FStar.TypeChecker.Tc.fst"
let _57_2568 = t
in (let _146_1245 = (let _146_1244 = (let _146_1243 = (let _146_1242 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _146_1242))
in ((binder)::[], _146_1243))
in FStar_Syntax_Syntax.Tm_arrow (_146_1244))
in {FStar_Syntax_Syntax.n = _146_1245; FStar_Syntax_Syntax.tk = _57_2568.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2568.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2568.FStar_Syntax_Syntax.vars}))
in (mk_leq t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_57_2572) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _57_2575 -> begin
(
# 2025 "FStar.TypeChecker.Tc.fst"
let _57_2576 = (let _146_1247 = (FStar_Syntax_Print.term_to_string x)
in (let _146_1246 = (FStar_Syntax_Print.term_to_string y)
in (FStar_Util.print2 "base, x=%s, y=%s\n" _146_1247 _146_1246)))
in (FStar_Syntax_Util.mk_eq t t x y))
end))
in (
# 2028 "FStar.TypeChecker.Tc.fst"
let stronger = (
# 2029 "FStar.TypeChecker.Tc.fst"
let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (
# 2030 "FStar.TypeChecker.Tc.fst"
let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (
# 2031 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1249 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _146_1248 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_leq wp_a _146_1249 _146_1248)))
in (let _146_1250 = (FStar_Syntax_Syntax.binders_of_list ((wp1)::(wp2)::[]))
in (FStar_Syntax_Util.abs _146_1250 body ret_tot_type0)))))
in (
# 2034 "FStar.TypeChecker.Tc.fst"
let _57_2582 = (let _146_1254 = (let _146_1253 = (let _146_1252 = (let _146_1251 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1251)::[])
in (FStar_List.append binders _146_1252))
in (FStar_Syntax_Util.abs _146_1253 stronger None))
in (check "stronger" _146_1254))
in (
# 2036 "FStar.TypeChecker.Tc.fst"
let null_wp = (Prims.snd ed.FStar_Syntax_Syntax.null_wp)
in (
# 2040 "FStar.TypeChecker.Tc.fst"
let wp_trivial = (
# 2041 "FStar.TypeChecker.Tc.fst"
let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (
# 2042 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1262 = (let _146_1261 = (let _146_1260 = (let _146_1257 = (let _146_1256 = (let _146_1255 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _146_1255))
in (_146_1256)::[])
in (FStar_Syntax_Util.mk_app null_wp _146_1257))
in (let _146_1259 = (let _146_1258 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_146_1258)::[])
in (_146_1260)::_146_1259))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1261))
in (FStar_Syntax_Util.mk_app stronger _146_1262))
in (let _146_1263 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_Syntax_Util.abs _146_1263 body ret_tot_type0))))
in (
# 2048 "FStar.TypeChecker.Tc.fst"
let wp_trivial = (normalize_and_make_binders_explicit wp_trivial)
in (
# 2049 "FStar.TypeChecker.Tc.fst"
let _57_2589 = (let _146_1264 = (FStar_Syntax_Util.abs binders wp_trivial None)
in (check "wp_trivial" _146_1264))
in (
# 2051 "FStar.TypeChecker.Tc.fst"
let _57_2591 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2591.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2591.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2591.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2591.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2591.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _57_2591.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2591.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _57_2591.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = ([], wp_if_then_else); FStar_Syntax_Syntax.ite_wp = _57_2591.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _57_2591.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = ([], wp_binop); FStar_Syntax_Syntax.wp_as_type = _57_2591.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = ([], wp_close); FStar_Syntax_Syntax.assert_p = ([], wp_assert); FStar_Syntax_Syntax.assume_p = ([], wp_assume); FStar_Syntax_Syntax.null_wp = _57_2591.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = ([], wp_trivial)})))))))))))))))))))))))))))))))))))))))))
end)))))))

# 2061 "FStar.TypeChecker.Tc.fst"
let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  effect_cost  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed is_for_free -> (
# 2062 "FStar.TypeChecker.Tc.fst"
let _57_2596 = ()
in (
# 2063 "FStar.TypeChecker.Tc.fst"
let _57_2600 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_57_2600) with
| (binders_un, signature_un) -> begin
(
# 2064 "FStar.TypeChecker.Tc.fst"
let _57_2605 = (tc_tparams env0 binders_un)
in (match (_57_2605) with
| (binders, env, _57_2604) -> begin
(
# 2065 "FStar.TypeChecker.Tc.fst"
let _57_2609 = (tc_trivial_guard env signature_un)
in (match (_57_2609) with
| (signature, _57_2608) -> begin
(
# 2066 "FStar.TypeChecker.Tc.fst"
let ed = (
# 2066 "FStar.TypeChecker.Tc.fst"
let _57_2610 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2610.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2610.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2610.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _57_2610.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2610.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _57_2610.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = _57_2610.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _57_2610.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _57_2610.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = _57_2610.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _57_2610.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _57_2610.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _57_2610.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _57_2610.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _57_2610.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _57_2610.FStar_Syntax_Syntax.trivial})
in (
# 2069 "FStar.TypeChecker.Tc.fst"
let _57_2616 = (open_effect_decl env ed)
in (match (_57_2616) with
| (ed, a, wp_a) -> begin
(
# 2070 "FStar.TypeChecker.Tc.fst"
let get_effect_signature = (fun _57_2618 -> (match (()) with
| () -> begin
(
# 2071 "FStar.TypeChecker.Tc.fst"
let _57_2622 = (tc_trivial_guard env signature_un)
in (match (_57_2622) with
| (signature, _57_2621) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (
# 2075 "FStar.TypeChecker.Tc.fst"
let env = (let _146_1273 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _146_1273))
in (
# 2077 "FStar.TypeChecker.Tc.fst"
let _57_2624 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _146_1276 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _146_1275 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _146_1274 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checking effect signature: %s %s : %s\n" _146_1276 _146_1275 _146_1274))))
end else begin
()
end
in (
# 2083 "FStar.TypeChecker.Tc.fst"
let check_and_gen' = (fun env _57_2631 k -> (match (_57_2631) with
| (_57_2629, t) -> begin
(check_and_gen env t k)
end))
in (
# 2087 "FStar.TypeChecker.Tc.fst"
let ed = (match (is_for_free) with
| NotForFree -> begin
ed
end
| ForFree -> begin
(gen_wps_for_free env binders a wp_a ed)
end)
in (
# 2092 "FStar.TypeChecker.Tc.fst"
let ret = (
# 2093 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1288 = (let _146_1286 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1285 = (let _146_1284 = (let _146_1283 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_1283))
in (_146_1284)::[])
in (_146_1286)::_146_1285))
in (let _146_1287 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _146_1288 _146_1287)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (
# 2096 "FStar.TypeChecker.Tc.fst"
let bind_wp = (
# 2097 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 2098 "FStar.TypeChecker.Tc.fst"
let _57_2641 = (get_effect_signature ())
in (match (_57_2641) with
| (b, wp_b) -> begin
(
# 2099 "FStar.TypeChecker.Tc.fst"
let a_wp_b = (let _146_1292 = (let _146_1290 = (let _146_1289 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_1289))
in (_146_1290)::[])
in (let _146_1291 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _146_1292 _146_1291)))
in (
# 2100 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = a_wp_b
in (
# 2101 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1305 = (let _146_1303 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1302 = (let _146_1301 = (FStar_Syntax_Syntax.mk_binder b)
in (let _146_1300 = (let _146_1299 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_1298 = (let _146_1297 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _146_1296 = (let _146_1295 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (let _146_1294 = (let _146_1293 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_146_1293)::[])
in (_146_1295)::_146_1294))
in (_146_1297)::_146_1296))
in (_146_1299)::_146_1298))
in (_146_1301)::_146_1300))
in (_146_1303)::_146_1302))
in (let _146_1304 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _146_1305 _146_1304)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k))))
end)))
in (
# 2107 "FStar.TypeChecker.Tc.fst"
let bind_wlp = (
# 2108 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 2109 "FStar.TypeChecker.Tc.fst"
let _57_2649 = (get_effect_signature ())
in (match (_57_2649) with
| (b, wlp_b) -> begin
(
# 2110 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = (let _146_1309 = (let _146_1307 = (let _146_1306 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_1306))
in (_146_1307)::[])
in (let _146_1308 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _146_1309 _146_1308)))
in (
# 2111 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1318 = (let _146_1316 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1315 = (let _146_1314 = (FStar_Syntax_Syntax.mk_binder b)
in (let _146_1313 = (let _146_1312 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _146_1311 = (let _146_1310 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_146_1310)::[])
in (_146_1312)::_146_1311))
in (_146_1314)::_146_1313))
in (_146_1316)::_146_1315))
in (let _146_1317 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _146_1318 _146_1317)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wlp expected_k)))
end)))
in (
# 2117 "FStar.TypeChecker.Tc.fst"
let if_then_else = (
# 2118 "FStar.TypeChecker.Tc.fst"
let p = (let _146_1320 = (let _146_1319 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1319 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _146_1320))
in (
# 2119 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1329 = (let _146_1327 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1326 = (let _146_1325 = (FStar_Syntax_Syntax.mk_binder p)
in (let _146_1324 = (let _146_1323 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_1322 = (let _146_1321 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1321)::[])
in (_146_1323)::_146_1322))
in (_146_1325)::_146_1324))
in (_146_1327)::_146_1326))
in (let _146_1328 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1329 _146_1328)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (
# 2125 "FStar.TypeChecker.Tc.fst"
let ite_wp = (
# 2126 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 2127 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1336 = (let _146_1334 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1333 = (let _146_1332 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _146_1331 = (let _146_1330 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1330)::[])
in (_146_1332)::_146_1331))
in (_146_1334)::_146_1333))
in (let _146_1335 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1336 _146_1335)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k)))
in (
# 2133 "FStar.TypeChecker.Tc.fst"
let ite_wlp = (
# 2134 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 2135 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1341 = (let _146_1339 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1338 = (let _146_1337 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (_146_1337)::[])
in (_146_1339)::_146_1338))
in (let _146_1340 = (FStar_Syntax_Syntax.mk_Total wlp_a)
in (FStar_Syntax_Util.arrow _146_1341 _146_1340)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wlp expected_k)))
in (
# 2140 "FStar.TypeChecker.Tc.fst"
let wp_binop = (
# 2141 "FStar.TypeChecker.Tc.fst"
let bin_op = (
# 2142 "FStar.TypeChecker.Tc.fst"
let _57_2664 = (FStar_Syntax_Util.type_u ())
in (match (_57_2664) with
| (t1, u1) -> begin
(
# 2143 "FStar.TypeChecker.Tc.fst"
let _57_2667 = (FStar_Syntax_Util.type_u ())
in (match (_57_2667) with
| (t2, u2) -> begin
(
# 2144 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1342 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_max ((u1)::(u2)::[]))) None _146_1342))
in (let _146_1347 = (let _146_1345 = (FStar_Syntax_Syntax.null_binder t1)
in (let _146_1344 = (let _146_1343 = (FStar_Syntax_Syntax.null_binder t2)
in (_146_1343)::[])
in (_146_1345)::_146_1344))
in (let _146_1346 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _146_1347 _146_1346))))
end))
end))
in (
# 2146 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1356 = (let _146_1354 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1353 = (let _146_1352 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_1351 = (let _146_1350 = (FStar_Syntax_Syntax.null_binder bin_op)
in (let _146_1349 = (let _146_1348 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1348)::[])
in (_146_1350)::_146_1349))
in (_146_1352)::_146_1351))
in (_146_1354)::_146_1353))
in (let _146_1355 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1356 _146_1355)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_binop expected_k)))
in (
# 2153 "FStar.TypeChecker.Tc.fst"
let wp_as_type = (
# 2154 "FStar.TypeChecker.Tc.fst"
let _57_2675 = (FStar_Syntax_Util.type_u ())
in (match (_57_2675) with
| (t, _57_2674) -> begin
(
# 2155 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1361 = (let _146_1359 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1358 = (let _146_1357 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1357)::[])
in (_146_1359)::_146_1358))
in (let _146_1360 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _146_1361 _146_1360)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (
# 2160 "FStar.TypeChecker.Tc.fst"
let close_wp = (
# 2161 "FStar.TypeChecker.Tc.fst"
let b = (let _146_1363 = (let _146_1362 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1362 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _146_1363))
in (
# 2162 "FStar.TypeChecker.Tc.fst"
let b_wp_a = (let _146_1367 = (let _146_1365 = (let _146_1364 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _146_1364))
in (_146_1365)::[])
in (let _146_1366 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1367 _146_1366)))
in (
# 2163 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1374 = (let _146_1372 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1371 = (let _146_1370 = (FStar_Syntax_Syntax.mk_binder b)
in (let _146_1369 = (let _146_1368 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_146_1368)::[])
in (_146_1370)::_146_1369))
in (_146_1372)::_146_1371))
in (let _146_1373 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1374 _146_1373)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (
# 2167 "FStar.TypeChecker.Tc.fst"
let assert_p = (
# 2168 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1383 = (let _146_1381 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1380 = (let _146_1379 = (let _146_1376 = (let _146_1375 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1375 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _146_1376))
in (let _146_1378 = (let _146_1377 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1377)::[])
in (_146_1379)::_146_1378))
in (_146_1381)::_146_1380))
in (let _146_1382 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1383 _146_1382)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (
# 2174 "FStar.TypeChecker.Tc.fst"
let assume_p = (
# 2175 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1392 = (let _146_1390 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1389 = (let _146_1388 = (let _146_1385 = (let _146_1384 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1384 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _146_1385))
in (let _146_1387 = (let _146_1386 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1386)::[])
in (_146_1388)::_146_1387))
in (_146_1390)::_146_1389))
in (let _146_1391 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1392 _146_1391)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (
# 2181 "FStar.TypeChecker.Tc.fst"
let null_wp = (
# 2182 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1395 = (let _146_1393 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1393)::[])
in (let _146_1394 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1395 _146_1394)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (
# 2186 "FStar.TypeChecker.Tc.fst"
let trivial_wp = (
# 2187 "FStar.TypeChecker.Tc.fst"
let _57_2691 = (FStar_Syntax_Util.type_u ())
in (match (_57_2691) with
| (t, _57_2690) -> begin
(
# 2188 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1400 = (let _146_1398 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1397 = (let _146_1396 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1396)::[])
in (_146_1398)::_146_1397))
in (let _146_1399 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _146_1400 _146_1399)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (
# 2194 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1401 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _146_1401))
in (
# 2195 "FStar.TypeChecker.Tc.fst"
let _57_2697 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_57_2697) with
| (univs, t) -> begin
(
# 2196 "FStar.TypeChecker.Tc.fst"
let _57_2713 = (match ((let _146_1403 = (let _146_1402 = (FStar_Syntax_Subst.compress t)
in _146_1402.FStar_Syntax_Syntax.n)
in (binders, _146_1403))) with
| ([], _57_2700) -> begin
([], t)
end
| (_57_2703, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _57_2710 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_2713) with
| (binders, signature) -> begin
(
# 2200 "FStar.TypeChecker.Tc.fst"
let close = (fun n ts -> (
# 2201 "FStar.TypeChecker.Tc.fst"
let ts = (let _146_1408 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _146_1408))
in (
# 2202 "FStar.TypeChecker.Tc.fst"
let _57_2718 = ()
in ts)))
in (
# 2204 "FStar.TypeChecker.Tc.fst"
let ed = (
# 2204 "FStar.TypeChecker.Tc.fst"
let _57_2720 = ed
in (let _146_1421 = (close 0 ret)
in (let _146_1420 = (close 1 bind_wp)
in (let _146_1419 = (close 1 bind_wlp)
in (let _146_1418 = (close 0 if_then_else)
in (let _146_1417 = (close 0 ite_wp)
in (let _146_1416 = (close 0 ite_wlp)
in (let _146_1415 = (close 0 wp_binop)
in (let _146_1414 = (close 0 wp_as_type)
in (let _146_1413 = (close 1 close_wp)
in (let _146_1412 = (close 0 assert_p)
in (let _146_1411 = (close 0 assume_p)
in (let _146_1410 = (close 0 null_wp)
in (let _146_1409 = (close 0 trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _57_2720.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2720.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _146_1421; FStar_Syntax_Syntax.bind_wp = _146_1420; FStar_Syntax_Syntax.bind_wlp = _146_1419; FStar_Syntax_Syntax.if_then_else = _146_1418; FStar_Syntax_Syntax.ite_wp = _146_1417; FStar_Syntax_Syntax.ite_wlp = _146_1416; FStar_Syntax_Syntax.wp_binop = _146_1415; FStar_Syntax_Syntax.wp_as_type = _146_1414; FStar_Syntax_Syntax.close_wp = _146_1413; FStar_Syntax_Syntax.assert_p = _146_1412; FStar_Syntax_Syntax.assume_p = _146_1411; FStar_Syntax_Syntax.null_wp = _146_1410; FStar_Syntax_Syntax.trivial = _146_1409}))))))))))))))
in (
# 2222 "FStar.TypeChecker.Tc.fst"
let _57_2723 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1422 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _146_1422))
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

# 2226 "FStar.TypeChecker.Tc.fst"
let tc_lex_t = (fun env ses quals lids -> (
# 2233 "FStar.TypeChecker.Tc.fst"
let _57_2729 = ()
in (
# 2234 "FStar.TypeChecker.Tc.fst"
let _57_2737 = ()
in (match (ses) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _57_2766, _57_2768, [], r)::FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _57_2757, r1)::FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _57_2746, r2)::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(
# 2249 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (
# 2250 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (
# 2251 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (
# 2252 "FStar.TypeChecker.Tc.fst"
let tc = FStar_Syntax_Syntax.Sig_inductive_typ ((lex_t, (u)::[], [], t, [], (FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[], [], r))
in (
# 2254 "FStar.TypeChecker.Tc.fst"
let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (
# 2255 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (let _146_1430 = (let _146_1429 = (let _146_1428 = (let _146_1427 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _146_1427 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1428, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1429))
in (FStar_Syntax_Syntax.mk _146_1430 None r1))
in (
# 2256 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (
# 2257 "FStar.TypeChecker.Tc.fst"
let dc_lextop = FStar_Syntax_Syntax.Sig_datacon ((lex_top, (utop)::[], lex_top_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r1))
in (
# 2259 "FStar.TypeChecker.Tc.fst"
let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 2260 "FStar.TypeChecker.Tc.fst"
let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 2261 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (
# 2262 "FStar.TypeChecker.Tc.fst"
let a = (let _146_1431 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1431))
in (
# 2263 "FStar.TypeChecker.Tc.fst"
let hd = (let _146_1432 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1432))
in (
# 2264 "FStar.TypeChecker.Tc.fst"
let tl = (let _146_1437 = (let _146_1436 = (let _146_1435 = (let _146_1434 = (let _146_1433 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _146_1433 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1434, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1435))
in (FStar_Syntax_Syntax.mk _146_1436 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1437))
in (
# 2265 "FStar.TypeChecker.Tc.fst"
let res = (let _146_1441 = (let _146_1440 = (let _146_1439 = (let _146_1438 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _146_1438 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1439, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1440))
in (FStar_Syntax_Syntax.mk _146_1441 None r2))
in (let _146_1442 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _146_1442))))))
in (
# 2267 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (
# 2268 "FStar.TypeChecker.Tc.fst"
let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _146_1444 = (let _146_1443 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _146_1443))
in FStar_Syntax_Syntax.Sig_bundle (_146_1444)))))))))))))))
end
| _57_2792 -> begin
(let _146_1446 = (let _146_1445 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _146_1445))
in (FStar_All.failwith _146_1446))
end))))

# 2274 "FStar.TypeChecker.Tc.fst"
let tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (
# 2275 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2276 "FStar.TypeChecker.Tc.fst"
let _57_2802 = (FStar_Syntax_Util.type_u ())
in (match (_57_2802) with
| (k, _57_2801) -> begin
(
# 2277 "FStar.TypeChecker.Tc.fst"
let phi = (let _146_1457 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _146_1457 (norm env)))
in (
# 2278 "FStar.TypeChecker.Tc.fst"
let _57_2804 = (FStar_TypeChecker_Util.check_uvars r phi)
in FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))))
end))))

# 2281 "FStar.TypeChecker.Tc.fst"
let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (
# 2344 "FStar.TypeChecker.Tc.fst"
let warn_positivity = (fun l r -> (let _146_1471 = (let _146_1470 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _146_1470))
in (FStar_TypeChecker_Errors.diag r _146_1471)))
in (
# 2346 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2349 "FStar.TypeChecker.Tc.fst"
let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(
# 2354 "FStar.TypeChecker.Tc.fst"
let _57_2827 = ()
in (
# 2355 "FStar.TypeChecker.Tc.fst"
let _57_2829 = (warn_positivity tc r)
in (
# 2356 "FStar.TypeChecker.Tc.fst"
let _57_2833 = (FStar_Syntax_Subst.open_term tps k)
in (match (_57_2833) with
| (tps, k) -> begin
(
# 2357 "FStar.TypeChecker.Tc.fst"
let _57_2837 = (tc_tparams env tps)
in (match (_57_2837) with
| (tps, env_tps, us) -> begin
(
# 2358 "FStar.TypeChecker.Tc.fst"
let _57_2840 = (FStar_Syntax_Util.arrow_formals k)
in (match (_57_2840) with
| (indices, t) -> begin
(
# 2359 "FStar.TypeChecker.Tc.fst"
let _57_2844 = (tc_tparams env_tps indices)
in (match (_57_2844) with
| (indices, env', us') -> begin
(
# 2360 "FStar.TypeChecker.Tc.fst"
let _57_2848 = (tc_trivial_guard env' t)
in (match (_57_2848) with
| (t, _57_2847) -> begin
(
# 2361 "FStar.TypeChecker.Tc.fst"
let k = (let _146_1476 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _146_1476))
in (
# 2362 "FStar.TypeChecker.Tc.fst"
let _57_2852 = (FStar_Syntax_Util.type_u ())
in (match (_57_2852) with
| (t_type, u) -> begin
(
# 2363 "FStar.TypeChecker.Tc.fst"
let _57_2853 = (let _146_1477 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _146_1477))
in (
# 2365 "FStar.TypeChecker.Tc.fst"
let t_tc = (let _146_1478 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _146_1478))
in (
# 2366 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 2367 "FStar.TypeChecker.Tc.fst"
let k = (FStar_Syntax_Subst.close tps k)
in (
# 2368 "FStar.TypeChecker.Tc.fst"
let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _146_1479 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) ([], t_tc))
in (_146_1479, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u)))))))
end)))
end))
end))
end))
end))
end))))
end
| _57_2860 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 2375 "FStar.TypeChecker.Tc.fst"
let positive_if_pure = (fun _57_2862 l -> ())
in (
# 2378 "FStar.TypeChecker.Tc.fst"
let tc_data = (fun env tcs _57_6 -> (match (_57_6) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(
# 2380 "FStar.TypeChecker.Tc.fst"
let _57_2879 = ()
in (
# 2382 "FStar.TypeChecker.Tc.fst"
let _57_2914 = (
# 2383 "FStar.TypeChecker.Tc.fst"
let tps_u_opt = (FStar_Util.find_map tcs (fun _57_2883 -> (match (_57_2883) with
| (se, u_tc) -> begin
if (let _146_1492 = (let _146_1491 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _146_1491))
in (FStar_Ident.lid_equals tc_lid _146_1492)) then begin
(
# 2385 "FStar.TypeChecker.Tc.fst"
let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2885, _57_2887, tps, _57_2890, _57_2892, _57_2894, _57_2896, _57_2898) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _57_2904 -> (match (_57_2904) with
| (x, _57_2903) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _57_2906 -> begin
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
in (match (_57_2914) with
| (tps, u_tc) -> begin
(
# 2398 "FStar.TypeChecker.Tc.fst"
let _57_2934 = (match ((let _146_1494 = (FStar_Syntax_Subst.compress t)
in _146_1494.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(
# 2403 "FStar.TypeChecker.Tc.fst"
let _57_2922 = (FStar_Util.first_N ntps bs)
in (match (_57_2922) with
| (_57_2920, bs') -> begin
(
# 2404 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (
# 2405 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _57_2928 -> (match (_57_2928) with
| (x, _57_2927) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _146_1497 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _146_1497))))
end))
end
| _57_2931 -> begin
([], t)
end)
in (match (_57_2934) with
| (arguments, result) -> begin
(
# 2409 "FStar.TypeChecker.Tc.fst"
let _57_2935 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1500 = (FStar_Syntax_Print.lid_to_string c)
in (let _146_1499 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _146_1498 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _146_1500 _146_1499 _146_1498))))
end else begin
()
end
in (
# 2415 "FStar.TypeChecker.Tc.fst"
let _57_2940 = (tc_tparams env arguments)
in (match (_57_2940) with
| (arguments, env', us) -> begin
(
# 2416 "FStar.TypeChecker.Tc.fst"
let _57_2944 = (tc_trivial_guard env' result)
in (match (_57_2944) with
| (result, _57_2943) -> begin
(
# 2417 "FStar.TypeChecker.Tc.fst"
let _57_2948 = (FStar_Syntax_Util.head_and_args result)
in (match (_57_2948) with
| (head, _57_2947) -> begin
(
# 2418 "FStar.TypeChecker.Tc.fst"
let _57_2953 = (match ((let _146_1501 = (FStar_Syntax_Subst.compress head)
in _146_1501.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _57_2952 -> begin
(let _146_1505 = (let _146_1504 = (let _146_1503 = (let _146_1502 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _146_1502))
in (_146_1503, r))
in FStar_Syntax_Syntax.Error (_146_1504))
in (Prims.raise _146_1505))
end)
in (
# 2421 "FStar.TypeChecker.Tc.fst"
let g = (FStar_List.fold_left2 (fun g _57_2959 u_x -> (match (_57_2959) with
| (x, _57_2958) -> begin
(
# 2422 "FStar.TypeChecker.Tc.fst"
let _57_2961 = ()
in (let _146_1509 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _146_1509)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (
# 2428 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1513 = (let _146_1511 = (FStar_All.pipe_right tps (FStar_List.map (fun _57_2967 -> (match (_57_2967) with
| (x, _57_2966) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _146_1511 arguments))
in (let _146_1512 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _146_1513 _146_1512)))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _57_2970 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 2436 "FStar.TypeChecker.Tc.fst"
let generalize_and_inst_within = (fun env g tcs datas -> (
# 2437 "FStar.TypeChecker.Tc.fst"
let _57_2976 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2438 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_7 -> (match (_57_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2980, _57_2982, tps, k, _57_2986, _57_2988, _57_2990, _57_2992) -> begin
(let _146_1524 = (let _146_1523 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _146_1523))
in (FStar_Syntax_Syntax.null_binder _146_1524))
end
| _57_2996 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2441 "FStar.TypeChecker.Tc.fst"
let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _57_8 -> (match (_57_8) with
| FStar_Syntax_Syntax.Sig_datacon (_57_3000, _57_3002, t, _57_3005, _57_3007, _57_3009, _57_3011, _57_3013) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _57_3017 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2444 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1526 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _146_1526))
in (
# 2445 "FStar.TypeChecker.Tc.fst"
let _57_3020 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1527 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _146_1527))
end else begin
()
end
in (
# 2446 "FStar.TypeChecker.Tc.fst"
let _57_3024 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_57_3024) with
| (uvs, t) -> begin
(
# 2447 "FStar.TypeChecker.Tc.fst"
let _57_3026 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1531 = (let _146_1529 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _146_1529 (FStar_String.concat ", ")))
in (let _146_1530 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _146_1531 _146_1530)))
end else begin
()
end
in (
# 2450 "FStar.TypeChecker.Tc.fst"
let _57_3030 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_57_3030) with
| (uvs, t) -> begin
(
# 2451 "FStar.TypeChecker.Tc.fst"
let _57_3034 = (FStar_Syntax_Util.arrow_formals t)
in (match (_57_3034) with
| (args, _57_3033) -> begin
(
# 2452 "FStar.TypeChecker.Tc.fst"
let _57_3037 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_57_3037) with
| (tc_types, data_types) -> begin
(
# 2453 "FStar.TypeChecker.Tc.fst"
let tcs = (FStar_List.map2 (fun _57_3041 se -> (match (_57_3041) with
| (x, _57_3040) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3045, tps, _57_3048, mutuals, datas, quals, r) -> begin
(
# 2455 "FStar.TypeChecker.Tc.fst"
let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (
# 2456 "FStar.TypeChecker.Tc.fst"
let _57_3071 = (match ((let _146_1534 = (FStar_Syntax_Subst.compress ty)
in _146_1534.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 2458 "FStar.TypeChecker.Tc.fst"
let _57_3062 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_57_3062) with
| (tps, rest) -> begin
(
# 2459 "FStar.TypeChecker.Tc.fst"
let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _57_3065 -> begin
(let _146_1535 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _146_1535 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _57_3068 -> begin
([], ty)
end)
in (match (_57_3071) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _57_3073 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (
# 2469 "FStar.TypeChecker.Tc.fst"
let datas = (match (uvs) with
| [] -> begin
datas
end
| _57_3077 -> begin
(
# 2472 "FStar.TypeChecker.Tc.fst"
let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _146_1536 -> FStar_Syntax_Syntax.U_name (_146_1536))))
in (
# 2473 "FStar.TypeChecker.Tc.fst"
let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_9 -> (match (_57_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3082, _57_3084, _57_3086, _57_3088, _57_3090, _57_3092, _57_3094) -> begin
(tc, uvs_universes)
end
| _57_3098 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _57_3103 d -> (match (_57_3103) with
| (t, _57_3102) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _57_3107, _57_3109, tc, ntps, quals, mutuals, r) -> begin
(
# 2477 "FStar.TypeChecker.Tc.fst"
let ty = (let _146_1540 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _146_1540 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _57_3119 -> begin
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
# 2483 "FStar.TypeChecker.Tc.fst"
let _57_3129 = (FStar_All.pipe_right ses (FStar_List.partition (fun _57_10 -> (match (_57_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_3123) -> begin
true
end
| _57_3126 -> begin
false
end))))
in (match (_57_3129) with
| (tys, datas) -> begin
(
# 2485 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2488 "FStar.TypeChecker.Tc.fst"
let _57_3146 = (FStar_List.fold_right (fun tc _57_3135 -> (match (_57_3135) with
| (env, all_tcs, g) -> begin
(
# 2489 "FStar.TypeChecker.Tc.fst"
let _57_3139 = (tc_tycon env tc)
in (match (_57_3139) with
| (env, tc, tc_u) -> begin
(
# 2490 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (
# 2491 "FStar.TypeChecker.Tc.fst"
let _57_3141 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1544 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _146_1544))
end else begin
()
end
in (let _146_1545 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _146_1545))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_3146) with
| (env, tcs, g) -> begin
(
# 2498 "FStar.TypeChecker.Tc.fst"
let _57_3156 = (FStar_List.fold_right (fun se _57_3150 -> (match (_57_3150) with
| (datas, g) -> begin
(
# 2499 "FStar.TypeChecker.Tc.fst"
let _57_3153 = (tc_data env tcs se)
in (match (_57_3153) with
| (data, g') -> begin
(let _146_1548 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _146_1548))
end))
end)) datas ([], g))
in (match (_57_3156) with
| (datas, g) -> begin
(
# 2504 "FStar.TypeChecker.Tc.fst"
let _57_3159 = (let _146_1549 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _146_1549 datas))
in (match (_57_3159) with
| (tcs, datas) -> begin
(
# 2505 "FStar.TypeChecker.Tc.fst"
let sig_bndle = (let _146_1551 = (let _146_1550 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _146_1550))
in FStar_Syntax_Syntax.Sig_bundle (_146_1551))
in (
# 2509 "FStar.TypeChecker.Tc.fst"
let split_arrow = (fun t -> (match ((let _146_1554 = (FStar_Syntax_Subst.compress t)
in _146_1554.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(bs, c)
end
| _57_3168 -> begin
(FStar_All.failwith "Impossible!")
end))
in (
# 2515 "FStar.TypeChecker.Tc.fst"
let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (_57_3172, _57_3174, t, _57_3177, _57_3179, _57_3181, _57_3183, _57_3185) -> begin
t
end
| _57_3189 -> begin
(FStar_All.failwith "Impossible!")
end))
in (
# 2521 "FStar.TypeChecker.Tc.fst"
let subst_in_binders = (fun bs s -> (match (bs) with
| [] -> begin
[]
end
| _57_3195 -> begin
(let _146_1564 = (let _146_1563 = (let _146_1562 = (let _146_1561 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow bs _146_1561))
in (FStar_Syntax_Subst.subst s _146_1562))
in (split_arrow _146_1563))
in (Prims.fst _146_1564))
end))
in (
# 2527 "FStar.TypeChecker.Tc.fst"
let dr = FStar_Range.dummyRange
in (
# 2530 "FStar.TypeChecker.Tc.fst"
let us = (
# 2531 "FStar.TypeChecker.Tc.fst"
let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_3199, us, _57_3202, _57_3204, _57_3206, _57_3208, _57_3210, _57_3212) -> begin
us
end
| _57_3216 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 2536 "FStar.TypeChecker.Tc.fst"
let _57_3220 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_57_3220) with
| (usubst, us) -> begin
(
# 2546 "FStar.TypeChecker.Tc.fst"
let haseq_ty = (fun acc ty -> (
# 2547 "FStar.TypeChecker.Tc.fst"
let _57_3244 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _57_3226, bs, t, _57_3230, d_lids, _57_3233, _57_3235) -> begin
(lid, bs, t, d_lids)
end
| _57_3239 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_57_3244) with
| (lid, bs, t, d_lids) -> begin
(
# 2554 "FStar.TypeChecker.Tc.fst"
let bs = (subst_in_binders bs usubst)
in (
# 2556 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.subst usubst t)
in (
# 2558 "FStar.TypeChecker.Tc.fst"
let _57_3249 = (FStar_Syntax_Subst.open_term bs t)
in (match (_57_3249) with
| (bs, t) -> begin
(
# 2560 "FStar.TypeChecker.Tc.fst"
let ibs = (match ((let _146_1569 = (FStar_Syntax_Subst.compress t)
in _146_1569.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _57_3252) -> begin
ibs
end
| _57_3256 -> begin
[]
end)
in (
# 2566 "FStar.TypeChecker.Tc.fst"
let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (
# 2568 "FStar.TypeChecker.Tc.fst"
let ind = (let _146_1572 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _146_1571 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_1572 _146_1571)))
in (
# 2570 "FStar.TypeChecker.Tc.fst"
let ind = (let _146_1575 = (FStar_List.map (fun _57_3264 -> (match (_57_3264) with
| (bv, _57_3263) -> begin
(let _146_1574 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_Syntax_Syntax.as_arg _146_1574))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _146_1575 None dr))
in (
# 2572 "FStar.TypeChecker.Tc.fst"
let ind = (let _146_1578 = (FStar_List.map (fun _57_3269 -> (match (_57_3269) with
| (bv, _57_3268) -> begin
(let _146_1577 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_Syntax_Syntax.as_arg _146_1577))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _146_1578 None dr))
in (
# 2574 "FStar.TypeChecker.Tc.fst"
let haseq_ind = (let _146_1580 = (let _146_1579 = (FStar_Syntax_Syntax.as_arg ind)
in (_146_1579)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _146_1580 None dr))
in (
# 2576 "FStar.TypeChecker.Tc.fst"
let haseq_bs = (FStar_List.fold_left (fun t b -> (let _146_1586 = (let _146_1585 = (let _146_1584 = (let _146_1583 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg _146_1583))
in (_146_1584)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _146_1585 None dr))
in (FStar_Syntax_Util.mk_conj t _146_1586))) FStar_Syntax_Util.t_true bs)
in (
# 2578 "FStar.TypeChecker.Tc.fst"
let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (
# 2580 "FStar.TypeChecker.Tc.fst"
let fml = (FStar_List.fold_right (fun b t -> (let _146_1592 = (let _146_1591 = (let _146_1590 = (let _146_1589 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs ((b)::[]) _146_1589 None))
in (FStar_Syntax_Syntax.as_arg _146_1590))
in (_146_1591)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _146_1592 None dr))) ibs fml)
in (
# 2582 "FStar.TypeChecker.Tc.fst"
let fml = (FStar_List.fold_right (fun b t -> (let _146_1598 = (let _146_1597 = (let _146_1596 = (let _146_1595 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs ((b)::[]) _146_1595 None))
in (FStar_Syntax_Syntax.as_arg _146_1596))
in (_146_1597)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _146_1598 None dr))) bs fml)
in (
# 2586 "FStar.TypeChecker.Tc.fst"
let guard = (let _146_1599 = (FStar_Syntax_Util.mk_conj haseq_bs haseq_ind)
in (FStar_Syntax_Util.mk_conj _146_1599 fml))
in (
# 2590 "FStar.TypeChecker.Tc.fst"
let _57_3287 = acc
in (match (_57_3287) with
| (l_axioms, env, guard', cond') -> begin
(
# 2594 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_binders env bs)
in (
# 2595 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (
# 2599 "FStar.TypeChecker.Tc.fst"
let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_57_3292, _57_3294, _57_3296, t_lid, _57_3299, _57_3301, _57_3303, _57_3305) -> begin
(t_lid = lid)
end
| _57_3309 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (
# 2609 "FStar.TypeChecker.Tc.fst"
let haseq_data = (fun acc data -> (
# 2610 "FStar.TypeChecker.Tc.fst"
let dt = (datacon_typ data)
in (
# 2612 "FStar.TypeChecker.Tc.fst"
let dt = (FStar_Syntax_Subst.subst usubst dt)
in (match ((let _146_1605 = (FStar_Syntax_Subst.compress dt)
in _146_1605.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _57_3318) -> begin
(
# 2616 "FStar.TypeChecker.Tc.fst"
let dbs = (let _146_1606 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _146_1606))
in (
# 2618 "FStar.TypeChecker.Tc.fst"
let dbs = (let _146_1607 = (FStar_Syntax_Subst.opening_of_binders bs)
in (subst_in_binders dbs _146_1607))
in (
# 2620 "FStar.TypeChecker.Tc.fst"
let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (
# 2622 "FStar.TypeChecker.Tc.fst"
let cond = (FStar_List.fold_left (fun t b -> (let _146_1612 = (let _146_1611 = (let _146_1610 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_146_1610)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _146_1611 None dr))
in (FStar_Syntax_Util.mk_conj t _146_1612))) FStar_Syntax_Util.t_true dbs)
in (
# 2624 "FStar.TypeChecker.Tc.fst"
let _57_3329 = acc
in (match (_57_3329) with
| (env, cond') -> begin
(let _146_1614 = (FStar_TypeChecker_Env.push_binders env dbs)
in (let _146_1613 = (FStar_Syntax_Util.mk_conj cond' cond)
in (_146_1614, _146_1613)))
end))))))
end
| _57_3331 -> begin
acc
end))))
in (
# 2630 "FStar.TypeChecker.Tc.fst"
let _57_3334 = (FStar_List.fold_left haseq_data (env, FStar_Syntax_Util.t_true) t_datas)
in (match (_57_3334) with
| (env, cond) -> begin
(
# 2633 "FStar.TypeChecker.Tc.fst"
let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (let _146_1616 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _146_1615 = (FStar_Syntax_Util.mk_conj cond' cond)
in ((FStar_List.append l_axioms (((axiom_lid, fml))::[])), env, _146_1616, _146_1615))))
end))))))
end)))))))))))))
end))))
end)))
in if true then begin
(
# 2639 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (
# 2640 "FStar.TypeChecker.Tc.fst"
let _57_3337 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (
# 2641 "FStar.TypeChecker.Tc.fst"
let _57_3339 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (
# 2642 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (
# 2644 "FStar.TypeChecker.Tc.fst"
let _57_3346 = (FStar_List.fold_left haseq_ty ([], env, FStar_Syntax_Util.t_true, FStar_Syntax_Util.t_true) tcs)
in (match (_57_3346) with
| (axioms, env, guard, cond) -> begin
(
# 2646 "FStar.TypeChecker.Tc.fst"
let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (
# 2648 "FStar.TypeChecker.Tc.fst"
let _57_3351 = (tc_trivial_guard env phi)
in (match (_57_3351) with
| (phi, _57_3350) -> begin
(
# 2650 "FStar.TypeChecker.Tc.fst"
let debug_lid = (match ((FStar_List.hd tcs)) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _57_3354, _57_3356, _57_3358, _57_3360, _57_3362, _57_3364, _57_3366) -> begin
lid
end
| _57_3370 -> begin
(FStar_All.failwith "Impossible!")
end)
in (
# 2656 "FStar.TypeChecker.Tc.fst"
let _57_3372 = (FStar_Util.print1 "Checking haseq soundness for %s:\n" debug_lid.FStar_Ident.str)
in (
# 2657 "FStar.TypeChecker.Tc.fst"
let _57_3374 = (let _146_1617 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _146_1617))
in (
# 2659 "FStar.TypeChecker.Tc.fst"
let _57_3376 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in (
# 2663 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_univ_vars env0 us)
in (
# 2664 "FStar.TypeChecker.Tc.fst"
let ses = (FStar_List.fold_left (fun l _57_3382 -> (match (_57_3382) with
| (lid, fml) -> begin
(
# 2665 "FStar.TypeChecker.Tc.fst"
let _57_3383 = (FStar_Util.print1 "Checking tc_assume for axiom:\n" lid.FStar_Ident.str)
in (
# 2666 "FStar.TypeChecker.Tc.fst"
let se = (tc_assume env lid fml [] dr)
in (FStar_List.append l ((se)::[]))))
end)) [] axioms)
in (let _146_1621 = (let _146_1620 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append (FStar_List.append tcs datas) ses), quals, lids, _146_1620))
in FStar_Syntax_Syntax.Sig_bundle (_146_1621))))))))
end)))
end))))))
end else begin
sig_bndle
end)
end))))))))
end))
end))
end)))
end)))))))))

# 2673 "FStar.TypeChecker.Tc.fst"
let rec tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.env) = (fun env se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(
# 2686 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2687 "FStar.TypeChecker.Tc.fst"
let se = (tc_lex_t env ses quals lids)
in (let _146_1626 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _146_1626))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(
# 2691 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2692 "FStar.TypeChecker.Tc.fst"
let se = (tc_inductive env ses quals lids)
in (let _146_1627 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _146_1627))))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(
# 2696 "FStar.TypeChecker.Tc.fst"
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
# 2702 "FStar.TypeChecker.Tc.fst"
let _57_3424 = (set_options FStar_Options.Set o)
in (se, env))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(
# 2705 "FStar.TypeChecker.Tc.fst"
let _57_3428 = (let _146_1632 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _146_1632 Prims.ignore))
in (
# 2706 "FStar.TypeChecker.Tc.fst"
let _57_3433 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (
# 2709 "FStar.TypeChecker.Tc.fst"
let _57_3435 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (se, env))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(
# 2714 "FStar.TypeChecker.Tc.fst"
let ne = (tc_eff_decl env ne ForFree)
in (
# 2716 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (
# 2717 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(
# 2721 "FStar.TypeChecker.Tc.fst"
let ne = (tc_eff_decl env ne NotForFree)
in (
# 2722 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (
# 2723 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(
# 2727 "FStar.TypeChecker.Tc.fst"
let _57_3457 = (let _146_1633 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _146_1633))
in (match (_57_3457) with
| (a, wp_a_src) -> begin
(
# 2728 "FStar.TypeChecker.Tc.fst"
let _57_3460 = (let _146_1634 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _146_1634))
in (match (_57_3460) with
| (b, wp_b_tgt) -> begin
(
# 2729 "FStar.TypeChecker.Tc.fst"
let wp_a_tgt = (let _146_1638 = (let _146_1637 = (let _146_1636 = (let _146_1635 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _146_1635))
in FStar_Syntax_Syntax.NT (_146_1636))
in (_146_1637)::[])
in (FStar_Syntax_Subst.subst _146_1638 wp_b_tgt))
in (
# 2730 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1643 = (let _146_1641 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1640 = (let _146_1639 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_146_1639)::[])
in (_146_1641)::_146_1640))
in (let _146_1642 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _146_1643 _146_1642)))
in (
# 2731 "FStar.TypeChecker.Tc.fst"
let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (
# 2732 "FStar.TypeChecker.Tc.fst"
let sub = (
# 2732 "FStar.TypeChecker.Tc.fst"
let _57_3464 = sub
in {FStar_Syntax_Syntax.source = _57_3464.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _57_3464.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
in (
# 2733 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect ((sub, r))
in (
# 2734 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(
# 2738 "FStar.TypeChecker.Tc.fst"
let _57_3477 = ()
in (
# 2739 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2740 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2741 "FStar.TypeChecker.Tc.fst"
let _57_3483 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_57_3483) with
| (tps, c) -> begin
(
# 2742 "FStar.TypeChecker.Tc.fst"
let _57_3487 = (tc_tparams env tps)
in (match (_57_3487) with
| (tps, env, us) -> begin
(
# 2743 "FStar.TypeChecker.Tc.fst"
let _57_3491 = (tc_comp env c)
in (match (_57_3491) with
| (c, u, g) -> begin
(
# 2744 "FStar.TypeChecker.Tc.fst"
let _57_3492 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2745 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 2746 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.close_comp tps c)
in (
# 2747 "FStar.TypeChecker.Tc.fst"
let _57_3498 = (let _146_1644 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _146_1644))
in (match (_57_3498) with
| (uvs, t) -> begin
(
# 2748 "FStar.TypeChecker.Tc.fst"
let _57_3517 = (match ((let _146_1646 = (let _146_1645 = (FStar_Syntax_Subst.compress t)
in _146_1645.FStar_Syntax_Syntax.n)
in (tps, _146_1646))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_57_3501, c)) -> begin
([], c)
end
| (_57_3507, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _57_3514 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_3517) with
| (tps, c) -> begin
(
# 2752 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_effect_abbrev ((lid, uvs, tps, c, tags, r))
in (
# 2753 "FStar.TypeChecker.Tc.fst"
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
# 2757 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2758 "FStar.TypeChecker.Tc.fst"
let _57_3528 = ()
in (
# 2759 "FStar.TypeChecker.Tc.fst"
let _57_3532 = (let _146_1648 = (let _146_1647 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _146_1647))
in (check_and_gen env t _146_1648))
in (match (_57_3532) with
| (uvs, t) -> begin
(
# 2760 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (
# 2761 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(
# 2765 "FStar.TypeChecker.Tc.fst"
let se = (tc_assume env lid phi quals r)
in (
# 2766 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(
# 2770 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2771 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (
# 2772 "FStar.TypeChecker.Tc.fst"
let _57_3552 = (tc_term env e)
in (match (_57_3552) with
| (e, c, g1) -> begin
(
# 2773 "FStar.TypeChecker.Tc.fst"
let _57_3557 = (let _146_1652 = (let _146_1649 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_146_1649))
in (let _146_1651 = (let _146_1650 = (c.FStar_Syntax_Syntax.comp ())
in (e, _146_1650))
in (check_expected_effect env _146_1652 _146_1651)))
in (match (_57_3557) with
| (e, _57_3555, g) -> begin
(
# 2774 "FStar.TypeChecker.Tc.fst"
let _57_3558 = (let _146_1653 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _146_1653))
in (
# 2775 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, r))
in (
# 2776 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(
# 2780 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2781 "FStar.TypeChecker.Tc.fst"
let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
if (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q')) then begin
Some (q)
end else begin
(let _146_1665 = (let _146_1664 = (let _146_1663 = (let _146_1662 = (FStar_Syntax_Print.lid_to_string l)
in (let _146_1661 = (FStar_Syntax_Print.quals_to_string q)
in (let _146_1660 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _146_1662 _146_1661 _146_1660))))
in (_146_1663, r))
in FStar_Syntax_Syntax.Error (_146_1664))
in (Prims.raise _146_1665))
end
end))
in (
# 2795 "FStar.TypeChecker.Tc.fst"
let _57_3602 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _57_3579 lb -> (match (_57_3579) with
| (gen, lbs, quals_opt) -> begin
(
# 2796 "FStar.TypeChecker.Tc.fst"
let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2797 "FStar.TypeChecker.Tc.fst"
let _57_3598 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(
# 2801 "FStar.TypeChecker.Tc.fst"
let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (
# 2802 "FStar.TypeChecker.Tc.fst"
let _57_3593 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _57_3592 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _146_1668 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _146_1668, quals_opt))))
end)
in (match (_57_3598) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_57_3602) with
| (should_generalize, lbs', quals_opt) -> begin
(
# 2811 "FStar.TypeChecker.Tc.fst"
let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _57_11 -> (match (_57_11) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _57_3611 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (
# 2818 "FStar.TypeChecker.Tc.fst"
let lbs' = (FStar_List.rev lbs')
in (
# 2821 "FStar.TypeChecker.Tc.fst"
let e = (let _146_1672 = (let _146_1671 = (let _146_1670 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _146_1670))
in FStar_Syntax_Syntax.Tm_let (_146_1671))
in (FStar_Syntax_Syntax.mk _146_1672 None r))
in (
# 2824 "FStar.TypeChecker.Tc.fst"
let _57_3645 = (match ((tc_maybe_toplevel_term (
# 2824 "FStar.TypeChecker.Tc.fst"
let _57_3615 = env
in {FStar_TypeChecker_Env.solver = _57_3615.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3615.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3615.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3615.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3615.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3615.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3615.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3615.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3615.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3615.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3615.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _57_3615.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _57_3615.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3615.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3615.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3615.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3615.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3615.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3615.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _57_3622; FStar_Syntax_Syntax.pos = _57_3620; FStar_Syntax_Syntax.vars = _57_3618}, _57_3629, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(
# 2827 "FStar.TypeChecker.Tc.fst"
let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_57_3633, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _57_3639 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _57_3642 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_57_3645) with
| (se, lbs) -> begin
(
# 2834 "FStar.TypeChecker.Tc.fst"
let _57_3651 = if (log env) then begin
(let _146_1680 = (let _146_1679 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 2836 "FStar.TypeChecker.Tc.fst"
let should_log = (match ((let _146_1676 = (let _146_1675 = (let _146_1674 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _146_1674.FStar_Syntax_Syntax.fv_name)
in _146_1675.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _146_1676))) with
| None -> begin
true
end
| _57_3649 -> begin
false
end)
in if should_log then begin
(let _146_1678 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _146_1677 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _146_1678 _146_1677)))
end else begin
""
end))))
in (FStar_All.pipe_right _146_1679 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _146_1680))
end else begin
()
end
in (
# 2843 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end))))
end))

# 2847 "FStar.TypeChecker.Tc.fst"
let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (
# 2871 "FStar.TypeChecker.Tc.fst"
let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _57_12 -> (match (_57_12) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _57_3661 -> begin
false
end)))))
in (
# 2872 "FStar.TypeChecker.Tc.fst"
let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _57_3671 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_57_3673) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _57_3684, _57_3686) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _57_3692 -> (match (_57_3692) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _57_3698, _57_3700, quals, r) -> begin
(
# 2886 "FStar.TypeChecker.Tc.fst"
let dec = (let _146_1696 = (let _146_1695 = (let _146_1694 = (let _146_1693 = (let _146_1692 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _146_1692))
in FStar_Syntax_Syntax.Tm_arrow (_146_1693))
in (FStar_Syntax_Syntax.mk _146_1694 None r))
in (l, us, _146_1695, (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_146_1696))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _57_3710, _57_3712, _57_3714, _57_3716, r) -> begin
(
# 2889 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _57_3722 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_57_3724, _57_3726, quals, _57_3729) -> begin
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
| _57_3748 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_57_3750) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _57_3769, _57_3771, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(
# 2920 "FStar.TypeChecker.Tc.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2921 "FStar.TypeChecker.Tc.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))) then begin
([], hidden)
end else begin
(
# 2924 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::[], (FStar_Ident.range_of_lid lid)))
in ((dec)::[], (lid)::hidden))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (is_abstract quals) then begin
(let _146_1703 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _146_1702 = (let _146_1701 = (let _146_1700 = (let _146_1699 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _146_1699.FStar_Syntax_Syntax.fv_name)
in _146_1700.FStar_Syntax_Syntax.v)
in (_146_1701, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_146_1702)))))
in (_146_1703, hidden))
end else begin
((se)::[], hidden)
end
end))))

# 2933 "FStar.TypeChecker.Tc.fst"
let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (
# 2934 "FStar.TypeChecker.Tc.fst"
let _57_3810 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _57_3791 se -> (match (_57_3791) with
| (ses, exports, env, hidden) -> begin
(
# 2936 "FStar.TypeChecker.Tc.fst"
let _57_3793 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1710 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _146_1710))
end else begin
()
end
in (
# 2939 "FStar.TypeChecker.Tc.fst"
let _57_3797 = (tc_decl env se)
in (match (_57_3797) with
| (se, env) -> begin
(
# 2941 "FStar.TypeChecker.Tc.fst"
let _57_3798 = if ((FStar_ST.read FStar_Options.log_types) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _146_1711 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _146_1711))
end else begin
()
end
in (
# 2944 "FStar.TypeChecker.Tc.fst"
let _57_3800 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (
# 2946 "FStar.TypeChecker.Tc.fst"
let _57_3804 = (for_export hidden se)
in (match (_57_3804) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_57_3810) with
| (ses, exports, env, _57_3809) -> begin
(let _146_1712 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _146_1712, env))
end)))

# 2951 "FStar.TypeChecker.Tc.fst"
let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2952 "FStar.TypeChecker.Tc.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 2953 "FStar.TypeChecker.Tc.fst"
let msg = (Prims.strcat "Internals for " name)
in (
# 2954 "FStar.TypeChecker.Tc.fst"
let env = (
# 2954 "FStar.TypeChecker.Tc.fst"
let _57_3815 = env
in (let _146_1717 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _57_3815.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3815.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3815.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3815.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3815.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3815.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3815.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3815.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3815.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3815.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3815.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3815.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3815.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_3815.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_3815.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3815.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _146_1717; FStar_TypeChecker_Env.type_of = _57_3815.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3815.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3815.FStar_TypeChecker_Env.use_bv_sorts}))
in (
# 2955 "FStar.TypeChecker.Tc.fst"
let _57_3818 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (
# 2956 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (
# 2957 "FStar.TypeChecker.Tc.fst"
let _57_3824 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_57_3824) with
| (ses, exports, env) -> begin
((
# 2958 "FStar.TypeChecker.Tc.fst"
let _57_3825 = modul
in {FStar_Syntax_Syntax.name = _57_3825.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _57_3825.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3825.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))

# 2960 "FStar.TypeChecker.Tc.fst"
let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (
# 2961 "FStar.TypeChecker.Tc.fst"
let _57_3833 = (tc_decls env decls)
in (match (_57_3833) with
| (ses, exports, env) -> begin
(
# 2962 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2962 "FStar.TypeChecker.Tc.fst"
let _57_3834 = modul
in {FStar_Syntax_Syntax.name = _57_3834.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _57_3834.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3834.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))

# 2965 "FStar.TypeChecker.Tc.fst"
let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (
# 2966 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2966 "FStar.TypeChecker.Tc.fst"
let _57_3840 = modul
in {FStar_Syntax_Syntax.name = _57_3840.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _57_3840.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (
# 2967 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.finish_module env modul)
in (
# 2968 "FStar.TypeChecker.Tc.fst"
let _57_3850 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(
# 2970 "FStar.TypeChecker.Tc.fst"
let _57_3844 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (
# 2971 "FStar.TypeChecker.Tc.fst"
let _57_3846 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (
# 2972 "FStar.TypeChecker.Tc.fst"
let _57_3848 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _146_1730 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _146_1730 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))

# 2977 "FStar.TypeChecker.Tc.fst"
let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2978 "FStar.TypeChecker.Tc.fst"
let _57_3857 = (tc_partial_modul env modul)
in (match (_57_3857) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

# 2981 "FStar.TypeChecker.Tc.fst"
let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 2982 "FStar.TypeChecker.Tc.fst"
let _57_3860 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _146_1739 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _146_1739))
end else begin
()
end
in (
# 2984 "FStar.TypeChecker.Tc.fst"
let env = (
# 2984 "FStar.TypeChecker.Tc.fst"
let _57_3862 = env
in {FStar_TypeChecker_Env.solver = _57_3862.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3862.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3862.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3862.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3862.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3862.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3862.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3862.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3862.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3862.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3862.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3862.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3862.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_3862.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3862.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3862.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3862.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3862.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3862.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3862.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 2985 "FStar.TypeChecker.Tc.fst"
let _57_3878 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _57_3870) -> begin
(let _146_1744 = (let _146_1743 = (let _146_1742 = (FStar_TypeChecker_Env.get_range env)
in ((Prims.strcat "Implicit argument: " msg), _146_1742))
in FStar_Syntax_Syntax.Error (_146_1743))
in (Prims.raise _146_1744))
end
in (match (_57_3878) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(t, c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(let _146_1749 = (let _146_1748 = (let _146_1747 = (let _146_1745 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _146_1745))
in (let _146_1746 = (FStar_TypeChecker_Env.get_range env)
in (_146_1747, _146_1746)))
in FStar_Syntax_Syntax.Error (_146_1748))
in (Prims.raise _146_1749))
end
end)))))

# 2992 "FStar.TypeChecker.Tc.fst"
let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (
# 2993 "FStar.TypeChecker.Tc.fst"
let _57_3881 = if ((let _146_1754 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _146_1754)) <> 0) then begin
(let _146_1755 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _146_1755))
end else begin
()
end
in (
# 2995 "FStar.TypeChecker.Tc.fst"
let _57_3885 = (tc_modul env m)
in (match (_57_3885) with
| (m, env) -> begin
(
# 2996 "FStar.TypeChecker.Tc.fst"
let _57_3886 = if (FStar_Options.should_dump m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _146_1756 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _146_1756))
end else begin
()
end
in (m, env))
end))))




