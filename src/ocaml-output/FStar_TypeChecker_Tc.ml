
open Prims
# 42 "FStar.TypeChecker.Tc.fst"
type effect_cost =
| ForFree
| NotForFree

# 42 "FStar.TypeChecker.Tc.fst"
let is_ForFree = (fun _discr_ -> (match (_discr_) with
| ForFree (_) -> begin
true
end
| _ -> begin
false
end))

# 42 "FStar.TypeChecker.Tc.fst"
let is_NotForFree = (fun _discr_ -> (match (_discr_) with
| NotForFree (_) -> begin
true
end
| _ -> begin
false
end))

# 44 "FStar.TypeChecker.Tc.fst"
let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_ST.read FStar_Options.log_types) && (not ((let _146_5 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _146_5))))))

# 45 "FStar.TypeChecker.Tc.fst"
let rng : FStar_TypeChecker_Env.env  ->  FStar_Range.range = (fun env -> (FStar_TypeChecker_Env.get_range env))

# 46 "FStar.TypeChecker.Tc.fst"
let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (
# 46 "FStar.TypeChecker.Tc.fst"
let _57_17 = env
in {FStar_TypeChecker_Env.solver = _57_17.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_17.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_17.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_17.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_17.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_17.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_17.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_17.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_17.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _57_17.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_17.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_17.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_17.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_17.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_17.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_17.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_17.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_17.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_17.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_17.FStar_TypeChecker_Env.use_bv_sorts}))

# 47 "FStar.TypeChecker.Tc.fst"
let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (
# 47 "FStar.TypeChecker.Tc.fst"
let _57_20 = env
in {FStar_TypeChecker_Env.solver = _57_20.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_20.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_20.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_20.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_20.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_20.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_20.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_20.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_20.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _57_20.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_20.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_20.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_20.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_20.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_20.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_20.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_20.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_20.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_20.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_20.FStar_TypeChecker_Env.use_bv_sorts}))

# 48 "FStar.TypeChecker.Tc.fst"
let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (
# 50 "FStar.TypeChecker.Tc.fst"
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

# 53 "FStar.TypeChecker.Tc.fst"
let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _57_1 -> (match (_57_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _57_30 -> begin
false
end))

# 56 "FStar.TypeChecker.Tc.fst"
let steps : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Normalize.step Prims.list = (fun env -> if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::[]
end else begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]
end)

# 60 "FStar.TypeChecker.Tc.fst"
let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Beta)::[]) env t))

# 61 "FStar.TypeChecker.Tc.fst"
let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _146_32 = (steps env)
in (FStar_TypeChecker_Normalize.normalize _146_32 env t)))

# 62 "FStar.TypeChecker.Tc.fst"
let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _146_37 = (steps env)
in (FStar_TypeChecker_Normalize.normalize_comp _146_37 env c)))

# 63 "FStar.TypeChecker.Tc.fst"
let check_no_escape : FStar_Syntax_Syntax.term Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun head_opt env fvs kt -> (
# 64 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
()
end
| _57_47 -> begin
(
# 67 "FStar.TypeChecker.Tc.fst"
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
# 73 "FStar.TypeChecker.Tc.fst"
let fail = (fun _57_54 -> (match (()) with
| () -> begin
(
# 74 "FStar.TypeChecker.Tc.fst"
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
# 79 "FStar.TypeChecker.Tc.fst"
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

# 86 "FStar.TypeChecker.Tc.fst"
let maybe_push_binding : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder  ->  FStar_TypeChecker_Env.env = (fun env b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
env
end else begin
(
# 88 "FStar.TypeChecker.Tc.fst"
let _57_66 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_67 = (FStar_Syntax_Print.bv_to_string (Prims.fst b))
in (let _146_66 = (FStar_Syntax_Print.term_to_string (Prims.fst b).FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _146_67 _146_66)))
end else begin
()
end
in (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))
end)

# 92 "FStar.TypeChecker.Tc.fst"
let maybe_make_subst = (fun _57_2 -> (match (_57_2) with
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Syntax_Syntax.NT ((x, e)))::[]
end
| _57_75 -> begin
[]
end))

# 96 "FStar.TypeChecker.Tc.fst"
let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.subst_t = (fun s b v -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
s
end else begin
(FStar_Syntax_Syntax.NT (((Prims.fst b), v)))::s
end)

# 100 "FStar.TypeChecker.Tc.fst"
let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (
# 101 "FStar.TypeChecker.Tc.fst"
let _57_81 = lc
in {FStar_Syntax_Syntax.eff_name = _57_81.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _57_81.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _57_83 -> (match (()) with
| () -> begin
(let _146_80 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _146_80 t))
end))}))

# 103 "FStar.TypeChecker.Tc.fst"
let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (
# 104 "FStar.TypeChecker.Tc.fst"
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
# 109 "FStar.TypeChecker.Tc.fst"
let t = lc.FStar_Syntax_Syntax.res_typ
in (
# 110 "FStar.TypeChecker.Tc.fst"
let _57_115 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, guard)
end
| Some (t') -> begin
(
# 113 "FStar.TypeChecker.Tc.fst"
let _57_97 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_91 = (FStar_Syntax_Print.term_to_string t)
in (let _146_90 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _146_91 _146_90)))
end else begin
()
end
in (
# 115 "FStar.TypeChecker.Tc.fst"
let _57_101 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_57_101) with
| (e, lc) -> begin
(
# 116 "FStar.TypeChecker.Tc.fst"
let t = lc.FStar_Syntax_Syntax.res_typ
in (
# 117 "FStar.TypeChecker.Tc.fst"
let _57_105 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_57_105) with
| (e, g) -> begin
(
# 118 "FStar.TypeChecker.Tc.fst"
let _57_106 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_93 = (FStar_Syntax_Print.term_to_string t)
in (let _146_92 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _146_93 _146_92)))
end else begin
()
end
in (
# 120 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (
# 121 "FStar.TypeChecker.Tc.fst"
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
# 123 "FStar.TypeChecker.Tc.fst"
let _57_116 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_100 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _146_100))
end else begin
()
end
in (e, lc, g))
end)))))

# 127 "FStar.TypeChecker.Tc.fst"
let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (t) -> begin
(
# 131 "FStar.TypeChecker.Tc.fst"
let _57_126 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_57_126) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))

# 134 "FStar.TypeChecker.Tc.fst"
let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _57_131 -> (match (_57_131) with
| (e, c) -> begin
(
# 135 "FStar.TypeChecker.Tc.fst"
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
# 151 "FStar.TypeChecker.Tc.fst"
let _57_140 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_119 = (FStar_Syntax_Print.term_to_string e)
in (let _146_118 = (FStar_Syntax_Print.comp_to_string c)
in (let _146_117 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _146_119 _146_118 _146_117))))
end else begin
()
end
in (
# 154 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 155 "FStar.TypeChecker.Tc.fst"
let _57_143 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_122 = (FStar_Syntax_Print.term_to_string e)
in (let _146_121 = (FStar_Syntax_Print.comp_to_string c)
in (let _146_120 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _146_122 _146_121 _146_120))))
end else begin
()
end
in (
# 160 "FStar.TypeChecker.Tc.fst"
let _57_149 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_57_149) with
| (e, _57_147, g) -> begin
(
# 161 "FStar.TypeChecker.Tc.fst"
let g = (let _146_123 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _146_123 "could not prove post-condition" g))
in (
# 162 "FStar.TypeChecker.Tc.fst"
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

# 165 "FStar.TypeChecker.Tc.fst"
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

# 170 "FStar.TypeChecker.Tc.fst"
let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _146_134 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _146_134))
end))

# 177 "FStar.TypeChecker.Tc.fst"
let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _57_181; FStar_Syntax_Syntax.result_typ = _57_179; FStar_Syntax_Syntax.effect_args = _pre::_post::(pats, _57_173)::[]; FStar_Syntax_Syntax.flags = _57_170}) -> begin
(
# 181 "FStar.TypeChecker.Tc.fst"
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

# 192 "FStar.TypeChecker.Tc.fst"
let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun env actuals expected_c -> (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(
# 196 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 197 "FStar.TypeChecker.Tc.fst"
let env = (
# 197 "FStar.TypeChecker.Tc.fst"
let _57_203 = env
in {FStar_TypeChecker_Env.solver = _57_203.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_203.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_203.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_203.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_203.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_203.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_203.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_203.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_203.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_203.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_203.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_203.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_203.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_203.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_203.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_203.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_203.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_203.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_203.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_203.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 198 "FStar.TypeChecker.Tc.fst"
let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (
# 200 "FStar.TypeChecker.Tc.fst"
let decreases_clause = (fun bs c -> (
# 202 "FStar.TypeChecker.Tc.fst"
let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _57_215 -> (match (_57_215) with
| (b, _57_214) -> begin
(
# 204 "FStar.TypeChecker.Tc.fst"
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
# 209 "FStar.TypeChecker.Tc.fst"
let as_lex_list = (fun dec -> (
# 210 "FStar.TypeChecker.Tc.fst"
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
# 214 "FStar.TypeChecker.Tc.fst"
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
# 218 "FStar.TypeChecker.Tc.fst"
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
# 223 "FStar.TypeChecker.Tc.fst"
let previous_dec = (decreases_clause actuals expected_c)
in (
# 224 "FStar.TypeChecker.Tc.fst"
let guard_one_letrec = (fun _57_256 -> (match (_57_256) with
| (l, t) -> begin
(match ((let _146_162 = (FStar_Syntax_Subst.compress t)
in _146_162.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 228 "FStar.TypeChecker.Tc.fst"
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
# 229 "FStar.TypeChecker.Tc.fst"
let _57_267 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_57_267) with
| (formals, c) -> begin
(
# 230 "FStar.TypeChecker.Tc.fst"
let dec = (decreases_clause formals c)
in (
# 231 "FStar.TypeChecker.Tc.fst"
let precedes = (let _146_170 = (let _146_169 = (FStar_Syntax_Syntax.as_arg dec)
in (let _146_168 = (let _146_167 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_146_167)::[])
in (_146_169)::_146_168))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _146_170 None r))
in (
# 232 "FStar.TypeChecker.Tc.fst"
let _57_274 = (FStar_Util.prefix formals)
in (match (_57_274) with
| (bs, (last, imp)) -> begin
(
# 233 "FStar.TypeChecker.Tc.fst"
let last = (
# 233 "FStar.TypeChecker.Tc.fst"
let _57_275 = last
in (let _146_171 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _57_275.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_275.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_171}))
in (
# 234 "FStar.TypeChecker.Tc.fst"
let refined_formals = (FStar_List.append bs (((last, imp))::[]))
in (
# 235 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (
# 236 "FStar.TypeChecker.Tc.fst"
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

# 248 "FStar.TypeChecker.Tc.fst"
let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (
# 248 "FStar.TypeChecker.Tc.fst"
let _57_286 = env
in {FStar_TypeChecker_Env.solver = _57_286.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_286.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_286.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_286.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_286.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_286.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_286.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_286.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_286.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_286.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_286.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_286.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_286.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_286.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_286.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_286.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_286.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_286.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_286.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_286.FStar_TypeChecker_Env.use_bv_sorts}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 253 "FStar.TypeChecker.Tc.fst"
let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (
# 254 "FStar.TypeChecker.Tc.fst"
let _57_291 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_243 = (let _146_241 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _146_241))
in (let _146_242 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _146_243 _146_242)))
end else begin
()
end
in (
# 255 "FStar.TypeChecker.Tc.fst"
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
# 272 "FStar.TypeChecker.Tc.fst"
let _57_336 = (tc_tot_or_gtot_term env e)
in (match (_57_336) with
| (e, c, g) -> begin
(
# 273 "FStar.TypeChecker.Tc.fst"
let g = (
# 273 "FStar.TypeChecker.Tc.fst"
let _57_337 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_337.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_337.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_337.FStar_TypeChecker_Env.implicits})
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(
# 277 "FStar.TypeChecker.Tc.fst"
let _57_347 = (FStar_Syntax_Util.type_u ())
in (match (_57_347) with
| (t, u) -> begin
(
# 278 "FStar.TypeChecker.Tc.fst"
let _57_351 = (tc_check_tot_or_gtot_term env e t)
in (match (_57_351) with
| (e, c, g) -> begin
(
# 279 "FStar.TypeChecker.Tc.fst"
let _57_358 = (
# 280 "FStar.TypeChecker.Tc.fst"
let _57_355 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_355) with
| (env, _57_354) -> begin
(tc_pats env pats)
end))
in (match (_57_358) with
| (pats, g') -> begin
(
# 282 "FStar.TypeChecker.Tc.fst"
let g' = (
# 282 "FStar.TypeChecker.Tc.fst"
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
# 290 "FStar.TypeChecker.Tc.fst"
let _57_386 = (let _146_251 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _146_251 e1))
in (match (_57_386) with
| (e1, c1, g1) -> begin
(
# 291 "FStar.TypeChecker.Tc.fst"
let _57_390 = (tc_term env e2)
in (match (_57_390) with
| (e2, c2, g2) -> begin
(
# 292 "FStar.TypeChecker.Tc.fst"
let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (None, c2))
in (
# 293 "FStar.TypeChecker.Tc.fst"
let e = (let _146_256 = (let _146_255 = (let _146_254 = (let _146_253 = (let _146_252 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Common.t_unit, e1))
in (_146_252)::[])
in (false, _146_253))
in (_146_254, e2))
in FStar_Syntax_Syntax.Tm_let (_146_255))
in (FStar_Syntax_Syntax.mk _146_256 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 294 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_257 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _146_257)))))
end))
end))
end
| _57_395 -> begin
(
# 297 "FStar.TypeChecker.Tc.fst"
let _57_399 = (tc_term env e)
in (match (_57_399) with
| (e, c, g) -> begin
(
# 298 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(
# 303 "FStar.TypeChecker.Tc.fst"
let _57_408 = (tc_term env e)
in (match (_57_408) with
| (e, c, g) -> begin
(
# 304 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, m))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _57_414) -> begin
(
# 308 "FStar.TypeChecker.Tc.fst"
let _57_421 = (tc_comp env expected_c)
in (match (_57_421) with
| (expected_c, _57_419, g) -> begin
(
# 309 "FStar.TypeChecker.Tc.fst"
let _57_425 = (tc_term env e)
in (match (_57_425) with
| (e, c', g') -> begin
(
# 310 "FStar.TypeChecker.Tc.fst"
let _57_429 = (let _146_259 = (let _146_258 = (c'.FStar_Syntax_Syntax.comp ())
in (e, _146_258))
in (check_expected_effect env (Some (expected_c)) _146_259))
in (match (_57_429) with
| (e, expected_c, g'') -> begin
(
# 311 "FStar.TypeChecker.Tc.fst"
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
# 317 "FStar.TypeChecker.Tc.fst"
let _57_440 = (FStar_Syntax_Util.type_u ())
in (match (_57_440) with
| (k, u) -> begin
(
# 318 "FStar.TypeChecker.Tc.fst"
let _57_445 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_445) with
| (t, _57_443, f) -> begin
(
# 319 "FStar.TypeChecker.Tc.fst"
let _57_449 = (let _146_263 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _146_263 e))
in (match (_57_449) with
| (e, c, g) -> begin
(
# 320 "FStar.TypeChecker.Tc.fst"
let _57_453 = (let _146_267 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_450 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _146_267 e c f))
in (match (_57_453) with
| (c, f) -> begin
(
# 321 "FStar.TypeChecker.Tc.fst"
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
# 325 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 326 "FStar.TypeChecker.Tc.fst"
let env = (let _146_272 = (let _146_271 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_271 Prims.fst))
in (FStar_All.pipe_right _146_272 instantiate_both))
in (
# 327 "FStar.TypeChecker.Tc.fst"
let _57_464 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_274 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _146_273 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _146_274 _146_273)))
end else begin
()
end
in (
# 331 "FStar.TypeChecker.Tc.fst"
let _57_469 = (tc_term (no_inst env) head)
in (match (_57_469) with
| (head, chead, g_head) -> begin
(
# 332 "FStar.TypeChecker.Tc.fst"
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
# 335 "FStar.TypeChecker.Tc.fst"
let _57_474 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_277 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _146_277))
end else begin
()
end
in (
# 337 "FStar.TypeChecker.Tc.fst"
let c = if (((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) && (not ((FStar_Syntax_Util.is_lcomp_partial_return c)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)) then begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e c)
end else begin
c
end
in (
# 342 "FStar.TypeChecker.Tc.fst"
let _57_480 = (comp_check_expected_typ env0 e c)
in (match (_57_480) with
| (e, c, g') -> begin
(
# 343 "FStar.TypeChecker.Tc.fst"
let gimp = (match ((let _146_278 = (FStar_Syntax_Subst.compress head)
in _146_278.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _57_483) -> begin
(
# 346 "FStar.TypeChecker.Tc.fst"
let imp = ("head of application is a uvar", env0, u, e, c.FStar_Syntax_Syntax.res_typ, head.FStar_Syntax_Syntax.pos)
in (
# 347 "FStar.TypeChecker.Tc.fst"
let _57_487 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_487.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_487.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_487.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _57_490 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (
# 349 "FStar.TypeChecker.Tc.fst"
let gres = (let _146_279 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _146_279))
in (
# 350 "FStar.TypeChecker.Tc.fst"
let _57_493 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_280 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print1 "Guard from application node is %s\n" _146_280))
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
# 355 "FStar.TypeChecker.Tc.fst"
let _57_501 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_501) with
| (env1, topt) -> begin
(
# 356 "FStar.TypeChecker.Tc.fst"
let env1 = (instantiate_both env1)
in (
# 357 "FStar.TypeChecker.Tc.fst"
let _57_506 = (tc_term env1 e1)
in (match (_57_506) with
| (e1, c1, g1) -> begin
(
# 358 "FStar.TypeChecker.Tc.fst"
let _57_517 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(
# 361 "FStar.TypeChecker.Tc.fst"
let _57_513 = (FStar_Syntax_Util.type_u ())
in (match (_57_513) with
| (k, _57_512) -> begin
(
# 362 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _146_281 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_146_281, res_t)))
end))
end)
in (match (_57_517) with
| (env_branches, res_t) -> begin
(
# 365 "FStar.TypeChecker.Tc.fst"
let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (
# 366 "FStar.TypeChecker.Tc.fst"
let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (
# 367 "FStar.TypeChecker.Tc.fst"
let _57_534 = (
# 368 "FStar.TypeChecker.Tc.fst"
let _57_531 = (FStar_List.fold_right (fun _57_525 _57_528 -> (match ((_57_525, _57_528)) with
| ((_57_521, f, c, g), (caccum, gaccum)) -> begin
(let _146_284 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _146_284))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_531) with
| (cases, g) -> begin
(let _146_285 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_146_285, g))
end))
in (match (_57_534) with
| (c_branches, g_branches) -> begin
(
# 372 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (Some (guard_x), c_branches))
in (
# 373 "FStar.TypeChecker.Tc.fst"
let e = (let _146_289 = (let _146_288 = (let _146_287 = (FStar_List.map (fun _57_543 -> (match (_57_543) with
| (f, _57_538, _57_540, _57_542) -> begin
f
end)) t_eqns)
in (e1, _146_287))
in FStar_Syntax_Syntax.Tm_match (_146_288))
in (FStar_Syntax_Syntax.mk _146_289 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (
# 375 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ), Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (
# 376 "FStar.TypeChecker.Tc.fst"
let _57_546 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_292 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _146_291 = (let _146_290 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _146_290))
in (FStar_Util.print2 "(%s) comp type = %s\n" _146_292 _146_291)))
end else begin
()
end
in (let _146_293 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _146_293))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_558); FStar_Syntax_Syntax.lbunivs = _57_556; FStar_Syntax_Syntax.lbtyp = _57_554; FStar_Syntax_Syntax.lbeff = _57_552; FStar_Syntax_Syntax.lbdef = _57_550}::[]), _57_564) -> begin
(
# 383 "FStar.TypeChecker.Tc.fst"
let _57_567 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_294 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _146_294))
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
# 390 "FStar.TypeChecker.Tc.fst"
let _57_598 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_295 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _146_295))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _57_602), _57_605) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 403 "FStar.TypeChecker.Tc.fst"
let check_instantiated_fvar = (fun env v dc e t -> (
# 404 "FStar.TypeChecker.Tc.fst"
let _57_619 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_619) with
| (e, t, implicits) -> begin
(
# 406 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _146_309 = (let _146_308 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_308))
in FStar_Util.Inr (_146_309))
end
in (
# 407 "FStar.TypeChecker.Tc.fst"
let is_data_ctor = (fun _57_4 -> (match (_57_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _57_629 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _146_315 = (let _146_314 = (let _146_313 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _146_312 = (FStar_TypeChecker_Env.get_range env)
in (_146_313, _146_312)))
in FStar_Syntax_Syntax.Error (_146_314))
in (Prims.raise _146_315))
end else begin
(value_check_expected_typ env e tc implicits)
end))
end)))
in (
# 417 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (
# 418 "FStar.TypeChecker.Tc.fst"
let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(FStar_All.failwith "Impossible: Violation of locally nameless convention")
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(
# 424 "FStar.TypeChecker.Tc.fst"
let g = (match ((let _146_316 = (FStar_Syntax_Subst.compress t1)
in _146_316.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_640) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _57_643 -> begin
(
# 426 "FStar.TypeChecker.Tc.fst"
let imp = ("uvar in term", env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (
# 427 "FStar.TypeChecker.Tc.fst"
let _57_645 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_645.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_645.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_645.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 432 "FStar.TypeChecker.Tc.fst"
let _57_651 = (FStar_Syntax_Util.type_u ())
in (match (_57_651) with
| (k, u) -> begin
(
# 433 "FStar.TypeChecker.Tc.fst"
let t = (FStar_TypeChecker_Util.new_uvar env k)
in (
# 434 "FStar.TypeChecker.Tc.fst"
let e = (FStar_TypeChecker_Util.new_uvar env t)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 438 "FStar.TypeChecker.Tc.fst"
let t = if env.FStar_TypeChecker_Env.use_bv_sorts then begin
x.FStar_Syntax_Syntax.sort
end else begin
(FStar_TypeChecker_Env.lookup_bv env x)
end
in (
# 439 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.bv_to_name (
# 439 "FStar.TypeChecker.Tc.fst"
let _57_657 = x
in {FStar_Syntax_Syntax.ppname = _57_657.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_657.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (
# 440 "FStar.TypeChecker.Tc.fst"
let _57_663 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_663) with
| (e, t, implicits) -> begin
(
# 441 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _146_318 = (let _146_317 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_317))
in FStar_Util.Inr (_146_318))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _57_670; FStar_Syntax_Syntax.pos = _57_668; FStar_Syntax_Syntax.vars = _57_666}, us) -> begin
(
# 445 "FStar.TypeChecker.Tc.fst"
let us = (FStar_List.map (tc_universe env) us)
in (
# 446 "FStar.TypeChecker.Tc.fst"
let _57_680 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_680) with
| (us', t) -> begin
(
# 447 "FStar.TypeChecker.Tc.fst"
let _57_687 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _146_321 = (let _146_320 = (let _146_319 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _146_319))
in FStar_Syntax_Syntax.Error (_146_320))
in (Prims.raise _146_321))
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
# 452 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 452 "FStar.TypeChecker.Tc.fst"
let _57_689 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 452 "FStar.TypeChecker.Tc.fst"
let _57_691 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_691.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_691.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_689.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_689.FStar_Syntax_Syntax.fv_qual})
in (
# 453 "FStar.TypeChecker.Tc.fst"
let e = (let _146_324 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_324 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(
# 457 "FStar.TypeChecker.Tc.fst"
let _57_699 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_699) with
| (us, t) -> begin
(
# 458 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 458 "FStar.TypeChecker.Tc.fst"
let _57_700 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 458 "FStar.TypeChecker.Tc.fst"
let _57_702 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_702.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_702.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_700.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_700.FStar_Syntax_Syntax.fv_qual})
in (
# 459 "FStar.TypeChecker.Tc.fst"
let e = (let _146_325 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_325 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t)))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(
# 463 "FStar.TypeChecker.Tc.fst"
let t = (tc_constant env top.FStar_Syntax_Syntax.pos c)
in (
# 464 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 468 "FStar.TypeChecker.Tc.fst"
let _57_716 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_716) with
| (bs, c) -> begin
(
# 469 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 470 "FStar.TypeChecker.Tc.fst"
let _57_721 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_721) with
| (env, _57_720) -> begin
(
# 471 "FStar.TypeChecker.Tc.fst"
let _57_726 = (tc_binders env bs)
in (match (_57_726) with
| (bs, env, g, us) -> begin
(
# 472 "FStar.TypeChecker.Tc.fst"
let _57_730 = (tc_comp env c)
in (match (_57_730) with
| (c, uc, f) -> begin
(
# 473 "FStar.TypeChecker.Tc.fst"
let e = (
# 473 "FStar.TypeChecker.Tc.fst"
let _57_731 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _57_731.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_731.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_731.FStar_Syntax_Syntax.vars})
in (
# 474 "FStar.TypeChecker.Tc.fst"
let _57_734 = (check_smt_pat env e bs c)
in (
# 475 "FStar.TypeChecker.Tc.fst"
let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (
# 476 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 477 "FStar.TypeChecker.Tc.fst"
let g = (let _146_326 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _146_326))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(
# 481 "FStar.TypeChecker.Tc.fst"
let u = (tc_universe env u)
in (
# 482 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) None top.FStar_Syntax_Syntax.pos)
in (
# 483 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 487 "FStar.TypeChecker.Tc.fst"
let _57_750 = (let _146_328 = (let _146_327 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_327)::[])
in (FStar_Syntax_Subst.open_term _146_328 phi))
in (match (_57_750) with
| (x, phi) -> begin
(
# 488 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 489 "FStar.TypeChecker.Tc.fst"
let _57_755 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_755) with
| (env, _57_754) -> begin
(
# 490 "FStar.TypeChecker.Tc.fst"
let _57_760 = (let _146_329 = (FStar_List.hd x)
in (tc_binder env _146_329))
in (match (_57_760) with
| (x, env, f1, u) -> begin
(
# 491 "FStar.TypeChecker.Tc.fst"
let _57_761 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_332 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _146_331 = (FStar_Syntax_Print.term_to_string phi)
in (let _146_330 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _146_332 _146_331 _146_330))))
end else begin
()
end
in (
# 494 "FStar.TypeChecker.Tc.fst"
let _57_766 = (FStar_Syntax_Util.type_u ())
in (match (_57_766) with
| (t_phi, _57_765) -> begin
(
# 495 "FStar.TypeChecker.Tc.fst"
let _57_771 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_57_771) with
| (phi, _57_769, f2) -> begin
(
# 496 "FStar.TypeChecker.Tc.fst"
let e = (
# 496 "FStar.TypeChecker.Tc.fst"
let _57_772 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _57_772.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_772.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_772.FStar_Syntax_Syntax.vars})
in (
# 497 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 498 "FStar.TypeChecker.Tc.fst"
let g = (let _146_333 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _146_333))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _57_780) -> begin
(
# 502 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (
# 503 "FStar.TypeChecker.Tc.fst"
let _57_786 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_334 = (FStar_Syntax_Print.term_to_string (
# 504 "FStar.TypeChecker.Tc.fst"
let _57_784 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _57_784.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_784.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_784.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _146_334))
end else begin
()
end
in (
# 505 "FStar.TypeChecker.Tc.fst"
let _57_790 = (FStar_Syntax_Subst.open_term bs body)
in (match (_57_790) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _57_792 -> begin
(let _146_336 = (let _146_335 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _146_335))
in (FStar_All.failwith _146_336))
end)))))
and tc_constant : FStar_TypeChecker_Env.env  ->  FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun env r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_57_798) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_57_801, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_57_806, Some (FStar_Const.Unsigned, FStar_Const.Int8)) -> begin
FStar_TypeChecker_Common.t_uint8
end
| FStar_Const.Const_int (_57_814, Some (FStar_Const.Signed, FStar_Const.Int8)) -> begin
FStar_TypeChecker_Common.t_int8
end
| FStar_Const.Const_int (_57_822, Some (FStar_Const.Unsigned, FStar_Const.Int16)) -> begin
FStar_TypeChecker_Common.t_uint16
end
| FStar_Const.Const_int (_57_830, Some (FStar_Const.Signed, FStar_Const.Int16)) -> begin
FStar_TypeChecker_Common.t_int16
end
| FStar_Const.Const_int (_57_838, Some (FStar_Const.Unsigned, FStar_Const.Int32)) -> begin
FStar_TypeChecker_Common.t_uint32
end
| FStar_Const.Const_int (_57_846, Some (FStar_Const.Signed, FStar_Const.Int32)) -> begin
FStar_TypeChecker_Common.t_int32
end
| FStar_Const.Const_int (_57_854, Some (FStar_Const.Unsigned, FStar_Const.Int64)) -> begin
FStar_TypeChecker_Common.t_uint64
end
| FStar_Const.Const_int (_57_862, Some (FStar_Const.Signed, FStar_Const.Int64)) -> begin
FStar_TypeChecker_Common.t_int64
end
| FStar_Const.Const_string (_57_870) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_57_873) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_57_876) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_57_880) -> begin
FStar_TypeChecker_Common.t_range
end
| _57_883 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 541 "FStar.TypeChecker.Tc.fst"
let _57_890 = (FStar_Syntax_Util.type_u ())
in (match (_57_890) with
| (k, u) -> begin
(
# 542 "FStar.TypeChecker.Tc.fst"
let _57_895 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_895) with
| (t, _57_893, g) -> begin
(let _146_342 = (FStar_Syntax_Syntax.mk_Total t)
in (_146_342, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 546 "FStar.TypeChecker.Tc.fst"
let _57_900 = (FStar_Syntax_Util.type_u ())
in (match (_57_900) with
| (k, u) -> begin
(
# 547 "FStar.TypeChecker.Tc.fst"
let _57_905 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_905) with
| (t, _57_903, g) -> begin
(let _146_343 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_146_343, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 551 "FStar.TypeChecker.Tc.fst"
let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (
# 552 "FStar.TypeChecker.Tc.fst"
let tc = (let _146_345 = (let _146_344 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_146_344)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _146_345 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 553 "FStar.TypeChecker.Tc.fst"
let _57_914 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_57_914) with
| (tc, _57_912, f) -> begin
(
# 554 "FStar.TypeChecker.Tc.fst"
let _57_918 = (FStar_Syntax_Util.head_and_args tc)
in (match (_57_918) with
| (_57_916, args) -> begin
(
# 555 "FStar.TypeChecker.Tc.fst"
let _57_921 = (let _146_347 = (FStar_List.hd args)
in (let _146_346 = (FStar_List.tl args)
in (_146_347, _146_346)))
in (match (_57_921) with
| (res, args) -> begin
(
# 556 "FStar.TypeChecker.Tc.fst"
let _57_937 = (let _146_349 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _57_5 -> (match (_57_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(
# 558 "FStar.TypeChecker.Tc.fst"
let _57_928 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_928) with
| (env, _57_927) -> begin
(
# 559 "FStar.TypeChecker.Tc.fst"
let _57_933 = (tc_tot_or_gtot_term env e)
in (match (_57_933) with
| (e, _57_931, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _146_349 FStar_List.unzip))
in (match (_57_937) with
| (flags, guards) -> begin
(
# 562 "FStar.TypeChecker.Tc.fst"
let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| _57_942 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _146_351 = (FStar_Syntax_Syntax.mk_Comp (
# 565 "FStar.TypeChecker.Tc.fst"
let _57_944 = c
in {FStar_Syntax_Syntax.effect_name = _57_944.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _57_944.FStar_Syntax_Syntax.flags}))
in (let _146_350 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_146_351, u, _146_350))))
end))
end))
end))
end))))
end))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (
# 572 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun u -> (
# 573 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_57_952) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _146_356 = (aux u)
in FStar_Syntax_Syntax.U_succ (_146_356))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _146_357 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_146_357))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _146_361 = (let _146_360 = (let _146_359 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _146_358 = (FStar_TypeChecker_Env.get_range env)
in (_146_359, _146_358)))
in FStar_Syntax_Syntax.Error (_146_360))
in (Prims.raise _146_361))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _146_362 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_362 Prims.snd))
end
| _57_967 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (
# 595 "FStar.TypeChecker.Tc.fst"
let fail = (fun msg t -> (let _146_371 = (let _146_370 = (let _146_369 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_146_369, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_370))
in (Prims.raise _146_371)))
in (
# 604 "FStar.TypeChecker.Tc.fst"
let check_binders = (fun env bs bs_expected -> (
# 609 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun _57_985 bs bs_expected -> (match (_57_985) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| ((hd, imp)::bs, (hd_expected, imp')::bs_expected) -> begin
(
# 613 "FStar.TypeChecker.Tc.fst"
let _57_1016 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _146_388 = (let _146_387 = (let _146_386 = (let _146_384 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _146_384))
in (let _146_385 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_146_386, _146_385)))
in FStar_Syntax_Syntax.Error (_146_387))
in (Prims.raise _146_388))
end
| _57_1015 -> begin
()
end)
in (
# 620 "FStar.TypeChecker.Tc.fst"
let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (
# 621 "FStar.TypeChecker.Tc.fst"
let _57_1033 = (match ((let _146_389 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _146_389.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _57_1021 -> begin
(
# 624 "FStar.TypeChecker.Tc.fst"
let _57_1022 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_390 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _146_390))
end else begin
()
end
in (
# 625 "FStar.TypeChecker.Tc.fst"
let _57_1028 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_57_1028) with
| (t, _57_1026, g1) -> begin
(
# 626 "FStar.TypeChecker.Tc.fst"
let g2 = (let _146_392 = (FStar_TypeChecker_Env.get_range env)
in (let _146_391 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _146_392 "Type annotation on parameter incompatible with the expected type" _146_391)))
in (
# 630 "FStar.TypeChecker.Tc.fst"
let g = (let _146_393 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _146_393))
in (t, g)))
end)))
end)
in (match (_57_1033) with
| (t, g) -> begin
(
# 632 "FStar.TypeChecker.Tc.fst"
let hd = (
# 632 "FStar.TypeChecker.Tc.fst"
let _57_1034 = hd
in {FStar_Syntax_Syntax.ppname = _57_1034.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1034.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 633 "FStar.TypeChecker.Tc.fst"
let b = (hd, imp)
in (
# 634 "FStar.TypeChecker.Tc.fst"
let b_expected = (hd_expected, imp')
in (
# 635 "FStar.TypeChecker.Tc.fst"
let env = (maybe_push_binding env b)
in (
# 636 "FStar.TypeChecker.Tc.fst"
let subst = (let _146_394 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _146_394))
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
# 646 "FStar.TypeChecker.Tc.fst"
let rec expected_function_typ = (fun env t0 body -> (match (t0) with
| None -> begin
(
# 657 "FStar.TypeChecker.Tc.fst"
let _57_1055 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1054 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (
# 660 "FStar.TypeChecker.Tc.fst"
let _57_1062 = (tc_binders env bs)
in (match (_57_1062) with
| (bs, envbody, g, _57_1061) -> begin
(
# 661 "FStar.TypeChecker.Tc.fst"
let _57_1080 = (match ((let _146_401 = (FStar_Syntax_Subst.compress body)
in _146_401.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _57_1067) -> begin
(
# 663 "FStar.TypeChecker.Tc.fst"
let _57_1074 = (tc_comp envbody c)
in (match (_57_1074) with
| (c, _57_1072, g') -> begin
(let _146_402 = (FStar_TypeChecker_Rel.conj_guard g g')
in (Some (c), body, _146_402))
end))
end
| _57_1076 -> begin
(None, body, g)
end)
in (match (_57_1080) with
| (copt, body, g) -> begin
(None, bs, [], copt, envbody, body, g)
end))
end)))
end
| Some (t) -> begin
(
# 669 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 670 "FStar.TypeChecker.Tc.fst"
let rec as_function_typ = (fun norm t -> (match ((let _146_407 = (FStar_Syntax_Subst.compress t)
in _146_407.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 674 "FStar.TypeChecker.Tc.fst"
let _57_1107 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1106 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 675 "FStar.TypeChecker.Tc.fst"
let _57_1114 = (tc_binders env bs)
in (match (_57_1114) with
| (bs, envbody, g, _57_1113) -> begin
(
# 676 "FStar.TypeChecker.Tc.fst"
let _57_1118 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_57_1118) with
| (envbody, _57_1117) -> begin
(Some ((t, true)), bs, [], None, envbody, body, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _57_1121) -> begin
(
# 682 "FStar.TypeChecker.Tc.fst"
let _57_1132 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_57_1132) with
| (_57_1125, bs, bs', copt, env, body, g) -> begin
(Some ((t, false)), bs, bs', copt, env, body, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 686 "FStar.TypeChecker.Tc.fst"
let _57_1139 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_57_1139) with
| (bs_expected, c_expected) -> begin
(
# 693 "FStar.TypeChecker.Tc.fst"
let check_actuals_against_formals = (fun env bs bs_expected -> (
# 694 "FStar.TypeChecker.Tc.fst"
let rec handle_more = (fun _57_1150 c_expected -> (match (_57_1150) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _146_418 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _146_418))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(
# 699 "FStar.TypeChecker.Tc.fst"
let c = (let _146_419 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _146_419))
in (let _146_420 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _146_420)))
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
let _57_1171 = (check_binders env more_bs bs_expected)
in (match (_57_1171) with
| (env, bs', more, guard', subst) -> begin
(let _146_422 = (let _146_421 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _146_421, subst))
in (handle_more _146_422 c_expected))
end))
end
| _57_1173 -> begin
(let _146_424 = (let _146_423 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _146_423))
in (fail _146_424 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _146_425 = (check_binders env bs bs_expected)
in (handle_more _146_425 c_expected))))
in (
# 716 "FStar.TypeChecker.Tc.fst"
let mk_letrec_env = (fun envbody bs c -> (
# 717 "FStar.TypeChecker.Tc.fst"
let letrecs = (guard_letrecs envbody bs c)
in (
# 718 "FStar.TypeChecker.Tc.fst"
let envbody = (
# 718 "FStar.TypeChecker.Tc.fst"
let _57_1179 = envbody
in {FStar_TypeChecker_Env.solver = _57_1179.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1179.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1179.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1179.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1179.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1179.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1179.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1179.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1179.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1179.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1179.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1179.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_1179.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1179.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1179.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1179.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1179.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1179.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1179.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1179.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _57_1184 _57_1187 -> (match ((_57_1184, _57_1187)) with
| ((env, letrec_binders), (l, t)) -> begin
(
# 722 "FStar.TypeChecker.Tc.fst"
let _57_1193 = (let _146_435 = (let _146_434 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_434 Prims.fst))
in (tc_term _146_435 t))
in (match (_57_1193) with
| (t, _57_1190, _57_1192) -> begin
(
# 723 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (
# 724 "FStar.TypeChecker.Tc.fst"
let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _146_436 = (FStar_Syntax_Syntax.mk_binder (
# 725 "FStar.TypeChecker.Tc.fst"
let _57_1197 = x
in {FStar_Syntax_Syntax.ppname = _57_1197.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1197.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_146_436)::letrec_binders)
end
| _57_1200 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (
# 730 "FStar.TypeChecker.Tc.fst"
let _57_1206 = (check_actuals_against_formals env bs bs_expected)
in (match (_57_1206) with
| (envbody, bs, g, c) -> begin
(
# 731 "FStar.TypeChecker.Tc.fst"
let _57_1209 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_57_1209) with
| (envbody, letrecs) -> begin
(
# 732 "FStar.TypeChecker.Tc.fst"
let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, body, g))
end))
end))))
end))
end
| _57_1212 -> begin
if (not (norm)) then begin
(let _146_437 = (unfold_whnf env t)
in (as_function_typ true _146_437))
end else begin
(
# 740 "FStar.TypeChecker.Tc.fst"
let _57_1222 = (expected_function_typ env None body)
in (match (_57_1222) with
| (_57_1214, bs, _57_1217, c_opt, envbody, body, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, body, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (
# 744 "FStar.TypeChecker.Tc.fst"
let use_eq = env.FStar_TypeChecker_Env.use_eq
in (
# 745 "FStar.TypeChecker.Tc.fst"
let _57_1226 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1226) with
| (env, topt) -> begin
(
# 747 "FStar.TypeChecker.Tc.fst"
let _57_1230 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_438 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _146_438 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (
# 752 "FStar.TypeChecker.Tc.fst"
let _57_1239 = (expected_function_typ env topt body)
in (match (_57_1239) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(
# 753 "FStar.TypeChecker.Tc.fst"
let _57_1245 = (tc_term (
# 753 "FStar.TypeChecker.Tc.fst"
let _57_1240 = envbody
in {FStar_TypeChecker_Env.solver = _57_1240.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1240.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1240.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1240.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1240.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1240.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1240.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1240.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1240.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1240.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1240.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1240.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1240.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1240.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1240.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1240.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1240.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1240.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1240.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_57_1245) with
| (body, cbody, guard_body) -> begin
(
# 755 "FStar.TypeChecker.Tc.fst"
let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (
# 758 "FStar.TypeChecker.Tc.fst"
let _57_1247 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _146_441 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _146_440 = (let _146_439 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _146_439))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _146_441 _146_440)))
end else begin
()
end
in (
# 763 "FStar.TypeChecker.Tc.fst"
let _57_1254 = (let _146_443 = (let _146_442 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _146_442))
in (check_expected_effect (
# 763 "FStar.TypeChecker.Tc.fst"
let _57_1249 = envbody
in {FStar_TypeChecker_Env.solver = _57_1249.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1249.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1249.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1249.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1249.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1249.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1249.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1249.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1249.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1249.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1249.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1249.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1249.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1249.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1249.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1249.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1249.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1249.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1249.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1249.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _146_443))
in (match (_57_1254) with
| (body, cbody, guard) -> begin
(
# 764 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (
# 765 "FStar.TypeChecker.Tc.fst"
let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _146_444 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _146_444))
end else begin
(
# 767 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (
# 770 "FStar.TypeChecker.Tc.fst"
let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (
# 771 "FStar.TypeChecker.Tc.fst"
let e = (let _146_447 = (let _146_446 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _146_445 -> FStar_Util.Inl (_146_445)))
in Some (_146_446))
in (FStar_Syntax_Util.abs bs body _146_447))
in (
# 772 "FStar.TypeChecker.Tc.fst"
let _57_1277 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(
# 774 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_1266) -> begin
(e, t, guard)
end
| _57_1269 -> begin
(
# 781 "FStar.TypeChecker.Tc.fst"
let _57_1272 = if use_teq then begin
(let _146_448 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _146_448))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_57_1272) with
| (e, guard') -> begin
(let _146_449 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _146_449))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_57_1277) with
| (e, tfun, guard) -> begin
(
# 790 "FStar.TypeChecker.Tc.fst"
let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (
# 791 "FStar.TypeChecker.Tc.fst"
let _57_1281 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_57_1281) with
| (c, g) -> begin
(e, c, g)
end)))
end))))))
end))))
end))
end)))
end)))))))
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead ghead args expected_topt -> (
# 799 "FStar.TypeChecker.Tc.fst"
let n_args = (FStar_List.length args)
in (
# 800 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 801 "FStar.TypeChecker.Tc.fst"
let thead = chead.FStar_Syntax_Syntax.res_typ
in (
# 802 "FStar.TypeChecker.Tc.fst"
let _57_1291 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_458 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _146_457 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _146_458 _146_457)))
end else begin
()
end
in (
# 803 "FStar.TypeChecker.Tc.fst"
let rec check_function_app = (fun norm tf -> (match ((let _146_463 = (FStar_Syntax_Util.unrefine tf)
in _146_463.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 807 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| (e, imp)::tl -> begin
(
# 810 "FStar.TypeChecker.Tc.fst"
let _57_1325 = (tc_term env e)
in (match (_57_1325) with
| (e, c, g_e) -> begin
(
# 811 "FStar.TypeChecker.Tc.fst"
let _57_1329 = (tc_args env tl)
in (match (_57_1329) with
| (args, comps, g_rest) -> begin
(let _146_468 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, ((e.FStar_Syntax_Syntax.pos, c))::comps, _146_468))
end))
end))
end))
in (
# 819 "FStar.TypeChecker.Tc.fst"
let _57_1333 = (tc_args env args)
in (match (_57_1333) with
| (args, comps, g_args) -> begin
(
# 820 "FStar.TypeChecker.Tc.fst"
let bs = (let _146_470 = (FStar_All.pipe_right comps (FStar_List.map (fun _57_1337 -> (match (_57_1337) with
| (_57_1335, c) -> begin
(c.FStar_Syntax_Syntax.res_typ, None)
end))))
in (FStar_Syntax_Util.null_binders_of_tks _146_470))
in (
# 821 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _57_1343 -> begin
FStar_Syntax_Util.ml_comp
end)
in (
# 824 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _146_485 = (FStar_Syntax_Subst.compress t)
in _146_485.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_1349) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _57_1354 -> begin
ml_or_tot
end)
end)
in (
# 831 "FStar.TypeChecker.Tc.fst"
let cres = (let _146_490 = (let _146_489 = (let _146_488 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_488 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _146_489))
in (ml_or_tot _146_490 r))
in (
# 832 "FStar.TypeChecker.Tc.fst"
let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (
# 833 "FStar.TypeChecker.Tc.fst"
let _57_1358 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_493 = (FStar_Syntax_Print.term_to_string head)
in (let _146_492 = (FStar_Syntax_Print.term_to_string tf)
in (let _146_491 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _146_493 _146_492 _146_491))))
end else begin
()
end
in (
# 838 "FStar.TypeChecker.Tc.fst"
let _57_1360 = (let _146_494 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _146_494))
in (
# 839 "FStar.TypeChecker.Tc.fst"
let comp = (let _146_497 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _57_1364 out -> (match (_57_1364) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c (None, out))
end)) (((head.FStar_Syntax_Syntax.pos, chead))::comps) _146_497))
in (let _146_499 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _146_498 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_146_499, comp, _146_498)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 847 "FStar.TypeChecker.Tc.fst"
let _57_1373 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_1373) with
| (bs, c) -> begin
(
# 849 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun _57_1381 bs cres args -> (match (_57_1381) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (_57_1388)))::rest, (_57_1396, None)::_57_1394) -> begin
(
# 860 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 861 "FStar.TypeChecker.Tc.fst"
let _57_1402 = (check_no_escape (Some (head)) env fvs t)
in (
# 862 "FStar.TypeChecker.Tc.fst"
let _57_1408 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_57_1408) with
| (varg, _57_1406, implicits) -> begin
(
# 863 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (
# 864 "FStar.TypeChecker.Tc.fst"
let arg = (let _146_508 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _146_508))
in (let _146_510 = (let _146_509 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _146_509, fvs))
in (tc_args _146_510 rest cres args))))
end))))
end
| ((x, aqual)::rest, (e, aq)::rest') -> begin
(
# 868 "FStar.TypeChecker.Tc.fst"
let _57_1440 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _57_1439 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (
# 873 "FStar.TypeChecker.Tc.fst"
let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 874 "FStar.TypeChecker.Tc.fst"
let x = (
# 874 "FStar.TypeChecker.Tc.fst"
let _57_1443 = x
in {FStar_Syntax_Syntax.ppname = _57_1443.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1443.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (
# 875 "FStar.TypeChecker.Tc.fst"
let _57_1446 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_511 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _146_511))
end else begin
()
end
in (
# 876 "FStar.TypeChecker.Tc.fst"
let _57_1448 = (check_no_escape (Some (head)) env fvs targ)
in (
# 877 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (
# 878 "FStar.TypeChecker.Tc.fst"
let env = (
# 878 "FStar.TypeChecker.Tc.fst"
let _57_1451 = env
in {FStar_TypeChecker_Env.solver = _57_1451.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1451.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1451.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1451.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1451.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1451.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1451.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1451.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1451.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1451.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1451.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1451.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1451.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1451.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1451.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _57_1451.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1451.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1451.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1451.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1451.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 879 "FStar.TypeChecker.Tc.fst"
let _57_1454 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_514 = (FStar_Syntax_Print.tag_of_term e)
in (let _146_513 = (FStar_Syntax_Print.term_to_string e)
in (let _146_512 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _146_514 _146_513 _146_512))))
end else begin
()
end
in (
# 880 "FStar.TypeChecker.Tc.fst"
let _57_1459 = (tc_term env e)
in (match (_57_1459) with
| (e, c, g_e) -> begin
(
# 881 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (
# 883 "FStar.TypeChecker.Tc.fst"
let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(
# 885 "FStar.TypeChecker.Tc.fst"
let subst = (let _146_515 = (FStar_List.hd bs)
in (maybe_extend_subst subst _146_515 e))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(
# 888 "FStar.TypeChecker.Tc.fst"
let subst = (let _146_516 = (FStar_List.hd bs)
in (maybe_extend_subst subst _146_516 e))
in (
# 889 "FStar.TypeChecker.Tc.fst"
let _57_1466 = (((e.FStar_Syntax_Syntax.pos, Some (x), c))::comps, g)
in (match (_57_1466) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _146_517 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _146_517)) then begin
(
# 893 "FStar.TypeChecker.Tc.fst"
let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (
# 894 "FStar.TypeChecker.Tc.fst"
let arg' = (let _146_518 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _146_518))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((e.FStar_Syntax_Syntax.pos, Some (newx), c))::comps, g, fvs) rest cres rest')))
end else begin
(let _146_522 = (let _146_521 = (let _146_520 = (let _146_519 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _146_519))
in (_146_520)::arg_rets)
in (subst, (arg)::outargs, _146_521, ((e.FStar_Syntax_Syntax.pos, Some (x), c))::comps, g, (x)::fvs))
in (tc_args _146_522 rest cres rest'))
end
end
end))
end))))))))))
end
| (_57_1470, []) -> begin
(
# 903 "FStar.TypeChecker.Tc.fst"
let _57_1473 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (
# 904 "FStar.TypeChecker.Tc.fst"
let _57_1493 = (match (bs) with
| [] -> begin
(
# 907 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (
# 913 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (
# 915 "FStar.TypeChecker.Tc.fst"
let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _57_1483 -> (match (_57_1483) with
| (_57_1479, _57_1481, c) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (
# 922 "FStar.TypeChecker.Tc.fst"
let cres = if refine_with_equality then begin
(let _146_524 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _146_524 cres))
end else begin
(
# 928 "FStar.TypeChecker.Tc.fst"
let _57_1485 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_527 = (FStar_Syntax_Print.term_to_string head)
in (let _146_526 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _146_525 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _146_527 _146_526 _146_525))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _57_1489 -> begin
(
# 937 "FStar.TypeChecker.Tc.fst"
let g = (let _146_528 = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (FStar_All.pipe_right _146_528 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _146_533 = (let _146_532 = (let _146_531 = (let _146_530 = (let _146_529 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _146_529))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _146_530))
in (FStar_Syntax_Syntax.mk_Total _146_531))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_532))
in (_146_533, g)))
end)
in (match (_57_1493) with
| (cres, g) -> begin
(
# 940 "FStar.TypeChecker.Tc.fst"
let _57_1494 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_534 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _146_534))
end else begin
()
end
in (
# 941 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_List.fold_left (fun out _57_1500 -> (match (_57_1500) with
| (r1, x, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c (x, out))
end)) cres comps)
in (
# 942 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.bind head.FStar_Syntax_Syntax.pos env None chead (None, comp))
in (
# 943 "FStar.TypeChecker.Tc.fst"
let app = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev outargs) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (
# 944 "FStar.TypeChecker.Tc.fst"
let _57_1506 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp g)
in (match (_57_1506) with
| (comp, g) -> begin
(app, comp, g)
end))))))
end)))
end
| ([], arg::_57_1509) -> begin
(
# 949 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun norm tres -> (
# 950 "FStar.TypeChecker.Tc.fst"
let tres = (let _146_542 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _146_542 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(
# 953 "FStar.TypeChecker.Tc.fst"
let _57_1521 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_543 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _146_543))
end else begin
()
end
in (let _146_547 = (let _146_546 = (let _146_545 = (let _146_544 = (FStar_TypeChecker_Env.get_range env)
in (_146_544, None, cres))
in (_146_545)::comps)
in (subst, outargs, arg_rets, _146_546, g, fvs))
in (tc_args _146_547 bs (FStar_Syntax_Util.lcomp_of_comp cres') args)))
end
| _57_1524 when (not (norm)) -> begin
(let _146_548 = (unfold_whnf env tres)
in (aux true _146_548))
end
| _57_1526 -> begin
(let _146_554 = (let _146_553 = (let _146_552 = (let _146_550 = (FStar_TypeChecker_Normalize.term_to_string env tf)
in (let _146_549 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _146_550 _146_549)))
in (let _146_551 = (FStar_Syntax_Syntax.argpos arg)
in (_146_552, _146_551)))
in FStar_Syntax_Syntax.Error (_146_553))
in (Prims.raise _146_554))
end)))
in (aux false cres.FStar_Syntax_Syntax.res_typ))
end)
end))
in (tc_args ([], [], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs (FStar_Syntax_Util.lcomp_of_comp c) args))
end))
end
| _57_1528 -> begin
if (not (norm)) then begin
(let _146_555 = (unfold_whnf env tf)
in (check_function_app true _146_555))
end else begin
(let _146_558 = (let _146_557 = (let _146_556 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_146_556, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_557))
in (Prims.raise _146_558))
end
end))
in (let _146_560 = (let _146_559 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _146_559))
in (check_function_app false _146_560))))))))
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
let _57_1564 = (FStar_List.fold_left2 (fun _57_1545 _57_1548 _57_1551 -> (match ((_57_1545, _57_1548, _57_1551)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(
# 985 "FStar.TypeChecker.Tc.fst"
let _57_1552 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 986 "FStar.TypeChecker.Tc.fst"
let _57_1557 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_57_1557) with
| (e, c, g) -> begin
(
# 987 "FStar.TypeChecker.Tc.fst"
let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (
# 988 "FStar.TypeChecker.Tc.fst"
let g = (let _146_570 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _146_570 g))
in (
# 989 "FStar.TypeChecker.Tc.fst"
let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _146_574 = (let _146_572 = (let _146_571 = (FStar_Syntax_Syntax.as_arg e)
in (_146_571)::[])
in (FStar_List.append seen _146_572))
in (let _146_573 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_146_574, _146_573, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_57_1564) with
| (args, guard, ghost) -> begin
(
# 993 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (
# 994 "FStar.TypeChecker.Tc.fst"
let c = if ghost then begin
(let _146_575 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _146_575 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (
# 995 "FStar.TypeChecker.Tc.fst"
let _57_1569 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_57_1569) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _57_1571 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (
# 1015 "FStar.TypeChecker.Tc.fst"
let _57_1578 = (FStar_Syntax_Subst.open_branch branch)
in (match (_57_1578) with
| (pattern, when_clause, branch_exp) -> begin
(
# 1016 "FStar.TypeChecker.Tc.fst"
let _57_1583 = branch
in (match (_57_1583) with
| (cpat, _57_1581, cbr) -> begin
(
# 1019 "FStar.TypeChecker.Tc.fst"
let tc_pat = (fun allow_implicits pat_t p0 -> (
# 1026 "FStar.TypeChecker.Tc.fst"
let _57_1591 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_57_1591) with
| (pat_bvs, exps, p) -> begin
(
# 1027 "FStar.TypeChecker.Tc.fst"
let _57_1592 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_587 = (FStar_Syntax_Print.pat_to_string p0)
in (let _146_586 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _146_587 _146_586)))
end else begin
()
end
in (
# 1029 "FStar.TypeChecker.Tc.fst"
let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (
# 1030 "FStar.TypeChecker.Tc.fst"
let _57_1598 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_57_1598) with
| (env1, _57_1597) -> begin
(
# 1031 "FStar.TypeChecker.Tc.fst"
let env1 = (
# 1031 "FStar.TypeChecker.Tc.fst"
let _57_1599 = env1
in {FStar_TypeChecker_Env.solver = _57_1599.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1599.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1599.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1599.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1599.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1599.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1599.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1599.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _57_1599.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1599.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1599.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1599.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1599.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1599.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1599.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1599.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1599.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1599.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1599.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1599.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1032 "FStar.TypeChecker.Tc.fst"
let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (
# 1033 "FStar.TypeChecker.Tc.fst"
let _57_1638 = (let _146_610 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (
# 1034 "FStar.TypeChecker.Tc.fst"
let _57_1604 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_590 = (FStar_Syntax_Print.term_to_string e)
in (let _146_589 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _146_590 _146_589)))
end else begin
()
end
in (
# 1037 "FStar.TypeChecker.Tc.fst"
let _57_1609 = (tc_term env1 e)
in (match (_57_1609) with
| (e, lc, g) -> begin
(
# 1039 "FStar.TypeChecker.Tc.fst"
let _57_1610 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_592 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _146_591 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _146_592 _146_591)))
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
let _57_1616 = (let _146_593 = (FStar_TypeChecker_Rel.discharge_guard env (
# 1044 "FStar.TypeChecker.Tc.fst"
let _57_1614 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_1614.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_1614.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_1614.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _146_593 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1045 "FStar.TypeChecker.Tc.fst"
let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (
# 1046 "FStar.TypeChecker.Tc.fst"
let uvars_to_string = (fun uvs -> (let _146_598 = (let _146_597 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _146_597 (FStar_List.map (fun _57_1624 -> (match (_57_1624) with
| (u, _57_1623) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _146_598 (FStar_String.concat ", "))))
in (
# 1047 "FStar.TypeChecker.Tc.fst"
let uvs1 = (FStar_Syntax_Free.uvars e')
in (
# 1048 "FStar.TypeChecker.Tc.fst"
let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (
# 1049 "FStar.TypeChecker.Tc.fst"
let _57_1632 = if (let _146_599 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _146_599)) then begin
(
# 1050 "FStar.TypeChecker.Tc.fst"
let unresolved = (let _146_600 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _146_600 FStar_Util.set_elements))
in (let _146_608 = (let _146_607 = (let _146_606 = (let _146_605 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _146_604 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _146_603 = (let _146_602 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _57_1631 -> (match (_57_1631) with
| (u, _57_1630) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _146_602 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _146_605 _146_604 _146_603))))
in (_146_606, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_146_607))
in (Prims.raise _146_608)))
end else begin
()
end
in (
# 1057 "FStar.TypeChecker.Tc.fst"
let _57_1634 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_609 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _146_609))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _146_610 FStar_List.unzip))
in (match (_57_1638) with
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
let _57_1645 = (let _146_611 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _146_611 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_57_1645) with
| (scrutinee_env, _57_1644) -> begin
(
# 1071 "FStar.TypeChecker.Tc.fst"
let _57_1651 = (tc_pat true pat_t pattern)
in (match (_57_1651) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(
# 1074 "FStar.TypeChecker.Tc.fst"
let _57_1661 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(
# 1081 "FStar.TypeChecker.Tc.fst"
let _57_1658 = (let _146_612 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _146_612 e))
in (match (_57_1658) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_57_1661) with
| (when_clause, g_when) -> begin
(
# 1085 "FStar.TypeChecker.Tc.fst"
let _57_1665 = (tc_term pat_env branch_exp)
in (match (_57_1665) with
| (branch_exp, c, g_branch) -> begin
(
# 1089 "FStar.TypeChecker.Tc.fst"
let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _146_614 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _146_613 -> Some (_146_613)) _146_614))
end)
in (
# 1096 "FStar.TypeChecker.Tc.fst"
let _57_1721 = (
# 1099 "FStar.TypeChecker.Tc.fst"
let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (
# 1100 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _57_1683 -> begin
(
# 1106 "FStar.TypeChecker.Tc.fst"
let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _146_618 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _146_617 -> Some (_146_617)) _146_618))
end))
end))) None))
in (
# 1111 "FStar.TypeChecker.Tc.fst"
let _57_1691 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_57_1691) with
| (c, g_branch) -> begin
(
# 1115 "FStar.TypeChecker.Tc.fst"
let _57_1716 = (match ((eqs, when_condition)) with
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
in (let _146_621 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _146_620 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_146_621, _146_620)))))
end
| (Some (f), Some (w)) -> begin
(
# 1127 "FStar.TypeChecker.Tc.fst"
let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1128 "FStar.TypeChecker.Tc.fst"
let g_fw = (let _146_622 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_146_622))
in (let _146_625 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _146_624 = (let _146_623 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _146_623 g_when))
in (_146_625, _146_624)))))
end
| (None, Some (w)) -> begin
(
# 1133 "FStar.TypeChecker.Tc.fst"
let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (
# 1134 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _146_626 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_146_626, g_when))))
end)
in (match (_57_1716) with
| (c_weak, g_when_weak) -> begin
(
# 1139 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _146_628 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _146_627 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_146_628, _146_627, g_branch))))
end))
end)))
in (match (_57_1721) with
| (c, g_when, g_branch) -> begin
(
# 1157 "FStar.TypeChecker.Tc.fst"
let branch_guard = (
# 1159 "FStar.TypeChecker.Tc.fst"
let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (
# 1160 "FStar.TypeChecker.Tc.fst"
let discriminate = (fun scrutinee_tm f -> if ((let _146_638 = (let _146_637 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _146_637))
in (FStar_List.length _146_638)) > 1) then begin
(
# 1163 "FStar.TypeChecker.Tc.fst"
let disc = (let _146_639 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _146_639 FStar_Syntax_Syntax.Delta_equational None))
in (
# 1164 "FStar.TypeChecker.Tc.fst"
let disc = (let _146_641 = (let _146_640 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_146_640)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _146_641 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _146_642 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_146_642)::[])))
end else begin
[]
end)
in (
# 1168 "FStar.TypeChecker.Tc.fst"
let fail = (fun _57_1731 -> (match (()) with
| () -> begin
(let _146_648 = (let _146_647 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _146_646 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _146_645 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _146_647 _146_646 _146_645))))
in (FStar_All.failwith _146_648))
end))
in (
# 1174 "FStar.TypeChecker.Tc.fst"
let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _57_1738) -> begin
(head_constructor t)
end
| _57_1742 -> begin
(fail ())
end))
in (
# 1179 "FStar.TypeChecker.Tc.fst"
let pat_exp = (let _146_651 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _146_651 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_57_1767) -> begin
(let _146_656 = (let _146_655 = (let _146_654 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _146_653 = (let _146_652 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_146_652)::[])
in (_146_654)::_146_653))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _146_655 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_146_656)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 1188 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _146_657 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _146_657))
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
let sub_term_guards = (let _146_664 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _57_1785 -> (match (_57_1785) with
| (ei, _57_1784) -> begin
(
# 1197 "FStar.TypeChecker.Tc.fst"
let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _57_1789 -> begin
(
# 1201 "FStar.TypeChecker.Tc.fst"
let sub_term = (let _146_663 = (let _146_660 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _146_660 FStar_Syntax_Syntax.Delta_equational None))
in (let _146_662 = (let _146_661 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_146_661)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _146_663 _146_662 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _146_664 FStar_List.flatten))
in (let _146_665 = (discriminate scrutinee_tm f)
in (FStar_List.append _146_665 sub_term_guards)))
end)
end
| _57_1793 -> begin
[]
end))))))
in (
# 1207 "FStar.TypeChecker.Tc.fst"
let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(
# 1210 "FStar.TypeChecker.Tc.fst"
let t = (let _146_670 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _146_670))
in (
# 1211 "FStar.TypeChecker.Tc.fst"
let _57_1801 = (FStar_Syntax_Util.type_u ())
in (match (_57_1801) with
| (k, _57_1800) -> begin
(
# 1212 "FStar.TypeChecker.Tc.fst"
let _57_1807 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_57_1807) with
| (t, _57_1804, _57_1806) -> begin
t
end))
end)))
end)
in (
# 1216 "FStar.TypeChecker.Tc.fst"
let branch_guard = (let _146_671 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _146_671 FStar_Syntax_Util.mk_disj_l))
in (
# 1219 "FStar.TypeChecker.Tc.fst"
let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
in (
# 1225 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (
# 1227 "FStar.TypeChecker.Tc.fst"
let _57_1815 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_672 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _146_672))
end else begin
()
end
in (let _146_673 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_146_673, branch_guard, c, guard)))))
end)))
end))
end))
end))
end)))))
end))
end)))
and check_top_level_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1241 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1244 "FStar.TypeChecker.Tc.fst"
let _57_1832 = (check_let_bound_def true env lb)
in (match (_57_1832) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(
# 1246 "FStar.TypeChecker.Tc.fst"
let _57_1844 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(
# 1249 "FStar.TypeChecker.Tc.fst"
let g1 = (let _146_676 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _146_676 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1250 "FStar.TypeChecker.Tc.fst"
let _57_1839 = (let _146_680 = (let _146_679 = (let _146_678 = (let _146_677 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _146_677))
in (_146_678)::[])
in (FStar_TypeChecker_Util.generalize env _146_679))
in (FStar_List.hd _146_680))
in (match (_57_1839) with
| (_57_1835, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_57_1844) with
| (g1, e1, univ_vars, c1) -> begin
(
# 1254 "FStar.TypeChecker.Tc.fst"
let _57_1854 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(
# 1256 "FStar.TypeChecker.Tc.fst"
let _57_1847 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_57_1847) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(
# 1259 "FStar.TypeChecker.Tc.fst"
let _57_1848 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _146_681 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _146_681 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _146_682 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_146_682, c1)))
end
end))
end else begin
(
# 1263 "FStar.TypeChecker.Tc.fst"
let _57_1850 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _146_683 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _146_683)))
end
in (match (_57_1854) with
| (e2, c1) -> begin
(
# 1268 "FStar.TypeChecker.Tc.fst"
let cres = (let _146_684 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_684))
in (
# 1269 "FStar.TypeChecker.Tc.fst"
let _57_1856 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1271 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _146_685 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_146_685, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _57_1860 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1288 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1291 "FStar.TypeChecker.Tc.fst"
let env = (
# 1291 "FStar.TypeChecker.Tc.fst"
let _57_1871 = env
in {FStar_TypeChecker_Env.solver = _57_1871.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1871.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1871.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1871.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1871.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1871.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1871.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1871.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1871.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1871.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1871.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1871.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1871.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1871.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1871.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1871.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1871.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1871.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1871.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1871.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1292 "FStar.TypeChecker.Tc.fst"
let _57_1880 = (let _146_689 = (let _146_688 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_688 Prims.fst))
in (check_let_bound_def false _146_689 lb))
in (match (_57_1880) with
| (e1, _57_1876, c1, g1, annotated) -> begin
(
# 1293 "FStar.TypeChecker.Tc.fst"
let x = (
# 1293 "FStar.TypeChecker.Tc.fst"
let _57_1881 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1881.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1881.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (
# 1294 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (
# 1295 "FStar.TypeChecker.Tc.fst"
let _57_1887 = (let _146_691 = (let _146_690 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_690)::[])
in (FStar_Syntax_Subst.open_term _146_691 e2))
in (match (_57_1887) with
| (xb, e2) -> begin
(
# 1296 "FStar.TypeChecker.Tc.fst"
let xbinder = (FStar_List.hd xb)
in (
# 1297 "FStar.TypeChecker.Tc.fst"
let x = (Prims.fst xbinder)
in (
# 1298 "FStar.TypeChecker.Tc.fst"
let _57_1893 = (let _146_692 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _146_692 e2))
in (match (_57_1893) with
| (e2, c2, g2) -> begin
(
# 1299 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (Some (x), c2))
in (
# 1300 "FStar.TypeChecker.Tc.fst"
let e = (let _146_695 = (let _146_694 = (let _146_693 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _146_693))
in FStar_Syntax_Syntax.Tm_let (_146_694))
in (FStar_Syntax_Syntax.mk _146_695 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 1301 "FStar.TypeChecker.Tc.fst"
let x_eq_e1 = (let _146_698 = (let _146_697 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _146_697 e1))
in (FStar_All.pipe_left (fun _146_696 -> FStar_TypeChecker_Common.NonTrivial (_146_696)) _146_698))
in (
# 1302 "FStar.TypeChecker.Tc.fst"
let g2 = (let _146_700 = (let _146_699 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _146_699 g2))
in (FStar_TypeChecker_Rel.close_guard xb _146_700))
in (
# 1304 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if annotated then begin
(e, cres, guard)
end else begin
(
# 1308 "FStar.TypeChecker.Tc.fst"
let _57_1899 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end)))))
end))))
end))))
end)))
end
| _57_1902 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1317 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1320 "FStar.TypeChecker.Tc.fst"
let _57_1914 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1914) with
| (lbs, e2) -> begin
(
# 1322 "FStar.TypeChecker.Tc.fst"
let _57_1917 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1917) with
| (env0, topt) -> begin
(
# 1323 "FStar.TypeChecker.Tc.fst"
let _57_1920 = (build_let_rec_env true env0 lbs)
in (match (_57_1920) with
| (lbs, rec_env) -> begin
(
# 1324 "FStar.TypeChecker.Tc.fst"
let _57_1923 = (check_let_recs rec_env lbs)
in (match (_57_1923) with
| (lbs, g_lbs) -> begin
(
# 1325 "FStar.TypeChecker.Tc.fst"
let g_lbs = (let _146_703 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _146_703 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1327 "FStar.TypeChecker.Tc.fst"
let all_lb_names = (let _146_706 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _146_706 (fun _146_705 -> Some (_146_705))))
in (
# 1329 "FStar.TypeChecker.Tc.fst"
let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(
# 1335 "FStar.TypeChecker.Tc.fst"
let ecs = (let _146_710 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _146_709 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _146_709)))))
in (FStar_TypeChecker_Util.generalize env _146_710))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _57_1934 -> (match (_57_1934) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (
# 1342 "FStar.TypeChecker.Tc.fst"
let cres = (let _146_712 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_712))
in (
# 1343 "FStar.TypeChecker.Tc.fst"
let _57_1937 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1345 "FStar.TypeChecker.Tc.fst"
let _57_1941 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1941) with
| (lbs, e2) -> begin
(let _146_714 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_713 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_146_714, cres, _146_713)))
end)))))))
end))
end))
end))
end))
end
| _57_1943 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1356 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1359 "FStar.TypeChecker.Tc.fst"
let _57_1955 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1955) with
| (lbs, e2) -> begin
(
# 1361 "FStar.TypeChecker.Tc.fst"
let _57_1958 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1958) with
| (env0, topt) -> begin
(
# 1362 "FStar.TypeChecker.Tc.fst"
let _57_1961 = (build_let_rec_env false env0 lbs)
in (match (_57_1961) with
| (lbs, rec_env) -> begin
(
# 1363 "FStar.TypeChecker.Tc.fst"
let _57_1964 = (check_let_recs rec_env lbs)
in (match (_57_1964) with
| (lbs, g_lbs) -> begin
(
# 1365 "FStar.TypeChecker.Tc.fst"
let _57_1976 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (
# 1366 "FStar.TypeChecker.Tc.fst"
let x = (
# 1366 "FStar.TypeChecker.Tc.fst"
let _57_1967 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1967.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1967.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (
# 1367 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1367 "FStar.TypeChecker.Tc.fst"
let _57_1970 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _57_1970.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1970.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1970.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _57_1970.FStar_Syntax_Syntax.lbdef})
in (
# 1368 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], lb.FStar_Syntax_Syntax.lbtyp))
in (env, lb))))) env))
in (match (_57_1976) with
| (env, lbs) -> begin
(
# 1371 "FStar.TypeChecker.Tc.fst"
let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (
# 1373 "FStar.TypeChecker.Tc.fst"
let _57_1982 = (tc_term env e2)
in (match (_57_1982) with
| (e2, cres, g2) -> begin
(
# 1374 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (
# 1375 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (
# 1376 "FStar.TypeChecker.Tc.fst"
let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (
# 1377 "FStar.TypeChecker.Tc.fst"
let cres = (
# 1377 "FStar.TypeChecker.Tc.fst"
let _57_1986 = cres
in {FStar_Syntax_Syntax.eff_name = _57_1986.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _57_1986.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_1986.FStar_Syntax_Syntax.comp})
in (
# 1379 "FStar.TypeChecker.Tc.fst"
let _57_1991 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1991) with
| (lbs, e2) -> begin
(
# 1380 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_57_1994) -> begin
(e, cres, guard)
end
| None -> begin
(
# 1384 "FStar.TypeChecker.Tc.fst"
let _57_1997 = (check_no_escape None env bvs tres)
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
| _57_2000 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (
# 1395 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1396 "FStar.TypeChecker.Tc.fst"
let _57_2033 = (FStar_List.fold_left (fun _57_2007 lb -> (match (_57_2007) with
| (lbs, env) -> begin
(
# 1397 "FStar.TypeChecker.Tc.fst"
let _57_2012 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_57_2012) with
| (univ_vars, t, check_t) -> begin
(
# 1398 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (
# 1399 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (
# 1400 "FStar.TypeChecker.Tc.fst"
let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(
# 1405 "FStar.TypeChecker.Tc.fst"
let _57_2021 = (let _146_726 = (let _146_725 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _146_725))
in (tc_check_tot_or_gtot_term (
# 1405 "FStar.TypeChecker.Tc.fst"
let _57_2015 = env0
in {FStar_TypeChecker_Env.solver = _57_2015.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2015.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2015.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2015.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2015.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2015.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2015.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2015.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2015.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2015.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2015.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2015.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2015.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2015.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _57_2015.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2015.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2015.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2015.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2015.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2015.FStar_TypeChecker_Env.use_bv_sorts}) t _146_726))
in (match (_57_2021) with
| (t, _57_2019, g) -> begin
(
# 1406 "FStar.TypeChecker.Tc.fst"
let _57_2022 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (
# 1408 "FStar.TypeChecker.Tc.fst"
let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(
# 1410 "FStar.TypeChecker.Tc.fst"
let _57_2025 = env
in {FStar_TypeChecker_Env.solver = _57_2025.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2025.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2025.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2025.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2025.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2025.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2025.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2025.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2025.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2025.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2025.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2025.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2025.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_2025.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2025.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2025.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2025.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2025.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2025.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2025.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (
# 1412 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1412 "FStar.TypeChecker.Tc.fst"
let _57_2028 = lb
in {FStar_Syntax_Syntax.lbname = _57_2028.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _57_2028.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_57_2033) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (
# 1419 "FStar.TypeChecker.Tc.fst"
let _57_2046 = (let _146_731 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 1420 "FStar.TypeChecker.Tc.fst"
let _57_2040 = (let _146_730 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _146_730 lb.FStar_Syntax_Syntax.lbdef))
in (match (_57_2040) with
| (e, c, g) -> begin
(
# 1421 "FStar.TypeChecker.Tc.fst"
let _57_2041 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1423 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _146_731 FStar_List.unzip))
in (match (_57_2046) with
| (lbs, gs) -> begin
(
# 1425 "FStar.TypeChecker.Tc.fst"
let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (
# 1439 "FStar.TypeChecker.Tc.fst"
let _57_2054 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_2054) with
| (env1, _57_2053) -> begin
(
# 1440 "FStar.TypeChecker.Tc.fst"
let e1 = lb.FStar_Syntax_Syntax.lbdef
in (
# 1443 "FStar.TypeChecker.Tc.fst"
let _57_2060 = (check_lbtyp top_level env lb)
in (match (_57_2060) with
| (topt, wf_annot, univ_vars, env1) -> begin
(
# 1445 "FStar.TypeChecker.Tc.fst"
let _57_2061 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1449 "FStar.TypeChecker.Tc.fst"
let _57_2068 = (tc_maybe_toplevel_term (
# 1449 "FStar.TypeChecker.Tc.fst"
let _57_2063 = env1
in {FStar_TypeChecker_Env.solver = _57_2063.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2063.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2063.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2063.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2063.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2063.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2063.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2063.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2063.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2063.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2063.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2063.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2063.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _57_2063.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2063.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2063.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2063.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2063.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2063.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2063.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_57_2068) with
| (e1, c1, g1) -> begin
(
# 1452 "FStar.TypeChecker.Tc.fst"
let _57_2072 = (let _146_738 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_2069 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _146_738 e1 c1 wf_annot))
in (match (_57_2072) with
| (c1, guard_f) -> begin
(
# 1455 "FStar.TypeChecker.Tc.fst"
let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (
# 1457 "FStar.TypeChecker.Tc.fst"
let _57_2074 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_739 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _146_739))
end else begin
()
end
in (let _146_740 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _146_740))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (
# 1469 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 1472 "FStar.TypeChecker.Tc.fst"
let _57_2081 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _57_2084 -> begin
(
# 1476 "FStar.TypeChecker.Tc.fst"
let _57_2087 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_57_2087) with
| (univ_vars, t) -> begin
(
# 1477 "FStar.TypeChecker.Tc.fst"
let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _146_744 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _146_744))
end else begin
(
# 1484 "FStar.TypeChecker.Tc.fst"
let _57_2092 = (FStar_Syntax_Util.type_u ())
in (match (_57_2092) with
| (k, _57_2091) -> begin
(
# 1485 "FStar.TypeChecker.Tc.fst"
let _57_2097 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_57_2097) with
| (t, _57_2095, g) -> begin
(
# 1486 "FStar.TypeChecker.Tc.fst"
let _57_2098 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _146_747 = (let _146_745 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _146_745))
in (let _146_746 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _146_747 _146_746)))
end else begin
()
end
in (
# 1490 "FStar.TypeChecker.Tc.fst"
let t = (norm env1 t)
in (let _146_748 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _146_748))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _57_2104 -> (match (_57_2104) with
| (x, imp) -> begin
(
# 1495 "FStar.TypeChecker.Tc.fst"
let _57_2107 = (FStar_Syntax_Util.type_u ())
in (match (_57_2107) with
| (tu, u) -> begin
(
# 1496 "FStar.TypeChecker.Tc.fst"
let _57_2112 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_57_2112) with
| (t, _57_2110, g) -> begin
(
# 1497 "FStar.TypeChecker.Tc.fst"
let x = ((
# 1497 "FStar.TypeChecker.Tc.fst"
let _57_2113 = x
in {FStar_Syntax_Syntax.ppname = _57_2113.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2113.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (
# 1498 "FStar.TypeChecker.Tc.fst"
let _57_2116 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_752 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _146_751 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _146_752 _146_751)))
end else begin
()
end
in (let _146_753 = (maybe_push_binding env x)
in (x, _146_753, g, u))))
end))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe Prims.list) = (fun env bs -> (
# 1503 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_TypeChecker_Rel.trivial_guard, [])
end
| b::bs -> begin
(
# 1506 "FStar.TypeChecker.Tc.fst"
let _57_2131 = (tc_binder env b)
in (match (_57_2131) with
| (b, env', g, u) -> begin
(
# 1507 "FStar.TypeChecker.Tc.fst"
let _57_2136 = (aux env' bs)
in (match (_57_2136) with
| (bs, env', g', us) -> begin
(let _146_761 = (let _146_760 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _146_760))
in ((b)::bs, env', _146_761, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (
# 1512 "FStar.TypeChecker.Tc.fst"
let tc_args = (fun env args -> (FStar_List.fold_right (fun _57_2144 _57_2147 -> (match ((_57_2144, _57_2147)) with
| ((t, imp), (args, g)) -> begin
(
# 1516 "FStar.TypeChecker.Tc.fst"
let _57_2152 = (tc_term env t)
in (match (_57_2152) with
| (t, _57_2150, g') -> begin
(let _146_770 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _146_770))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _57_2156 -> (match (_57_2156) with
| (pats, g) -> begin
(
# 1519 "FStar.TypeChecker.Tc.fst"
let _57_2159 = (tc_args env p)
in (match (_57_2159) with
| (args, g') -> begin
(let _146_773 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _146_773))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1524 "FStar.TypeChecker.Tc.fst"
let _57_2165 = (tc_maybe_toplevel_term env e)
in (match (_57_2165) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(
# 1527 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (
# 1528 "FStar.TypeChecker.Tc.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 1529 "FStar.TypeChecker.Tc.fst"
let _57_2168 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_776 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _146_776))
end else begin
()
end
in (
# 1530 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 1531 "FStar.TypeChecker.Tc.fst"
let _57_2173 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _146_777 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_146_777, false))
end else begin
(let _146_778 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_146_778, true))
end
in (match (_57_2173) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _146_779 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _146_779))
end
| _57_2177 -> begin
if allow_ghost then begin
(let _146_782 = (let _146_781 = (let _146_780 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_146_780, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_781))
in (Prims.raise _146_782))
end else begin
(let _146_785 = (let _146_784 = (let _146_783 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_146_783, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_784))
in (Prims.raise _146_785))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 1545 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))

# 1549 "FStar.TypeChecker.Tc.fst"
let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (
# 1550 "FStar.TypeChecker.Tc.fst"
let _57_2187 = (tc_tot_or_gtot_term env t)
in (match (_57_2187) with
| (t, c, g) -> begin
(
# 1551 "FStar.TypeChecker.Tc.fst"
let _57_2188 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))

# 1554 "FStar.TypeChecker.Tc.fst"
let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (
# 1555 "FStar.TypeChecker.Tc.fst"
let _57_2196 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_2196) with
| (t, c, g) -> begin
(
# 1556 "FStar.TypeChecker.Tc.fst"
let _57_2197 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))

# 1559 "FStar.TypeChecker.Tc.fst"
let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _146_805 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _146_805)))

# 1564 "FStar.TypeChecker.Tc.fst"
let check_nogen = (fun env t k -> (
# 1565 "FStar.TypeChecker.Tc.fst"
let t = (tc_check_trivial_guard env t k)
in (let _146_809 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _146_809))))

# 1568 "FStar.TypeChecker.Tc.fst"
let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (
# 1569 "FStar.TypeChecker.Tc.fst"
let _57_2212 = (tc_binders env tps)
in (match (_57_2212) with
| (tps, env, g, us) -> begin
(
# 1570 "FStar.TypeChecker.Tc.fst"
let _57_2213 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))

# 1573 "FStar.TypeChecker.Tc.fst"
let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (
# 1574 "FStar.TypeChecker.Tc.fst"
let fail = (fun _57_2219 -> (match (()) with
| () -> begin
(let _146_824 = (let _146_823 = (let _146_822 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_146_822, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_146_823))
in (Prims.raise _146_824))
end))
in (
# 1575 "FStar.TypeChecker.Tc.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1578 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _57_2236)::(wp, _57_2232)::(_wlp, _57_2228)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2240 -> begin
(fail ())
end))
end
| _57_2242 -> begin
(fail ())
end))))

# 1585 "FStar.TypeChecker.Tc.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 1588 "FStar.TypeChecker.Tc.fst"
let _57_2249 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_57_2249) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _57_2251 -> begin
(
# 1591 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow binders c)
in (
# 1592 "FStar.TypeChecker.Tc.fst"
let _57_2255 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_57_2255) with
| (uvs, t') -> begin
(match ((let _146_831 = (FStar_Syntax_Subst.compress t')
in _146_831.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _57_2261 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 1597 "FStar.TypeChecker.Tc.fst"
let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (
# 1598 "FStar.TypeChecker.Tc.fst"
let fail = (fun t -> (let _146_842 = (let _146_841 = (let _146_840 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_146_840, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_146_841))
in (Prims.raise _146_842)))
in (match ((let _146_843 = (FStar_Syntax_Subst.compress signature)
in _146_843.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1601 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _57_2282)::(wp, _57_2278)::(_wlp, _57_2274)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2286 -> begin
(fail signature)
end))
end
| _57_2288 -> begin
(fail signature)
end)))

# 1608 "FStar.TypeChecker.Tc.fst"
let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (
# 1609 "FStar.TypeChecker.Tc.fst"
let _57_2293 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_57_2293) with
| (a, wp) -> begin
(
# 1610 "FStar.TypeChecker.Tc.fst"
let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _57_2296 -> begin
(
# 1614 "FStar.TypeChecker.Tc.fst"
let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (
# 1615 "FStar.TypeChecker.Tc.fst"
let op = (fun ts -> (
# 1616 "FStar.TypeChecker.Tc.fst"
let _57_2300 = ()
in (
# 1617 "FStar.TypeChecker.Tc.fst"
let t0 = (Prims.snd ts)
in (
# 1618 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (
# 1620 "FStar.TypeChecker.Tc.fst"
let _57_2304 = ed
in (let _146_862 = (op ed.FStar_Syntax_Syntax.ret)
in (let _146_861 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _146_860 = (op ed.FStar_Syntax_Syntax.bind_wlp)
in (let _146_859 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _146_858 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _146_857 = (op ed.FStar_Syntax_Syntax.ite_wlp)
in (let _146_856 = (op ed.FStar_Syntax_Syntax.wp_binop)
in (let _146_855 = (op ed.FStar_Syntax_Syntax.wp_as_type)
in (let _146_854 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _146_853 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _146_852 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _146_851 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _146_850 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _57_2304.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2304.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2304.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2304.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2304.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _146_862; FStar_Syntax_Syntax.bind_wp = _146_861; FStar_Syntax_Syntax.bind_wlp = _146_860; FStar_Syntax_Syntax.if_then_else = _146_859; FStar_Syntax_Syntax.ite_wp = _146_858; FStar_Syntax_Syntax.ite_wlp = _146_857; FStar_Syntax_Syntax.wp_binop = _146_856; FStar_Syntax_Syntax.wp_as_type = _146_855; FStar_Syntax_Syntax.close_wp = _146_854; FStar_Syntax_Syntax.assert_p = _146_853; FStar_Syntax_Syntax.assume_p = _146_852; FStar_Syntax_Syntax.null_wp = _146_851; FStar_Syntax_Syntax.trivial = _146_850}))))))))))))))))
end)
in (ed, a, wp))
end)))

# 1636 "FStar.TypeChecker.Tc.fst"
let gen_wps_for_free : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env binders a wp_a ed -> (
# 1641 "FStar.TypeChecker.Tc.fst"
let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env)
in (
# 1643 "FStar.TypeChecker.Tc.fst"
let d = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))
in (
# 1644 "FStar.TypeChecker.Tc.fst"
let normalize_and_make_binders_explicit = (fun tm -> (
# 1645 "FStar.TypeChecker.Tc.fst"
let tm = (normalize tm)
in (
# 1646 "FStar.TypeChecker.Tc.fst"
let rec visit_term = (fun tm -> (
# 1647 "FStar.TypeChecker.Tc.fst"
let n = (match ((let _146_884 = (FStar_Syntax_Subst.compress tm)
in _146_884.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(
# 1649 "FStar.TypeChecker.Tc.fst"
let comp = (visit_comp comp)
in (
# 1650 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map visit_binder binders)
in FStar_Syntax_Syntax.Tm_arrow ((binders, comp))))
end
| FStar_Syntax_Syntax.Tm_abs (binders, term, comp) -> begin
(
# 1653 "FStar.TypeChecker.Tc.fst"
let comp = (visit_maybe_lcomp comp)
in (
# 1654 "FStar.TypeChecker.Tc.fst"
let term = (visit_term term)
in (
# 1655 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map visit_binder binders)
in FStar_Syntax_Syntax.Tm_abs ((binders, term, comp)))))
end
| _57_2339 -> begin
tm.FStar_Syntax_Syntax.n
end)
in (
# 1660 "FStar.TypeChecker.Tc.fst"
let _57_2341 = tm
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2341.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2341.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2341.FStar_Syntax_Syntax.vars})))
and visit_binder = (fun _57_2345 -> (match (_57_2345) with
| (bv, a) -> begin
(let _146_888 = (
# 1662 "FStar.TypeChecker.Tc.fst"
let _57_2346 = bv
in (let _146_886 = (visit_term bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_2346.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2346.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_886}))
in (let _146_887 = (FStar_Syntax_Syntax.as_implicit false)
in (_146_888, _146_887)))
end))
and visit_maybe_lcomp = (fun lcomp -> (match (lcomp) with
| Some (FStar_Util.Inl (lcomp)) -> begin
(let _146_893 = (let _146_892 = (let _146_891 = (let _146_890 = (lcomp.FStar_Syntax_Syntax.comp ())
in (visit_comp _146_890))
in (FStar_Syntax_Util.lcomp_of_comp _146_891))
in FStar_Util.Inl (_146_892))
in Some (_146_893))
end
| comp -> begin
comp
end))
and visit_comp = (fun comp -> (
# 1670 "FStar.TypeChecker.Tc.fst"
let n = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tm) -> begin
(let _146_895 = (visit_term tm)
in FStar_Syntax_Syntax.Total (_146_895))
end
| FStar_Syntax_Syntax.GTotal (tm) -> begin
(let _146_896 = (visit_term tm)
in FStar_Syntax_Syntax.GTotal (_146_896))
end
| comp -> begin
comp
end)
in (
# 1678 "FStar.TypeChecker.Tc.fst"
let _57_2360 = comp
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2360.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2360.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2360.FStar_Syntax_Syntax.vars})))
and visit_args = (fun args -> (FStar_List.map (fun _57_2365 -> (match (_57_2365) with
| (tm, q) -> begin
(let _146_899 = (visit_term tm)
in (_146_899, q))
end)) args))
in (visit_term tm))))
in (
# 1686 "FStar.TypeChecker.Tc.fst"
let check = (fun str t -> if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(
# 1688 "FStar.TypeChecker.Tc.fst"
let _57_2369 = (let _146_904 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Generated term for %s: %s\n" str _146_904))
in (
# 1689 "FStar.TypeChecker.Tc.fst"
let t = (normalize t)
in (
# 1690 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 1691 "FStar.TypeChecker.Tc.fst"
let _57_2384 = (tc_term env t)
in (match (_57_2384) with
| (e, {FStar_Syntax_Syntax.eff_name = _57_2380; FStar_Syntax_Syntax.res_typ = res_typ; FStar_Syntax_Syntax.cflags = _57_2377; FStar_Syntax_Syntax.comp = _57_2375}, _57_2383) -> begin
(
# 1692 "FStar.TypeChecker.Tc.fst"
let _57_2385 = (let _146_907 = (let _146_906 = (normalize res_typ)
in (FStar_Syntax_Print.term_to_string _146_906))
in (FStar_Util.print2 "Inferred type for %s: %s\n" str _146_907))
in (let _146_909 = (let _146_908 = (normalize e)
in (FStar_Syntax_Print.term_to_string _146_908))
in (FStar_Util.print2 "Elaborated term for %s: %s\n" str _146_909)))
end)))))
end else begin
()
end)
in (
# 1708 "FStar.TypeChecker.Tc.fst"
let rec collect_binders = (fun t -> (match ((let _146_912 = (FStar_Syntax_Subst.compress t)
in _146_912.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(
# 1711 "FStar.TypeChecker.Tc.fst"
let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
t
end
| _57_2396 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _146_913 = (collect_binders rest)
in (FStar_List.append bs _146_913)))
end
| FStar_Syntax_Syntax.Tm_type (_57_2399) -> begin
[]
end
| _57_2402 -> begin
(FStar_All.failwith "wp_a doesn\'t end in Type0")
end))
in (
# 1720 "FStar.TypeChecker.Tc.fst"
let _57_2417 = (
# 1721 "FStar.TypeChecker.Tc.fst"
let i = (FStar_ST.alloc 0)
in (
# 1722 "FStar.TypeChecker.Tc.fst"
let wp_binders = (let _146_920 = (normalize wp_a)
in (collect_binders _146_920))
in ((fun t -> (let _146_926 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow wp_binders _146_926))), (fun t -> (let _146_929 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow wp_binders _146_929))), (fun _57_2407 -> (match (()) with
| () -> begin
(FStar_List.map (fun _57_2411 -> (match (_57_2411) with
| (bv, _57_2410) -> begin
(
# 1731 "FStar.TypeChecker.Tc.fst"
let _57_2412 = (let _146_933 = ((FStar_ST.read i) + 1)
in (FStar_ST.op_Colon_Equals i _146_933))
in (let _146_936 = (let _146_935 = (let _146_934 = (FStar_ST.read i)
in (FStar_Util.string_of_int _146_934))
in (Prims.strcat "g" _146_935))
in (FStar_Syntax_Syntax.gen_bv _146_936 None bv.FStar_Syntax_Syntax.sort)))
end)) wp_binders)
end)))))
in (match (_57_2417) with
| (mk_ctx, mk_gctx, mk_gamma) -> begin
(
# 1737 "FStar.TypeChecker.Tc.fst"
let binders_of_list = (FStar_List.map (fun _57_2420 -> (match (_57_2420) with
| (t, b) -> begin
(let _146_942 = (FStar_Syntax_Syntax.as_implicit b)
in (t, _146_942))
end)))
in (
# 1739 "FStar.TypeChecker.Tc.fst"
let implicit_binders_of_list = (FStar_List.map (fun t -> (let _146_945 = (FStar_Syntax_Syntax.as_implicit true)
in (t, _146_945))))
in (
# 1741 "FStar.TypeChecker.Tc.fst"
let args_of_bv = (FStar_List.map (fun bv -> (let _146_948 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_Syntax_Syntax.as_arg _146_948))))
in (
# 1746 "FStar.TypeChecker.Tc.fst"
let c_pure = (
# 1747 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (
# 1748 "FStar.TypeChecker.Tc.fst"
let x = (let _146_949 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _146_949))
in (
# 1749 "FStar.TypeChecker.Tc.fst"
let ret = (let _146_954 = (let _146_953 = (let _146_952 = (let _146_951 = (let _146_950 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx _146_950))
in (FStar_Syntax_Syntax.mk_Total _146_951))
in (FStar_Syntax_Util.lcomp_of_comp _146_952))
in FStar_Util.Inl (_146_953))
in Some (_146_954))
in (
# 1750 "FStar.TypeChecker.Tc.fst"
let gamma = (mk_gamma ())
in (
# 1751 "FStar.TypeChecker.Tc.fst"
let body = (let _146_956 = (implicit_binders_of_list gamma)
in (let _146_955 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs _146_956 _146_955 ret)))
in (let _146_957 = (binders_of_list (((t, true))::((x, false))::[]))
in (FStar_Syntax_Util.abs _146_957 body ret)))))))
in (
# 1754 "FStar.TypeChecker.Tc.fst"
let _57_2432 = (let _146_961 = (let _146_960 = (let _146_959 = (let _146_958 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_958)::[])
in (FStar_List.append binders _146_959))
in (FStar_Syntax_Util.abs _146_960 c_pure None))
in (check "pure" _146_961))
in (
# 1761 "FStar.TypeChecker.Tc.fst"
let c_app = (
# 1762 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (
# 1763 "FStar.TypeChecker.Tc.fst"
let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (
# 1764 "FStar.TypeChecker.Tc.fst"
let l = (let _146_969 = (let _146_968 = (let _146_967 = (let _146_964 = (let _146_963 = (let _146_962 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _146_962))
in (FStar_Syntax_Syntax.mk_binder _146_963))
in (_146_964)::[])
in (let _146_966 = (let _146_965 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _146_965))
in (FStar_Syntax_Util.arrow _146_967 _146_966)))
in (mk_gctx _146_968))
in (FStar_Syntax_Syntax.gen_bv "l" None _146_969))
in (
# 1767 "FStar.TypeChecker.Tc.fst"
let r = (let _146_971 = (let _146_970 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _146_970))
in (FStar_Syntax_Syntax.gen_bv "r" None _146_971))
in (
# 1768 "FStar.TypeChecker.Tc.fst"
let ret = (let _146_976 = (let _146_975 = (let _146_974 = (let _146_973 = (let _146_972 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_972))
in (FStar_Syntax_Syntax.mk_Total _146_973))
in (FStar_Syntax_Util.lcomp_of_comp _146_974))
in FStar_Util.Inl (_146_975))
in Some (_146_976))
in (
# 1769 "FStar.TypeChecker.Tc.fst"
let outer_body = (
# 1770 "FStar.TypeChecker.Tc.fst"
let gamma = (mk_gamma ())
in (
# 1771 "FStar.TypeChecker.Tc.fst"
let gamma_as_args = (args_of_bv gamma)
in (
# 1772 "FStar.TypeChecker.Tc.fst"
let inner_body = (let _146_982 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _146_981 = (let _146_980 = (let _146_979 = (let _146_978 = (let _146_977 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _146_977 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg _146_978))
in (_146_979)::[])
in (FStar_List.append gamma_as_args _146_980))
in (FStar_Syntax_Util.mk_app _146_982 _146_981)))
in (let _146_983 = (implicit_binders_of_list gamma)
in (FStar_Syntax_Util.abs _146_983 inner_body ret)))))
in (let _146_984 = (binders_of_list (((t1, true))::((t2, true))::((l, false))::((r, false))::[]))
in (FStar_Syntax_Util.abs _146_984 outer_body ret))))))))
in (
# 1781 "FStar.TypeChecker.Tc.fst"
let _57_2444 = (let _146_988 = (let _146_987 = (let _146_986 = (let _146_985 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_985)::[])
in (FStar_List.append binders _146_986))
in (FStar_Syntax_Util.abs _146_987 c_app None))
in (check "app" _146_988))
in (
# 1790 "FStar.TypeChecker.Tc.fst"
let unknown = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (
# 1791 "FStar.TypeChecker.Tc.fst"
let c_lift1 = (
# 1792 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (
# 1793 "FStar.TypeChecker.Tc.fst"
let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (
# 1794 "FStar.TypeChecker.Tc.fst"
let t_f = (let _146_993 = (let _146_990 = (let _146_989 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_989))
in (_146_990)::[])
in (let _146_992 = (let _146_991 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _146_991))
in (FStar_Syntax_Util.arrow _146_993 _146_992)))
in (
# 1795 "FStar.TypeChecker.Tc.fst"
let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (
# 1796 "FStar.TypeChecker.Tc.fst"
let a1 = (let _146_995 = (let _146_994 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _146_994))
in (FStar_Syntax_Syntax.gen_bv "a1" None _146_995))
in (
# 1797 "FStar.TypeChecker.Tc.fst"
let ret = (let _146_1000 = (let _146_999 = (let _146_998 = (let _146_997 = (let _146_996 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_996))
in (FStar_Syntax_Syntax.mk_Total _146_997))
in (FStar_Syntax_Util.lcomp_of_comp _146_998))
in FStar_Util.Inl (_146_999))
in Some (_146_1000))
in (let _146_1013 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::((a1, false))::[]))
in (let _146_1012 = (let _146_1011 = (let _146_1010 = (let _146_1009 = (let _146_1008 = (let _146_1007 = (let _146_1004 = (let _146_1003 = (let _146_1002 = (let _146_1001 = (FStar_Syntax_Syntax.bv_to_name f)
in (_146_1001)::[])
in (unknown)::_146_1002)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1003))
in (FStar_Syntax_Util.mk_app c_pure _146_1004))
in (let _146_1006 = (let _146_1005 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_146_1005)::[])
in (_146_1007)::_146_1006))
in (unknown)::_146_1008)
in (unknown)::_146_1009)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1010))
in (FStar_Syntax_Util.mk_app c_app _146_1011))
in (FStar_Syntax_Util.abs _146_1013 _146_1012 ret)))))))))
in (
# 1805 "FStar.TypeChecker.Tc.fst"
let _57_2454 = (let _146_1017 = (let _146_1016 = (let _146_1015 = (let _146_1014 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1014)::[])
in (FStar_List.append binders _146_1015))
in (FStar_Syntax_Util.abs _146_1016 c_lift1 None))
in (check "lift1" _146_1017))
in (
# 1816 "FStar.TypeChecker.Tc.fst"
let c_lift2 = (
# 1817 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (
# 1818 "FStar.TypeChecker.Tc.fst"
let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (
# 1819 "FStar.TypeChecker.Tc.fst"
let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (
# 1820 "FStar.TypeChecker.Tc.fst"
let t_f = (let _146_1025 = (let _146_1022 = (let _146_1018 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_1018))
in (let _146_1021 = (let _146_1020 = (let _146_1019 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder _146_1019))
in (_146_1020)::[])
in (_146_1022)::_146_1021))
in (let _146_1024 = (let _146_1023 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal _146_1023))
in (FStar_Syntax_Util.arrow _146_1025 _146_1024)))
in (
# 1824 "FStar.TypeChecker.Tc.fst"
let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (
# 1825 "FStar.TypeChecker.Tc.fst"
let a1 = (let _146_1027 = (let _146_1026 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _146_1026))
in (FStar_Syntax_Syntax.gen_bv "a1" None _146_1027))
in (
# 1826 "FStar.TypeChecker.Tc.fst"
let a2 = (let _146_1029 = (let _146_1028 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_1028))
in (FStar_Syntax_Syntax.gen_bv "a2" None _146_1029))
in (
# 1827 "FStar.TypeChecker.Tc.fst"
let ret = (let _146_1034 = (let _146_1033 = (let _146_1032 = (let _146_1031 = (let _146_1030 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx _146_1030))
in (FStar_Syntax_Syntax.mk_Total _146_1031))
in (FStar_Syntax_Util.lcomp_of_comp _146_1032))
in FStar_Util.Inl (_146_1033))
in Some (_146_1034))
in (let _146_1054 = (binders_of_list (((t1, true))::((t2, true))::((t3, true))::((f, false))::((a1, false))::((a2, false))::[]))
in (let _146_1053 = (let _146_1052 = (let _146_1051 = (let _146_1050 = (let _146_1049 = (let _146_1048 = (let _146_1045 = (let _146_1044 = (let _146_1043 = (let _146_1042 = (let _146_1041 = (let _146_1038 = (let _146_1037 = (let _146_1036 = (let _146_1035 = (FStar_Syntax_Syntax.bv_to_name f)
in (_146_1035)::[])
in (unknown)::_146_1036)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1037))
in (FStar_Syntax_Util.mk_app c_pure _146_1038))
in (let _146_1040 = (let _146_1039 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_146_1039)::[])
in (_146_1041)::_146_1040))
in (unknown)::_146_1042)
in (unknown)::_146_1043)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1044))
in (FStar_Syntax_Util.mk_app c_app _146_1045))
in (let _146_1047 = (let _146_1046 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_146_1046)::[])
in (_146_1048)::_146_1047))
in (unknown)::_146_1049)
in (unknown)::_146_1050)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1051))
in (FStar_Syntax_Util.mk_app c_app _146_1052))
in (FStar_Syntax_Util.abs _146_1054 _146_1053 ret)))))))))))
in (
# 1838 "FStar.TypeChecker.Tc.fst"
let _57_2465 = (let _146_1058 = (let _146_1057 = (let _146_1056 = (let _146_1055 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1055)::[])
in (FStar_List.append binders _146_1056))
in (FStar_Syntax_Util.abs _146_1057 c_lift2 None))
in (check "lift2" _146_1058))
in (
# 1844 "FStar.TypeChecker.Tc.fst"
let c_push = (
# 1845 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (
# 1846 "FStar.TypeChecker.Tc.fst"
let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (
# 1847 "FStar.TypeChecker.Tc.fst"
let t_f = (let _146_1064 = (let _146_1060 = (let _146_1059 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_1059))
in (_146_1060)::[])
in (let _146_1063 = (let _146_1062 = (let _146_1061 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_1061))
in (FStar_Syntax_Syntax.mk_Total _146_1062))
in (FStar_Syntax_Util.arrow _146_1064 _146_1063)))
in (
# 1851 "FStar.TypeChecker.Tc.fst"
let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (
# 1852 "FStar.TypeChecker.Tc.fst"
let ret = (let _146_1074 = (let _146_1073 = (let _146_1072 = (let _146_1071 = (let _146_1070 = (let _146_1069 = (let _146_1066 = (let _146_1065 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_1065))
in (_146_1066)::[])
in (let _146_1068 = (let _146_1067 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _146_1067))
in (FStar_Syntax_Util.arrow _146_1069 _146_1068)))
in (mk_ctx _146_1070))
in (FStar_Syntax_Syntax.mk_Total _146_1071))
in (FStar_Syntax_Util.lcomp_of_comp _146_1072))
in FStar_Util.Inl (_146_1073))
in Some (_146_1074))
in (
# 1855 "FStar.TypeChecker.Tc.fst"
let e1 = (let _146_1075 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _146_1075))
in (
# 1856 "FStar.TypeChecker.Tc.fst"
let gamma = (mk_gamma ())
in (
# 1857 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1085 = (let _146_1078 = (FStar_Syntax_Syntax.binders_of_list gamma)
in (let _146_1077 = (let _146_1076 = (FStar_Syntax_Syntax.mk_binder e1)
in (_146_1076)::[])
in (FStar_List.append _146_1078 _146_1077)))
in (let _146_1084 = (let _146_1083 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _146_1082 = (let _146_1081 = (let _146_1079 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _146_1079))
in (let _146_1080 = (args_of_bv gamma)
in (_146_1081)::_146_1080))
in (FStar_Syntax_Util.mk_app _146_1083 _146_1082)))
in (FStar_Syntax_Util.abs _146_1085 _146_1084 ret)))
in (let _146_1086 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::[]))
in (FStar_Syntax_Util.abs _146_1086 body ret))))))))))
in (
# 1862 "FStar.TypeChecker.Tc.fst"
let _57_2476 = (let _146_1090 = (let _146_1089 = (let _146_1088 = (let _146_1087 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1087)::[])
in (FStar_List.append binders _146_1088))
in (FStar_Syntax_Util.abs _146_1089 c_push None))
in (check "push" _146_1090))
in (
# 1864 "FStar.TypeChecker.Tc.fst"
let ret_tot_wp_a = (let _146_1093 = (let _146_1092 = (let _146_1091 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _146_1091))
in FStar_Util.Inl (_146_1092))
in Some (_146_1093))
in (
# 1870 "FStar.TypeChecker.Tc.fst"
let wp_if_then_else = (
# 1871 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _146_1104 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (let _146_1103 = (
# 1876 "FStar.TypeChecker.Tc.fst"
let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_unfoldable (2)) None)
in (let _146_1102 = (let _146_1101 = (let _146_1100 = (let _146_1099 = (let _146_1098 = (let _146_1097 = (let _146_1096 = (let _146_1095 = (let _146_1094 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _146_1094))
in (_146_1095)::[])
in (FStar_Syntax_Util.mk_app l_ite _146_1096))
in (_146_1097)::[])
in (unknown)::_146_1098)
in (unknown)::_146_1099)
in (unknown)::_146_1100)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1101))
in (FStar_Syntax_Util.mk_app c_lift2 _146_1102)))
in (FStar_Syntax_Util.abs _146_1104 _146_1103 ret_tot_wp_a))))
in (
# 1884 "FStar.TypeChecker.Tc.fst"
let wp_if_then_else = (normalize_and_make_binders_explicit wp_if_then_else)
in (
# 1885 "FStar.TypeChecker.Tc.fst"
let _57_2483 = (let _146_1105 = (FStar_Syntax_Util.abs binders wp_if_then_else None)
in (check "wp_if_then_else" _146_1105))
in (
# 1891 "FStar.TypeChecker.Tc.fst"
let wp_binop = (
# 1892 "FStar.TypeChecker.Tc.fst"
let l = (FStar_Syntax_Syntax.gen_bv "l" None wp_a)
in (
# 1893 "FStar.TypeChecker.Tc.fst"
let op = (let _146_1111 = (let _146_1110 = (let _146_1108 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Util.ktype0)
in (let _146_1107 = (let _146_1106 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Util.ktype0)
in (_146_1106)::[])
in (_146_1108)::_146_1107))
in (let _146_1109 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _146_1110 _146_1109)))
in (FStar_Syntax_Syntax.gen_bv "op" None _146_1111))
in (
# 1896 "FStar.TypeChecker.Tc.fst"
let r = (FStar_Syntax_Syntax.gen_bv "r" None wp_a)
in (let _146_1123 = (FStar_Syntax_Syntax.binders_of_list ((a)::(l)::(op)::(r)::[]))
in (let _146_1122 = (let _146_1121 = (let _146_1120 = (let _146_1119 = (let _146_1118 = (let _146_1117 = (let _146_1116 = (FStar_Syntax_Syntax.bv_to_name op)
in (let _146_1115 = (let _146_1114 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _146_1113 = (let _146_1112 = (FStar_Syntax_Syntax.bv_to_name r)
in (_146_1112)::[])
in (_146_1114)::_146_1113))
in (_146_1116)::_146_1115))
in (unknown)::_146_1117)
in (unknown)::_146_1118)
in (unknown)::_146_1119)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1120))
in (FStar_Syntax_Util.mk_app c_lift2 _146_1121))
in (FStar_Syntax_Util.abs _146_1123 _146_1122 ret_tot_wp_a))))))
in (
# 1904 "FStar.TypeChecker.Tc.fst"
let wp_binop = (normalize_and_make_binders_explicit wp_binop)
in (
# 1905 "FStar.TypeChecker.Tc.fst"
let _57_2490 = (let _146_1124 = (FStar_Syntax_Util.abs binders wp_binop None)
in (check "wp_binop" _146_1124))
in (
# 1910 "FStar.TypeChecker.Tc.fst"
let wp_assert = (
# 1911 "FStar.TypeChecker.Tc.fst"
let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (
# 1912 "FStar.TypeChecker.Tc.fst"
let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (
# 1913 "FStar.TypeChecker.Tc.fst"
let l_and = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (
# 1914 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1138 = (let _146_1137 = (let _146_1136 = (let _146_1135 = (let _146_1134 = (let _146_1131 = (let _146_1130 = (let _146_1129 = (let _146_1128 = (let _146_1127 = (let _146_1126 = (let _146_1125 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _146_1125))
in (_146_1126)::[])
in (FStar_Syntax_Util.mk_app l_and _146_1127))
in (_146_1128)::[])
in (unknown)::_146_1129)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1130))
in (FStar_Syntax_Util.mk_app c_pure _146_1131))
in (let _146_1133 = (let _146_1132 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_146_1132)::[])
in (_146_1134)::_146_1133))
in (unknown)::_146_1135)
in (unknown)::_146_1136)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1137))
in (FStar_Syntax_Util.mk_app c_app _146_1138))
in (let _146_1139 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _146_1139 body ret_tot_wp_a))))))
in (
# 1924 "FStar.TypeChecker.Tc.fst"
let wp_assert = (normalize_and_make_binders_explicit wp_assert)
in (
# 1925 "FStar.TypeChecker.Tc.fst"
let _57_2498 = (let _146_1140 = (FStar_Syntax_Util.abs binders wp_assert None)
in (check "wp_assert" _146_1140))
in (
# 1930 "FStar.TypeChecker.Tc.fst"
let wp_assume = (
# 1931 "FStar.TypeChecker.Tc.fst"
let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (
# 1932 "FStar.TypeChecker.Tc.fst"
let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (
# 1933 "FStar.TypeChecker.Tc.fst"
let l_imp = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (
# 1934 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1154 = (let _146_1153 = (let _146_1152 = (let _146_1151 = (let _146_1150 = (let _146_1147 = (let _146_1146 = (let _146_1145 = (let _146_1144 = (let _146_1143 = (let _146_1142 = (let _146_1141 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _146_1141))
in (_146_1142)::[])
in (FStar_Syntax_Util.mk_app l_imp _146_1143))
in (_146_1144)::[])
in (unknown)::_146_1145)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1146))
in (FStar_Syntax_Util.mk_app c_pure _146_1147))
in (let _146_1149 = (let _146_1148 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_146_1148)::[])
in (_146_1150)::_146_1149))
in (unknown)::_146_1151)
in (unknown)::_146_1152)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1153))
in (FStar_Syntax_Util.mk_app c_app _146_1154))
in (let _146_1155 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _146_1155 body ret_tot_wp_a))))))
in (
# 1944 "FStar.TypeChecker.Tc.fst"
let wp_assume = (normalize_and_make_binders_explicit wp_assume)
in (
# 1945 "FStar.TypeChecker.Tc.fst"
let _57_2506 = (let _146_1156 = (FStar_Syntax_Util.abs binders wp_assume None)
in (check "wp_assume" _146_1156))
in (
# 1947 "FStar.TypeChecker.Tc.fst"
let tforall = (let _146_1159 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _146_1158 = (let _146_1157 = (FStar_Syntax_Syntax.as_arg unknown)
in (_146_1157)::[])
in (FStar_Syntax_Util.mk_app _146_1159 _146_1158)))
in (
# 1953 "FStar.TypeChecker.Tc.fst"
let wp_close = (
# 1954 "FStar.TypeChecker.Tc.fst"
let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (
# 1955 "FStar.TypeChecker.Tc.fst"
let t_f = (let _146_1163 = (let _146_1161 = (let _146_1160 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _146_1160))
in (_146_1161)::[])
in (let _146_1162 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1163 _146_1162)))
in (
# 1956 "FStar.TypeChecker.Tc.fst"
let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (
# 1957 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1176 = (let _146_1175 = (let _146_1174 = (let _146_1173 = (let _146_1172 = (let _146_1164 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((unknown)::(tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _146_1164))
in (let _146_1171 = (let _146_1170 = (let _146_1169 = (let _146_1168 = (let _146_1167 = (let _146_1166 = (let _146_1165 = (FStar_Syntax_Syntax.bv_to_name f)
in (_146_1165)::[])
in (unknown)::_146_1166)
in (unknown)::_146_1167)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1168))
in (FStar_Syntax_Util.mk_app c_push _146_1169))
in (_146_1170)::[])
in (_146_1172)::_146_1171))
in (unknown)::_146_1173)
in (unknown)::_146_1174)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1175))
in (FStar_Syntax_Util.mk_app c_app _146_1176))
in (let _146_1177 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_Syntax_Util.abs _146_1177 body ret_tot_wp_a))))))
in (
# 1969 "FStar.TypeChecker.Tc.fst"
let wp_close = (normalize_and_make_binders_explicit wp_close)
in (
# 1970 "FStar.TypeChecker.Tc.fst"
let _57_2515 = (let _146_1178 = (FStar_Syntax_Util.abs binders wp_close None)
in (check "wp_close" _146_1178))
in (
# 1972 "FStar.TypeChecker.Tc.fst"
let ret_tot_type0 = (let _146_1181 = (let _146_1180 = (let _146_1179 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_1179))
in FStar_Util.Inl (_146_1180))
in Some (_146_1181))
in (
# 1973 "FStar.TypeChecker.Tc.fst"
let mk_forall = (fun x body -> (
# 1974 "FStar.TypeChecker.Tc.fst"
let tforall = (let _146_1188 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _146_1187 = (let _146_1186 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (_146_1186)::[])
in (FStar_Syntax_Util.mk_app _146_1188 _146_1187)))
in (let _146_1195 = (let _146_1194 = (let _146_1193 = (let _146_1192 = (let _146_1191 = (let _146_1190 = (let _146_1189 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_1189)::[])
in (FStar_Syntax_Util.abs _146_1190 body ret_tot_type0))
in (FStar_Syntax_Syntax.as_arg _146_1191))
in (_146_1192)::[])
in (tforall, _146_1193))
in FStar_Syntax_Syntax.Tm_app (_146_1194))
in (FStar_Syntax_Syntax.mk _146_1195 None FStar_Range.dummyRange))))
in (
# 1985 "FStar.TypeChecker.Tc.fst"
let rec mk_leq = (fun t x y -> (match ((let _146_1203 = (let _146_1202 = (FStar_Syntax_Subst.compress t)
in (normalize _146_1202))
in _146_1203.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_2527) -> begin
(FStar_Syntax_Util.mk_imp x y)
end
| (FStar_Syntax_Syntax.Tm_arrow (binder::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow (binder::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) when (FStar_Syntax_Syntax.is_null_binder binder) -> begin
(
# 1992 "FStar.TypeChecker.Tc.fst"
let a = (Prims.fst binder).FStar_Syntax_Syntax.sort
in (
# 1994 "FStar.TypeChecker.Tc.fst"
let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (
# 1995 "FStar.TypeChecker.Tc.fst"
let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (
# 1996 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1215 = (let _146_1205 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _146_1204 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_leq a _146_1205 _146_1204)))
in (let _146_1214 = (let _146_1213 = (let _146_1208 = (let _146_1207 = (let _146_1206 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _146_1206))
in (_146_1207)::[])
in (FStar_Syntax_Util.mk_app x _146_1208))
in (let _146_1212 = (let _146_1211 = (let _146_1210 = (let _146_1209 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _146_1209))
in (_146_1210)::[])
in (FStar_Syntax_Util.mk_app y _146_1211))
in (mk_leq b _146_1213 _146_1212)))
in (FStar_Syntax_Util.mk_imp _146_1215 _146_1214)))
in (let _146_1216 = (mk_forall a2 body)
in (mk_forall a1 _146_1216))))))
end
| FStar_Syntax_Syntax.Tm_arrow (binder::binders, comp) -> begin
(
# 2004 "FStar.TypeChecker.Tc.fst"
let t = (
# 2004 "FStar.TypeChecker.Tc.fst"
let _57_2563 = t
in (let _146_1220 = (let _146_1219 = (let _146_1218 = (let _146_1217 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _146_1217))
in ((binder)::[], _146_1218))
in FStar_Syntax_Syntax.Tm_arrow (_146_1219))
in {FStar_Syntax_Syntax.n = _146_1220; FStar_Syntax_Syntax.tk = _57_2563.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2563.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2563.FStar_Syntax_Syntax.vars}))
in (mk_leq t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_57_2567) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _57_2570 -> begin
(FStar_Syntax_Util.mk_eq t t x y)
end))
in (
# 2013 "FStar.TypeChecker.Tc.fst"
let stronger = (
# 2014 "FStar.TypeChecker.Tc.fst"
let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (
# 2015 "FStar.TypeChecker.Tc.fst"
let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (
# 2016 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1222 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _146_1221 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_leq wp_a _146_1222 _146_1221)))
in (let _146_1223 = (FStar_Syntax_Syntax.binders_of_list ((wp1)::(wp2)::[]))
in (FStar_Syntax_Util.abs _146_1223 body ret_tot_type0)))))
in (
# 2019 "FStar.TypeChecker.Tc.fst"
let _57_2575 = (let _146_1227 = (let _146_1226 = (let _146_1225 = (let _146_1224 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1224)::[])
in (FStar_List.append binders _146_1225))
in (FStar_Syntax_Util.abs _146_1226 stronger None))
in (check "stronger" _146_1227))
in (
# 2021 "FStar.TypeChecker.Tc.fst"
let null_wp = (Prims.snd ed.FStar_Syntax_Syntax.null_wp)
in (
# 2025 "FStar.TypeChecker.Tc.fst"
let wp_trivial = (
# 2026 "FStar.TypeChecker.Tc.fst"
let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (
# 2027 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1235 = (let _146_1234 = (let _146_1233 = (let _146_1230 = (let _146_1229 = (let _146_1228 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _146_1228))
in (_146_1229)::[])
in (FStar_Syntax_Util.mk_app null_wp _146_1230))
in (let _146_1232 = (let _146_1231 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_146_1231)::[])
in (_146_1233)::_146_1232))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1234))
in (FStar_Syntax_Util.mk_app stronger _146_1235))
in (let _146_1236 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_Syntax_Util.abs _146_1236 body ret_tot_type0))))
in (
# 2033 "FStar.TypeChecker.Tc.fst"
let wp_trivial = (normalize_and_make_binders_explicit wp_trivial)
in (
# 2034 "FStar.TypeChecker.Tc.fst"
let _57_2582 = (let _146_1237 = (FStar_Syntax_Util.abs binders wp_trivial None)
in (check "wp_trivial" _146_1237))
in (
# 2036 "FStar.TypeChecker.Tc.fst"
let _57_2584 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2584.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2584.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2584.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2584.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2584.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _57_2584.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2584.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _57_2584.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = ([], wp_if_then_else); FStar_Syntax_Syntax.ite_wp = _57_2584.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _57_2584.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = ([], wp_binop); FStar_Syntax_Syntax.wp_as_type = _57_2584.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = ([], wp_close); FStar_Syntax_Syntax.assert_p = ([], wp_assert); FStar_Syntax_Syntax.assume_p = ([], wp_assume); FStar_Syntax_Syntax.null_wp = _57_2584.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = ([], wp_trivial)})))))))))))))))))))))))))))))))))))))))))
end))))))))

# 2046 "FStar.TypeChecker.Tc.fst"
let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  effect_cost  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed is_for_free -> (
# 2047 "FStar.TypeChecker.Tc.fst"
let _57_2589 = ()
in (
# 2048 "FStar.TypeChecker.Tc.fst"
let _57_2593 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_57_2593) with
| (binders_un, signature_un) -> begin
(
# 2049 "FStar.TypeChecker.Tc.fst"
let _57_2598 = (tc_tparams env0 binders_un)
in (match (_57_2598) with
| (binders, env, _57_2597) -> begin
(
# 2050 "FStar.TypeChecker.Tc.fst"
let _57_2602 = (tc_trivial_guard env signature_un)
in (match (_57_2602) with
| (signature, _57_2601) -> begin
(
# 2051 "FStar.TypeChecker.Tc.fst"
let ed = (
# 2051 "FStar.TypeChecker.Tc.fst"
let _57_2603 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2603.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2603.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2603.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _57_2603.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2603.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _57_2603.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = _57_2603.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _57_2603.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _57_2603.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = _57_2603.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _57_2603.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _57_2603.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _57_2603.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _57_2603.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _57_2603.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _57_2603.FStar_Syntax_Syntax.trivial})
in (
# 2054 "FStar.TypeChecker.Tc.fst"
let _57_2609 = (open_effect_decl env ed)
in (match (_57_2609) with
| (ed, a, wp_a) -> begin
(
# 2055 "FStar.TypeChecker.Tc.fst"
let get_effect_signature = (fun _57_2611 -> (match (()) with
| () -> begin
(
# 2056 "FStar.TypeChecker.Tc.fst"
let _57_2615 = (tc_trivial_guard env signature_un)
in (match (_57_2615) with
| (signature, _57_2614) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (
# 2060 "FStar.TypeChecker.Tc.fst"
let env = (let _146_1246 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _146_1246))
in (
# 2062 "FStar.TypeChecker.Tc.fst"
let _57_2617 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _146_1249 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _146_1248 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _146_1247 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checking effect signature: %s %s : %s\n" _146_1249 _146_1248 _146_1247))))
end else begin
()
end
in (
# 2068 "FStar.TypeChecker.Tc.fst"
let check_and_gen' = (fun env _57_2624 k -> (match (_57_2624) with
| (_57_2622, t) -> begin
(check_and_gen env t k)
end))
in (
# 2072 "FStar.TypeChecker.Tc.fst"
let ed = (match (is_for_free) with
| NotForFree -> begin
ed
end
| ForFree -> begin
(gen_wps_for_free env binders a wp_a ed)
end)
in (
# 2077 "FStar.TypeChecker.Tc.fst"
let ret = (
# 2078 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1261 = (let _146_1259 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1258 = (let _146_1257 = (let _146_1256 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_1256))
in (_146_1257)::[])
in (_146_1259)::_146_1258))
in (let _146_1260 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _146_1261 _146_1260)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (
# 2081 "FStar.TypeChecker.Tc.fst"
let bind_wp = (
# 2082 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 2083 "FStar.TypeChecker.Tc.fst"
let _57_2634 = (get_effect_signature ())
in (match (_57_2634) with
| (b, wp_b) -> begin
(
# 2084 "FStar.TypeChecker.Tc.fst"
let a_wp_b = (let _146_1265 = (let _146_1263 = (let _146_1262 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_1262))
in (_146_1263)::[])
in (let _146_1264 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _146_1265 _146_1264)))
in (
# 2085 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = a_wp_b
in (
# 2086 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1280 = (let _146_1278 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _146_1277 = (let _146_1276 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1275 = (let _146_1274 = (FStar_Syntax_Syntax.mk_binder b)
in (let _146_1273 = (let _146_1272 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_1271 = (let _146_1270 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _146_1269 = (let _146_1268 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (let _146_1267 = (let _146_1266 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_146_1266)::[])
in (_146_1268)::_146_1267))
in (_146_1270)::_146_1269))
in (_146_1272)::_146_1271))
in (_146_1274)::_146_1273))
in (_146_1276)::_146_1275))
in (_146_1278)::_146_1277))
in (let _146_1279 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _146_1280 _146_1279)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k))))
end)))
in (
# 2093 "FStar.TypeChecker.Tc.fst"
let bind_wlp = (
# 2094 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 2095 "FStar.TypeChecker.Tc.fst"
let _57_2642 = (get_effect_signature ())
in (match (_57_2642) with
| (b, wlp_b) -> begin
(
# 2096 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = (let _146_1284 = (let _146_1282 = (let _146_1281 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_1281))
in (_146_1282)::[])
in (let _146_1283 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _146_1284 _146_1283)))
in (
# 2097 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1295 = (let _146_1293 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _146_1292 = (let _146_1291 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1290 = (let _146_1289 = (FStar_Syntax_Syntax.mk_binder b)
in (let _146_1288 = (let _146_1287 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _146_1286 = (let _146_1285 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_146_1285)::[])
in (_146_1287)::_146_1286))
in (_146_1289)::_146_1288))
in (_146_1291)::_146_1290))
in (_146_1293)::_146_1292))
in (let _146_1294 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _146_1295 _146_1294)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wlp expected_k)))
end)))
in (
# 2104 "FStar.TypeChecker.Tc.fst"
let if_then_else = (
# 2105 "FStar.TypeChecker.Tc.fst"
let p = (let _146_1297 = (let _146_1296 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1296 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _146_1297))
in (
# 2106 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1306 = (let _146_1304 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1303 = (let _146_1302 = (FStar_Syntax_Syntax.mk_binder p)
in (let _146_1301 = (let _146_1300 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_1299 = (let _146_1298 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1298)::[])
in (_146_1300)::_146_1299))
in (_146_1302)::_146_1301))
in (_146_1304)::_146_1303))
in (let _146_1305 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1306 _146_1305)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (
# 2112 "FStar.TypeChecker.Tc.fst"
let ite_wp = (
# 2113 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 2114 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1313 = (let _146_1311 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1310 = (let _146_1309 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _146_1308 = (let _146_1307 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1307)::[])
in (_146_1309)::_146_1308))
in (_146_1311)::_146_1310))
in (let _146_1312 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1313 _146_1312)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k)))
in (
# 2120 "FStar.TypeChecker.Tc.fst"
let ite_wlp = (
# 2121 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 2122 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1318 = (let _146_1316 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1315 = (let _146_1314 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (_146_1314)::[])
in (_146_1316)::_146_1315))
in (let _146_1317 = (FStar_Syntax_Syntax.mk_Total wlp_a)
in (FStar_Syntax_Util.arrow _146_1318 _146_1317)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wlp expected_k)))
in (
# 2127 "FStar.TypeChecker.Tc.fst"
let wp_binop = (
# 2128 "FStar.TypeChecker.Tc.fst"
let bin_op = (
# 2129 "FStar.TypeChecker.Tc.fst"
let _57_2657 = (FStar_Syntax_Util.type_u ())
in (match (_57_2657) with
| (t1, u1) -> begin
(
# 2130 "FStar.TypeChecker.Tc.fst"
let _57_2660 = (FStar_Syntax_Util.type_u ())
in (match (_57_2660) with
| (t2, u2) -> begin
(
# 2131 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1319 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_max ((u1)::(u2)::[]))) None _146_1319))
in (let _146_1324 = (let _146_1322 = (FStar_Syntax_Syntax.null_binder t1)
in (let _146_1321 = (let _146_1320 = (FStar_Syntax_Syntax.null_binder t2)
in (_146_1320)::[])
in (_146_1322)::_146_1321))
in (let _146_1323 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _146_1324 _146_1323))))
end))
end))
in (
# 2133 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1333 = (let _146_1331 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1330 = (let _146_1329 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_1328 = (let _146_1327 = (FStar_Syntax_Syntax.null_binder bin_op)
in (let _146_1326 = (let _146_1325 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1325)::[])
in (_146_1327)::_146_1326))
in (_146_1329)::_146_1328))
in (_146_1331)::_146_1330))
in (let _146_1332 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1333 _146_1332)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_binop expected_k)))
in (
# 2140 "FStar.TypeChecker.Tc.fst"
let wp_as_type = (
# 2141 "FStar.TypeChecker.Tc.fst"
let _57_2668 = (FStar_Syntax_Util.type_u ())
in (match (_57_2668) with
| (t, _57_2667) -> begin
(
# 2142 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1338 = (let _146_1336 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1335 = (let _146_1334 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1334)::[])
in (_146_1336)::_146_1335))
in (let _146_1337 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _146_1338 _146_1337)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (
# 2147 "FStar.TypeChecker.Tc.fst"
let close_wp = (
# 2148 "FStar.TypeChecker.Tc.fst"
let b = (let _146_1340 = (let _146_1339 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1339 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _146_1340))
in (
# 2149 "FStar.TypeChecker.Tc.fst"
let b_wp_a = (let _146_1344 = (let _146_1342 = (let _146_1341 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _146_1341))
in (_146_1342)::[])
in (let _146_1343 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1344 _146_1343)))
in (
# 2150 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1351 = (let _146_1349 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1348 = (let _146_1347 = (FStar_Syntax_Syntax.mk_binder b)
in (let _146_1346 = (let _146_1345 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_146_1345)::[])
in (_146_1347)::_146_1346))
in (_146_1349)::_146_1348))
in (let _146_1350 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1351 _146_1350)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (
# 2154 "FStar.TypeChecker.Tc.fst"
let assert_p = (
# 2155 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1360 = (let _146_1358 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1357 = (let _146_1356 = (let _146_1353 = (let _146_1352 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1352 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _146_1353))
in (let _146_1355 = (let _146_1354 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1354)::[])
in (_146_1356)::_146_1355))
in (_146_1358)::_146_1357))
in (let _146_1359 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1360 _146_1359)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (
# 2161 "FStar.TypeChecker.Tc.fst"
let assume_p = (
# 2162 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1369 = (let _146_1367 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1366 = (let _146_1365 = (let _146_1362 = (let _146_1361 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1361 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _146_1362))
in (let _146_1364 = (let _146_1363 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1363)::[])
in (_146_1365)::_146_1364))
in (_146_1367)::_146_1366))
in (let _146_1368 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1369 _146_1368)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (
# 2168 "FStar.TypeChecker.Tc.fst"
let null_wp = (
# 2169 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1372 = (let _146_1370 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1370)::[])
in (let _146_1371 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1372 _146_1371)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (
# 2173 "FStar.TypeChecker.Tc.fst"
let trivial_wp = (
# 2174 "FStar.TypeChecker.Tc.fst"
let _57_2684 = (FStar_Syntax_Util.type_u ())
in (match (_57_2684) with
| (t, _57_2683) -> begin
(
# 2175 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1377 = (let _146_1375 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1374 = (let _146_1373 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1373)::[])
in (_146_1375)::_146_1374))
in (let _146_1376 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _146_1377 _146_1376)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (
# 2181 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1378 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _146_1378))
in (
# 2182 "FStar.TypeChecker.Tc.fst"
let _57_2690 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_57_2690) with
| (univs, t) -> begin
(
# 2183 "FStar.TypeChecker.Tc.fst"
let _57_2706 = (match ((let _146_1380 = (let _146_1379 = (FStar_Syntax_Subst.compress t)
in _146_1379.FStar_Syntax_Syntax.n)
in (binders, _146_1380))) with
| ([], _57_2693) -> begin
([], t)
end
| (_57_2696, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _57_2703 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_2706) with
| (binders, signature) -> begin
(
# 2187 "FStar.TypeChecker.Tc.fst"
let close = (fun n ts -> (
# 2188 "FStar.TypeChecker.Tc.fst"
let ts = (let _146_1385 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _146_1385))
in (
# 2189 "FStar.TypeChecker.Tc.fst"
let _57_2711 = ()
in ts)))
in (
# 2191 "FStar.TypeChecker.Tc.fst"
let ed = (
# 2191 "FStar.TypeChecker.Tc.fst"
let _57_2713 = ed
in (let _146_1398 = (close 0 ret)
in (let _146_1397 = (close 1 bind_wp)
in (let _146_1396 = (close 1 bind_wlp)
in (let _146_1395 = (close 0 if_then_else)
in (let _146_1394 = (close 0 ite_wp)
in (let _146_1393 = (close 0 ite_wlp)
in (let _146_1392 = (close 0 wp_binop)
in (let _146_1391 = (close 0 wp_as_type)
in (let _146_1390 = (close 1 close_wp)
in (let _146_1389 = (close 0 assert_p)
in (let _146_1388 = (close 0 assume_p)
in (let _146_1387 = (close 0 null_wp)
in (let _146_1386 = (close 0 trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _57_2713.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2713.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _146_1398; FStar_Syntax_Syntax.bind_wp = _146_1397; FStar_Syntax_Syntax.bind_wlp = _146_1396; FStar_Syntax_Syntax.if_then_else = _146_1395; FStar_Syntax_Syntax.ite_wp = _146_1394; FStar_Syntax_Syntax.ite_wlp = _146_1393; FStar_Syntax_Syntax.wp_binop = _146_1392; FStar_Syntax_Syntax.wp_as_type = _146_1391; FStar_Syntax_Syntax.close_wp = _146_1390; FStar_Syntax_Syntax.assert_p = _146_1389; FStar_Syntax_Syntax.assume_p = _146_1388; FStar_Syntax_Syntax.null_wp = _146_1387; FStar_Syntax_Syntax.trivial = _146_1386}))))))))))))))
in (
# 2209 "FStar.TypeChecker.Tc.fst"
let _57_2716 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1399 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _146_1399))
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

# 2213 "FStar.TypeChecker.Tc.fst"
let tc_lex_t = (fun env ses quals lids -> (
# 2220 "FStar.TypeChecker.Tc.fst"
let _57_2722 = ()
in (
# 2221 "FStar.TypeChecker.Tc.fst"
let _57_2730 = ()
in (match (ses) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _57_2759, _57_2761, [], r)::FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _57_2750, r1)::FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _57_2739, r2)::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(
# 2236 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (
# 2237 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (
# 2238 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (
# 2239 "FStar.TypeChecker.Tc.fst"
let tc = FStar_Syntax_Syntax.Sig_inductive_typ ((lex_t, (u)::[], [], t, [], (FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[], [], r))
in (
# 2241 "FStar.TypeChecker.Tc.fst"
let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (
# 2242 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (let _146_1407 = (let _146_1406 = (let _146_1405 = (let _146_1404 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _146_1404 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1405, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1406))
in (FStar_Syntax_Syntax.mk _146_1407 None r1))
in (
# 2243 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (
# 2244 "FStar.TypeChecker.Tc.fst"
let dc_lextop = FStar_Syntax_Syntax.Sig_datacon ((lex_top, (utop)::[], lex_top_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r1))
in (
# 2246 "FStar.TypeChecker.Tc.fst"
let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 2247 "FStar.TypeChecker.Tc.fst"
let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 2248 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (
# 2249 "FStar.TypeChecker.Tc.fst"
let a = (let _146_1408 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1408))
in (
# 2250 "FStar.TypeChecker.Tc.fst"
let hd = (let _146_1409 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1409))
in (
# 2251 "FStar.TypeChecker.Tc.fst"
let tl = (let _146_1414 = (let _146_1413 = (let _146_1412 = (let _146_1411 = (let _146_1410 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _146_1410 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1411, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1412))
in (FStar_Syntax_Syntax.mk _146_1413 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1414))
in (
# 2252 "FStar.TypeChecker.Tc.fst"
let res = (let _146_1418 = (let _146_1417 = (let _146_1416 = (let _146_1415 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _146_1415 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1416, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1417))
in (FStar_Syntax_Syntax.mk _146_1418 None r2))
in (let _146_1419 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _146_1419))))))
in (
# 2254 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (
# 2255 "FStar.TypeChecker.Tc.fst"
let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _146_1421 = (let _146_1420 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _146_1420))
in FStar_Syntax_Syntax.Sig_bundle (_146_1421)))))))))))))))
end
| _57_2785 -> begin
(let _146_1423 = (let _146_1422 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _146_1422))
in (FStar_All.failwith _146_1423))
end))))

# 2261 "FStar.TypeChecker.Tc.fst"
let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (
# 2324 "FStar.TypeChecker.Tc.fst"
let warn_positivity = (fun l r -> (let _146_1437 = (let _146_1436 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _146_1436))
in (FStar_TypeChecker_Errors.diag r _146_1437)))
in (
# 2326 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2329 "FStar.TypeChecker.Tc.fst"
let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(
# 2334 "FStar.TypeChecker.Tc.fst"
let _57_2807 = ()
in (
# 2335 "FStar.TypeChecker.Tc.fst"
let _57_2809 = (warn_positivity tc r)
in (
# 2336 "FStar.TypeChecker.Tc.fst"
let _57_2813 = (FStar_Syntax_Subst.open_term tps k)
in (match (_57_2813) with
| (tps, k) -> begin
(
# 2337 "FStar.TypeChecker.Tc.fst"
let _57_2817 = (tc_tparams env tps)
in (match (_57_2817) with
| (tps, env_tps, us) -> begin
(
# 2338 "FStar.TypeChecker.Tc.fst"
let _57_2820 = (FStar_Syntax_Util.arrow_formals k)
in (match (_57_2820) with
| (indices, t) -> begin
(
# 2339 "FStar.TypeChecker.Tc.fst"
let _57_2824 = (tc_tparams env_tps indices)
in (match (_57_2824) with
| (indices, env', us') -> begin
(
# 2340 "FStar.TypeChecker.Tc.fst"
let _57_2828 = (tc_trivial_guard env' t)
in (match (_57_2828) with
| (t, _57_2827) -> begin
(
# 2341 "FStar.TypeChecker.Tc.fst"
let k = (let _146_1442 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _146_1442))
in (
# 2342 "FStar.TypeChecker.Tc.fst"
let _57_2832 = (FStar_Syntax_Util.type_u ())
in (match (_57_2832) with
| (t_type, u) -> begin
(
# 2343 "FStar.TypeChecker.Tc.fst"
let _57_2833 = (let _146_1443 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _146_1443))
in (
# 2345 "FStar.TypeChecker.Tc.fst"
let t_tc = (let _146_1444 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _146_1444))
in (
# 2346 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 2347 "FStar.TypeChecker.Tc.fst"
let k = (FStar_Syntax_Subst.close tps k)
in (
# 2348 "FStar.TypeChecker.Tc.fst"
let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _146_1445 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) ([], t_tc))
in (_146_1445, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u)))))))
end)))
end))
end))
end))
end))
end))))
end
| _57_2840 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 2355 "FStar.TypeChecker.Tc.fst"
let positive_if_pure = (fun _57_2842 l -> ())
in (
# 2358 "FStar.TypeChecker.Tc.fst"
let tc_data = (fun env tcs _57_6 -> (match (_57_6) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(
# 2360 "FStar.TypeChecker.Tc.fst"
let _57_2859 = ()
in (
# 2362 "FStar.TypeChecker.Tc.fst"
let _57_2894 = (
# 2363 "FStar.TypeChecker.Tc.fst"
let tps_u_opt = (FStar_Util.find_map tcs (fun _57_2863 -> (match (_57_2863) with
| (se, u_tc) -> begin
if (let _146_1458 = (let _146_1457 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _146_1457))
in (FStar_Ident.lid_equals tc_lid _146_1458)) then begin
(
# 2365 "FStar.TypeChecker.Tc.fst"
let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2865, _57_2867, tps, _57_2870, _57_2872, _57_2874, _57_2876, _57_2878) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _57_2884 -> (match (_57_2884) with
| (x, _57_2883) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _57_2886 -> begin
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
in (match (_57_2894) with
| (tps, u_tc) -> begin
(
# 2378 "FStar.TypeChecker.Tc.fst"
let _57_2914 = (match ((let _146_1460 = (FStar_Syntax_Subst.compress t)
in _146_1460.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(
# 2383 "FStar.TypeChecker.Tc.fst"
let _57_2902 = (FStar_Util.first_N ntps bs)
in (match (_57_2902) with
| (_57_2900, bs') -> begin
(
# 2384 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (
# 2385 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _57_2908 -> (match (_57_2908) with
| (x, _57_2907) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _146_1463 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _146_1463))))
end))
end
| _57_2911 -> begin
([], t)
end)
in (match (_57_2914) with
| (arguments, result) -> begin
(
# 2389 "FStar.TypeChecker.Tc.fst"
let _57_2915 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1466 = (FStar_Syntax_Print.lid_to_string c)
in (let _146_1465 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _146_1464 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _146_1466 _146_1465 _146_1464))))
end else begin
()
end
in (
# 2395 "FStar.TypeChecker.Tc.fst"
let _57_2920 = (tc_tparams env arguments)
in (match (_57_2920) with
| (arguments, env', us) -> begin
(
# 2396 "FStar.TypeChecker.Tc.fst"
let _57_2924 = (tc_trivial_guard env' result)
in (match (_57_2924) with
| (result, _57_2923) -> begin
(
# 2397 "FStar.TypeChecker.Tc.fst"
let _57_2928 = (FStar_Syntax_Util.head_and_args result)
in (match (_57_2928) with
| (head, _57_2927) -> begin
(
# 2398 "FStar.TypeChecker.Tc.fst"
let _57_2933 = (match ((let _146_1467 = (FStar_Syntax_Subst.compress head)
in _146_1467.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _57_2932 -> begin
(let _146_1471 = (let _146_1470 = (let _146_1469 = (let _146_1468 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _146_1468))
in (_146_1469, r))
in FStar_Syntax_Syntax.Error (_146_1470))
in (Prims.raise _146_1471))
end)
in (
# 2401 "FStar.TypeChecker.Tc.fst"
let g = (FStar_List.fold_left2 (fun g _57_2939 u_x -> (match (_57_2939) with
| (x, _57_2938) -> begin
(
# 2402 "FStar.TypeChecker.Tc.fst"
let _57_2941 = ()
in (let _146_1475 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _146_1475)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (
# 2408 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1479 = (let _146_1477 = (FStar_All.pipe_right tps (FStar_List.map (fun _57_2947 -> (match (_57_2947) with
| (x, _57_2946) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _146_1477 arguments))
in (let _146_1478 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _146_1479 _146_1478)))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _57_2950 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 2416 "FStar.TypeChecker.Tc.fst"
let generalize_and_inst_within = (fun env g tcs datas -> (
# 2417 "FStar.TypeChecker.Tc.fst"
let _57_2956 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2418 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_7 -> (match (_57_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2960, _57_2962, tps, k, _57_2966, _57_2968, _57_2970, _57_2972) -> begin
(let _146_1490 = (let _146_1489 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _146_1489))
in (FStar_Syntax_Syntax.null_binder _146_1490))
end
| _57_2976 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2421 "FStar.TypeChecker.Tc.fst"
let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _57_8 -> (match (_57_8) with
| FStar_Syntax_Syntax.Sig_datacon (_57_2980, _57_2982, t, _57_2985, _57_2987, _57_2989, _57_2991, _57_2993) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _57_2997 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2424 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1492 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _146_1492))
in (
# 2425 "FStar.TypeChecker.Tc.fst"
let _57_3000 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1493 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _146_1493))
end else begin
()
end
in (
# 2426 "FStar.TypeChecker.Tc.fst"
let _57_3004 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_57_3004) with
| (uvs, t) -> begin
(
# 2427 "FStar.TypeChecker.Tc.fst"
let _57_3006 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1497 = (let _146_1495 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _146_1495 (FStar_String.concat ", ")))
in (let _146_1496 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _146_1497 _146_1496)))
end else begin
()
end
in (
# 2430 "FStar.TypeChecker.Tc.fst"
let _57_3010 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_57_3010) with
| (uvs, t) -> begin
(
# 2431 "FStar.TypeChecker.Tc.fst"
let _57_3014 = (FStar_Syntax_Util.arrow_formals t)
in (match (_57_3014) with
| (args, _57_3013) -> begin
(
# 2432 "FStar.TypeChecker.Tc.fst"
let _57_3017 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_57_3017) with
| (tc_types, data_types) -> begin
(
# 2433 "FStar.TypeChecker.Tc.fst"
let tcs = (FStar_List.map2 (fun _57_3021 se -> (match (_57_3021) with
| (x, _57_3020) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3025, tps, _57_3028, mutuals, datas, quals, r) -> begin
(
# 2435 "FStar.TypeChecker.Tc.fst"
let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (
# 2436 "FStar.TypeChecker.Tc.fst"
let _57_3051 = (match ((let _146_1500 = (FStar_Syntax_Subst.compress ty)
in _146_1500.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 2438 "FStar.TypeChecker.Tc.fst"
let _57_3042 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_57_3042) with
| (tps, rest) -> begin
(
# 2439 "FStar.TypeChecker.Tc.fst"
let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _57_3045 -> begin
(let _146_1501 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _146_1501 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _57_3048 -> begin
([], ty)
end)
in (match (_57_3051) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _57_3053 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (
# 2449 "FStar.TypeChecker.Tc.fst"
let datas = (match (uvs) with
| [] -> begin
datas
end
| _57_3057 -> begin
(
# 2452 "FStar.TypeChecker.Tc.fst"
let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _146_1502 -> FStar_Syntax_Syntax.U_name (_146_1502))))
in (
# 2453 "FStar.TypeChecker.Tc.fst"
let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_9 -> (match (_57_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3062, _57_3064, _57_3066, _57_3068, _57_3070, _57_3072, _57_3074) -> begin
(tc, uvs_universes)
end
| _57_3078 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _57_3083 d -> (match (_57_3083) with
| (t, _57_3082) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _57_3087, _57_3089, tc, ntps, quals, mutuals, r) -> begin
(
# 2457 "FStar.TypeChecker.Tc.fst"
let ty = (let _146_1506 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _146_1506 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _57_3099 -> begin
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
# 2463 "FStar.TypeChecker.Tc.fst"
let _57_3109 = (FStar_All.pipe_right ses (FStar_List.partition (fun _57_10 -> (match (_57_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_3103) -> begin
true
end
| _57_3106 -> begin
false
end))))
in (match (_57_3109) with
| (tys, datas) -> begin
(
# 2465 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2468 "FStar.TypeChecker.Tc.fst"
let _57_3126 = (FStar_List.fold_right (fun tc _57_3115 -> (match (_57_3115) with
| (env, all_tcs, g) -> begin
(
# 2469 "FStar.TypeChecker.Tc.fst"
let _57_3119 = (tc_tycon env tc)
in (match (_57_3119) with
| (env, tc, tc_u) -> begin
(
# 2470 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (
# 2471 "FStar.TypeChecker.Tc.fst"
let _57_3121 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1510 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _146_1510))
end else begin
()
end
in (let _146_1511 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _146_1511))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_3126) with
| (env, tcs, g) -> begin
(
# 2478 "FStar.TypeChecker.Tc.fst"
let _57_3136 = (FStar_List.fold_right (fun se _57_3130 -> (match (_57_3130) with
| (datas, g) -> begin
(
# 2479 "FStar.TypeChecker.Tc.fst"
let _57_3133 = (tc_data env tcs se)
in (match (_57_3133) with
| (data, g') -> begin
(let _146_1514 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _146_1514))
end))
end)) datas ([], g))
in (match (_57_3136) with
| (datas, g) -> begin
(
# 2484 "FStar.TypeChecker.Tc.fst"
let _57_3139 = (let _146_1515 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _146_1515 datas))
in (match (_57_3139) with
| (tcs, datas) -> begin
(let _146_1517 = (let _146_1516 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _146_1516))
in FStar_Syntax_Syntax.Sig_bundle (_146_1517))
end))
end))
end)))
end)))))))))

# 2487 "FStar.TypeChecker.Tc.fst"
let rec tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.env) = (fun env se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(
# 2500 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2501 "FStar.TypeChecker.Tc.fst"
let se = (tc_lex_t env ses quals lids)
in (let _146_1522 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _146_1522))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(
# 2505 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2506 "FStar.TypeChecker.Tc.fst"
let se = (tc_inductive env ses quals lids)
in (let _146_1523 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _146_1523))))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(
# 2510 "FStar.TypeChecker.Tc.fst"
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
# 2516 "FStar.TypeChecker.Tc.fst"
let _57_3177 = (set_options FStar_Options.Set o)
in (se, env))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(
# 2519 "FStar.TypeChecker.Tc.fst"
let _57_3181 = (let _146_1528 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _146_1528 Prims.ignore))
in (
# 2520 "FStar.TypeChecker.Tc.fst"
let _57_3186 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (
# 2523 "FStar.TypeChecker.Tc.fst"
let _57_3188 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (se, env))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(
# 2528 "FStar.TypeChecker.Tc.fst"
let ne = (tc_eff_decl env ne ForFree)
in (
# 2530 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (
# 2531 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(
# 2535 "FStar.TypeChecker.Tc.fst"
let ne = (tc_eff_decl env ne NotForFree)
in (
# 2536 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (
# 2537 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(
# 2541 "FStar.TypeChecker.Tc.fst"
let _57_3210 = (let _146_1529 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _146_1529))
in (match (_57_3210) with
| (a, wp_a_src) -> begin
(
# 2542 "FStar.TypeChecker.Tc.fst"
let _57_3213 = (let _146_1530 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _146_1530))
in (match (_57_3213) with
| (b, wp_b_tgt) -> begin
(
# 2543 "FStar.TypeChecker.Tc.fst"
let wp_a_tgt = (let _146_1534 = (let _146_1533 = (let _146_1532 = (let _146_1531 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _146_1531))
in FStar_Syntax_Syntax.NT (_146_1532))
in (_146_1533)::[])
in (FStar_Syntax_Subst.subst _146_1534 wp_b_tgt))
in (
# 2544 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1539 = (let _146_1537 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1536 = (let _146_1535 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_146_1535)::[])
in (_146_1537)::_146_1536))
in (let _146_1538 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _146_1539 _146_1538)))
in (
# 2545 "FStar.TypeChecker.Tc.fst"
let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (
# 2546 "FStar.TypeChecker.Tc.fst"
let sub = (
# 2546 "FStar.TypeChecker.Tc.fst"
let _57_3217 = sub
in {FStar_Syntax_Syntax.source = _57_3217.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _57_3217.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
in (
# 2547 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect ((sub, r))
in (
# 2548 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(
# 2552 "FStar.TypeChecker.Tc.fst"
let _57_3230 = ()
in (
# 2553 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2554 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2555 "FStar.TypeChecker.Tc.fst"
let _57_3236 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_57_3236) with
| (tps, c) -> begin
(
# 2556 "FStar.TypeChecker.Tc.fst"
let _57_3240 = (tc_tparams env tps)
in (match (_57_3240) with
| (tps, env, us) -> begin
(
# 2557 "FStar.TypeChecker.Tc.fst"
let _57_3244 = (tc_comp env c)
in (match (_57_3244) with
| (c, u, g) -> begin
(
# 2558 "FStar.TypeChecker.Tc.fst"
let _57_3245 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2559 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 2560 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.close_comp tps c)
in (
# 2561 "FStar.TypeChecker.Tc.fst"
let _57_3251 = (let _146_1540 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _146_1540))
in (match (_57_3251) with
| (uvs, t) -> begin
(
# 2562 "FStar.TypeChecker.Tc.fst"
let _57_3270 = (match ((let _146_1542 = (let _146_1541 = (FStar_Syntax_Subst.compress t)
in _146_1541.FStar_Syntax_Syntax.n)
in (tps, _146_1542))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_57_3254, c)) -> begin
([], c)
end
| (_57_3260, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _57_3267 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_3270) with
| (tps, c) -> begin
(
# 2566 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_effect_abbrev ((lid, uvs, tps, c, tags, r))
in (
# 2567 "FStar.TypeChecker.Tc.fst"
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
# 2571 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2572 "FStar.TypeChecker.Tc.fst"
let _57_3281 = ()
in (
# 2573 "FStar.TypeChecker.Tc.fst"
let _57_3285 = (let _146_1544 = (let _146_1543 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _146_1543))
in (check_and_gen env t _146_1544))
in (match (_57_3285) with
| (uvs, t) -> begin
(
# 2574 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (
# 2575 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(
# 2579 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2580 "FStar.TypeChecker.Tc.fst"
let _57_3298 = (FStar_Syntax_Util.type_u ())
in (match (_57_3298) with
| (k, _57_3297) -> begin
(
# 2581 "FStar.TypeChecker.Tc.fst"
let phi = (let _146_1545 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _146_1545 (norm env)))
in (
# 2582 "FStar.TypeChecker.Tc.fst"
let _57_3300 = (FStar_TypeChecker_Util.check_uvars r phi)
in (
# 2583 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))
in (
# 2584 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(
# 2588 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2589 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (
# 2590 "FStar.TypeChecker.Tc.fst"
let _57_3313 = (tc_term env e)
in (match (_57_3313) with
| (e, c, g1) -> begin
(
# 2591 "FStar.TypeChecker.Tc.fst"
let _57_3318 = (let _146_1549 = (let _146_1546 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_146_1546))
in (let _146_1548 = (let _146_1547 = (c.FStar_Syntax_Syntax.comp ())
in (e, _146_1547))
in (check_expected_effect env _146_1549 _146_1548)))
in (match (_57_3318) with
| (e, _57_3316, g) -> begin
(
# 2592 "FStar.TypeChecker.Tc.fst"
let _57_3319 = (let _146_1550 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _146_1550))
in (
# 2593 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, r))
in (
# 2594 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(
# 2598 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2599 "FStar.TypeChecker.Tc.fst"
let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
if (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q')) then begin
Some (q)
end else begin
(let _146_1562 = (let _146_1561 = (let _146_1560 = (let _146_1559 = (FStar_Syntax_Print.lid_to_string l)
in (let _146_1558 = (FStar_Syntax_Print.quals_to_string q)
in (let _146_1557 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _146_1559 _146_1558 _146_1557))))
in (_146_1560, r))
in FStar_Syntax_Syntax.Error (_146_1561))
in (Prims.raise _146_1562))
end
end))
in (
# 2613 "FStar.TypeChecker.Tc.fst"
let _57_3363 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _57_3340 lb -> (match (_57_3340) with
| (gen, lbs, quals_opt) -> begin
(
# 2614 "FStar.TypeChecker.Tc.fst"
let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2615 "FStar.TypeChecker.Tc.fst"
let _57_3359 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(
# 2619 "FStar.TypeChecker.Tc.fst"
let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (
# 2620 "FStar.TypeChecker.Tc.fst"
let _57_3354 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _57_3353 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _146_1565 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _146_1565, quals_opt))))
end)
in (match (_57_3359) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_57_3363) with
| (should_generalize, lbs', quals_opt) -> begin
(
# 2629 "FStar.TypeChecker.Tc.fst"
let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _57_11 -> (match (_57_11) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _57_3372 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (
# 2636 "FStar.TypeChecker.Tc.fst"
let lbs' = (FStar_List.rev lbs')
in (
# 2639 "FStar.TypeChecker.Tc.fst"
let e = (let _146_1569 = (let _146_1568 = (let _146_1567 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _146_1567))
in FStar_Syntax_Syntax.Tm_let (_146_1568))
in (FStar_Syntax_Syntax.mk _146_1569 None r))
in (
# 2642 "FStar.TypeChecker.Tc.fst"
let _57_3406 = (match ((tc_maybe_toplevel_term (
# 2642 "FStar.TypeChecker.Tc.fst"
let _57_3376 = env
in {FStar_TypeChecker_Env.solver = _57_3376.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3376.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3376.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3376.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3376.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3376.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3376.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3376.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3376.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3376.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3376.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _57_3376.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _57_3376.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3376.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3376.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3376.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3376.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3376.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3376.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _57_3383; FStar_Syntax_Syntax.pos = _57_3381; FStar_Syntax_Syntax.vars = _57_3379}, _57_3390, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(
# 2645 "FStar.TypeChecker.Tc.fst"
let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_57_3394, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _57_3400 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _57_3403 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_57_3406) with
| (se, lbs) -> begin
(
# 2652 "FStar.TypeChecker.Tc.fst"
let _57_3412 = if (log env) then begin
(let _146_1577 = (let _146_1576 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 2654 "FStar.TypeChecker.Tc.fst"
let should_log = (match ((let _146_1573 = (let _146_1572 = (let _146_1571 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _146_1571.FStar_Syntax_Syntax.fv_name)
in _146_1572.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _146_1573))) with
| None -> begin
true
end
| _57_3410 -> begin
false
end)
in if should_log then begin
(let _146_1575 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _146_1574 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _146_1575 _146_1574)))
end else begin
""
end))))
in (FStar_All.pipe_right _146_1576 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _146_1577))
end else begin
()
end
in (
# 2661 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end))))
end))

# 2665 "FStar.TypeChecker.Tc.fst"
let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (
# 2689 "FStar.TypeChecker.Tc.fst"
let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _57_12 -> (match (_57_12) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _57_3422 -> begin
false
end)))))
in (
# 2690 "FStar.TypeChecker.Tc.fst"
let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _57_3432 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_57_3434) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _57_3445, _57_3447) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _57_3453 -> (match (_57_3453) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _57_3459, _57_3461, quals, r) -> begin
(
# 2704 "FStar.TypeChecker.Tc.fst"
let dec = (let _146_1593 = (let _146_1592 = (let _146_1591 = (let _146_1590 = (let _146_1589 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _146_1589))
in FStar_Syntax_Syntax.Tm_arrow (_146_1590))
in (FStar_Syntax_Syntax.mk _146_1591 None r))
in (l, us, _146_1592, (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_146_1593))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _57_3471, _57_3473, _57_3475, _57_3477, r) -> begin
(
# 2707 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _57_3483 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_57_3485, _57_3487, quals, _57_3490) -> begin
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
| _57_3509 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_57_3511) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _57_3530, _57_3532, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(
# 2738 "FStar.TypeChecker.Tc.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2739 "FStar.TypeChecker.Tc.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))) then begin
([], hidden)
end else begin
(
# 2742 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::[], (FStar_Ident.range_of_lid lid)))
in ((dec)::[], (lid)::hidden))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (is_abstract quals) then begin
(let _146_1600 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _146_1599 = (let _146_1598 = (let _146_1597 = (let _146_1596 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _146_1596.FStar_Syntax_Syntax.fv_name)
in _146_1597.FStar_Syntax_Syntax.v)
in (_146_1598, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_146_1599)))))
in (_146_1600, hidden))
end else begin
((se)::[], hidden)
end
end))))

# 2751 "FStar.TypeChecker.Tc.fst"
let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (
# 2752 "FStar.TypeChecker.Tc.fst"
let _57_3571 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _57_3552 se -> (match (_57_3552) with
| (ses, exports, env, hidden) -> begin
(
# 2754 "FStar.TypeChecker.Tc.fst"
let _57_3554 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1607 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _146_1607))
end else begin
()
end
in (
# 2757 "FStar.TypeChecker.Tc.fst"
let _57_3558 = (tc_decl env se)
in (match (_57_3558) with
| (se, env) -> begin
(
# 2759 "FStar.TypeChecker.Tc.fst"
let _57_3559 = if ((FStar_ST.read FStar_Options.log_types) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _146_1608 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _146_1608))
end else begin
()
end
in (
# 2762 "FStar.TypeChecker.Tc.fst"
let _57_3561 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (
# 2764 "FStar.TypeChecker.Tc.fst"
let _57_3565 = (for_export hidden se)
in (match (_57_3565) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_57_3571) with
| (ses, exports, env, _57_3570) -> begin
(let _146_1609 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _146_1609, env))
end)))

# 2769 "FStar.TypeChecker.Tc.fst"
let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2770 "FStar.TypeChecker.Tc.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 2771 "FStar.TypeChecker.Tc.fst"
let msg = (Prims.strcat "Internals for " name)
in (
# 2772 "FStar.TypeChecker.Tc.fst"
let env = (
# 2772 "FStar.TypeChecker.Tc.fst"
let _57_3576 = env
in (let _146_1614 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _57_3576.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3576.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3576.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3576.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3576.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3576.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3576.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3576.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3576.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3576.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3576.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3576.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3576.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_3576.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_3576.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3576.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _146_1614; FStar_TypeChecker_Env.type_of = _57_3576.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3576.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3576.FStar_TypeChecker_Env.use_bv_sorts}))
in (
# 2773 "FStar.TypeChecker.Tc.fst"
let _57_3579 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (
# 2774 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (
# 2775 "FStar.TypeChecker.Tc.fst"
let _57_3585 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_57_3585) with
| (ses, exports, env) -> begin
((
# 2776 "FStar.TypeChecker.Tc.fst"
let _57_3586 = modul
in {FStar_Syntax_Syntax.name = _57_3586.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _57_3586.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3586.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))

# 2778 "FStar.TypeChecker.Tc.fst"
let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (
# 2779 "FStar.TypeChecker.Tc.fst"
let _57_3594 = (tc_decls env decls)
in (match (_57_3594) with
| (ses, exports, env) -> begin
(
# 2780 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2780 "FStar.TypeChecker.Tc.fst"
let _57_3595 = modul
in {FStar_Syntax_Syntax.name = _57_3595.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _57_3595.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3595.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))

# 2783 "FStar.TypeChecker.Tc.fst"
let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (
# 2784 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2784 "FStar.TypeChecker.Tc.fst"
let _57_3601 = modul
in {FStar_Syntax_Syntax.name = _57_3601.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _57_3601.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (
# 2785 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.finish_module env modul)
in (
# 2786 "FStar.TypeChecker.Tc.fst"
let _57_3611 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(
# 2788 "FStar.TypeChecker.Tc.fst"
let _57_3605 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (
# 2789 "FStar.TypeChecker.Tc.fst"
let _57_3607 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (
# 2790 "FStar.TypeChecker.Tc.fst"
let _57_3609 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _146_1627 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _146_1627 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))

# 2795 "FStar.TypeChecker.Tc.fst"
let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2796 "FStar.TypeChecker.Tc.fst"
let _57_3618 = (tc_partial_modul env modul)
in (match (_57_3618) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

# 2799 "FStar.TypeChecker.Tc.fst"
let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 2800 "FStar.TypeChecker.Tc.fst"
let _57_3621 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _146_1636 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _146_1636))
end else begin
()
end
in (
# 2802 "FStar.TypeChecker.Tc.fst"
let env = (
# 2802 "FStar.TypeChecker.Tc.fst"
let _57_3623 = env
in {FStar_TypeChecker_Env.solver = _57_3623.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3623.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3623.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3623.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3623.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3623.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3623.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3623.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3623.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3623.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3623.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3623.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3623.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_3623.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3623.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3623.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3623.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3623.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3623.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3623.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 2803 "FStar.TypeChecker.Tc.fst"
let _57_3639 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _57_3631) -> begin
(let _146_1641 = (let _146_1640 = (let _146_1639 = (FStar_TypeChecker_Env.get_range env)
in ((Prims.strcat "Implicit argument: " msg), _146_1639))
in FStar_Syntax_Syntax.Error (_146_1640))
in (Prims.raise _146_1641))
end
in (match (_57_3639) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(t, c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(let _146_1646 = (let _146_1645 = (let _146_1644 = (let _146_1642 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _146_1642))
in (let _146_1643 = (FStar_TypeChecker_Env.get_range env)
in (_146_1644, _146_1643)))
in FStar_Syntax_Syntax.Error (_146_1645))
in (Prims.raise _146_1646))
end
end)))))

# 2810 "FStar.TypeChecker.Tc.fst"
let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (
# 2811 "FStar.TypeChecker.Tc.fst"
let _57_3642 = if ((let _146_1651 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _146_1651)) <> 0) then begin
(let _146_1652 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _146_1652))
end else begin
()
end
in (
# 2813 "FStar.TypeChecker.Tc.fst"
let _57_3646 = (tc_modul env m)
in (match (_57_3646) with
| (m, env) -> begin
(
# 2814 "FStar.TypeChecker.Tc.fst"
let _57_3647 = if (FStar_Options.should_dump m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _146_1653 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _146_1653))
end else begin
()
end
in (m, env))
end))))




