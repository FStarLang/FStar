
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
let c = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (None, c2))
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
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (guard_x), c_branches))
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
(
# 529 "FStar.TypeChecker.Tc.fst"
let fail = (fun _57_883 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Range constant cannot be checked in this context; expected an instance of \'range_of\'", r))))
end))
in (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(fail ())
end
| Some (t) -> begin
if (let _146_342 = (FStar_Syntax_Util.destruct t FStar_Syntax_Const.range_of_lid)
in (FStar_Option.isSome _146_342)) then begin
t
end else begin
(fail ())
end
end))
end
| _57_888 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 550 "FStar.TypeChecker.Tc.fst"
let _57_895 = (FStar_Syntax_Util.type_u ())
in (match (_57_895) with
| (k, u) -> begin
(
# 551 "FStar.TypeChecker.Tc.fst"
let _57_900 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_900) with
| (t, _57_898, g) -> begin
(let _146_345 = (FStar_Syntax_Syntax.mk_Total t)
in (_146_345, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 555 "FStar.TypeChecker.Tc.fst"
let _57_905 = (FStar_Syntax_Util.type_u ())
in (match (_57_905) with
| (k, u) -> begin
(
# 556 "FStar.TypeChecker.Tc.fst"
let _57_910 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_910) with
| (t, _57_908, g) -> begin
(let _146_346 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_146_346, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 560 "FStar.TypeChecker.Tc.fst"
let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (
# 561 "FStar.TypeChecker.Tc.fst"
let tc = (let _146_348 = (let _146_347 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_146_347)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _146_348 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 562 "FStar.TypeChecker.Tc.fst"
let _57_919 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_57_919) with
| (tc, _57_917, f) -> begin
(
# 563 "FStar.TypeChecker.Tc.fst"
let _57_923 = (FStar_Syntax_Util.head_and_args tc)
in (match (_57_923) with
| (_57_921, args) -> begin
(
# 564 "FStar.TypeChecker.Tc.fst"
let _57_926 = (let _146_350 = (FStar_List.hd args)
in (let _146_349 = (FStar_List.tl args)
in (_146_350, _146_349)))
in (match (_57_926) with
| (res, args) -> begin
(
# 565 "FStar.TypeChecker.Tc.fst"
let _57_942 = (let _146_352 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _57_5 -> (match (_57_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(
# 567 "FStar.TypeChecker.Tc.fst"
let _57_933 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_933) with
| (env, _57_932) -> begin
(
# 568 "FStar.TypeChecker.Tc.fst"
let _57_938 = (tc_tot_or_gtot_term env e)
in (match (_57_938) with
| (e, _57_936, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _146_352 FStar_List.unzip))
in (match (_57_942) with
| (flags, guards) -> begin
(
# 571 "FStar.TypeChecker.Tc.fst"
let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| _57_947 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _146_354 = (FStar_Syntax_Syntax.mk_Comp (
# 574 "FStar.TypeChecker.Tc.fst"
let _57_949 = c
in {FStar_Syntax_Syntax.effect_name = _57_949.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _57_949.FStar_Syntax_Syntax.flags}))
in (let _146_353 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_146_354, u, _146_353))))
end))
end))
end))
end))))
end))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (
# 581 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun u -> (
# 582 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_57_957) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _146_359 = (aux u)
in FStar_Syntax_Syntax.U_succ (_146_359))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _146_360 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_146_360))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _146_364 = (let _146_363 = (let _146_362 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _146_361 = (FStar_TypeChecker_Env.get_range env)
in (_146_362, _146_361)))
in FStar_Syntax_Syntax.Error (_146_363))
in (Prims.raise _146_364))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _146_365 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_365 Prims.snd))
end
| _57_972 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (
# 604 "FStar.TypeChecker.Tc.fst"
let fail = (fun msg t -> (let _146_374 = (let _146_373 = (let _146_372 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_146_372, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_373))
in (Prims.raise _146_374)))
in (
# 613 "FStar.TypeChecker.Tc.fst"
let check_binders = (fun env bs bs_expected -> (
# 618 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun _57_990 bs bs_expected -> (match (_57_990) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| ((hd, imp)::bs, (hd_expected, imp')::bs_expected) -> begin
(
# 622 "FStar.TypeChecker.Tc.fst"
let _57_1021 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _146_391 = (let _146_390 = (let _146_389 = (let _146_387 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _146_387))
in (let _146_388 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_146_389, _146_388)))
in FStar_Syntax_Syntax.Error (_146_390))
in (Prims.raise _146_391))
end
| _57_1020 -> begin
()
end)
in (
# 629 "FStar.TypeChecker.Tc.fst"
let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (
# 630 "FStar.TypeChecker.Tc.fst"
let _57_1038 = (match ((let _146_392 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _146_392.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _57_1026 -> begin
(
# 633 "FStar.TypeChecker.Tc.fst"
let _57_1027 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_393 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _146_393))
end else begin
()
end
in (
# 634 "FStar.TypeChecker.Tc.fst"
let _57_1033 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_57_1033) with
| (t, _57_1031, g1) -> begin
(
# 635 "FStar.TypeChecker.Tc.fst"
let g2 = (let _146_395 = (FStar_TypeChecker_Env.get_range env)
in (let _146_394 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _146_395 "Type annotation on parameter incompatible with the expected type" _146_394)))
in (
# 639 "FStar.TypeChecker.Tc.fst"
let g = (let _146_396 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _146_396))
in (t, g)))
end)))
end)
in (match (_57_1038) with
| (t, g) -> begin
(
# 641 "FStar.TypeChecker.Tc.fst"
let hd = (
# 641 "FStar.TypeChecker.Tc.fst"
let _57_1039 = hd
in {FStar_Syntax_Syntax.ppname = _57_1039.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1039.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 642 "FStar.TypeChecker.Tc.fst"
let b = (hd, imp)
in (
# 643 "FStar.TypeChecker.Tc.fst"
let b_expected = (hd_expected, imp')
in (
# 644 "FStar.TypeChecker.Tc.fst"
let env = (maybe_push_binding env b)
in (
# 645 "FStar.TypeChecker.Tc.fst"
let subst = (let _146_397 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _146_397))
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
# 655 "FStar.TypeChecker.Tc.fst"
let rec expected_function_typ = (fun env t0 body -> (match (t0) with
| None -> begin
(
# 666 "FStar.TypeChecker.Tc.fst"
let _57_1060 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1059 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (
# 669 "FStar.TypeChecker.Tc.fst"
let _57_1067 = (tc_binders env bs)
in (match (_57_1067) with
| (bs, envbody, g, _57_1066) -> begin
(
# 670 "FStar.TypeChecker.Tc.fst"
let _57_1085 = (match ((let _146_404 = (FStar_Syntax_Subst.compress body)
in _146_404.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _57_1072) -> begin
(
# 672 "FStar.TypeChecker.Tc.fst"
let _57_1079 = (tc_comp envbody c)
in (match (_57_1079) with
| (c, _57_1077, g') -> begin
(let _146_405 = (FStar_TypeChecker_Rel.conj_guard g g')
in (Some (c), body, _146_405))
end))
end
| _57_1081 -> begin
(None, body, g)
end)
in (match (_57_1085) with
| (copt, body, g) -> begin
(None, bs, [], copt, envbody, body, g)
end))
end)))
end
| Some (t) -> begin
(
# 678 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 679 "FStar.TypeChecker.Tc.fst"
let rec as_function_typ = (fun norm t -> (match ((let _146_410 = (FStar_Syntax_Subst.compress t)
in _146_410.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 683 "FStar.TypeChecker.Tc.fst"
let _57_1112 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1111 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 684 "FStar.TypeChecker.Tc.fst"
let _57_1119 = (tc_binders env bs)
in (match (_57_1119) with
| (bs, envbody, g, _57_1118) -> begin
(
# 685 "FStar.TypeChecker.Tc.fst"
let _57_1123 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_57_1123) with
| (envbody, _57_1122) -> begin
(Some ((t, true)), bs, [], None, envbody, body, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _57_1126) -> begin
(
# 691 "FStar.TypeChecker.Tc.fst"
let _57_1137 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_57_1137) with
| (_57_1130, bs, bs', copt, env, body, g) -> begin
(Some ((t, false)), bs, bs', copt, env, body, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 695 "FStar.TypeChecker.Tc.fst"
let _57_1144 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_57_1144) with
| (bs_expected, c_expected) -> begin
(
# 702 "FStar.TypeChecker.Tc.fst"
let check_actuals_against_formals = (fun env bs bs_expected -> (
# 703 "FStar.TypeChecker.Tc.fst"
let rec handle_more = (fun _57_1155 c_expected -> (match (_57_1155) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _146_421 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _146_421))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(
# 708 "FStar.TypeChecker.Tc.fst"
let c = (let _146_422 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _146_422))
in (let _146_423 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _146_423)))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(
# 712 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.subst_comp subst c_expected)
in if (FStar_Syntax_Util.is_total_comp c) then begin
(
# 715 "FStar.TypeChecker.Tc.fst"
let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 718 "FStar.TypeChecker.Tc.fst"
let _57_1176 = (check_binders env more_bs bs_expected)
in (match (_57_1176) with
| (env, bs', more, guard', subst) -> begin
(let _146_425 = (let _146_424 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _146_424, subst))
in (handle_more _146_425 c_expected))
end))
end
| _57_1178 -> begin
(let _146_427 = (let _146_426 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _146_426))
in (fail _146_427 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _146_428 = (check_binders env bs bs_expected)
in (handle_more _146_428 c_expected))))
in (
# 725 "FStar.TypeChecker.Tc.fst"
let mk_letrec_env = (fun envbody bs c -> (
# 726 "FStar.TypeChecker.Tc.fst"
let letrecs = (guard_letrecs envbody bs c)
in (
# 727 "FStar.TypeChecker.Tc.fst"
let envbody = (
# 727 "FStar.TypeChecker.Tc.fst"
let _57_1184 = envbody
in {FStar_TypeChecker_Env.solver = _57_1184.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1184.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1184.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1184.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1184.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1184.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1184.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1184.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1184.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1184.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1184.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1184.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_1184.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1184.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1184.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1184.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1184.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1184.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1184.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1184.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _57_1189 _57_1192 -> (match ((_57_1189, _57_1192)) with
| ((env, letrec_binders), (l, t)) -> begin
(
# 731 "FStar.TypeChecker.Tc.fst"
let _57_1198 = (let _146_438 = (let _146_437 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_437 Prims.fst))
in (tc_term _146_438 t))
in (match (_57_1198) with
| (t, _57_1195, _57_1197) -> begin
(
# 732 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (
# 733 "FStar.TypeChecker.Tc.fst"
let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _146_439 = (FStar_Syntax_Syntax.mk_binder (
# 734 "FStar.TypeChecker.Tc.fst"
let _57_1202 = x
in {FStar_Syntax_Syntax.ppname = _57_1202.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1202.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_146_439)::letrec_binders)
end
| _57_1205 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (
# 739 "FStar.TypeChecker.Tc.fst"
let _57_1211 = (check_actuals_against_formals env bs bs_expected)
in (match (_57_1211) with
| (envbody, bs, g, c) -> begin
(
# 740 "FStar.TypeChecker.Tc.fst"
let _57_1214 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_57_1214) with
| (envbody, letrecs) -> begin
(
# 741 "FStar.TypeChecker.Tc.fst"
let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, body, g))
end))
end))))
end))
end
| _57_1217 -> begin
if (not (norm)) then begin
(let _146_440 = (unfold_whnf env t)
in (as_function_typ true _146_440))
end else begin
(
# 749 "FStar.TypeChecker.Tc.fst"
let _57_1227 = (expected_function_typ env None body)
in (match (_57_1227) with
| (_57_1219, bs, _57_1222, c_opt, envbody, body, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, body, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (
# 753 "FStar.TypeChecker.Tc.fst"
let use_eq = env.FStar_TypeChecker_Env.use_eq
in (
# 754 "FStar.TypeChecker.Tc.fst"
let _57_1231 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1231) with
| (env, topt) -> begin
(
# 756 "FStar.TypeChecker.Tc.fst"
let _57_1235 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_441 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _146_441 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (
# 761 "FStar.TypeChecker.Tc.fst"
let _57_1244 = (expected_function_typ env topt body)
in (match (_57_1244) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(
# 762 "FStar.TypeChecker.Tc.fst"
let _57_1250 = (tc_term (
# 762 "FStar.TypeChecker.Tc.fst"
let _57_1245 = envbody
in {FStar_TypeChecker_Env.solver = _57_1245.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1245.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1245.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1245.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1245.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1245.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1245.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1245.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1245.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1245.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1245.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1245.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1245.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1245.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1245.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1245.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1245.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1245.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1245.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_57_1250) with
| (body, cbody, guard_body) -> begin
(
# 764 "FStar.TypeChecker.Tc.fst"
let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (
# 767 "FStar.TypeChecker.Tc.fst"
let _57_1252 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _146_444 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _146_443 = (let _146_442 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _146_442))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _146_444 _146_443)))
end else begin
()
end
in (
# 772 "FStar.TypeChecker.Tc.fst"
let _57_1259 = (let _146_446 = (let _146_445 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _146_445))
in (check_expected_effect (
# 772 "FStar.TypeChecker.Tc.fst"
let _57_1254 = envbody
in {FStar_TypeChecker_Env.solver = _57_1254.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1254.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1254.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1254.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1254.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1254.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1254.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1254.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1254.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1254.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1254.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1254.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1254.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1254.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1254.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1254.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1254.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1254.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1254.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1254.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _146_446))
in (match (_57_1259) with
| (body, cbody, guard) -> begin
(
# 773 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (
# 774 "FStar.TypeChecker.Tc.fst"
let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _146_447 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _146_447))
end else begin
(
# 776 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (
# 779 "FStar.TypeChecker.Tc.fst"
let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (
# 780 "FStar.TypeChecker.Tc.fst"
let e = (let _146_450 = (let _146_449 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _146_448 -> FStar_Util.Inl (_146_448)))
in Some (_146_449))
in (FStar_Syntax_Util.abs bs body _146_450))
in (
# 781 "FStar.TypeChecker.Tc.fst"
let _57_1282 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(
# 783 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_1271) -> begin
(e, t, guard)
end
| _57_1274 -> begin
(
# 790 "FStar.TypeChecker.Tc.fst"
let _57_1277 = if use_teq then begin
(let _146_451 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _146_451))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_57_1277) with
| (e, guard') -> begin
(let _146_452 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _146_452))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_57_1282) with
| (e, tfun, guard) -> begin
(
# 799 "FStar.TypeChecker.Tc.fst"
let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (
# 800 "FStar.TypeChecker.Tc.fst"
let _57_1286 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_57_1286) with
| (c, g) -> begin
(e, c, g)
end)))
end))))))
end))))
end))
end)))
end)))))))
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead ghead args expected_topt -> (
# 808 "FStar.TypeChecker.Tc.fst"
let n_args = (FStar_List.length args)
in (
# 809 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 810 "FStar.TypeChecker.Tc.fst"
let thead = chead.FStar_Syntax_Syntax.res_typ
in (
# 811 "FStar.TypeChecker.Tc.fst"
let _57_1296 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_461 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _146_460 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _146_461 _146_460)))
end else begin
()
end
in (
# 812 "FStar.TypeChecker.Tc.fst"
let rec check_function_app = (fun norm tf -> (match ((let _146_466 = (FStar_Syntax_Util.unrefine tf)
in _146_466.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 816 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| (e, imp)::tl -> begin
(
# 819 "FStar.TypeChecker.Tc.fst"
let _57_1330 = (tc_term env e)
in (match (_57_1330) with
| (e, c, g_e) -> begin
(
# 820 "FStar.TypeChecker.Tc.fst"
let _57_1334 = (tc_args env tl)
in (match (_57_1334) with
| (args, comps, g_rest) -> begin
(let _146_471 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, (c)::comps, _146_471))
end))
end))
end))
in (
# 828 "FStar.TypeChecker.Tc.fst"
let _57_1338 = (tc_args env args)
in (match (_57_1338) with
| (args, comps, g_args) -> begin
(
# 829 "FStar.TypeChecker.Tc.fst"
let bs = (let _146_473 = (FStar_All.pipe_right comps (FStar_List.map (fun c -> (c.FStar_Syntax_Syntax.res_typ, None))))
in (FStar_Syntax_Util.null_binders_of_tks _146_473))
in (
# 830 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _57_1345 -> begin
FStar_Syntax_Util.ml_comp
end)
in (
# 833 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _146_488 = (FStar_Syntax_Subst.compress t)
in _146_488.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_1351) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _57_1356 -> begin
ml_or_tot
end)
end)
in (
# 840 "FStar.TypeChecker.Tc.fst"
let cres = (let _146_493 = (let _146_492 = (let _146_491 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_491 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _146_492))
in (ml_or_tot _146_493 r))
in (
# 841 "FStar.TypeChecker.Tc.fst"
let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (
# 842 "FStar.TypeChecker.Tc.fst"
let _57_1360 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_496 = (FStar_Syntax_Print.term_to_string head)
in (let _146_495 = (FStar_Syntax_Print.term_to_string tf)
in (let _146_494 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _146_496 _146_495 _146_494))))
end else begin
()
end
in (
# 847 "FStar.TypeChecker.Tc.fst"
let _57_1362 = (let _146_497 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _146_497))
in (
# 848 "FStar.TypeChecker.Tc.fst"
let comp = (let _146_500 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_TypeChecker_Util.bind env None c (None, out))) ((chead)::comps) _146_500))
in (let _146_502 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _146_501 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_146_502, comp, _146_501)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 852 "FStar.TypeChecker.Tc.fst"
let _57_1373 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_1373) with
| (bs, c) -> begin
(
# 854 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun _57_1381 bs cres args -> (match (_57_1381) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (_57_1388)))::rest, (_57_1396, None)::_57_1394) -> begin
(
# 865 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 866 "FStar.TypeChecker.Tc.fst"
let _57_1402 = (check_no_escape (Some (head)) env fvs t)
in (
# 867 "FStar.TypeChecker.Tc.fst"
let _57_1408 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_57_1408) with
| (varg, _57_1406, implicits) -> begin
(
# 868 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (
# 869 "FStar.TypeChecker.Tc.fst"
let arg = (let _146_511 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _146_511))
in (let _146_513 = (let _146_512 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _146_512, fvs))
in (tc_args _146_513 rest cres args))))
end))))
end
| ((x, aqual)::rest, (e, aq)::rest') -> begin
(
# 873 "FStar.TypeChecker.Tc.fst"
let _57_1440 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _57_1439 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (
# 878 "FStar.TypeChecker.Tc.fst"
let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 879 "FStar.TypeChecker.Tc.fst"
let x = (
# 879 "FStar.TypeChecker.Tc.fst"
let _57_1443 = x
in {FStar_Syntax_Syntax.ppname = _57_1443.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1443.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (
# 880 "FStar.TypeChecker.Tc.fst"
let _57_1446 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_514 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _146_514))
end else begin
()
end
in (
# 881 "FStar.TypeChecker.Tc.fst"
let _57_1448 = (check_no_escape (Some (head)) env fvs targ)
in (
# 882 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (
# 883 "FStar.TypeChecker.Tc.fst"
let env = (
# 883 "FStar.TypeChecker.Tc.fst"
let _57_1451 = env
in {FStar_TypeChecker_Env.solver = _57_1451.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1451.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1451.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1451.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1451.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1451.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1451.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1451.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1451.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1451.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1451.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1451.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1451.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1451.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1451.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _57_1451.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1451.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1451.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1451.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1451.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 884 "FStar.TypeChecker.Tc.fst"
let _57_1454 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_517 = (FStar_Syntax_Print.tag_of_term e)
in (let _146_516 = (FStar_Syntax_Print.term_to_string e)
in (let _146_515 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _146_517 _146_516 _146_515))))
end else begin
()
end
in (
# 885 "FStar.TypeChecker.Tc.fst"
let _57_1459 = (tc_term env e)
in (match (_57_1459) with
| (e, c, g_e) -> begin
(
# 886 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (
# 888 "FStar.TypeChecker.Tc.fst"
let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(
# 890 "FStar.TypeChecker.Tc.fst"
let subst = (let _146_518 = (FStar_List.hd bs)
in (maybe_extend_subst subst _146_518 e))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(
# 893 "FStar.TypeChecker.Tc.fst"
let subst = (let _146_519 = (FStar_List.hd bs)
in (maybe_extend_subst subst _146_519 e))
in (
# 894 "FStar.TypeChecker.Tc.fst"
let _57_1466 = (((Some (x), c))::comps, g)
in (match (_57_1466) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _146_520 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _146_520)) then begin
(
# 898 "FStar.TypeChecker.Tc.fst"
let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (
# 899 "FStar.TypeChecker.Tc.fst"
let arg' = (let _146_521 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _146_521))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (newx), c))::comps, g, fvs) rest cres rest')))
end else begin
(let _146_525 = (let _146_524 = (let _146_523 = (let _146_522 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _146_522))
in (_146_523)::arg_rets)
in (subst, (arg)::outargs, _146_524, ((Some (x), c))::comps, g, (x)::fvs))
in (tc_args _146_525 rest cres rest'))
end
end
end))
end))))))))))
end
| (_57_1470, []) -> begin
(
# 908 "FStar.TypeChecker.Tc.fst"
let _57_1473 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (
# 909 "FStar.TypeChecker.Tc.fst"
let _57_1491 = (match (bs) with
| [] -> begin
(
# 912 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (
# 918 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (
# 920 "FStar.TypeChecker.Tc.fst"
let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _57_1481 -> (match (_57_1481) with
| (_57_1479, c) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (
# 927 "FStar.TypeChecker.Tc.fst"
let cres = if refine_with_equality then begin
(let _146_527 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _146_527 cres))
end else begin
(
# 933 "FStar.TypeChecker.Tc.fst"
let _57_1483 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_530 = (FStar_Syntax_Print.term_to_string head)
in (let _146_529 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _146_528 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _146_530 _146_529 _146_528))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _57_1487 -> begin
(
# 942 "FStar.TypeChecker.Tc.fst"
let g = (let _146_531 = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (FStar_All.pipe_right _146_531 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _146_536 = (let _146_535 = (let _146_534 = (let _146_533 = (let _146_532 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _146_532))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _146_533))
in (FStar_Syntax_Syntax.mk_Total _146_534))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_535))
in (_146_536, g)))
end)
in (match (_57_1491) with
| (cres, g) -> begin
(
# 945 "FStar.TypeChecker.Tc.fst"
let _57_1492 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_537 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _146_537))
end else begin
()
end
in (
# 946 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_List.fold_left (fun out c -> (FStar_TypeChecker_Util.bind env None (Prims.snd c) ((Prims.fst c), out))) cres comps)
in (
# 947 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.bind env None chead (None, comp))
in (
# 948 "FStar.TypeChecker.Tc.fst"
let app = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev outargs) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (
# 949 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.record_application_site env app comp)
in (
# 950 "FStar.TypeChecker.Tc.fst"
let _57_1502 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp g)
in (match (_57_1502) with
| (comp, g) -> begin
(app, comp, g)
end)))))))
end)))
end
| ([], arg::_57_1505) -> begin
(
# 955 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun norm tres -> (
# 956 "FStar.TypeChecker.Tc.fst"
let tres = (let _146_545 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _146_545 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(
# 959 "FStar.TypeChecker.Tc.fst"
let _57_1517 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_546 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _146_546))
end else begin
()
end
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs (FStar_Syntax_Util.lcomp_of_comp cres') args))
end
| _57_1520 when (not (norm)) -> begin
(let _146_547 = (unfold_whnf env tres)
in (aux true _146_547))
end
| _57_1522 -> begin
(let _146_553 = (let _146_552 = (let _146_551 = (let _146_549 = (FStar_TypeChecker_Normalize.term_to_string env tf)
in (let _146_548 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _146_549 _146_548)))
in (let _146_550 = (FStar_Syntax_Syntax.argpos arg)
in (_146_551, _146_550)))
in FStar_Syntax_Syntax.Error (_146_552))
in (Prims.raise _146_553))
end)))
in (aux false cres.FStar_Syntax_Syntax.res_typ))
end)
end))
in (tc_args ([], [], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs (FStar_Syntax_Util.lcomp_of_comp c) args))
end))
end
| _57_1524 -> begin
if (not (norm)) then begin
(let _146_554 = (unfold_whnf env tf)
in (check_function_app true _146_554))
end else begin
(let _146_557 = (let _146_556 = (let _146_555 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_146_555, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_556))
in (Prims.raise _146_557))
end
end))
in (let _146_559 = (let _146_558 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _146_558))
in (check_function_app false _146_559))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (
# 985 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 986 "FStar.TypeChecker.Tc.fst"
let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(
# 989 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in (
# 990 "FStar.TypeChecker.Tc.fst"
let _57_1560 = (FStar_List.fold_left2 (fun _57_1541 _57_1544 _57_1547 -> (match ((_57_1541, _57_1544, _57_1547)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(
# 991 "FStar.TypeChecker.Tc.fst"
let _57_1548 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 992 "FStar.TypeChecker.Tc.fst"
let _57_1553 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_57_1553) with
| (e, c, g) -> begin
(
# 993 "FStar.TypeChecker.Tc.fst"
let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (
# 994 "FStar.TypeChecker.Tc.fst"
let g = (let _146_569 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _146_569 g))
in (
# 995 "FStar.TypeChecker.Tc.fst"
let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _146_573 = (let _146_571 = (let _146_570 = (FStar_Syntax_Syntax.as_arg e)
in (_146_570)::[])
in (FStar_List.append seen _146_571))
in (let _146_572 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_146_573, _146_572, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_57_1560) with
| (args, guard, ghost) -> begin
(
# 999 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (
# 1000 "FStar.TypeChecker.Tc.fst"
let c = if ghost then begin
(let _146_574 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _146_574 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (
# 1001 "FStar.TypeChecker.Tc.fst"
let _57_1565 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_57_1565) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _57_1567 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (
# 1021 "FStar.TypeChecker.Tc.fst"
let _57_1574 = (FStar_Syntax_Subst.open_branch branch)
in (match (_57_1574) with
| (pattern, when_clause, branch_exp) -> begin
(
# 1022 "FStar.TypeChecker.Tc.fst"
let _57_1579 = branch
in (match (_57_1579) with
| (cpat, _57_1577, cbr) -> begin
(
# 1025 "FStar.TypeChecker.Tc.fst"
let tc_pat = (fun allow_implicits pat_t p0 -> (
# 1032 "FStar.TypeChecker.Tc.fst"
let _57_1587 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_57_1587) with
| (pat_bvs, exps, p) -> begin
(
# 1033 "FStar.TypeChecker.Tc.fst"
let _57_1588 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_586 = (FStar_Syntax_Print.pat_to_string p0)
in (let _146_585 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _146_586 _146_585)))
end else begin
()
end
in (
# 1035 "FStar.TypeChecker.Tc.fst"
let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (
# 1036 "FStar.TypeChecker.Tc.fst"
let _57_1594 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_57_1594) with
| (env1, _57_1593) -> begin
(
# 1037 "FStar.TypeChecker.Tc.fst"
let env1 = (
# 1037 "FStar.TypeChecker.Tc.fst"
let _57_1595 = env1
in {FStar_TypeChecker_Env.solver = _57_1595.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1595.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1595.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1595.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1595.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1595.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1595.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1595.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _57_1595.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1595.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1595.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1595.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1595.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1595.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1595.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1595.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1595.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1595.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1595.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1595.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1038 "FStar.TypeChecker.Tc.fst"
let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (
# 1039 "FStar.TypeChecker.Tc.fst"
let _57_1634 = (let _146_609 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (
# 1040 "FStar.TypeChecker.Tc.fst"
let _57_1600 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_589 = (FStar_Syntax_Print.term_to_string e)
in (let _146_588 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _146_589 _146_588)))
end else begin
()
end
in (
# 1043 "FStar.TypeChecker.Tc.fst"
let _57_1605 = (tc_term env1 e)
in (match (_57_1605) with
| (e, lc, g) -> begin
(
# 1045 "FStar.TypeChecker.Tc.fst"
let _57_1606 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_591 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _146_590 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _146_591 _146_590)))
end else begin
()
end
in (
# 1048 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (
# 1049 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (
# 1050 "FStar.TypeChecker.Tc.fst"
let _57_1612 = (let _146_592 = (FStar_TypeChecker_Rel.discharge_guard env (
# 1050 "FStar.TypeChecker.Tc.fst"
let _57_1610 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_1610.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_1610.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_1610.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _146_592 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1051 "FStar.TypeChecker.Tc.fst"
let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (
# 1052 "FStar.TypeChecker.Tc.fst"
let uvars_to_string = (fun uvs -> (let _146_597 = (let _146_596 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _146_596 (FStar_List.map (fun _57_1620 -> (match (_57_1620) with
| (u, _57_1619) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _146_597 (FStar_String.concat ", "))))
in (
# 1053 "FStar.TypeChecker.Tc.fst"
let uvs1 = (FStar_Syntax_Free.uvars e')
in (
# 1054 "FStar.TypeChecker.Tc.fst"
let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (
# 1055 "FStar.TypeChecker.Tc.fst"
let _57_1628 = if (let _146_598 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _146_598)) then begin
(
# 1056 "FStar.TypeChecker.Tc.fst"
let unresolved = (let _146_599 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _146_599 FStar_Util.set_elements))
in (let _146_607 = (let _146_606 = (let _146_605 = (let _146_604 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _146_603 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _146_602 = (let _146_601 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _57_1627 -> (match (_57_1627) with
| (u, _57_1626) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _146_601 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _146_604 _146_603 _146_602))))
in (_146_605, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_146_606))
in (Prims.raise _146_607)))
end else begin
()
end
in (
# 1063 "FStar.TypeChecker.Tc.fst"
let _57_1630 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_608 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _146_608))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _146_609 FStar_List.unzip))
in (match (_57_1634) with
| (exps, norm_exps) -> begin
(
# 1068 "FStar.TypeChecker.Tc.fst"
let p = (FStar_TypeChecker_Util.decorate_pattern env p exps)
in (p, pat_bvs, pat_env, exps, norm_exps))
end))))
end))))
end)))
in (
# 1072 "FStar.TypeChecker.Tc.fst"
let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (
# 1073 "FStar.TypeChecker.Tc.fst"
let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (
# 1074 "FStar.TypeChecker.Tc.fst"
let _57_1641 = (let _146_610 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _146_610 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_57_1641) with
| (scrutinee_env, _57_1640) -> begin
(
# 1077 "FStar.TypeChecker.Tc.fst"
let _57_1647 = (tc_pat true pat_t pattern)
in (match (_57_1647) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(
# 1080 "FStar.TypeChecker.Tc.fst"
let _57_1657 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(
# 1087 "FStar.TypeChecker.Tc.fst"
let _57_1654 = (let _146_611 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _146_611 e))
in (match (_57_1654) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_57_1657) with
| (when_clause, g_when) -> begin
(
# 1091 "FStar.TypeChecker.Tc.fst"
let _57_1661 = (tc_term pat_env branch_exp)
in (match (_57_1661) with
| (branch_exp, c, g_branch) -> begin
(
# 1095 "FStar.TypeChecker.Tc.fst"
let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _146_613 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _146_612 -> Some (_146_612)) _146_613))
end)
in (
# 1102 "FStar.TypeChecker.Tc.fst"
let _57_1717 = (
# 1105 "FStar.TypeChecker.Tc.fst"
let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (
# 1106 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _57_1679 -> begin
(
# 1112 "FStar.TypeChecker.Tc.fst"
let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _146_617 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _146_616 -> Some (_146_616)) _146_617))
end))
end))) None))
in (
# 1117 "FStar.TypeChecker.Tc.fst"
let _57_1687 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_57_1687) with
| (c, g_branch) -> begin
(
# 1121 "FStar.TypeChecker.Tc.fst"
let _57_1712 = (match ((eqs, when_condition)) with
| (None, None) -> begin
(c, g_when)
end
| (Some (f), None) -> begin
(
# 1127 "FStar.TypeChecker.Tc.fst"
let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1128 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _146_620 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _146_619 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_146_620, _146_619)))))
end
| (Some (f), Some (w)) -> begin
(
# 1133 "FStar.TypeChecker.Tc.fst"
let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1134 "FStar.TypeChecker.Tc.fst"
let g_fw = (let _146_621 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_146_621))
in (let _146_624 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _146_623 = (let _146_622 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _146_622 g_when))
in (_146_624, _146_623)))))
end
| (None, Some (w)) -> begin
(
# 1139 "FStar.TypeChecker.Tc.fst"
let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (
# 1140 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _146_625 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_146_625, g_when))))
end)
in (match (_57_1712) with
| (c_weak, g_when_weak) -> begin
(
# 1145 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _146_627 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _146_626 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_146_627, _146_626, g_branch))))
end))
end)))
in (match (_57_1717) with
| (c, g_when, g_branch) -> begin
(
# 1163 "FStar.TypeChecker.Tc.fst"
let branch_guard = (
# 1165 "FStar.TypeChecker.Tc.fst"
let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (
# 1166 "FStar.TypeChecker.Tc.fst"
let discriminate = (fun scrutinee_tm f -> if ((let _146_637 = (let _146_636 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _146_636))
in (FStar_List.length _146_637)) > 1) then begin
(
# 1169 "FStar.TypeChecker.Tc.fst"
let disc = (let _146_638 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _146_638 FStar_Syntax_Syntax.Delta_equational None))
in (
# 1170 "FStar.TypeChecker.Tc.fst"
let disc = (let _146_640 = (let _146_639 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_146_639)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _146_640 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _146_641 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_146_641)::[])))
end else begin
[]
end)
in (
# 1174 "FStar.TypeChecker.Tc.fst"
let fail = (fun _57_1727 -> (match (()) with
| () -> begin
(let _146_647 = (let _146_646 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _146_645 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _146_644 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _146_646 _146_645 _146_644))))
in (FStar_All.failwith _146_647))
end))
in (
# 1180 "FStar.TypeChecker.Tc.fst"
let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _57_1734) -> begin
(head_constructor t)
end
| _57_1738 -> begin
(fail ())
end))
in (
# 1185 "FStar.TypeChecker.Tc.fst"
let pat_exp = (let _146_650 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _146_650 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_57_1763) -> begin
(let _146_655 = (let _146_654 = (let _146_653 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _146_652 = (let _146_651 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_146_651)::[])
in (_146_653)::_146_652))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _146_654 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_146_655)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 1194 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _146_656 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _146_656))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 1199 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(
# 1202 "FStar.TypeChecker.Tc.fst"
let sub_term_guards = (let _146_663 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _57_1781 -> (match (_57_1781) with
| (ei, _57_1780) -> begin
(
# 1203 "FStar.TypeChecker.Tc.fst"
let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _57_1785 -> begin
(
# 1207 "FStar.TypeChecker.Tc.fst"
let sub_term = (let _146_662 = (let _146_659 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _146_659 FStar_Syntax_Syntax.Delta_equational None))
in (let _146_661 = (let _146_660 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_146_660)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _146_662 _146_661 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _146_663 FStar_List.flatten))
in (let _146_664 = (discriminate scrutinee_tm f)
in (FStar_List.append _146_664 sub_term_guards)))
end)
end
| _57_1789 -> begin
[]
end))))))
in (
# 1213 "FStar.TypeChecker.Tc.fst"
let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(
# 1216 "FStar.TypeChecker.Tc.fst"
let t = (let _146_669 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _146_669))
in (
# 1217 "FStar.TypeChecker.Tc.fst"
let _57_1797 = (FStar_Syntax_Util.type_u ())
in (match (_57_1797) with
| (k, _57_1796) -> begin
(
# 1218 "FStar.TypeChecker.Tc.fst"
let _57_1803 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_57_1803) with
| (t, _57_1800, _57_1802) -> begin
t
end))
end)))
end)
in (
# 1222 "FStar.TypeChecker.Tc.fst"
let branch_guard = (let _146_670 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _146_670 FStar_Syntax_Util.mk_disj_l))
in (
# 1225 "FStar.TypeChecker.Tc.fst"
let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
in (
# 1231 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (
# 1233 "FStar.TypeChecker.Tc.fst"
let _57_1811 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_671 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _146_671))
end else begin
()
end
in (let _146_672 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_146_672, branch_guard, c, guard)))))
end)))
end))
end))
end))
end)))))
end))
end)))
and check_top_level_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1247 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1250 "FStar.TypeChecker.Tc.fst"
let _57_1828 = (check_let_bound_def true env lb)
in (match (_57_1828) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(
# 1252 "FStar.TypeChecker.Tc.fst"
let _57_1840 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(
# 1255 "FStar.TypeChecker.Tc.fst"
let g1 = (let _146_675 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _146_675 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1256 "FStar.TypeChecker.Tc.fst"
let _57_1835 = (let _146_679 = (let _146_678 = (let _146_677 = (let _146_676 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _146_676))
in (_146_677)::[])
in (FStar_TypeChecker_Util.generalize env _146_678))
in (FStar_List.hd _146_679))
in (match (_57_1835) with
| (_57_1831, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_57_1840) with
| (g1, e1, univ_vars, c1) -> begin
(
# 1260 "FStar.TypeChecker.Tc.fst"
let _57_1850 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(
# 1262 "FStar.TypeChecker.Tc.fst"
let _57_1843 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_57_1843) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(
# 1265 "FStar.TypeChecker.Tc.fst"
let _57_1844 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _146_680 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _146_680 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _146_681 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_146_681, c1)))
end
end))
end else begin
(
# 1269 "FStar.TypeChecker.Tc.fst"
let _57_1846 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _146_682 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _146_682)))
end
in (match (_57_1850) with
| (e2, c1) -> begin
(
# 1274 "FStar.TypeChecker.Tc.fst"
let cres = (let _146_683 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_683))
in (
# 1275 "FStar.TypeChecker.Tc.fst"
let _57_1852 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1277 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _146_684 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_146_684, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _57_1856 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1294 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1297 "FStar.TypeChecker.Tc.fst"
let env = (
# 1297 "FStar.TypeChecker.Tc.fst"
let _57_1867 = env
in {FStar_TypeChecker_Env.solver = _57_1867.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1867.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1867.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1867.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1867.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1867.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1867.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1867.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1867.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1867.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1867.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1867.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1867.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1867.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1867.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1867.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1867.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1867.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1867.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1867.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1298 "FStar.TypeChecker.Tc.fst"
let _57_1876 = (let _146_688 = (let _146_687 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_687 Prims.fst))
in (check_let_bound_def false _146_688 lb))
in (match (_57_1876) with
| (e1, _57_1872, c1, g1, annotated) -> begin
(
# 1299 "FStar.TypeChecker.Tc.fst"
let x = (
# 1299 "FStar.TypeChecker.Tc.fst"
let _57_1877 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1877.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1877.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (
# 1300 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (
# 1301 "FStar.TypeChecker.Tc.fst"
let _57_1883 = (let _146_690 = (let _146_689 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_689)::[])
in (FStar_Syntax_Subst.open_term _146_690 e2))
in (match (_57_1883) with
| (xb, e2) -> begin
(
# 1302 "FStar.TypeChecker.Tc.fst"
let xbinder = (FStar_List.hd xb)
in (
# 1303 "FStar.TypeChecker.Tc.fst"
let x = (Prims.fst xbinder)
in (
# 1304 "FStar.TypeChecker.Tc.fst"
let _57_1889 = (let _146_691 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _146_691 e2))
in (match (_57_1889) with
| (e2, c2, g2) -> begin
(
# 1305 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (x), c2))
in (
# 1306 "FStar.TypeChecker.Tc.fst"
let e = (let _146_694 = (let _146_693 = (let _146_692 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _146_692))
in FStar_Syntax_Syntax.Tm_let (_146_693))
in (FStar_Syntax_Syntax.mk _146_694 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 1307 "FStar.TypeChecker.Tc.fst"
let x_eq_e1 = (let _146_697 = (let _146_696 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _146_696 e1))
in (FStar_All.pipe_left (fun _146_695 -> FStar_TypeChecker_Common.NonTrivial (_146_695)) _146_697))
in (
# 1308 "FStar.TypeChecker.Tc.fst"
let g2 = (let _146_699 = (let _146_698 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _146_698 g2))
in (FStar_TypeChecker_Rel.close_guard xb _146_699))
in (
# 1310 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if annotated then begin
(e, cres, guard)
end else begin
(
# 1314 "FStar.TypeChecker.Tc.fst"
let _57_1895 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end)))))
end))))
end))))
end)))
end
| _57_1898 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1323 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1326 "FStar.TypeChecker.Tc.fst"
let _57_1910 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1910) with
| (lbs, e2) -> begin
(
# 1328 "FStar.TypeChecker.Tc.fst"
let _57_1913 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1913) with
| (env0, topt) -> begin
(
# 1329 "FStar.TypeChecker.Tc.fst"
let _57_1916 = (build_let_rec_env true env0 lbs)
in (match (_57_1916) with
| (lbs, rec_env) -> begin
(
# 1330 "FStar.TypeChecker.Tc.fst"
let _57_1919 = (check_let_recs rec_env lbs)
in (match (_57_1919) with
| (lbs, g_lbs) -> begin
(
# 1331 "FStar.TypeChecker.Tc.fst"
let g_lbs = (let _146_702 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _146_702 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1333 "FStar.TypeChecker.Tc.fst"
let all_lb_names = (let _146_705 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _146_705 (fun _146_704 -> Some (_146_704))))
in (
# 1335 "FStar.TypeChecker.Tc.fst"
let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(
# 1341 "FStar.TypeChecker.Tc.fst"
let ecs = (let _146_709 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _146_708 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _146_708)))))
in (FStar_TypeChecker_Util.generalize env _146_709))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _57_1930 -> (match (_57_1930) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (
# 1348 "FStar.TypeChecker.Tc.fst"
let cres = (let _146_711 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_711))
in (
# 1349 "FStar.TypeChecker.Tc.fst"
let _57_1933 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1351 "FStar.TypeChecker.Tc.fst"
let _57_1937 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1937) with
| (lbs, e2) -> begin
(let _146_713 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_712 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_146_713, cres, _146_712)))
end)))))))
end))
end))
end))
end))
end
| _57_1939 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1362 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1365 "FStar.TypeChecker.Tc.fst"
let _57_1951 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1951) with
| (lbs, e2) -> begin
(
# 1367 "FStar.TypeChecker.Tc.fst"
let _57_1954 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1954) with
| (env0, topt) -> begin
(
# 1368 "FStar.TypeChecker.Tc.fst"
let _57_1957 = (build_let_rec_env false env0 lbs)
in (match (_57_1957) with
| (lbs, rec_env) -> begin
(
# 1369 "FStar.TypeChecker.Tc.fst"
let _57_1960 = (check_let_recs rec_env lbs)
in (match (_57_1960) with
| (lbs, g_lbs) -> begin
(
# 1371 "FStar.TypeChecker.Tc.fst"
let _57_1972 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (
# 1372 "FStar.TypeChecker.Tc.fst"
let x = (
# 1372 "FStar.TypeChecker.Tc.fst"
let _57_1963 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1963.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1963.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (
# 1373 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1373 "FStar.TypeChecker.Tc.fst"
let _57_1966 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _57_1966.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1966.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1966.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _57_1966.FStar_Syntax_Syntax.lbdef})
in (
# 1374 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], lb.FStar_Syntax_Syntax.lbtyp))
in (env, lb))))) env))
in (match (_57_1972) with
| (env, lbs) -> begin
(
# 1377 "FStar.TypeChecker.Tc.fst"
let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (
# 1379 "FStar.TypeChecker.Tc.fst"
let _57_1978 = (tc_term env e2)
in (match (_57_1978) with
| (e2, cres, g2) -> begin
(
# 1380 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (
# 1381 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (
# 1382 "FStar.TypeChecker.Tc.fst"
let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (
# 1383 "FStar.TypeChecker.Tc.fst"
let cres = (
# 1383 "FStar.TypeChecker.Tc.fst"
let _57_1982 = cres
in {FStar_Syntax_Syntax.eff_name = _57_1982.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _57_1982.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_1982.FStar_Syntax_Syntax.comp})
in (
# 1385 "FStar.TypeChecker.Tc.fst"
let _57_1987 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1987) with
| (lbs, e2) -> begin
(
# 1386 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_57_1990) -> begin
(e, cres, guard)
end
| None -> begin
(
# 1390 "FStar.TypeChecker.Tc.fst"
let _57_1993 = (check_no_escape None env bvs tres)
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
| _57_1996 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (
# 1401 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1402 "FStar.TypeChecker.Tc.fst"
let _57_2029 = (FStar_List.fold_left (fun _57_2003 lb -> (match (_57_2003) with
| (lbs, env) -> begin
(
# 1403 "FStar.TypeChecker.Tc.fst"
let _57_2008 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_57_2008) with
| (univ_vars, t, check_t) -> begin
(
# 1404 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (
# 1405 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (
# 1406 "FStar.TypeChecker.Tc.fst"
let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(
# 1411 "FStar.TypeChecker.Tc.fst"
let _57_2017 = (let _146_725 = (let _146_724 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _146_724))
in (tc_check_tot_or_gtot_term (
# 1411 "FStar.TypeChecker.Tc.fst"
let _57_2011 = env0
in {FStar_TypeChecker_Env.solver = _57_2011.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2011.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2011.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2011.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2011.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2011.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2011.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2011.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2011.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2011.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2011.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2011.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2011.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2011.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _57_2011.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2011.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2011.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2011.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2011.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2011.FStar_TypeChecker_Env.use_bv_sorts}) t _146_725))
in (match (_57_2017) with
| (t, _57_2015, g) -> begin
(
# 1412 "FStar.TypeChecker.Tc.fst"
let _57_2018 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (
# 1414 "FStar.TypeChecker.Tc.fst"
let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(
# 1416 "FStar.TypeChecker.Tc.fst"
let _57_2021 = env
in {FStar_TypeChecker_Env.solver = _57_2021.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2021.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2021.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2021.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2021.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2021.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2021.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2021.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2021.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2021.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2021.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2021.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2021.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_2021.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2021.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2021.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2021.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2021.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2021.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2021.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (
# 1418 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1418 "FStar.TypeChecker.Tc.fst"
let _57_2024 = lb
in {FStar_Syntax_Syntax.lbname = _57_2024.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _57_2024.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_57_2029) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (
# 1425 "FStar.TypeChecker.Tc.fst"
let _57_2042 = (let _146_730 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 1426 "FStar.TypeChecker.Tc.fst"
let _57_2036 = (let _146_729 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _146_729 lb.FStar_Syntax_Syntax.lbdef))
in (match (_57_2036) with
| (e, c, g) -> begin
(
# 1427 "FStar.TypeChecker.Tc.fst"
let _57_2037 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1429 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _146_730 FStar_List.unzip))
in (match (_57_2042) with
| (lbs, gs) -> begin
(
# 1431 "FStar.TypeChecker.Tc.fst"
let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (
# 1445 "FStar.TypeChecker.Tc.fst"
let _57_2050 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_2050) with
| (env1, _57_2049) -> begin
(
# 1446 "FStar.TypeChecker.Tc.fst"
let e1 = lb.FStar_Syntax_Syntax.lbdef
in (
# 1449 "FStar.TypeChecker.Tc.fst"
let _57_2056 = (check_lbtyp top_level env lb)
in (match (_57_2056) with
| (topt, wf_annot, univ_vars, env1) -> begin
(
# 1451 "FStar.TypeChecker.Tc.fst"
let _57_2057 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1455 "FStar.TypeChecker.Tc.fst"
let _57_2064 = (tc_maybe_toplevel_term (
# 1455 "FStar.TypeChecker.Tc.fst"
let _57_2059 = env1
in {FStar_TypeChecker_Env.solver = _57_2059.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2059.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2059.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2059.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2059.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2059.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2059.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2059.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2059.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2059.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2059.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2059.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2059.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _57_2059.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2059.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2059.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2059.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2059.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2059.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2059.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_57_2064) with
| (e1, c1, g1) -> begin
(
# 1458 "FStar.TypeChecker.Tc.fst"
let _57_2068 = (let _146_737 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_2065 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _146_737 e1 c1 wf_annot))
in (match (_57_2068) with
| (c1, guard_f) -> begin
(
# 1461 "FStar.TypeChecker.Tc.fst"
let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (
# 1463 "FStar.TypeChecker.Tc.fst"
let _57_2070 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_738 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _146_738))
end else begin
()
end
in (let _146_739 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _146_739))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (
# 1475 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 1478 "FStar.TypeChecker.Tc.fst"
let _57_2077 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _57_2080 -> begin
(
# 1482 "FStar.TypeChecker.Tc.fst"
let _57_2083 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_57_2083) with
| (univ_vars, t) -> begin
(
# 1483 "FStar.TypeChecker.Tc.fst"
let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _146_743 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _146_743))
end else begin
(
# 1490 "FStar.TypeChecker.Tc.fst"
let _57_2088 = (FStar_Syntax_Util.type_u ())
in (match (_57_2088) with
| (k, _57_2087) -> begin
(
# 1491 "FStar.TypeChecker.Tc.fst"
let _57_2093 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_57_2093) with
| (t, _57_2091, g) -> begin
(
# 1492 "FStar.TypeChecker.Tc.fst"
let _57_2094 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _146_746 = (let _146_744 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _146_744))
in (let _146_745 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _146_746 _146_745)))
end else begin
()
end
in (
# 1496 "FStar.TypeChecker.Tc.fst"
let t = (norm env1 t)
in (let _146_747 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _146_747))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _57_2100 -> (match (_57_2100) with
| (x, imp) -> begin
(
# 1501 "FStar.TypeChecker.Tc.fst"
let _57_2103 = (FStar_Syntax_Util.type_u ())
in (match (_57_2103) with
| (tu, u) -> begin
(
# 1502 "FStar.TypeChecker.Tc.fst"
let _57_2108 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_57_2108) with
| (t, _57_2106, g) -> begin
(
# 1503 "FStar.TypeChecker.Tc.fst"
let x = ((
# 1503 "FStar.TypeChecker.Tc.fst"
let _57_2109 = x
in {FStar_Syntax_Syntax.ppname = _57_2109.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2109.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (
# 1504 "FStar.TypeChecker.Tc.fst"
let _57_2112 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_751 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _146_750 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _146_751 _146_750)))
end else begin
()
end
in (let _146_752 = (maybe_push_binding env x)
in (x, _146_752, g, u))))
end))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe Prims.list) = (fun env bs -> (
# 1509 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_TypeChecker_Rel.trivial_guard, [])
end
| b::bs -> begin
(
# 1512 "FStar.TypeChecker.Tc.fst"
let _57_2127 = (tc_binder env b)
in (match (_57_2127) with
| (b, env', g, u) -> begin
(
# 1513 "FStar.TypeChecker.Tc.fst"
let _57_2132 = (aux env' bs)
in (match (_57_2132) with
| (bs, env', g', us) -> begin
(let _146_760 = (let _146_759 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _146_759))
in ((b)::bs, env', _146_760, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (
# 1518 "FStar.TypeChecker.Tc.fst"
let tc_args = (fun env args -> (FStar_List.fold_right (fun _57_2140 _57_2143 -> (match ((_57_2140, _57_2143)) with
| ((t, imp), (args, g)) -> begin
(
# 1522 "FStar.TypeChecker.Tc.fst"
let _57_2148 = (tc_term env t)
in (match (_57_2148) with
| (t, _57_2146, g') -> begin
(let _146_769 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _146_769))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _57_2152 -> (match (_57_2152) with
| (pats, g) -> begin
(
# 1525 "FStar.TypeChecker.Tc.fst"
let _57_2155 = (tc_args env p)
in (match (_57_2155) with
| (args, g') -> begin
(let _146_772 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _146_772))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1530 "FStar.TypeChecker.Tc.fst"
let _57_2161 = (tc_maybe_toplevel_term env e)
in (match (_57_2161) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(
# 1533 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (
# 1534 "FStar.TypeChecker.Tc.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 1535 "FStar.TypeChecker.Tc.fst"
let _57_2164 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_775 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _146_775))
end else begin
()
end
in (
# 1536 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 1537 "FStar.TypeChecker.Tc.fst"
let _57_2169 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _146_776 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_146_776, false))
end else begin
(let _146_777 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_146_777, true))
end
in (match (_57_2169) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _146_778 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _146_778))
end
| _57_2173 -> begin
if allow_ghost then begin
(let _146_781 = (let _146_780 = (let _146_779 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_146_779, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_780))
in (Prims.raise _146_781))
end else begin
(let _146_784 = (let _146_783 = (let _146_782 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_146_782, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_783))
in (Prims.raise _146_784))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 1551 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))

# 1555 "FStar.TypeChecker.Tc.fst"
let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (
# 1556 "FStar.TypeChecker.Tc.fst"
let _57_2183 = (tc_tot_or_gtot_term env t)
in (match (_57_2183) with
| (t, c, g) -> begin
(
# 1557 "FStar.TypeChecker.Tc.fst"
let _57_2184 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))

# 1560 "FStar.TypeChecker.Tc.fst"
let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (
# 1561 "FStar.TypeChecker.Tc.fst"
let _57_2192 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_2192) with
| (t, c, g) -> begin
(
# 1562 "FStar.TypeChecker.Tc.fst"
let _57_2193 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))

# 1565 "FStar.TypeChecker.Tc.fst"
let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _146_804 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _146_804)))

# 1570 "FStar.TypeChecker.Tc.fst"
let check_nogen = (fun env t k -> (
# 1571 "FStar.TypeChecker.Tc.fst"
let t = (tc_check_trivial_guard env t k)
in (let _146_808 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _146_808))))

# 1574 "FStar.TypeChecker.Tc.fst"
let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (
# 1575 "FStar.TypeChecker.Tc.fst"
let _57_2208 = (tc_binders env tps)
in (match (_57_2208) with
| (tps, env, g, us) -> begin
(
# 1576 "FStar.TypeChecker.Tc.fst"
let _57_2209 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))

# 1579 "FStar.TypeChecker.Tc.fst"
let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (
# 1580 "FStar.TypeChecker.Tc.fst"
let fail = (fun _57_2215 -> (match (()) with
| () -> begin
(let _146_823 = (let _146_822 = (let _146_821 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_146_821, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_146_822))
in (Prims.raise _146_823))
end))
in (
# 1581 "FStar.TypeChecker.Tc.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1584 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _57_2232)::(wp, _57_2228)::(_wlp, _57_2224)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2236 -> begin
(fail ())
end))
end
| _57_2238 -> begin
(fail ())
end))))

# 1591 "FStar.TypeChecker.Tc.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 1594 "FStar.TypeChecker.Tc.fst"
let _57_2245 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_57_2245) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _57_2247 -> begin
(
# 1597 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow binders c)
in (
# 1598 "FStar.TypeChecker.Tc.fst"
let _57_2251 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_57_2251) with
| (uvs, t') -> begin
(match ((let _146_830 = (FStar_Syntax_Subst.compress t')
in _146_830.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _57_2257 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 1603 "FStar.TypeChecker.Tc.fst"
let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (
# 1604 "FStar.TypeChecker.Tc.fst"
let fail = (fun t -> (let _146_841 = (let _146_840 = (let _146_839 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_146_839, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_146_840))
in (Prims.raise _146_841)))
in (match ((let _146_842 = (FStar_Syntax_Subst.compress signature)
in _146_842.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1607 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _57_2278)::(wp, _57_2274)::(_wlp, _57_2270)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2282 -> begin
(fail signature)
end))
end
| _57_2284 -> begin
(fail signature)
end)))

# 1614 "FStar.TypeChecker.Tc.fst"
let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (
# 1615 "FStar.TypeChecker.Tc.fst"
let _57_2289 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_57_2289) with
| (a, wp) -> begin
(
# 1616 "FStar.TypeChecker.Tc.fst"
let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _57_2292 -> begin
(
# 1620 "FStar.TypeChecker.Tc.fst"
let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (
# 1621 "FStar.TypeChecker.Tc.fst"
let op = (fun ts -> (
# 1622 "FStar.TypeChecker.Tc.fst"
let _57_2296 = ()
in (
# 1623 "FStar.TypeChecker.Tc.fst"
let t0 = (Prims.snd ts)
in (
# 1624 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (
# 1626 "FStar.TypeChecker.Tc.fst"
let _57_2300 = ed
in (let _146_861 = (op ed.FStar_Syntax_Syntax.ret)
in (let _146_860 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _146_859 = (op ed.FStar_Syntax_Syntax.bind_wlp)
in (let _146_858 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _146_857 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _146_856 = (op ed.FStar_Syntax_Syntax.ite_wlp)
in (let _146_855 = (op ed.FStar_Syntax_Syntax.wp_binop)
in (let _146_854 = (op ed.FStar_Syntax_Syntax.wp_as_type)
in (let _146_853 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _146_852 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _146_851 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _146_850 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _146_849 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _57_2300.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2300.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2300.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2300.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2300.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _146_861; FStar_Syntax_Syntax.bind_wp = _146_860; FStar_Syntax_Syntax.bind_wlp = _146_859; FStar_Syntax_Syntax.if_then_else = _146_858; FStar_Syntax_Syntax.ite_wp = _146_857; FStar_Syntax_Syntax.ite_wlp = _146_856; FStar_Syntax_Syntax.wp_binop = _146_855; FStar_Syntax_Syntax.wp_as_type = _146_854; FStar_Syntax_Syntax.close_wp = _146_853; FStar_Syntax_Syntax.assert_p = _146_852; FStar_Syntax_Syntax.assume_p = _146_851; FStar_Syntax_Syntax.null_wp = _146_850; FStar_Syntax_Syntax.trivial = _146_849}))))))))))))))))
end)
in (ed, a, wp))
end)))

# 1642 "FStar.TypeChecker.Tc.fst"
let gen_wps_for_free : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env binders a wp_a ed -> (
# 1647 "FStar.TypeChecker.Tc.fst"
let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env)
in (
# 1649 "FStar.TypeChecker.Tc.fst"
let d = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))
in (
# 1650 "FStar.TypeChecker.Tc.fst"
let normalize_and_make_binders_explicit = (fun tm -> (
# 1651 "FStar.TypeChecker.Tc.fst"
let tm = (normalize tm)
in (
# 1652 "FStar.TypeChecker.Tc.fst"
let rec visit_term = (fun tm -> (
# 1653 "FStar.TypeChecker.Tc.fst"
let n = (match ((let _146_883 = (FStar_Syntax_Subst.compress tm)
in _146_883.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(
# 1655 "FStar.TypeChecker.Tc.fst"
let comp = (visit_comp comp)
in (
# 1656 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map visit_binder binders)
in FStar_Syntax_Syntax.Tm_arrow ((binders, comp))))
end
| FStar_Syntax_Syntax.Tm_abs (binders, term, comp) -> begin
(
# 1659 "FStar.TypeChecker.Tc.fst"
let comp = (visit_maybe_lcomp comp)
in (
# 1660 "FStar.TypeChecker.Tc.fst"
let term = (visit_term term)
in (
# 1661 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map visit_binder binders)
in FStar_Syntax_Syntax.Tm_abs ((binders, term, comp)))))
end
| _57_2335 -> begin
tm.FStar_Syntax_Syntax.n
end)
in (
# 1666 "FStar.TypeChecker.Tc.fst"
let _57_2337 = tm
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2337.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2337.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2337.FStar_Syntax_Syntax.vars})))
and visit_binder = (fun _57_2341 -> (match (_57_2341) with
| (bv, a) -> begin
(let _146_887 = (
# 1668 "FStar.TypeChecker.Tc.fst"
let _57_2342 = bv
in (let _146_885 = (visit_term bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_2342.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2342.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_885}))
in (let _146_886 = (FStar_Syntax_Syntax.as_implicit false)
in (_146_887, _146_886)))
end))
and visit_maybe_lcomp = (fun lcomp -> (match (lcomp) with
| Some (FStar_Util.Inl (lcomp)) -> begin
(let _146_892 = (let _146_891 = (let _146_890 = (let _146_889 = (lcomp.FStar_Syntax_Syntax.comp ())
in (visit_comp _146_889))
in (FStar_Syntax_Util.lcomp_of_comp _146_890))
in FStar_Util.Inl (_146_891))
in Some (_146_892))
end
| comp -> begin
comp
end))
and visit_comp = (fun comp -> (
# 1676 "FStar.TypeChecker.Tc.fst"
let n = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tm) -> begin
(let _146_894 = (visit_term tm)
in FStar_Syntax_Syntax.Total (_146_894))
end
| FStar_Syntax_Syntax.GTotal (tm) -> begin
(let _146_895 = (visit_term tm)
in FStar_Syntax_Syntax.GTotal (_146_895))
end
| comp -> begin
comp
end)
in (
# 1684 "FStar.TypeChecker.Tc.fst"
let _57_2356 = comp
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2356.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2356.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2356.FStar_Syntax_Syntax.vars})))
and visit_args = (fun args -> (FStar_List.map (fun _57_2361 -> (match (_57_2361) with
| (tm, q) -> begin
(let _146_898 = (visit_term tm)
in (_146_898, q))
end)) args))
in (visit_term tm))))
in (
# 1692 "FStar.TypeChecker.Tc.fst"
let check = (fun str t -> if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(
# 1694 "FStar.TypeChecker.Tc.fst"
let _57_2365 = (let _146_903 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Generated term for %s: %s\n" str _146_903))
in (
# 1695 "FStar.TypeChecker.Tc.fst"
let t = (normalize t)
in (
# 1696 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 1697 "FStar.TypeChecker.Tc.fst"
let _57_2380 = (tc_term env t)
in (match (_57_2380) with
| (e, {FStar_Syntax_Syntax.eff_name = _57_2376; FStar_Syntax_Syntax.res_typ = res_typ; FStar_Syntax_Syntax.cflags = _57_2373; FStar_Syntax_Syntax.comp = _57_2371}, _57_2379) -> begin
(
# 1698 "FStar.TypeChecker.Tc.fst"
let _57_2381 = (let _146_906 = (let _146_905 = (normalize res_typ)
in (FStar_Syntax_Print.term_to_string _146_905))
in (FStar_Util.print2 "Inferred type for %s: %s\n" str _146_906))
in (let _146_908 = (let _146_907 = (normalize e)
in (FStar_Syntax_Print.term_to_string _146_907))
in (FStar_Util.print2 "Elaborated term for %s: %s\n" str _146_908)))
end)))))
end else begin
()
end)
in (
# 1714 "FStar.TypeChecker.Tc.fst"
let _57_2406 = (
# 1715 "FStar.TypeChecker.Tc.fst"
let i = (FStar_ST.alloc 0)
in (match ((let _146_921 = (normalize wp_a)
in _146_921.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, comp) -> begin
((fun t -> (FStar_Syntax_Util.arrow wp_binders (
# 1718 "FStar.TypeChecker.Tc.fst"
let _57_2389 = comp
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t); FStar_Syntax_Syntax.tk = _57_2389.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2389.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2389.FStar_Syntax_Syntax.vars}))), (fun t -> (FStar_Syntax_Util.arrow wp_binders (
# 1719 "FStar.TypeChecker.Tc.fst"
let _57_2392 = comp
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (t); FStar_Syntax_Syntax.tk = _57_2392.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2392.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2392.FStar_Syntax_Syntax.vars}))), (fun _57_2394 -> (match (()) with
| () -> begin
(FStar_List.map (fun _57_2398 -> (match (_57_2398) with
| (bv, _57_2397) -> begin
(
# 1726 "FStar.TypeChecker.Tc.fst"
let _57_2399 = (let _146_932 = ((FStar_ST.read i) + 1)
in (FStar_ST.op_Colon_Equals i _146_932))
in (let _146_935 = (let _146_934 = (let _146_933 = (FStar_ST.read i)
in (FStar_Util.string_of_int _146_933))
in (Prims.strcat "g" _146_934))
in (FStar_Syntax_Syntax.gen_bv _146_935 None bv.FStar_Syntax_Syntax.sort)))
end)) wp_binders)
end)))
end
| _57_2402 -> begin
(FStar_All.failwith "wp_a doesn\'t have the right shape")
end))
in (match (_57_2406) with
| (mk_ctx, mk_gctx, mk_gamma) -> begin
(
# 1734 "FStar.TypeChecker.Tc.fst"
let binders_of_list = (FStar_List.map (fun _57_2409 -> (match (_57_2409) with
| (t, b) -> begin
(let _146_947 = (FStar_Syntax_Syntax.as_implicit b)
in (t, _146_947))
end)))
in (
# 1736 "FStar.TypeChecker.Tc.fst"
let implicit_binders_of_list = (FStar_List.map (fun t -> (let _146_950 = (FStar_Syntax_Syntax.as_implicit true)
in (t, _146_950))))
in (
# 1738 "FStar.TypeChecker.Tc.fst"
let args_of_bv = (FStar_List.map (fun bv -> (let _146_953 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_Syntax_Syntax.as_arg _146_953))))
in (
# 1743 "FStar.TypeChecker.Tc.fst"
let c_pure = (
# 1744 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (
# 1745 "FStar.TypeChecker.Tc.fst"
let x = (let _146_954 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _146_954))
in (
# 1746 "FStar.TypeChecker.Tc.fst"
let ret = (let _146_959 = (let _146_958 = (let _146_957 = (let _146_956 = (let _146_955 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx _146_955))
in (FStar_Syntax_Syntax.mk_Total _146_956))
in (FStar_Syntax_Util.lcomp_of_comp _146_957))
in FStar_Util.Inl (_146_958))
in Some (_146_959))
in (
# 1747 "FStar.TypeChecker.Tc.fst"
let gamma = (mk_gamma ())
in (
# 1748 "FStar.TypeChecker.Tc.fst"
let body = (let _146_961 = (implicit_binders_of_list gamma)
in (let _146_960 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs _146_961 _146_960 ret)))
in (let _146_962 = (binders_of_list (((t, true))::((x, false))::[]))
in (FStar_Syntax_Util.abs _146_962 body ret)))))))
in (
# 1751 "FStar.TypeChecker.Tc.fst"
let _57_2421 = (let _146_966 = (let _146_965 = (let _146_964 = (let _146_963 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_963)::[])
in (FStar_List.append binders _146_964))
in (FStar_Syntax_Util.abs _146_965 c_pure None))
in (check "pure" _146_966))
in (
# 1758 "FStar.TypeChecker.Tc.fst"
let c_app = (
# 1759 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (
# 1760 "FStar.TypeChecker.Tc.fst"
let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (
# 1761 "FStar.TypeChecker.Tc.fst"
let l = (let _146_974 = (let _146_973 = (let _146_972 = (let _146_969 = (let _146_968 = (let _146_967 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _146_967))
in (FStar_Syntax_Syntax.mk_binder _146_968))
in (_146_969)::[])
in (let _146_971 = (let _146_970 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _146_970))
in (FStar_Syntax_Util.arrow _146_972 _146_971)))
in (mk_gctx _146_973))
in (FStar_Syntax_Syntax.gen_bv "l" None _146_974))
in (
# 1764 "FStar.TypeChecker.Tc.fst"
let r = (let _146_976 = (let _146_975 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _146_975))
in (FStar_Syntax_Syntax.gen_bv "r" None _146_976))
in (
# 1765 "FStar.TypeChecker.Tc.fst"
let ret = (let _146_981 = (let _146_980 = (let _146_979 = (let _146_978 = (let _146_977 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_977))
in (FStar_Syntax_Syntax.mk_Total _146_978))
in (FStar_Syntax_Util.lcomp_of_comp _146_979))
in FStar_Util.Inl (_146_980))
in Some (_146_981))
in (
# 1766 "FStar.TypeChecker.Tc.fst"
let outer_body = (
# 1767 "FStar.TypeChecker.Tc.fst"
let gamma = (mk_gamma ())
in (
# 1768 "FStar.TypeChecker.Tc.fst"
let gamma_as_args = (args_of_bv gamma)
in (
# 1769 "FStar.TypeChecker.Tc.fst"
let inner_body = (let _146_987 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _146_986 = (let _146_985 = (let _146_984 = (let _146_983 = (let _146_982 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _146_982 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg _146_983))
in (_146_984)::[])
in (FStar_List.append gamma_as_args _146_985))
in (FStar_Syntax_Util.mk_app _146_987 _146_986)))
in (let _146_988 = (implicit_binders_of_list gamma)
in (FStar_Syntax_Util.abs _146_988 inner_body ret)))))
in (let _146_989 = (binders_of_list (((t1, true))::((t2, true))::((l, false))::((r, false))::[]))
in (FStar_Syntax_Util.abs _146_989 outer_body ret))))))))
in (
# 1778 "FStar.TypeChecker.Tc.fst"
let _57_2433 = (let _146_993 = (let _146_992 = (let _146_991 = (let _146_990 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_990)::[])
in (FStar_List.append binders _146_991))
in (FStar_Syntax_Util.abs _146_992 c_app None))
in (check "app" _146_993))
in (
# 1787 "FStar.TypeChecker.Tc.fst"
let unknown = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (
# 1788 "FStar.TypeChecker.Tc.fst"
let c_lift1 = (
# 1789 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (
# 1790 "FStar.TypeChecker.Tc.fst"
let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (
# 1791 "FStar.TypeChecker.Tc.fst"
let t_f = (let _146_998 = (let _146_995 = (let _146_994 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_994))
in (_146_995)::[])
in (let _146_997 = (let _146_996 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _146_996))
in (FStar_Syntax_Util.arrow _146_998 _146_997)))
in (
# 1792 "FStar.TypeChecker.Tc.fst"
let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (
# 1793 "FStar.TypeChecker.Tc.fst"
let a1 = (let _146_1000 = (let _146_999 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _146_999))
in (FStar_Syntax_Syntax.gen_bv "a1" None _146_1000))
in (
# 1794 "FStar.TypeChecker.Tc.fst"
let ret = (let _146_1005 = (let _146_1004 = (let _146_1003 = (let _146_1002 = (let _146_1001 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_1001))
in (FStar_Syntax_Syntax.mk_Total _146_1002))
in (FStar_Syntax_Util.lcomp_of_comp _146_1003))
in FStar_Util.Inl (_146_1004))
in Some (_146_1005))
in (let _146_1018 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::((a1, false))::[]))
in (let _146_1017 = (let _146_1016 = (let _146_1015 = (let _146_1014 = (let _146_1013 = (let _146_1012 = (let _146_1009 = (let _146_1008 = (let _146_1007 = (let _146_1006 = (FStar_Syntax_Syntax.bv_to_name f)
in (_146_1006)::[])
in (unknown)::_146_1007)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1008))
in (FStar_Syntax_Util.mk_app c_pure _146_1009))
in (let _146_1011 = (let _146_1010 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_146_1010)::[])
in (_146_1012)::_146_1011))
in (unknown)::_146_1013)
in (unknown)::_146_1014)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1015))
in (FStar_Syntax_Util.mk_app c_app _146_1016))
in (FStar_Syntax_Util.abs _146_1018 _146_1017 ret)))))))))
in (
# 1802 "FStar.TypeChecker.Tc.fst"
let _57_2443 = (let _146_1022 = (let _146_1021 = (let _146_1020 = (let _146_1019 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1019)::[])
in (FStar_List.append binders _146_1020))
in (FStar_Syntax_Util.abs _146_1021 c_lift1 None))
in (check "lift1" _146_1022))
in (
# 1813 "FStar.TypeChecker.Tc.fst"
let c_lift2 = (
# 1814 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (
# 1815 "FStar.TypeChecker.Tc.fst"
let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (
# 1816 "FStar.TypeChecker.Tc.fst"
let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (
# 1817 "FStar.TypeChecker.Tc.fst"
let t_f = (let _146_1030 = (let _146_1027 = (let _146_1023 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_1023))
in (let _146_1026 = (let _146_1025 = (let _146_1024 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder _146_1024))
in (_146_1025)::[])
in (_146_1027)::_146_1026))
in (let _146_1029 = (let _146_1028 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal _146_1028))
in (FStar_Syntax_Util.arrow _146_1030 _146_1029)))
in (
# 1821 "FStar.TypeChecker.Tc.fst"
let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (
# 1822 "FStar.TypeChecker.Tc.fst"
let a1 = (let _146_1032 = (let _146_1031 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _146_1031))
in (FStar_Syntax_Syntax.gen_bv "a1" None _146_1032))
in (
# 1823 "FStar.TypeChecker.Tc.fst"
let a2 = (let _146_1034 = (let _146_1033 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_1033))
in (FStar_Syntax_Syntax.gen_bv "a2" None _146_1034))
in (
# 1824 "FStar.TypeChecker.Tc.fst"
let ret = (let _146_1039 = (let _146_1038 = (let _146_1037 = (let _146_1036 = (let _146_1035 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx _146_1035))
in (FStar_Syntax_Syntax.mk_Total _146_1036))
in (FStar_Syntax_Util.lcomp_of_comp _146_1037))
in FStar_Util.Inl (_146_1038))
in Some (_146_1039))
in (let _146_1059 = (binders_of_list (((t1, true))::((t2, true))::((t3, true))::((f, false))::((a1, false))::((a2, false))::[]))
in (let _146_1058 = (let _146_1057 = (let _146_1056 = (let _146_1055 = (let _146_1054 = (let _146_1053 = (let _146_1050 = (let _146_1049 = (let _146_1048 = (let _146_1047 = (let _146_1046 = (let _146_1043 = (let _146_1042 = (let _146_1041 = (let _146_1040 = (FStar_Syntax_Syntax.bv_to_name f)
in (_146_1040)::[])
in (unknown)::_146_1041)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1042))
in (FStar_Syntax_Util.mk_app c_pure _146_1043))
in (let _146_1045 = (let _146_1044 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_146_1044)::[])
in (_146_1046)::_146_1045))
in (unknown)::_146_1047)
in (unknown)::_146_1048)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1049))
in (FStar_Syntax_Util.mk_app c_app _146_1050))
in (let _146_1052 = (let _146_1051 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_146_1051)::[])
in (_146_1053)::_146_1052))
in (unknown)::_146_1054)
in (unknown)::_146_1055)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1056))
in (FStar_Syntax_Util.mk_app c_app _146_1057))
in (FStar_Syntax_Util.abs _146_1059 _146_1058 ret)))))))))))
in (
# 1835 "FStar.TypeChecker.Tc.fst"
let _57_2454 = (let _146_1063 = (let _146_1062 = (let _146_1061 = (let _146_1060 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1060)::[])
in (FStar_List.append binders _146_1061))
in (FStar_Syntax_Util.abs _146_1062 c_lift2 None))
in (check "lift2" _146_1063))
in (
# 1841 "FStar.TypeChecker.Tc.fst"
let c_push = (
# 1842 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (
# 1843 "FStar.TypeChecker.Tc.fst"
let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (
# 1844 "FStar.TypeChecker.Tc.fst"
let t_f = (let _146_1069 = (let _146_1065 = (let _146_1064 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_1064))
in (_146_1065)::[])
in (let _146_1068 = (let _146_1067 = (let _146_1066 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_1066))
in (FStar_Syntax_Syntax.mk_Total _146_1067))
in (FStar_Syntax_Util.arrow _146_1069 _146_1068)))
in (
# 1848 "FStar.TypeChecker.Tc.fst"
let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (
# 1849 "FStar.TypeChecker.Tc.fst"
let ret = (let _146_1079 = (let _146_1078 = (let _146_1077 = (let _146_1076 = (let _146_1075 = (let _146_1074 = (let _146_1071 = (let _146_1070 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_1070))
in (_146_1071)::[])
in (let _146_1073 = (let _146_1072 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _146_1072))
in (FStar_Syntax_Util.arrow _146_1074 _146_1073)))
in (mk_ctx _146_1075))
in (FStar_Syntax_Syntax.mk_Total _146_1076))
in (FStar_Syntax_Util.lcomp_of_comp _146_1077))
in FStar_Util.Inl (_146_1078))
in Some (_146_1079))
in (
# 1852 "FStar.TypeChecker.Tc.fst"
let e1 = (let _146_1080 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _146_1080))
in (
# 1853 "FStar.TypeChecker.Tc.fst"
let gamma = (mk_gamma ())
in (
# 1854 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1090 = (let _146_1083 = (FStar_Syntax_Syntax.binders_of_list gamma)
in (let _146_1082 = (let _146_1081 = (FStar_Syntax_Syntax.mk_binder e1)
in (_146_1081)::[])
in (FStar_List.append _146_1083 _146_1082)))
in (let _146_1089 = (let _146_1088 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _146_1087 = (let _146_1086 = (let _146_1084 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _146_1084))
in (let _146_1085 = (args_of_bv gamma)
in (_146_1086)::_146_1085))
in (FStar_Syntax_Util.mk_app _146_1088 _146_1087)))
in (FStar_Syntax_Util.abs _146_1090 _146_1089 ret)))
in (let _146_1091 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::[]))
in (FStar_Syntax_Util.abs _146_1091 body ret))))))))))
in (
# 1859 "FStar.TypeChecker.Tc.fst"
let _57_2465 = (let _146_1095 = (let _146_1094 = (let _146_1093 = (let _146_1092 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1092)::[])
in (FStar_List.append binders _146_1093))
in (FStar_Syntax_Util.abs _146_1094 c_push None))
in (check "push" _146_1095))
in (
# 1861 "FStar.TypeChecker.Tc.fst"
let ret_tot_wp_a = (let _146_1098 = (let _146_1097 = (let _146_1096 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _146_1096))
in FStar_Util.Inl (_146_1097))
in Some (_146_1098))
in (
# 1867 "FStar.TypeChecker.Tc.fst"
let wp_if_then_else = (
# 1868 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _146_1109 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (let _146_1108 = (
# 1873 "FStar.TypeChecker.Tc.fst"
let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_unfoldable (2)) None)
in (let _146_1107 = (let _146_1106 = (let _146_1105 = (let _146_1104 = (let _146_1103 = (let _146_1102 = (let _146_1101 = (let _146_1100 = (let _146_1099 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _146_1099))
in (_146_1100)::[])
in (FStar_Syntax_Util.mk_app l_ite _146_1101))
in (_146_1102)::[])
in (unknown)::_146_1103)
in (unknown)::_146_1104)
in (unknown)::_146_1105)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1106))
in (FStar_Syntax_Util.mk_app c_lift2 _146_1107)))
in (FStar_Syntax_Util.abs _146_1109 _146_1108 ret_tot_wp_a))))
in (
# 1881 "FStar.TypeChecker.Tc.fst"
let wp_if_then_else = (normalize_and_make_binders_explicit wp_if_then_else)
in (
# 1882 "FStar.TypeChecker.Tc.fst"
let _57_2472 = (let _146_1110 = (FStar_Syntax_Util.abs binders wp_if_then_else None)
in (check "wp_if_then_else" _146_1110))
in (
# 1888 "FStar.TypeChecker.Tc.fst"
let wp_binop = (
# 1889 "FStar.TypeChecker.Tc.fst"
let l = (FStar_Syntax_Syntax.gen_bv "l" None wp_a)
in (
# 1890 "FStar.TypeChecker.Tc.fst"
let op = (let _146_1116 = (let _146_1115 = (let _146_1113 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Util.ktype0)
in (let _146_1112 = (let _146_1111 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Util.ktype0)
in (_146_1111)::[])
in (_146_1113)::_146_1112))
in (let _146_1114 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _146_1115 _146_1114)))
in (FStar_Syntax_Syntax.gen_bv "op" None _146_1116))
in (
# 1893 "FStar.TypeChecker.Tc.fst"
let r = (FStar_Syntax_Syntax.gen_bv "r" None wp_a)
in (let _146_1128 = (FStar_Syntax_Syntax.binders_of_list ((a)::(l)::(op)::(r)::[]))
in (let _146_1127 = (let _146_1126 = (let _146_1125 = (let _146_1124 = (let _146_1123 = (let _146_1122 = (let _146_1121 = (FStar_Syntax_Syntax.bv_to_name op)
in (let _146_1120 = (let _146_1119 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _146_1118 = (let _146_1117 = (FStar_Syntax_Syntax.bv_to_name r)
in (_146_1117)::[])
in (_146_1119)::_146_1118))
in (_146_1121)::_146_1120))
in (unknown)::_146_1122)
in (unknown)::_146_1123)
in (unknown)::_146_1124)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1125))
in (FStar_Syntax_Util.mk_app c_lift2 _146_1126))
in (FStar_Syntax_Util.abs _146_1128 _146_1127 ret_tot_wp_a))))))
in (
# 1901 "FStar.TypeChecker.Tc.fst"
let wp_binop = (normalize_and_make_binders_explicit wp_binop)
in (
# 1902 "FStar.TypeChecker.Tc.fst"
let _57_2479 = (let _146_1129 = (FStar_Syntax_Util.abs binders wp_binop None)
in (check "wp_binop" _146_1129))
in (
# 1907 "FStar.TypeChecker.Tc.fst"
let wp_assert = (
# 1908 "FStar.TypeChecker.Tc.fst"
let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (
# 1909 "FStar.TypeChecker.Tc.fst"
let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (
# 1910 "FStar.TypeChecker.Tc.fst"
let l_and = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (
# 1911 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1143 = (let _146_1142 = (let _146_1141 = (let _146_1140 = (let _146_1139 = (let _146_1136 = (let _146_1135 = (let _146_1134 = (let _146_1133 = (let _146_1132 = (let _146_1131 = (let _146_1130 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _146_1130))
in (_146_1131)::[])
in (FStar_Syntax_Util.mk_app l_and _146_1132))
in (_146_1133)::[])
in (unknown)::_146_1134)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1135))
in (FStar_Syntax_Util.mk_app c_pure _146_1136))
in (let _146_1138 = (let _146_1137 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_146_1137)::[])
in (_146_1139)::_146_1138))
in (unknown)::_146_1140)
in (unknown)::_146_1141)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1142))
in (FStar_Syntax_Util.mk_app c_app _146_1143))
in (let _146_1144 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _146_1144 body ret_tot_wp_a))))))
in (
# 1921 "FStar.TypeChecker.Tc.fst"
let wp_assert = (normalize_and_make_binders_explicit wp_assert)
in (
# 1922 "FStar.TypeChecker.Tc.fst"
let _57_2487 = (let _146_1145 = (FStar_Syntax_Util.abs binders wp_assert None)
in (check "wp_assert" _146_1145))
in (
# 1927 "FStar.TypeChecker.Tc.fst"
let wp_assume = (
# 1928 "FStar.TypeChecker.Tc.fst"
let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (
# 1929 "FStar.TypeChecker.Tc.fst"
let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (
# 1930 "FStar.TypeChecker.Tc.fst"
let l_imp = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (
# 1931 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1159 = (let _146_1158 = (let _146_1157 = (let _146_1156 = (let _146_1155 = (let _146_1152 = (let _146_1151 = (let _146_1150 = (let _146_1149 = (let _146_1148 = (let _146_1147 = (let _146_1146 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _146_1146))
in (_146_1147)::[])
in (FStar_Syntax_Util.mk_app l_imp _146_1148))
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
# 1941 "FStar.TypeChecker.Tc.fst"
let wp_assume = (normalize_and_make_binders_explicit wp_assume)
in (
# 1942 "FStar.TypeChecker.Tc.fst"
let _57_2495 = (let _146_1161 = (FStar_Syntax_Util.abs binders wp_assume None)
in (check "wp_assume" _146_1161))
in (
# 1944 "FStar.TypeChecker.Tc.fst"
let tforall = (let _146_1164 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _146_1163 = (let _146_1162 = (FStar_Syntax_Syntax.as_arg unknown)
in (_146_1162)::[])
in (FStar_Syntax_Util.mk_app _146_1164 _146_1163)))
in (
# 1950 "FStar.TypeChecker.Tc.fst"
let wp_close = (
# 1951 "FStar.TypeChecker.Tc.fst"
let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (
# 1952 "FStar.TypeChecker.Tc.fst"
let t_f = (let _146_1168 = (let _146_1166 = (let _146_1165 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _146_1165))
in (_146_1166)::[])
in (let _146_1167 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1168 _146_1167)))
in (
# 1953 "FStar.TypeChecker.Tc.fst"
let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (
# 1954 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1181 = (let _146_1180 = (let _146_1179 = (let _146_1178 = (let _146_1177 = (let _146_1169 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((unknown)::(tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _146_1169))
in (let _146_1176 = (let _146_1175 = (let _146_1174 = (let _146_1173 = (let _146_1172 = (let _146_1171 = (let _146_1170 = (FStar_Syntax_Syntax.bv_to_name f)
in (_146_1170)::[])
in (unknown)::_146_1171)
in (unknown)::_146_1172)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1173))
in (FStar_Syntax_Util.mk_app c_push _146_1174))
in (_146_1175)::[])
in (_146_1177)::_146_1176))
in (unknown)::_146_1178)
in (unknown)::_146_1179)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1180))
in (FStar_Syntax_Util.mk_app c_app _146_1181))
in (let _146_1182 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_Syntax_Util.abs _146_1182 body ret_tot_wp_a))))))
in (
# 1966 "FStar.TypeChecker.Tc.fst"
let wp_close = (normalize_and_make_binders_explicit wp_close)
in (
# 1967 "FStar.TypeChecker.Tc.fst"
let _57_2504 = (let _146_1183 = (FStar_Syntax_Util.abs binders wp_close None)
in (check "wp_close" _146_1183))
in (
# 1969 "FStar.TypeChecker.Tc.fst"
let ret_tot_type0 = (let _146_1186 = (let _146_1185 = (let _146_1184 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_1184))
in FStar_Util.Inl (_146_1185))
in Some (_146_1186))
in (
# 1970 "FStar.TypeChecker.Tc.fst"
let mk_forall = (fun x body -> (
# 1971 "FStar.TypeChecker.Tc.fst"
let tforall = (let _146_1193 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _146_1192 = (let _146_1191 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (_146_1191)::[])
in (FStar_Syntax_Util.mk_app _146_1193 _146_1192)))
in (let _146_1200 = (let _146_1199 = (let _146_1198 = (let _146_1197 = (let _146_1196 = (let _146_1195 = (let _146_1194 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_1194)::[])
in (FStar_Syntax_Util.abs _146_1195 body ret_tot_type0))
in (FStar_Syntax_Syntax.as_arg _146_1196))
in (_146_1197)::[])
in (tforall, _146_1198))
in FStar_Syntax_Syntax.Tm_app (_146_1199))
in (FStar_Syntax_Syntax.mk _146_1200 None FStar_Range.dummyRange))))
in (
# 1982 "FStar.TypeChecker.Tc.fst"
let rec mk_leq = (fun t x y -> (match ((let _146_1208 = (let _146_1207 = (FStar_Syntax_Subst.compress t)
in (normalize _146_1207))
in _146_1208.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_2516) -> begin
(
# 1985 "FStar.TypeChecker.Tc.fst"
let _57_2518 = (let _146_1210 = (FStar_Syntax_Print.term_to_string x)
in (let _146_1209 = (FStar_Syntax_Print.term_to_string y)
in (FStar_Util.print2 "type0, x=%s, y=%s\n" _146_1210 _146_1209)))
in (FStar_Syntax_Util.mk_imp x y))
end
| (FStar_Syntax_Syntax.Tm_arrow (binder::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow (binder::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) when (FStar_Syntax_Syntax.is_null_binder binder) -> begin
(
# 1989 "FStar.TypeChecker.Tc.fst"
let a = (Prims.fst binder).FStar_Syntax_Syntax.sort
in (
# 1990 "FStar.TypeChecker.Tc.fst"
let _57_2545 = (let _146_1212 = (FStar_Syntax_Print.term_to_string a)
in (let _146_1211 = (FStar_Syntax_Print.term_to_string b)
in (FStar_Util.print2 "arrow, a=%s, b=%s\n" _146_1212 _146_1211)))
in (
# 1991 "FStar.TypeChecker.Tc.fst"
let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (
# 1992 "FStar.TypeChecker.Tc.fst"
let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (
# 1993 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1224 = (let _146_1214 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _146_1213 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_leq a _146_1214 _146_1213)))
in (let _146_1223 = (let _146_1222 = (let _146_1217 = (let _146_1216 = (let _146_1215 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _146_1215))
in (_146_1216)::[])
in (FStar_Syntax_Util.mk_app x _146_1217))
in (let _146_1221 = (let _146_1220 = (let _146_1219 = (let _146_1218 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _146_1218))
in (_146_1219)::[])
in (FStar_Syntax_Util.mk_app y _146_1220))
in (mk_leq b _146_1222 _146_1221)))
in (FStar_Syntax_Util.mk_imp _146_1224 _146_1223)))
in (let _146_1225 = (mk_forall a2 body)
in (mk_forall a1 _146_1225)))))))
end
| FStar_Syntax_Syntax.Tm_arrow (binder::binders, comp) -> begin
(
# 2001 "FStar.TypeChecker.Tc.fst"
let t = (
# 2001 "FStar.TypeChecker.Tc.fst"
let _57_2556 = t
in (let _146_1229 = (let _146_1228 = (let _146_1227 = (let _146_1226 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _146_1226))
in ((binder)::[], _146_1227))
in FStar_Syntax_Syntax.Tm_arrow (_146_1228))
in {FStar_Syntax_Syntax.n = _146_1229; FStar_Syntax_Syntax.tk = _57_2556.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2556.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2556.FStar_Syntax_Syntax.vars}))
in (mk_leq t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_57_2560) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _57_2563 -> begin
(
# 2007 "FStar.TypeChecker.Tc.fst"
let _57_2564 = (let _146_1231 = (FStar_Syntax_Print.term_to_string x)
in (let _146_1230 = (FStar_Syntax_Print.term_to_string y)
in (FStar_Util.print2 "base, x=%s, y=%s\n" _146_1231 _146_1230)))
in (FStar_Syntax_Util.mk_eq t t x y))
end))
in (
# 2010 "FStar.TypeChecker.Tc.fst"
let stronger = (
# 2011 "FStar.TypeChecker.Tc.fst"
let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (
# 2012 "FStar.TypeChecker.Tc.fst"
let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (
# 2013 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1233 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _146_1232 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_leq wp_a _146_1233 _146_1232)))
in (let _146_1234 = (FStar_Syntax_Syntax.binders_of_list ((wp1)::(wp2)::[]))
in (FStar_Syntax_Util.abs _146_1234 body ret_tot_type0)))))
in (
# 2016 "FStar.TypeChecker.Tc.fst"
let _57_2570 = (let _146_1238 = (let _146_1237 = (let _146_1236 = (let _146_1235 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1235)::[])
in (FStar_List.append binders _146_1236))
in (FStar_Syntax_Util.abs _146_1237 stronger None))
in (check "stronger" _146_1238))
in (
# 2018 "FStar.TypeChecker.Tc.fst"
let null_wp = (Prims.snd ed.FStar_Syntax_Syntax.null_wp)
in (
# 2022 "FStar.TypeChecker.Tc.fst"
let wp_trivial = (
# 2023 "FStar.TypeChecker.Tc.fst"
let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (
# 2024 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1246 = (let _146_1245 = (let _146_1244 = (let _146_1241 = (let _146_1240 = (let _146_1239 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _146_1239))
in (_146_1240)::[])
in (FStar_Syntax_Util.mk_app null_wp _146_1241))
in (let _146_1243 = (let _146_1242 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_146_1242)::[])
in (_146_1244)::_146_1243))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1245))
in (FStar_Syntax_Util.mk_app stronger _146_1246))
in (let _146_1247 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_Syntax_Util.abs _146_1247 body ret_tot_type0))))
in (
# 2030 "FStar.TypeChecker.Tc.fst"
let wp_trivial = (normalize_and_make_binders_explicit wp_trivial)
in (
# 2031 "FStar.TypeChecker.Tc.fst"
let _57_2577 = (let _146_1248 = (FStar_Syntax_Util.abs binders wp_trivial None)
in (check "wp_trivial" _146_1248))
in (
# 2033 "FStar.TypeChecker.Tc.fst"
let _57_2579 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2579.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2579.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2579.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2579.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2579.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _57_2579.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2579.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _57_2579.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = ([], wp_if_then_else); FStar_Syntax_Syntax.ite_wp = _57_2579.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _57_2579.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = ([], wp_binop); FStar_Syntax_Syntax.wp_as_type = _57_2579.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = ([], wp_close); FStar_Syntax_Syntax.assert_p = ([], wp_assert); FStar_Syntax_Syntax.assume_p = ([], wp_assume); FStar_Syntax_Syntax.null_wp = _57_2579.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = ([], wp_trivial)})))))))))))))))))))))))))))))))))))))))))
end)))))))

# 2043 "FStar.TypeChecker.Tc.fst"
let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  effect_cost  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed is_for_free -> (
# 2044 "FStar.TypeChecker.Tc.fst"
let _57_2584 = ()
in (
# 2045 "FStar.TypeChecker.Tc.fst"
let _57_2588 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_57_2588) with
| (binders_un, signature_un) -> begin
(
# 2046 "FStar.TypeChecker.Tc.fst"
let _57_2593 = (tc_tparams env0 binders_un)
in (match (_57_2593) with
| (binders, env, _57_2592) -> begin
(
# 2047 "FStar.TypeChecker.Tc.fst"
let _57_2597 = (tc_trivial_guard env signature_un)
in (match (_57_2597) with
| (signature, _57_2596) -> begin
(
# 2048 "FStar.TypeChecker.Tc.fst"
let ed = (
# 2048 "FStar.TypeChecker.Tc.fst"
let _57_2598 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2598.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2598.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2598.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _57_2598.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2598.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _57_2598.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = _57_2598.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _57_2598.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _57_2598.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = _57_2598.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _57_2598.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _57_2598.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _57_2598.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _57_2598.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _57_2598.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _57_2598.FStar_Syntax_Syntax.trivial})
in (
# 2051 "FStar.TypeChecker.Tc.fst"
let _57_2604 = (open_effect_decl env ed)
in (match (_57_2604) with
| (ed, a, wp_a) -> begin
(
# 2052 "FStar.TypeChecker.Tc.fst"
let get_effect_signature = (fun _57_2606 -> (match (()) with
| () -> begin
(
# 2053 "FStar.TypeChecker.Tc.fst"
let _57_2610 = (tc_trivial_guard env signature_un)
in (match (_57_2610) with
| (signature, _57_2609) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (
# 2057 "FStar.TypeChecker.Tc.fst"
let env = (let _146_1257 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _146_1257))
in (
# 2059 "FStar.TypeChecker.Tc.fst"
let _57_2612 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _146_1260 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _146_1259 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _146_1258 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checking effect signature: %s %s : %s\n" _146_1260 _146_1259 _146_1258))))
end else begin
()
end
in (
# 2065 "FStar.TypeChecker.Tc.fst"
let check_and_gen' = (fun env _57_2619 k -> (match (_57_2619) with
| (_57_2617, t) -> begin
(check_and_gen env t k)
end))
in (
# 2069 "FStar.TypeChecker.Tc.fst"
let ed = (match (is_for_free) with
| NotForFree -> begin
ed
end
| ForFree -> begin
(gen_wps_for_free env binders a wp_a ed)
end)
in (
# 2074 "FStar.TypeChecker.Tc.fst"
let ret = (
# 2075 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1272 = (let _146_1270 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1269 = (let _146_1268 = (let _146_1267 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_1267))
in (_146_1268)::[])
in (_146_1270)::_146_1269))
in (let _146_1271 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _146_1272 _146_1271)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (
# 2078 "FStar.TypeChecker.Tc.fst"
let bind_wp = (
# 2079 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 2080 "FStar.TypeChecker.Tc.fst"
let _57_2629 = (get_effect_signature ())
in (match (_57_2629) with
| (b, wp_b) -> begin
(
# 2081 "FStar.TypeChecker.Tc.fst"
let a_wp_b = (let _146_1276 = (let _146_1274 = (let _146_1273 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_1273))
in (_146_1274)::[])
in (let _146_1275 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _146_1276 _146_1275)))
in (
# 2082 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = a_wp_b
in (
# 2083 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1289 = (let _146_1287 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1286 = (let _146_1285 = (FStar_Syntax_Syntax.mk_binder b)
in (let _146_1284 = (let _146_1283 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_1282 = (let _146_1281 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _146_1280 = (let _146_1279 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (let _146_1278 = (let _146_1277 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_146_1277)::[])
in (_146_1279)::_146_1278))
in (_146_1281)::_146_1280))
in (_146_1283)::_146_1282))
in (_146_1285)::_146_1284))
in (_146_1287)::_146_1286))
in (let _146_1288 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _146_1289 _146_1288)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k))))
end)))
in (
# 2089 "FStar.TypeChecker.Tc.fst"
let bind_wlp = (
# 2090 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 2091 "FStar.TypeChecker.Tc.fst"
let _57_2637 = (get_effect_signature ())
in (match (_57_2637) with
| (b, wlp_b) -> begin
(
# 2092 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = (let _146_1293 = (let _146_1291 = (let _146_1290 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_1290))
in (_146_1291)::[])
in (let _146_1292 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _146_1293 _146_1292)))
in (
# 2093 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1302 = (let _146_1300 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1299 = (let _146_1298 = (FStar_Syntax_Syntax.mk_binder b)
in (let _146_1297 = (let _146_1296 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _146_1295 = (let _146_1294 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_146_1294)::[])
in (_146_1296)::_146_1295))
in (_146_1298)::_146_1297))
in (_146_1300)::_146_1299))
in (let _146_1301 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _146_1302 _146_1301)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wlp expected_k)))
end)))
in (
# 2099 "FStar.TypeChecker.Tc.fst"
let if_then_else = (
# 2100 "FStar.TypeChecker.Tc.fst"
let p = (let _146_1304 = (let _146_1303 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1303 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _146_1304))
in (
# 2101 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1313 = (let _146_1311 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1310 = (let _146_1309 = (FStar_Syntax_Syntax.mk_binder p)
in (let _146_1308 = (let _146_1307 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_1306 = (let _146_1305 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1305)::[])
in (_146_1307)::_146_1306))
in (_146_1309)::_146_1308))
in (_146_1311)::_146_1310))
in (let _146_1312 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1313 _146_1312)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (
# 2107 "FStar.TypeChecker.Tc.fst"
let ite_wp = (
# 2108 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 2109 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1320 = (let _146_1318 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1317 = (let _146_1316 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _146_1315 = (let _146_1314 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1314)::[])
in (_146_1316)::_146_1315))
in (_146_1318)::_146_1317))
in (let _146_1319 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1320 _146_1319)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k)))
in (
# 2115 "FStar.TypeChecker.Tc.fst"
let ite_wlp = (
# 2116 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 2117 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1325 = (let _146_1323 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1322 = (let _146_1321 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (_146_1321)::[])
in (_146_1323)::_146_1322))
in (let _146_1324 = (FStar_Syntax_Syntax.mk_Total wlp_a)
in (FStar_Syntax_Util.arrow _146_1325 _146_1324)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wlp expected_k)))
in (
# 2122 "FStar.TypeChecker.Tc.fst"
let wp_binop = (
# 2123 "FStar.TypeChecker.Tc.fst"
let bin_op = (
# 2124 "FStar.TypeChecker.Tc.fst"
let _57_2652 = (FStar_Syntax_Util.type_u ())
in (match (_57_2652) with
| (t1, u1) -> begin
(
# 2125 "FStar.TypeChecker.Tc.fst"
let _57_2655 = (FStar_Syntax_Util.type_u ())
in (match (_57_2655) with
| (t2, u2) -> begin
(
# 2126 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1326 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_max ((u1)::(u2)::[]))) None _146_1326))
in (let _146_1331 = (let _146_1329 = (FStar_Syntax_Syntax.null_binder t1)
in (let _146_1328 = (let _146_1327 = (FStar_Syntax_Syntax.null_binder t2)
in (_146_1327)::[])
in (_146_1329)::_146_1328))
in (let _146_1330 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _146_1331 _146_1330))))
end))
end))
in (
# 2128 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1340 = (let _146_1338 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1337 = (let _146_1336 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_1335 = (let _146_1334 = (FStar_Syntax_Syntax.null_binder bin_op)
in (let _146_1333 = (let _146_1332 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1332)::[])
in (_146_1334)::_146_1333))
in (_146_1336)::_146_1335))
in (_146_1338)::_146_1337))
in (let _146_1339 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1340 _146_1339)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_binop expected_k)))
in (
# 2135 "FStar.TypeChecker.Tc.fst"
let wp_as_type = (
# 2136 "FStar.TypeChecker.Tc.fst"
let _57_2663 = (FStar_Syntax_Util.type_u ())
in (match (_57_2663) with
| (t, _57_2662) -> begin
(
# 2137 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1345 = (let _146_1343 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1342 = (let _146_1341 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1341)::[])
in (_146_1343)::_146_1342))
in (let _146_1344 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _146_1345 _146_1344)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (
# 2142 "FStar.TypeChecker.Tc.fst"
let close_wp = (
# 2143 "FStar.TypeChecker.Tc.fst"
let b = (let _146_1347 = (let _146_1346 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1346 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _146_1347))
in (
# 2144 "FStar.TypeChecker.Tc.fst"
let b_wp_a = (let _146_1351 = (let _146_1349 = (let _146_1348 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _146_1348))
in (_146_1349)::[])
in (let _146_1350 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1351 _146_1350)))
in (
# 2145 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1358 = (let _146_1356 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1355 = (let _146_1354 = (FStar_Syntax_Syntax.mk_binder b)
in (let _146_1353 = (let _146_1352 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_146_1352)::[])
in (_146_1354)::_146_1353))
in (_146_1356)::_146_1355))
in (let _146_1357 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1358 _146_1357)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (
# 2149 "FStar.TypeChecker.Tc.fst"
let assert_p = (
# 2150 "FStar.TypeChecker.Tc.fst"
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
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (
# 2156 "FStar.TypeChecker.Tc.fst"
let assume_p = (
# 2157 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1376 = (let _146_1374 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1373 = (let _146_1372 = (let _146_1369 = (let _146_1368 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1368 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _146_1369))
in (let _146_1371 = (let _146_1370 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1370)::[])
in (_146_1372)::_146_1371))
in (_146_1374)::_146_1373))
in (let _146_1375 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1376 _146_1375)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (
# 2163 "FStar.TypeChecker.Tc.fst"
let null_wp = (
# 2164 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1379 = (let _146_1377 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1377)::[])
in (let _146_1378 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1379 _146_1378)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (
# 2168 "FStar.TypeChecker.Tc.fst"
let trivial_wp = (
# 2169 "FStar.TypeChecker.Tc.fst"
let _57_2679 = (FStar_Syntax_Util.type_u ())
in (match (_57_2679) with
| (t, _57_2678) -> begin
(
# 2170 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1384 = (let _146_1382 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1381 = (let _146_1380 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1380)::[])
in (_146_1382)::_146_1381))
in (let _146_1383 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _146_1384 _146_1383)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (
# 2176 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1385 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _146_1385))
in (
# 2177 "FStar.TypeChecker.Tc.fst"
let _57_2685 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_57_2685) with
| (univs, t) -> begin
(
# 2178 "FStar.TypeChecker.Tc.fst"
let _57_2701 = (match ((let _146_1387 = (let _146_1386 = (FStar_Syntax_Subst.compress t)
in _146_1386.FStar_Syntax_Syntax.n)
in (binders, _146_1387))) with
| ([], _57_2688) -> begin
([], t)
end
| (_57_2691, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _57_2698 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_2701) with
| (binders, signature) -> begin
(
# 2182 "FStar.TypeChecker.Tc.fst"
let close = (fun n ts -> (
# 2183 "FStar.TypeChecker.Tc.fst"
let ts = (let _146_1392 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _146_1392))
in (
# 2184 "FStar.TypeChecker.Tc.fst"
let _57_2706 = ()
in ts)))
in (
# 2186 "FStar.TypeChecker.Tc.fst"
let ed = (
# 2186 "FStar.TypeChecker.Tc.fst"
let _57_2708 = ed
in (let _146_1405 = (close 0 ret)
in (let _146_1404 = (close 1 bind_wp)
in (let _146_1403 = (close 1 bind_wlp)
in (let _146_1402 = (close 0 if_then_else)
in (let _146_1401 = (close 0 ite_wp)
in (let _146_1400 = (close 0 ite_wlp)
in (let _146_1399 = (close 0 wp_binop)
in (let _146_1398 = (close 0 wp_as_type)
in (let _146_1397 = (close 1 close_wp)
in (let _146_1396 = (close 0 assert_p)
in (let _146_1395 = (close 0 assume_p)
in (let _146_1394 = (close 0 null_wp)
in (let _146_1393 = (close 0 trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _57_2708.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2708.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _146_1405; FStar_Syntax_Syntax.bind_wp = _146_1404; FStar_Syntax_Syntax.bind_wlp = _146_1403; FStar_Syntax_Syntax.if_then_else = _146_1402; FStar_Syntax_Syntax.ite_wp = _146_1401; FStar_Syntax_Syntax.ite_wlp = _146_1400; FStar_Syntax_Syntax.wp_binop = _146_1399; FStar_Syntax_Syntax.wp_as_type = _146_1398; FStar_Syntax_Syntax.close_wp = _146_1397; FStar_Syntax_Syntax.assert_p = _146_1396; FStar_Syntax_Syntax.assume_p = _146_1395; FStar_Syntax_Syntax.null_wp = _146_1394; FStar_Syntax_Syntax.trivial = _146_1393}))))))))))))))
in (
# 2204 "FStar.TypeChecker.Tc.fst"
let _57_2711 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1406 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _146_1406))
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

# 2208 "FStar.TypeChecker.Tc.fst"
let tc_lex_t = (fun env ses quals lids -> (
# 2215 "FStar.TypeChecker.Tc.fst"
let _57_2717 = ()
in (
# 2216 "FStar.TypeChecker.Tc.fst"
let _57_2725 = ()
in (match (ses) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _57_2754, _57_2756, [], r)::FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _57_2745, r1)::FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _57_2734, r2)::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(
# 2231 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (
# 2232 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (
# 2233 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (
# 2234 "FStar.TypeChecker.Tc.fst"
let tc = FStar_Syntax_Syntax.Sig_inductive_typ ((lex_t, (u)::[], [], t, [], (FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[], [], r))
in (
# 2236 "FStar.TypeChecker.Tc.fst"
let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (
# 2237 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (let _146_1414 = (let _146_1413 = (let _146_1412 = (let _146_1411 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _146_1411 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1412, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1413))
in (FStar_Syntax_Syntax.mk _146_1414 None r1))
in (
# 2238 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (
# 2239 "FStar.TypeChecker.Tc.fst"
let dc_lextop = FStar_Syntax_Syntax.Sig_datacon ((lex_top, (utop)::[], lex_top_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r1))
in (
# 2241 "FStar.TypeChecker.Tc.fst"
let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 2242 "FStar.TypeChecker.Tc.fst"
let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 2243 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (
# 2244 "FStar.TypeChecker.Tc.fst"
let a = (let _146_1415 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1415))
in (
# 2245 "FStar.TypeChecker.Tc.fst"
let hd = (let _146_1416 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1416))
in (
# 2246 "FStar.TypeChecker.Tc.fst"
let tl = (let _146_1421 = (let _146_1420 = (let _146_1419 = (let _146_1418 = (let _146_1417 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _146_1417 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1418, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1419))
in (FStar_Syntax_Syntax.mk _146_1420 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1421))
in (
# 2247 "FStar.TypeChecker.Tc.fst"
let res = (let _146_1425 = (let _146_1424 = (let _146_1423 = (let _146_1422 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _146_1422 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1423, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1424))
in (FStar_Syntax_Syntax.mk _146_1425 None r2))
in (let _146_1426 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _146_1426))))))
in (
# 2249 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (
# 2250 "FStar.TypeChecker.Tc.fst"
let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _146_1428 = (let _146_1427 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _146_1427))
in FStar_Syntax_Syntax.Sig_bundle (_146_1428)))))))))))))))
end
| _57_2780 -> begin
(let _146_1430 = (let _146_1429 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _146_1429))
in (FStar_All.failwith _146_1430))
end))))

# 2256 "FStar.TypeChecker.Tc.fst"
let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (
# 2319 "FStar.TypeChecker.Tc.fst"
let warn_positivity = (fun l r -> (let _146_1444 = (let _146_1443 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _146_1443))
in (FStar_TypeChecker_Errors.diag r _146_1444)))
in (
# 2321 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2324 "FStar.TypeChecker.Tc.fst"
let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(
# 2329 "FStar.TypeChecker.Tc.fst"
let _57_2802 = ()
in (
# 2330 "FStar.TypeChecker.Tc.fst"
let _57_2804 = (warn_positivity tc r)
in (
# 2331 "FStar.TypeChecker.Tc.fst"
let _57_2808 = (FStar_Syntax_Subst.open_term tps k)
in (match (_57_2808) with
| (tps, k) -> begin
(
# 2332 "FStar.TypeChecker.Tc.fst"
let _57_2812 = (tc_tparams env tps)
in (match (_57_2812) with
| (tps, env_tps, us) -> begin
(
# 2333 "FStar.TypeChecker.Tc.fst"
let _57_2815 = (FStar_Syntax_Util.arrow_formals k)
in (match (_57_2815) with
| (indices, t) -> begin
(
# 2334 "FStar.TypeChecker.Tc.fst"
let _57_2819 = (tc_tparams env_tps indices)
in (match (_57_2819) with
| (indices, env', us') -> begin
(
# 2335 "FStar.TypeChecker.Tc.fst"
let _57_2823 = (tc_trivial_guard env' t)
in (match (_57_2823) with
| (t, _57_2822) -> begin
(
# 2336 "FStar.TypeChecker.Tc.fst"
let k = (let _146_1449 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _146_1449))
in (
# 2337 "FStar.TypeChecker.Tc.fst"
let _57_2827 = (FStar_Syntax_Util.type_u ())
in (match (_57_2827) with
| (t_type, u) -> begin
(
# 2338 "FStar.TypeChecker.Tc.fst"
let _57_2828 = (let _146_1450 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _146_1450))
in (
# 2340 "FStar.TypeChecker.Tc.fst"
let t_tc = (let _146_1451 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _146_1451))
in (
# 2341 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 2342 "FStar.TypeChecker.Tc.fst"
let k = (FStar_Syntax_Subst.close tps k)
in (
# 2343 "FStar.TypeChecker.Tc.fst"
let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _146_1452 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) ([], t_tc))
in (_146_1452, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u)))))))
end)))
end))
end))
end))
end))
end))))
end
| _57_2835 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 2350 "FStar.TypeChecker.Tc.fst"
let positive_if_pure = (fun _57_2837 l -> ())
in (
# 2353 "FStar.TypeChecker.Tc.fst"
let tc_data = (fun env tcs _57_6 -> (match (_57_6) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(
# 2355 "FStar.TypeChecker.Tc.fst"
let _57_2854 = ()
in (
# 2357 "FStar.TypeChecker.Tc.fst"
let _57_2889 = (
# 2358 "FStar.TypeChecker.Tc.fst"
let tps_u_opt = (FStar_Util.find_map tcs (fun _57_2858 -> (match (_57_2858) with
| (se, u_tc) -> begin
if (let _146_1465 = (let _146_1464 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _146_1464))
in (FStar_Ident.lid_equals tc_lid _146_1465)) then begin
(
# 2360 "FStar.TypeChecker.Tc.fst"
let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2860, _57_2862, tps, _57_2865, _57_2867, _57_2869, _57_2871, _57_2873) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _57_2879 -> (match (_57_2879) with
| (x, _57_2878) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _57_2881 -> begin
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
in (match (_57_2889) with
| (tps, u_tc) -> begin
(
# 2373 "FStar.TypeChecker.Tc.fst"
let _57_2909 = (match ((let _146_1467 = (FStar_Syntax_Subst.compress t)
in _146_1467.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(
# 2378 "FStar.TypeChecker.Tc.fst"
let _57_2897 = (FStar_Util.first_N ntps bs)
in (match (_57_2897) with
| (_57_2895, bs') -> begin
(
# 2379 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (
# 2380 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _57_2903 -> (match (_57_2903) with
| (x, _57_2902) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _146_1470 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _146_1470))))
end))
end
| _57_2906 -> begin
([], t)
end)
in (match (_57_2909) with
| (arguments, result) -> begin
(
# 2384 "FStar.TypeChecker.Tc.fst"
let _57_2910 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1473 = (FStar_Syntax_Print.lid_to_string c)
in (let _146_1472 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _146_1471 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _146_1473 _146_1472 _146_1471))))
end else begin
()
end
in (
# 2390 "FStar.TypeChecker.Tc.fst"
let _57_2915 = (tc_tparams env arguments)
in (match (_57_2915) with
| (arguments, env', us) -> begin
(
# 2391 "FStar.TypeChecker.Tc.fst"
let _57_2919 = (tc_trivial_guard env' result)
in (match (_57_2919) with
| (result, _57_2918) -> begin
(
# 2392 "FStar.TypeChecker.Tc.fst"
let _57_2923 = (FStar_Syntax_Util.head_and_args result)
in (match (_57_2923) with
| (head, _57_2922) -> begin
(
# 2393 "FStar.TypeChecker.Tc.fst"
let _57_2928 = (match ((let _146_1474 = (FStar_Syntax_Subst.compress head)
in _146_1474.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _57_2927 -> begin
(let _146_1478 = (let _146_1477 = (let _146_1476 = (let _146_1475 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _146_1475))
in (_146_1476, r))
in FStar_Syntax_Syntax.Error (_146_1477))
in (Prims.raise _146_1478))
end)
in (
# 2396 "FStar.TypeChecker.Tc.fst"
let g = (FStar_List.fold_left2 (fun g _57_2934 u_x -> (match (_57_2934) with
| (x, _57_2933) -> begin
(
# 2397 "FStar.TypeChecker.Tc.fst"
let _57_2936 = ()
in (let _146_1482 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _146_1482)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (
# 2403 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1486 = (let _146_1484 = (FStar_All.pipe_right tps (FStar_List.map (fun _57_2942 -> (match (_57_2942) with
| (x, _57_2941) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _146_1484 arguments))
in (let _146_1485 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _146_1486 _146_1485)))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _57_2945 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 2411 "FStar.TypeChecker.Tc.fst"
let generalize_and_inst_within = (fun env g tcs datas -> (
# 2412 "FStar.TypeChecker.Tc.fst"
let _57_2951 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2413 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_7 -> (match (_57_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2955, _57_2957, tps, k, _57_2961, _57_2963, _57_2965, _57_2967) -> begin
(let _146_1497 = (let _146_1496 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _146_1496))
in (FStar_Syntax_Syntax.null_binder _146_1497))
end
| _57_2971 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2416 "FStar.TypeChecker.Tc.fst"
let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _57_8 -> (match (_57_8) with
| FStar_Syntax_Syntax.Sig_datacon (_57_2975, _57_2977, t, _57_2980, _57_2982, _57_2984, _57_2986, _57_2988) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _57_2992 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2419 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1499 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _146_1499))
in (
# 2420 "FStar.TypeChecker.Tc.fst"
let _57_2995 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1500 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _146_1500))
end else begin
()
end
in (
# 2421 "FStar.TypeChecker.Tc.fst"
let _57_2999 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_57_2999) with
| (uvs, t) -> begin
(
# 2422 "FStar.TypeChecker.Tc.fst"
let _57_3001 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1504 = (let _146_1502 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _146_1502 (FStar_String.concat ", ")))
in (let _146_1503 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _146_1504 _146_1503)))
end else begin
()
end
in (
# 2425 "FStar.TypeChecker.Tc.fst"
let _57_3005 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_57_3005) with
| (uvs, t) -> begin
(
# 2426 "FStar.TypeChecker.Tc.fst"
let _57_3009 = (FStar_Syntax_Util.arrow_formals t)
in (match (_57_3009) with
| (args, _57_3008) -> begin
(
# 2427 "FStar.TypeChecker.Tc.fst"
let _57_3012 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_57_3012) with
| (tc_types, data_types) -> begin
(
# 2428 "FStar.TypeChecker.Tc.fst"
let tcs = (FStar_List.map2 (fun _57_3016 se -> (match (_57_3016) with
| (x, _57_3015) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3020, tps, _57_3023, mutuals, datas, quals, r) -> begin
(
# 2430 "FStar.TypeChecker.Tc.fst"
let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (
# 2431 "FStar.TypeChecker.Tc.fst"
let _57_3046 = (match ((let _146_1507 = (FStar_Syntax_Subst.compress ty)
in _146_1507.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 2433 "FStar.TypeChecker.Tc.fst"
let _57_3037 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_57_3037) with
| (tps, rest) -> begin
(
# 2434 "FStar.TypeChecker.Tc.fst"
let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _57_3040 -> begin
(let _146_1508 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _146_1508 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _57_3043 -> begin
([], ty)
end)
in (match (_57_3046) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _57_3048 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (
# 2444 "FStar.TypeChecker.Tc.fst"
let datas = (match (uvs) with
| [] -> begin
datas
end
| _57_3052 -> begin
(
# 2447 "FStar.TypeChecker.Tc.fst"
let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _146_1509 -> FStar_Syntax_Syntax.U_name (_146_1509))))
in (
# 2448 "FStar.TypeChecker.Tc.fst"
let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_9 -> (match (_57_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3057, _57_3059, _57_3061, _57_3063, _57_3065, _57_3067, _57_3069) -> begin
(tc, uvs_universes)
end
| _57_3073 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _57_3078 d -> (match (_57_3078) with
| (t, _57_3077) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _57_3082, _57_3084, tc, ntps, quals, mutuals, r) -> begin
(
# 2452 "FStar.TypeChecker.Tc.fst"
let ty = (let _146_1513 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _146_1513 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _57_3094 -> begin
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
# 2458 "FStar.TypeChecker.Tc.fst"
let _57_3104 = (FStar_All.pipe_right ses (FStar_List.partition (fun _57_10 -> (match (_57_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_3098) -> begin
true
end
| _57_3101 -> begin
false
end))))
in (match (_57_3104) with
| (tys, datas) -> begin
(
# 2460 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2463 "FStar.TypeChecker.Tc.fst"
let _57_3121 = (FStar_List.fold_right (fun tc _57_3110 -> (match (_57_3110) with
| (env, all_tcs, g) -> begin
(
# 2464 "FStar.TypeChecker.Tc.fst"
let _57_3114 = (tc_tycon env tc)
in (match (_57_3114) with
| (env, tc, tc_u) -> begin
(
# 2465 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (
# 2466 "FStar.TypeChecker.Tc.fst"
let _57_3116 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1517 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _146_1517))
end else begin
()
end
in (let _146_1518 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _146_1518))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_3121) with
| (env, tcs, g) -> begin
(
# 2473 "FStar.TypeChecker.Tc.fst"
let _57_3131 = (FStar_List.fold_right (fun se _57_3125 -> (match (_57_3125) with
| (datas, g) -> begin
(
# 2474 "FStar.TypeChecker.Tc.fst"
let _57_3128 = (tc_data env tcs se)
in (match (_57_3128) with
| (data, g') -> begin
(let _146_1521 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _146_1521))
end))
end)) datas ([], g))
in (match (_57_3131) with
| (datas, g) -> begin
(
# 2479 "FStar.TypeChecker.Tc.fst"
let _57_3134 = (let _146_1522 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _146_1522 datas))
in (match (_57_3134) with
| (tcs, datas) -> begin
(let _146_1524 = (let _146_1523 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _146_1523))
in FStar_Syntax_Syntax.Sig_bundle (_146_1524))
end))
end))
end)))
end)))))))))

# 2482 "FStar.TypeChecker.Tc.fst"
let rec tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.env) = (fun env se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(
# 2495 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2496 "FStar.TypeChecker.Tc.fst"
let se = (tc_lex_t env ses quals lids)
in (let _146_1529 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _146_1529))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(
# 2500 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2501 "FStar.TypeChecker.Tc.fst"
let se = (tc_inductive env ses quals lids)
in (let _146_1530 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _146_1530))))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(
# 2505 "FStar.TypeChecker.Tc.fst"
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
# 2511 "FStar.TypeChecker.Tc.fst"
let _57_3172 = (set_options FStar_Options.Set o)
in (se, env))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(
# 2514 "FStar.TypeChecker.Tc.fst"
let _57_3176 = (let _146_1535 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _146_1535 Prims.ignore))
in (
# 2515 "FStar.TypeChecker.Tc.fst"
let _57_3181 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (
# 2518 "FStar.TypeChecker.Tc.fst"
let _57_3183 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (se, env))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(
# 2523 "FStar.TypeChecker.Tc.fst"
let ne = (tc_eff_decl env ne ForFree)
in (
# 2525 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (
# 2526 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(
# 2530 "FStar.TypeChecker.Tc.fst"
let ne = (tc_eff_decl env ne NotForFree)
in (
# 2531 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (
# 2532 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(
# 2536 "FStar.TypeChecker.Tc.fst"
let _57_3205 = (let _146_1536 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _146_1536))
in (match (_57_3205) with
| (a, wp_a_src) -> begin
(
# 2537 "FStar.TypeChecker.Tc.fst"
let _57_3208 = (let _146_1537 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _146_1537))
in (match (_57_3208) with
| (b, wp_b_tgt) -> begin
(
# 2538 "FStar.TypeChecker.Tc.fst"
let wp_a_tgt = (let _146_1541 = (let _146_1540 = (let _146_1539 = (let _146_1538 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _146_1538))
in FStar_Syntax_Syntax.NT (_146_1539))
in (_146_1540)::[])
in (FStar_Syntax_Subst.subst _146_1541 wp_b_tgt))
in (
# 2539 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1546 = (let _146_1544 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1543 = (let _146_1542 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_146_1542)::[])
in (_146_1544)::_146_1543))
in (let _146_1545 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _146_1546 _146_1545)))
in (
# 2540 "FStar.TypeChecker.Tc.fst"
let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (
# 2541 "FStar.TypeChecker.Tc.fst"
let sub = (
# 2541 "FStar.TypeChecker.Tc.fst"
let _57_3212 = sub
in {FStar_Syntax_Syntax.source = _57_3212.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _57_3212.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
in (
# 2542 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect ((sub, r))
in (
# 2543 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(
# 2547 "FStar.TypeChecker.Tc.fst"
let _57_3225 = ()
in (
# 2548 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2549 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2550 "FStar.TypeChecker.Tc.fst"
let _57_3231 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_57_3231) with
| (tps, c) -> begin
(
# 2551 "FStar.TypeChecker.Tc.fst"
let _57_3235 = (tc_tparams env tps)
in (match (_57_3235) with
| (tps, env, us) -> begin
(
# 2552 "FStar.TypeChecker.Tc.fst"
let _57_3239 = (tc_comp env c)
in (match (_57_3239) with
| (c, u, g) -> begin
(
# 2553 "FStar.TypeChecker.Tc.fst"
let _57_3240 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2554 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 2555 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.close_comp tps c)
in (
# 2556 "FStar.TypeChecker.Tc.fst"
let _57_3246 = (let _146_1547 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _146_1547))
in (match (_57_3246) with
| (uvs, t) -> begin
(
# 2557 "FStar.TypeChecker.Tc.fst"
let _57_3265 = (match ((let _146_1549 = (let _146_1548 = (FStar_Syntax_Subst.compress t)
in _146_1548.FStar_Syntax_Syntax.n)
in (tps, _146_1549))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_57_3249, c)) -> begin
([], c)
end
| (_57_3255, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _57_3262 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_3265) with
| (tps, c) -> begin
(
# 2561 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_effect_abbrev ((lid, uvs, tps, c, tags, r))
in (
# 2562 "FStar.TypeChecker.Tc.fst"
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
# 2566 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2567 "FStar.TypeChecker.Tc.fst"
let _57_3276 = ()
in (
# 2568 "FStar.TypeChecker.Tc.fst"
let _57_3280 = (let _146_1551 = (let _146_1550 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _146_1550))
in (check_and_gen env t _146_1551))
in (match (_57_3280) with
| (uvs, t) -> begin
(
# 2569 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (
# 2570 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(
# 2574 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2575 "FStar.TypeChecker.Tc.fst"
let _57_3293 = (FStar_Syntax_Util.type_u ())
in (match (_57_3293) with
| (k, _57_3292) -> begin
(
# 2576 "FStar.TypeChecker.Tc.fst"
let phi = (let _146_1552 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _146_1552 (norm env)))
in (
# 2577 "FStar.TypeChecker.Tc.fst"
let _57_3295 = (FStar_TypeChecker_Util.check_uvars r phi)
in (
# 2578 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))
in (
# 2579 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(
# 2583 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2584 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (
# 2585 "FStar.TypeChecker.Tc.fst"
let _57_3308 = (tc_term env e)
in (match (_57_3308) with
| (e, c, g1) -> begin
(
# 2586 "FStar.TypeChecker.Tc.fst"
let _57_3313 = (let _146_1556 = (let _146_1553 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_146_1553))
in (let _146_1555 = (let _146_1554 = (c.FStar_Syntax_Syntax.comp ())
in (e, _146_1554))
in (check_expected_effect env _146_1556 _146_1555)))
in (match (_57_3313) with
| (e, _57_3311, g) -> begin
(
# 2587 "FStar.TypeChecker.Tc.fst"
let _57_3314 = (let _146_1557 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _146_1557))
in (
# 2588 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, r))
in (
# 2589 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(
# 2593 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2594 "FStar.TypeChecker.Tc.fst"
let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
if (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q')) then begin
Some (q)
end else begin
(let _146_1569 = (let _146_1568 = (let _146_1567 = (let _146_1566 = (FStar_Syntax_Print.lid_to_string l)
in (let _146_1565 = (FStar_Syntax_Print.quals_to_string q)
in (let _146_1564 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _146_1566 _146_1565 _146_1564))))
in (_146_1567, r))
in FStar_Syntax_Syntax.Error (_146_1568))
in (Prims.raise _146_1569))
end
end))
in (
# 2608 "FStar.TypeChecker.Tc.fst"
let _57_3358 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _57_3335 lb -> (match (_57_3335) with
| (gen, lbs, quals_opt) -> begin
(
# 2609 "FStar.TypeChecker.Tc.fst"
let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2610 "FStar.TypeChecker.Tc.fst"
let _57_3354 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(
# 2614 "FStar.TypeChecker.Tc.fst"
let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (
# 2615 "FStar.TypeChecker.Tc.fst"
let _57_3349 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _57_3348 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _146_1572 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _146_1572, quals_opt))))
end)
in (match (_57_3354) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_57_3358) with
| (should_generalize, lbs', quals_opt) -> begin
(
# 2624 "FStar.TypeChecker.Tc.fst"
let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _57_11 -> (match (_57_11) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _57_3367 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (
# 2631 "FStar.TypeChecker.Tc.fst"
let lbs' = (FStar_List.rev lbs')
in (
# 2634 "FStar.TypeChecker.Tc.fst"
let e = (let _146_1576 = (let _146_1575 = (let _146_1574 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _146_1574))
in FStar_Syntax_Syntax.Tm_let (_146_1575))
in (FStar_Syntax_Syntax.mk _146_1576 None r))
in (
# 2637 "FStar.TypeChecker.Tc.fst"
let _57_3401 = (match ((tc_maybe_toplevel_term (
# 2637 "FStar.TypeChecker.Tc.fst"
let _57_3371 = env
in {FStar_TypeChecker_Env.solver = _57_3371.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3371.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3371.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3371.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3371.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3371.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3371.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3371.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3371.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3371.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3371.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _57_3371.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _57_3371.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3371.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3371.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3371.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3371.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3371.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3371.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _57_3378; FStar_Syntax_Syntax.pos = _57_3376; FStar_Syntax_Syntax.vars = _57_3374}, _57_3385, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(
# 2640 "FStar.TypeChecker.Tc.fst"
let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_57_3389, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _57_3395 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _57_3398 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_57_3401) with
| (se, lbs) -> begin
(
# 2647 "FStar.TypeChecker.Tc.fst"
let _57_3407 = if (log env) then begin
(let _146_1584 = (let _146_1583 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 2649 "FStar.TypeChecker.Tc.fst"
let should_log = (match ((let _146_1580 = (let _146_1579 = (let _146_1578 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _146_1578.FStar_Syntax_Syntax.fv_name)
in _146_1579.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _146_1580))) with
| None -> begin
true
end
| _57_3405 -> begin
false
end)
in if should_log then begin
(let _146_1582 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _146_1581 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _146_1582 _146_1581)))
end else begin
""
end))))
in (FStar_All.pipe_right _146_1583 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _146_1584))
end else begin
()
end
in (
# 2656 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end))))
end))

# 2660 "FStar.TypeChecker.Tc.fst"
let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (
# 2684 "FStar.TypeChecker.Tc.fst"
let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _57_12 -> (match (_57_12) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _57_3417 -> begin
false
end)))))
in (
# 2685 "FStar.TypeChecker.Tc.fst"
let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _57_3427 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_57_3429) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _57_3440, _57_3442) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _57_3448 -> (match (_57_3448) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _57_3454, _57_3456, quals, r) -> begin
(
# 2699 "FStar.TypeChecker.Tc.fst"
let dec = (let _146_1600 = (let _146_1599 = (let _146_1598 = (let _146_1597 = (let _146_1596 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _146_1596))
in FStar_Syntax_Syntax.Tm_arrow (_146_1597))
in (FStar_Syntax_Syntax.mk _146_1598 None r))
in (l, us, _146_1599, (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_146_1600))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _57_3466, _57_3468, _57_3470, _57_3472, r) -> begin
(
# 2702 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _57_3478 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_57_3480, _57_3482, quals, _57_3485) -> begin
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
| _57_3504 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_57_3506) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _57_3525, _57_3527, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(
# 2733 "FStar.TypeChecker.Tc.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2734 "FStar.TypeChecker.Tc.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))) then begin
([], hidden)
end else begin
(
# 2737 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::[], (FStar_Ident.range_of_lid lid)))
in ((dec)::[], (lid)::hidden))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (is_abstract quals) then begin
(let _146_1607 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _146_1606 = (let _146_1605 = (let _146_1604 = (let _146_1603 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _146_1603.FStar_Syntax_Syntax.fv_name)
in _146_1604.FStar_Syntax_Syntax.v)
in (_146_1605, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_146_1606)))))
in (_146_1607, hidden))
end else begin
((se)::[], hidden)
end
end))))

# 2746 "FStar.TypeChecker.Tc.fst"
let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (
# 2747 "FStar.TypeChecker.Tc.fst"
let _57_3566 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _57_3547 se -> (match (_57_3547) with
| (ses, exports, env, hidden) -> begin
(
# 2749 "FStar.TypeChecker.Tc.fst"
let _57_3549 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1614 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _146_1614))
end else begin
()
end
in (
# 2752 "FStar.TypeChecker.Tc.fst"
let _57_3553 = (tc_decl env se)
in (match (_57_3553) with
| (se, env) -> begin
(
# 2754 "FStar.TypeChecker.Tc.fst"
let _57_3554 = if ((FStar_ST.read FStar_Options.log_types) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _146_1615 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _146_1615))
end else begin
()
end
in (
# 2757 "FStar.TypeChecker.Tc.fst"
let _57_3556 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (
# 2759 "FStar.TypeChecker.Tc.fst"
let _57_3560 = (for_export hidden se)
in (match (_57_3560) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_57_3566) with
| (ses, exports, env, _57_3565) -> begin
(let _146_1616 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _146_1616, env))
end)))

# 2764 "FStar.TypeChecker.Tc.fst"
let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2765 "FStar.TypeChecker.Tc.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 2766 "FStar.TypeChecker.Tc.fst"
let msg = (Prims.strcat "Internals for " name)
in (
# 2767 "FStar.TypeChecker.Tc.fst"
let env = (
# 2767 "FStar.TypeChecker.Tc.fst"
let _57_3571 = env
in (let _146_1621 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _57_3571.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3571.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3571.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3571.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3571.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3571.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3571.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3571.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3571.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3571.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3571.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3571.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3571.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_3571.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_3571.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3571.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _146_1621; FStar_TypeChecker_Env.type_of = _57_3571.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3571.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3571.FStar_TypeChecker_Env.use_bv_sorts}))
in (
# 2768 "FStar.TypeChecker.Tc.fst"
let _57_3574 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (
# 2769 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (
# 2770 "FStar.TypeChecker.Tc.fst"
let _57_3580 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_57_3580) with
| (ses, exports, env) -> begin
((
# 2771 "FStar.TypeChecker.Tc.fst"
let _57_3581 = modul
in {FStar_Syntax_Syntax.name = _57_3581.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _57_3581.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3581.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))

# 2773 "FStar.TypeChecker.Tc.fst"
let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (
# 2774 "FStar.TypeChecker.Tc.fst"
let _57_3589 = (tc_decls env decls)
in (match (_57_3589) with
| (ses, exports, env) -> begin
(
# 2775 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2775 "FStar.TypeChecker.Tc.fst"
let _57_3590 = modul
in {FStar_Syntax_Syntax.name = _57_3590.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _57_3590.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3590.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))

# 2778 "FStar.TypeChecker.Tc.fst"
let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (
# 2779 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2779 "FStar.TypeChecker.Tc.fst"
let _57_3596 = modul
in {FStar_Syntax_Syntax.name = _57_3596.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _57_3596.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (
# 2780 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.finish_module env modul)
in (
# 2781 "FStar.TypeChecker.Tc.fst"
let _57_3606 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(
# 2783 "FStar.TypeChecker.Tc.fst"
let _57_3600 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (
# 2784 "FStar.TypeChecker.Tc.fst"
let _57_3602 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (
# 2785 "FStar.TypeChecker.Tc.fst"
let _57_3604 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _146_1634 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _146_1634 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))

# 2790 "FStar.TypeChecker.Tc.fst"
let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2791 "FStar.TypeChecker.Tc.fst"
let _57_3613 = (tc_partial_modul env modul)
in (match (_57_3613) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

# 2794 "FStar.TypeChecker.Tc.fst"
let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 2795 "FStar.TypeChecker.Tc.fst"
let _57_3616 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _146_1643 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _146_1643))
end else begin
()
end
in (
# 2797 "FStar.TypeChecker.Tc.fst"
let env = (
# 2797 "FStar.TypeChecker.Tc.fst"
let _57_3618 = env
in {FStar_TypeChecker_Env.solver = _57_3618.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3618.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3618.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3618.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3618.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3618.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3618.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3618.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3618.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3618.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3618.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3618.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3618.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_3618.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3618.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3618.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3618.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3618.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3618.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3618.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 2798 "FStar.TypeChecker.Tc.fst"
let _57_3634 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _57_3626) -> begin
(let _146_1648 = (let _146_1647 = (let _146_1646 = (FStar_TypeChecker_Env.get_range env)
in ((Prims.strcat "Implicit argument: " msg), _146_1646))
in FStar_Syntax_Syntax.Error (_146_1647))
in (Prims.raise _146_1648))
end
in (match (_57_3634) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(t, c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(let _146_1653 = (let _146_1652 = (let _146_1651 = (let _146_1649 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _146_1649))
in (let _146_1650 = (FStar_TypeChecker_Env.get_range env)
in (_146_1651, _146_1650)))
in FStar_Syntax_Syntax.Error (_146_1652))
in (Prims.raise _146_1653))
end
end)))))

# 2805 "FStar.TypeChecker.Tc.fst"
let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (
# 2806 "FStar.TypeChecker.Tc.fst"
let _57_3637 = if ((let _146_1658 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _146_1658)) <> 0) then begin
(let _146_1659 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _146_1659))
end else begin
()
end
in (
# 2808 "FStar.TypeChecker.Tc.fst"
let _57_3641 = (tc_modul env m)
in (match (_57_3641) with
| (m, env) -> begin
(
# 2809 "FStar.TypeChecker.Tc.fst"
let _57_3642 = if (FStar_Options.should_dump m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _146_1660 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _146_1660))
end else begin
()
end
in (m, env))
end))))




