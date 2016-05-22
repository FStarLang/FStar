
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
(FStar_Syntax_Syntax.Name2Term ((x, e)))::[]
end
| _57_75 -> begin
[]
end))

# 96 "FStar.TypeChecker.Tc.fst"
let maybe_extend_subst : FStar_Syntax_Syntax.instantiation  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.instantiation = (fun s b v -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
s
end else begin
(FStar_Syntax_Syntax.Name2Term (((Prims.fst b), v)))::s
end)

# 100 "FStar.TypeChecker.Tc.fst"
let maybe_extend_renaming : FStar_Syntax_Subst.renaming  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Subst.renaming = (fun s b n -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
s
end else begin
(FStar_Syntax_Syntax.Name2Name (((Prims.fst b), n)))::s
end)

# 104 "FStar.TypeChecker.Tc.fst"
let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (
# 105 "FStar.TypeChecker.Tc.fst"
let _57_84 = lc
in {FStar_Syntax_Syntax.eff_name = _57_84.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _57_84.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _57_86 -> (match (()) with
| () -> begin
(let _146_86 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _146_86 t))
end))}))

# 107 "FStar.TypeChecker.Tc.fst"
let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (
# 108 "FStar.TypeChecker.Tc.fst"
let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _146_95 = if (not ((FStar_Syntax_Util.is_pure_or_ghost_function t))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _146_95))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (
# 113 "FStar.TypeChecker.Tc.fst"
let t = lc.FStar_Syntax_Syntax.res_typ
in (
# 114 "FStar.TypeChecker.Tc.fst"
let _57_118 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, guard)
end
| Some (t') -> begin
(
# 117 "FStar.TypeChecker.Tc.fst"
let _57_100 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_97 = (FStar_Syntax_Print.term_to_string t)
in (let _146_96 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _146_97 _146_96)))
end else begin
()
end
in (
# 119 "FStar.TypeChecker.Tc.fst"
let _57_104 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_57_104) with
| (e, lc) -> begin
(
# 120 "FStar.TypeChecker.Tc.fst"
let t = lc.FStar_Syntax_Syntax.res_typ
in (
# 121 "FStar.TypeChecker.Tc.fst"
let _57_108 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_57_108) with
| (e, g) -> begin
(
# 122 "FStar.TypeChecker.Tc.fst"
let _57_109 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_99 = (FStar_Syntax_Print.term_to_string t)
in (let _146_98 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _146_99 _146_98)))
end else begin
()
end
in (
# 124 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (
# 125 "FStar.TypeChecker.Tc.fst"
let _57_114 = (let _146_105 = (FStar_All.pipe_left (fun _146_104 -> Some (_146_104)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _146_105 env e lc g))
in (match (_57_114) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))))
end)))
end)))
end)
in (match (_57_118) with
| (e, lc, g) -> begin
(
# 127 "FStar.TypeChecker.Tc.fst"
let _57_119 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_106 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _146_106))
end else begin
()
end
in (e, lc, g))
end)))))

# 131 "FStar.TypeChecker.Tc.fst"
let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (t) -> begin
(
# 135 "FStar.TypeChecker.Tc.fst"
let _57_129 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_57_129) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))

# 138 "FStar.TypeChecker.Tc.fst"
let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _57_134 -> (match (_57_134) with
| (e, c) -> begin
(
# 139 "FStar.TypeChecker.Tc.fst"
let expected_c_opt = (match (copt) with
| Some (_57_136) -> begin
copt
end
| None -> begin
if ((FStar_ST.read FStar_Options.ml_ish) && (FStar_Ident.lid_equals FStar_Syntax_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) then begin
(let _146_119 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (_146_119))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
if (FStar_Syntax_Util.is_pure_comp c) then begin
(let _146_120 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (_146_120))
end else begin
if (FStar_Syntax_Util.is_pure_or_ghost_comp c) then begin
(let _146_121 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (_146_121))
end else begin
None
end
end
end
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _146_122 = (norm_c env c)
in (e, _146_122, FStar_TypeChecker_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(
# 155 "FStar.TypeChecker.Tc.fst"
let _57_143 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_125 = (FStar_Syntax_Print.term_to_string e)
in (let _146_124 = (FStar_Syntax_Print.comp_to_string c)
in (let _146_123 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _146_125 _146_124 _146_123))))
end else begin
()
end
in (
# 158 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 159 "FStar.TypeChecker.Tc.fst"
let _57_146 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_128 = (FStar_Syntax_Print.term_to_string e)
in (let _146_127 = (FStar_Syntax_Print.comp_to_string c)
in (let _146_126 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _146_128 _146_127 _146_126))))
end else begin
()
end
in (
# 164 "FStar.TypeChecker.Tc.fst"
let _57_152 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_57_152) with
| (e, _57_150, g) -> begin
(
# 165 "FStar.TypeChecker.Tc.fst"
let g = (let _146_129 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _146_129 "could not prove post-condition" g))
in (
# 166 "FStar.TypeChecker.Tc.fst"
let _57_154 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_131 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _146_130 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _146_131 _146_130)))
end else begin
()
end
in (e, expected_c, g)))
end)))))
end))
end))

# 169 "FStar.TypeChecker.Tc.fst"
let no_logical_guard = (fun env _57_160 -> (match (_57_160) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
(te, kt, f)
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _146_137 = (let _146_136 = (let _146_135 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _146_134 = (FStar_TypeChecker_Env.get_range env)
in (_146_135, _146_134)))
in FStar_Syntax_Syntax.Error (_146_136))
in (Prims.raise _146_137))
end)
end))

# 174 "FStar.TypeChecker.Tc.fst"
let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _146_140 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _146_140))
end))

# 181 "FStar.TypeChecker.Tc.fst"
let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _57_184; FStar_Syntax_Syntax.result_typ = _57_182; FStar_Syntax_Syntax.effect_args = _pre::_post::(pats, _57_176)::[]; FStar_Syntax_Syntax.flags = _57_173}) -> begin
(
# 185 "FStar.TypeChecker.Tc.fst"
let pat_vars = (FStar_Syntax_Free.names pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _57_191 -> (match (_57_191) with
| (b, _57_190) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _57_195) -> begin
(let _146_147 = (let _146_146 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _146_146))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _146_147))
end))
end
| _57_199 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end)

# 196 "FStar.TypeChecker.Tc.fst"
let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun env actuals expected_c -> (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(
# 200 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 201 "FStar.TypeChecker.Tc.fst"
let env = (
# 201 "FStar.TypeChecker.Tc.fst"
let _57_206 = env
in {FStar_TypeChecker_Env.solver = _57_206.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_206.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_206.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_206.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_206.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_206.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_206.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_206.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_206.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_206.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_206.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_206.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_206.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_206.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_206.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_206.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_206.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_206.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_206.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_206.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 202 "FStar.TypeChecker.Tc.fst"
let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (
# 204 "FStar.TypeChecker.Tc.fst"
let decreases_clause = (fun bs c -> (
# 206 "FStar.TypeChecker.Tc.fst"
let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _57_218 -> (match (_57_218) with
| (b, _57_217) -> begin
(
# 208 "FStar.TypeChecker.Tc.fst"
let t = (let _146_161 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _146_161))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _57_227 -> begin
(let _146_162 = (FStar_Syntax_Syntax.bv_to_name b)
in (_146_162)::[])
end))
end)))))
in (
# 213 "FStar.TypeChecker.Tc.fst"
let as_lex_list = (fun dec -> (
# 214 "FStar.TypeChecker.Tc.fst"
let _57_233 = (FStar_Syntax_Util.head_and_args dec)
in (match (_57_233) with
| (head, _57_232) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _57_237 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (
# 218 "FStar.TypeChecker.Tc.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _57_3 -> (match (_57_3) with
| FStar_Syntax_Syntax.DECREASES (_57_241) -> begin
true
end
| _57_244 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _57_249 -> begin
(
# 222 "FStar.TypeChecker.Tc.fst"
let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| x::[] -> begin
x
end
| _57_254 -> begin
(mk_lex_list xs)
end))
end)))))
in (
# 227 "FStar.TypeChecker.Tc.fst"
let previous_dec = (decreases_clause actuals expected_c)
in (
# 228 "FStar.TypeChecker.Tc.fst"
let guard_one_letrec = (fun _57_259 -> (match (_57_259) with
| (l, t) -> begin
(match ((let _146_168 = (FStar_Syntax_Subst.compress t)
in _146_168.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 232 "FStar.TypeChecker.Tc.fst"
let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _57_266 -> (match (_57_266) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _146_172 = (let _146_171 = (let _146_170 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_146_170))
in (FStar_Syntax_Syntax.new_bv _146_171 x.FStar_Syntax_Syntax.sort))
in (_146_172, imp))
end else begin
(x, imp)
end
end))))
in (
# 233 "FStar.TypeChecker.Tc.fst"
let _57_270 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_57_270) with
| (formals, c) -> begin
(
# 234 "FStar.TypeChecker.Tc.fst"
let dec = (decreases_clause formals c)
in (
# 235 "FStar.TypeChecker.Tc.fst"
let precedes = (let _146_176 = (let _146_175 = (FStar_Syntax_Syntax.as_arg dec)
in (let _146_174 = (let _146_173 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_146_173)::[])
in (_146_175)::_146_174))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _146_176 None r))
in (
# 236 "FStar.TypeChecker.Tc.fst"
let _57_277 = (FStar_Util.prefix formals)
in (match (_57_277) with
| (bs, (last, imp)) -> begin
(
# 237 "FStar.TypeChecker.Tc.fst"
let last = (
# 237 "FStar.TypeChecker.Tc.fst"
let _57_278 = last
in (let _146_177 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _57_278.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_278.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_177}))
in (
# 238 "FStar.TypeChecker.Tc.fst"
let refined_formals = (FStar_List.append bs (((last, imp))::[]))
in (
# 239 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (
# 240 "FStar.TypeChecker.Tc.fst"
let _57_283 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_180 = (FStar_Syntax_Print.lbname_to_string l)
in (let _146_179 = (FStar_Syntax_Print.term_to_string t)
in (let _146_178 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _146_180 _146_179 _146_178))))
end else begin
()
end
in (l, t')))))
end))))
end)))
end
| _57_286 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end))

# 252 "FStar.TypeChecker.Tc.fst"
let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (
# 252 "FStar.TypeChecker.Tc.fst"
let _57_289 = env
in {FStar_TypeChecker_Env.solver = _57_289.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_289.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_289.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_289.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_289.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_289.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_289.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_289.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_289.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_289.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_289.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_289.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_289.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_289.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_289.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_289.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_289.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_289.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_289.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_289.FStar_TypeChecker_Env.use_bv_sorts}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 257 "FStar.TypeChecker.Tc.fst"
let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (
# 258 "FStar.TypeChecker.Tc.fst"
let _57_294 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_249 = (let _146_247 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _146_247))
in (let _146_248 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _146_249 _146_248)))
end else begin
()
end
in (
# 259 "FStar.TypeChecker.Tc.fst"
let top = e
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_57_298) -> begin
(let _146_253 = (FStar_Syntax_Subst.compress e)
in (tc_term env _146_253))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(
# 276 "FStar.TypeChecker.Tc.fst"
let _57_339 = (tc_tot_or_gtot_term env e)
in (match (_57_339) with
| (e, c, g) -> begin
(
# 277 "FStar.TypeChecker.Tc.fst"
let g = (
# 277 "FStar.TypeChecker.Tc.fst"
let _57_340 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_340.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_340.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_340.FStar_TypeChecker_Env.implicits})
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(
# 281 "FStar.TypeChecker.Tc.fst"
let _57_350 = (FStar_Syntax_Util.type_u ())
in (match (_57_350) with
| (t, u) -> begin
(
# 282 "FStar.TypeChecker.Tc.fst"
let _57_354 = (tc_check_tot_or_gtot_term env e t)
in (match (_57_354) with
| (e, c, g) -> begin
(
# 283 "FStar.TypeChecker.Tc.fst"
let _57_361 = (
# 284 "FStar.TypeChecker.Tc.fst"
let _57_358 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_358) with
| (env, _57_357) -> begin
(tc_pats env pats)
end))
in (match (_57_361) with
| (pats, g') -> begin
(
# 286 "FStar.TypeChecker.Tc.fst"
let g' = (
# 286 "FStar.TypeChecker.Tc.fst"
let _57_362 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_362.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_362.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_362.FStar_TypeChecker_Env.implicits})
in (let _146_255 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_pattern (pats)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_254 = (FStar_TypeChecker_Rel.conj_guard g g')
in (_146_255, c, _146_254))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _146_256 = (FStar_Syntax_Subst.compress e)
in _146_256.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_57_371, {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _57_378; FStar_Syntax_Syntax.lbtyp = _57_376; FStar_Syntax_Syntax.lbeff = _57_374; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 294 "FStar.TypeChecker.Tc.fst"
let _57_389 = (let _146_257 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _146_257 e1))
in (match (_57_389) with
| (e1, c1, g1) -> begin
(
# 295 "FStar.TypeChecker.Tc.fst"
let _57_393 = (tc_term env e2)
in (match (_57_393) with
| (e2, c2, g2) -> begin
(
# 296 "FStar.TypeChecker.Tc.fst"
let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (None, c2))
in (
# 297 "FStar.TypeChecker.Tc.fst"
let e = (let _146_262 = (let _146_261 = (let _146_260 = (let _146_259 = (let _146_258 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Common.t_unit, e1))
in (_146_258)::[])
in (false, _146_259))
in (_146_260, e2))
in FStar_Syntax_Syntax.Tm_let (_146_261))
in (FStar_Syntax_Syntax.mk _146_262 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 298 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_263 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _146_263)))))
end))
end))
end
| _57_398 -> begin
(
# 301 "FStar.TypeChecker.Tc.fst"
let _57_402 = (tc_term env e)
in (match (_57_402) with
| (e, c, g) -> begin
(
# 302 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(
# 307 "FStar.TypeChecker.Tc.fst"
let _57_411 = (tc_term env e)
in (match (_57_411) with
| (e, c, g) -> begin
(
# 308 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, m))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _57_417) -> begin
(
# 312 "FStar.TypeChecker.Tc.fst"
let _57_424 = (tc_comp env expected_c)
in (match (_57_424) with
| (expected_c, _57_422, g) -> begin
(
# 313 "FStar.TypeChecker.Tc.fst"
let _57_428 = (tc_term env e)
in (match (_57_428) with
| (e, c', g') -> begin
(
# 314 "FStar.TypeChecker.Tc.fst"
let _57_432 = (let _146_265 = (let _146_264 = (c'.FStar_Syntax_Syntax.comp ())
in (e, _146_264))
in (check_expected_effect env (Some (expected_c)) _146_265))
in (match (_57_432) with
| (e, expected_c, g'') -> begin
(
# 315 "FStar.TypeChecker.Tc.fst"
let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (let _146_268 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t_res), Some ((FStar_Syntax_Util.comp_effect_name expected_c))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_267 = (let _146_266 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _146_266))
in (_146_268, (FStar_Syntax_Util.lcomp_of_comp expected_c), _146_267))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _57_438) -> begin
(
# 321 "FStar.TypeChecker.Tc.fst"
let _57_443 = (FStar_Syntax_Util.type_u ())
in (match (_57_443) with
| (k, u) -> begin
(
# 322 "FStar.TypeChecker.Tc.fst"
let _57_448 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_448) with
| (t, _57_446, f) -> begin
(
# 323 "FStar.TypeChecker.Tc.fst"
let _57_452 = (let _146_269 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _146_269 e))
in (match (_57_452) with
| (e, c, g) -> begin
(
# 324 "FStar.TypeChecker.Tc.fst"
let _57_456 = (let _146_273 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_453 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _146_273 e c f))
in (match (_57_456) with
| (c, f) -> begin
(
# 325 "FStar.TypeChecker.Tc.fst"
let _57_460 = (let _146_274 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t), Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _146_274 c))
in (match (_57_460) with
| (e, c, f2) -> begin
(let _146_276 = (let _146_275 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _146_275))
in (e, c, _146_276))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 329 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 330 "FStar.TypeChecker.Tc.fst"
let env = (let _146_278 = (let _146_277 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_277 Prims.fst))
in (FStar_All.pipe_right _146_278 instantiate_both))
in (
# 331 "FStar.TypeChecker.Tc.fst"
let _57_467 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_280 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _146_279 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _146_280 _146_279)))
end else begin
()
end
in (
# 335 "FStar.TypeChecker.Tc.fst"
let _57_472 = (tc_term (no_inst env) head)
in (match (_57_472) with
| (head, chead, g_head) -> begin
(
# 336 "FStar.TypeChecker.Tc.fst"
let _57_476 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _146_281 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _146_281))
end else begin
(let _146_282 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _146_282))
end
in (match (_57_476) with
| (e, c, g) -> begin
(
# 339 "FStar.TypeChecker.Tc.fst"
let _57_477 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_283 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _146_283))
end else begin
()
end
in (
# 341 "FStar.TypeChecker.Tc.fst"
let c = if (((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) && (not ((FStar_Syntax_Util.is_lcomp_partial_return c)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)) then begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e c)
end else begin
c
end
in (
# 346 "FStar.TypeChecker.Tc.fst"
let _57_483 = (comp_check_expected_typ env0 e c)
in (match (_57_483) with
| (e, c, g') -> begin
(
# 347 "FStar.TypeChecker.Tc.fst"
let gimp = (match ((let _146_284 = (FStar_Syntax_Subst.compress head)
in _146_284.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _57_486) -> begin
(
# 350 "FStar.TypeChecker.Tc.fst"
let imp = ("head of application is a uvar", env0, u, e, c.FStar_Syntax_Syntax.res_typ, head.FStar_Syntax_Syntax.pos)
in (
# 351 "FStar.TypeChecker.Tc.fst"
let _57_490 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_490.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_490.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_490.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _57_493 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (
# 353 "FStar.TypeChecker.Tc.fst"
let gres = (let _146_285 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _146_285))
in (
# 354 "FStar.TypeChecker.Tc.fst"
let _57_496 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_286 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print1 "Guard from application node is %s\n" _146_286))
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
# 359 "FStar.TypeChecker.Tc.fst"
let _57_504 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_504) with
| (env1, topt) -> begin
(
# 360 "FStar.TypeChecker.Tc.fst"
let env1 = (instantiate_both env1)
in (
# 361 "FStar.TypeChecker.Tc.fst"
let _57_509 = (tc_term env1 e1)
in (match (_57_509) with
| (e1, c1, g1) -> begin
(
# 362 "FStar.TypeChecker.Tc.fst"
let _57_520 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(
# 365 "FStar.TypeChecker.Tc.fst"
let _57_516 = (FStar_Syntax_Util.type_u ())
in (match (_57_516) with
| (k, _57_515) -> begin
(
# 366 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _146_287 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_146_287, res_t)))
end))
end)
in (match (_57_520) with
| (env_branches, res_t) -> begin
(
# 369 "FStar.TypeChecker.Tc.fst"
let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (
# 370 "FStar.TypeChecker.Tc.fst"
let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (
# 371 "FStar.TypeChecker.Tc.fst"
let _57_537 = (
# 372 "FStar.TypeChecker.Tc.fst"
let _57_534 = (FStar_List.fold_right (fun _57_528 _57_531 -> (match ((_57_528, _57_531)) with
| ((_57_524, f, c, g), (caccum, gaccum)) -> begin
(let _146_290 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _146_290))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_534) with
| (cases, g) -> begin
(let _146_291 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_146_291, g))
end))
in (match (_57_537) with
| (c_branches, g_branches) -> begin
(
# 376 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (Some (guard_x), c_branches))
in (
# 377 "FStar.TypeChecker.Tc.fst"
let e = (let _146_295 = (let _146_294 = (let _146_293 = (FStar_List.map (fun _57_546 -> (match (_57_546) with
| (f, _57_541, _57_543, _57_545) -> begin
f
end)) t_eqns)
in (e1, _146_293))
in FStar_Syntax_Syntax.Tm_match (_146_294))
in (FStar_Syntax_Syntax.mk _146_295 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (
# 379 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ), Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (
# 380 "FStar.TypeChecker.Tc.fst"
let _57_549 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_298 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _146_297 = (let _146_296 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _146_296))
in (FStar_Util.print2 "(%s) comp type = %s\n" _146_298 _146_297)))
end else begin
()
end
in (let _146_299 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _146_299))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_561); FStar_Syntax_Syntax.lbunivs = _57_559; FStar_Syntax_Syntax.lbtyp = _57_557; FStar_Syntax_Syntax.lbeff = _57_555; FStar_Syntax_Syntax.lbdef = _57_553}::[]), _57_567) -> begin
(
# 387 "FStar.TypeChecker.Tc.fst"
let _57_570 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_300 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _146_300))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _57_574), _57_577) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_592); FStar_Syntax_Syntax.lbunivs = _57_590; FStar_Syntax_Syntax.lbtyp = _57_588; FStar_Syntax_Syntax.lbeff = _57_586; FStar_Syntax_Syntax.lbdef = _57_584}::_57_582), _57_598) -> begin
(
# 394 "FStar.TypeChecker.Tc.fst"
let _57_601 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_301 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _146_301))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _57_605), _57_608) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 407 "FStar.TypeChecker.Tc.fst"
let check_instantiated_fvar = (fun env v dc e t -> (
# 408 "FStar.TypeChecker.Tc.fst"
let _57_622 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_622) with
| (e, t, implicits) -> begin
(
# 410 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _146_315 = (let _146_314 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_314))
in FStar_Util.Inr (_146_315))
end
in (
# 411 "FStar.TypeChecker.Tc.fst"
let is_data_ctor = (fun _57_4 -> (match (_57_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _57_632 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _146_321 = (let _146_320 = (let _146_319 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _146_318 = (FStar_TypeChecker_Env.get_range env)
in (_146_319, _146_318)))
in FStar_Syntax_Syntax.Error (_146_320))
in (Prims.raise _146_321))
end else begin
(value_check_expected_typ env e tc implicits)
end))
end)))
in (
# 421 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (
# 422 "FStar.TypeChecker.Tc.fst"
let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(FStar_All.failwith "Impossible: Violation of locally nameless convention")
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(
# 428 "FStar.TypeChecker.Tc.fst"
let g = (match ((let _146_322 = (FStar_Syntax_Subst.compress t1)
in _146_322.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_643) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _57_646 -> begin
(
# 430 "FStar.TypeChecker.Tc.fst"
let imp = ("uvar in term", env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (
# 431 "FStar.TypeChecker.Tc.fst"
let _57_648 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_648.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_648.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_648.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 436 "FStar.TypeChecker.Tc.fst"
let _57_654 = (FStar_Syntax_Util.type_u ())
in (match (_57_654) with
| (k, u) -> begin
(
# 437 "FStar.TypeChecker.Tc.fst"
let t = (FStar_TypeChecker_Util.new_uvar env k)
in (
# 438 "FStar.TypeChecker.Tc.fst"
let e = (FStar_TypeChecker_Util.new_uvar env t)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 442 "FStar.TypeChecker.Tc.fst"
let t = if env.FStar_TypeChecker_Env.use_bv_sorts then begin
x.FStar_Syntax_Syntax.sort
end else begin
(FStar_TypeChecker_Env.lookup_bv env x)
end
in (
# 443 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.bv_to_name (
# 443 "FStar.TypeChecker.Tc.fst"
let _57_660 = x
in {FStar_Syntax_Syntax.ppname = _57_660.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_660.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (
# 444 "FStar.TypeChecker.Tc.fst"
let _57_666 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_666) with
| (e, t, implicits) -> begin
(
# 445 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _146_324 = (let _146_323 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_323))
in FStar_Util.Inr (_146_324))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _57_673; FStar_Syntax_Syntax.pos = _57_671; FStar_Syntax_Syntax.vars = _57_669}, us) -> begin
(
# 449 "FStar.TypeChecker.Tc.fst"
let us = (FStar_List.map (tc_universe env) us)
in (
# 450 "FStar.TypeChecker.Tc.fst"
let _57_683 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_683) with
| (us', t) -> begin
(
# 451 "FStar.TypeChecker.Tc.fst"
let _57_690 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _146_327 = (let _146_326 = (let _146_325 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _146_325))
in FStar_Syntax_Syntax.Error (_146_326))
in (Prims.raise _146_327))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _57_689 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (
# 456 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 456 "FStar.TypeChecker.Tc.fst"
let _57_692 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 456 "FStar.TypeChecker.Tc.fst"
let _57_694 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_694.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_694.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_692.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_692.FStar_Syntax_Syntax.fv_qual})
in (
# 457 "FStar.TypeChecker.Tc.fst"
let e = (let _146_330 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_330 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(
# 461 "FStar.TypeChecker.Tc.fst"
let _57_702 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_702) with
| (us, t) -> begin
(
# 462 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 462 "FStar.TypeChecker.Tc.fst"
let _57_703 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 462 "FStar.TypeChecker.Tc.fst"
let _57_705 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_705.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_705.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_703.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_703.FStar_Syntax_Syntax.fv_qual})
in (
# 463 "FStar.TypeChecker.Tc.fst"
let e = (let _146_331 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_331 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t)))
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
let _57_719 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_719) with
| (bs, c) -> begin
(
# 473 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 474 "FStar.TypeChecker.Tc.fst"
let _57_724 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_724) with
| (env, _57_723) -> begin
(
# 475 "FStar.TypeChecker.Tc.fst"
let _57_729 = (tc_binders env bs)
in (match (_57_729) with
| (bs, env, g, us) -> begin
(
# 476 "FStar.TypeChecker.Tc.fst"
let _57_733 = (tc_comp env c)
in (match (_57_733) with
| (c, uc, f) -> begin
(
# 477 "FStar.TypeChecker.Tc.fst"
let e = (
# 477 "FStar.TypeChecker.Tc.fst"
let _57_734 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _57_734.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_734.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_734.FStar_Syntax_Syntax.vars})
in (
# 478 "FStar.TypeChecker.Tc.fst"
let _57_737 = (check_smt_pat env e bs c)
in (
# 479 "FStar.TypeChecker.Tc.fst"
let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (
# 480 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 481 "FStar.TypeChecker.Tc.fst"
let g = (let _146_332 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _146_332))
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
let _57_753 = (let _146_334 = (let _146_333 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_333)::[])
in (FStar_Syntax_Subst.open_term _146_334 phi))
in (match (_57_753) with
| (x, phi) -> begin
(
# 492 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 493 "FStar.TypeChecker.Tc.fst"
let _57_758 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_758) with
| (env, _57_757) -> begin
(
# 494 "FStar.TypeChecker.Tc.fst"
let _57_763 = (let _146_335 = (FStar_List.hd x)
in (tc_binder env _146_335))
in (match (_57_763) with
| (x, env, f1, u) -> begin
(
# 495 "FStar.TypeChecker.Tc.fst"
let _57_764 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_338 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _146_337 = (FStar_Syntax_Print.term_to_string phi)
in (let _146_336 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _146_338 _146_337 _146_336))))
end else begin
()
end
in (
# 498 "FStar.TypeChecker.Tc.fst"
let _57_769 = (FStar_Syntax_Util.type_u ())
in (match (_57_769) with
| (t_phi, _57_768) -> begin
(
# 499 "FStar.TypeChecker.Tc.fst"
let _57_774 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_57_774) with
| (phi, _57_772, f2) -> begin
(
# 500 "FStar.TypeChecker.Tc.fst"
let e = (
# 500 "FStar.TypeChecker.Tc.fst"
let _57_775 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _57_775.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_775.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_775.FStar_Syntax_Syntax.vars})
in (
# 501 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 502 "FStar.TypeChecker.Tc.fst"
let g = (let _146_339 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _146_339))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _57_783) -> begin
(
# 506 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (
# 507 "FStar.TypeChecker.Tc.fst"
let _57_789 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_340 = (FStar_Syntax_Print.term_to_string (
# 508 "FStar.TypeChecker.Tc.fst"
let _57_787 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _57_787.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_787.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_787.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _146_340))
end else begin
()
end
in (
# 509 "FStar.TypeChecker.Tc.fst"
let _57_793 = (FStar_Syntax_Subst.open_term bs body)
in (match (_57_793) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _57_795 -> begin
(let _146_342 = (let _146_341 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _146_341))
in (FStar_All.failwith _146_342))
end)))))
and tc_constant : FStar_TypeChecker_Env.env  ->  FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun env r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_57_801) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_57_804, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_57_809, Some (FStar_Const.Unsigned, FStar_Const.Int8)) -> begin
FStar_TypeChecker_Common.t_uint8
end
| FStar_Const.Const_int (_57_817, Some (FStar_Const.Signed, FStar_Const.Int8)) -> begin
FStar_TypeChecker_Common.t_int8
end
| FStar_Const.Const_int (_57_825, Some (FStar_Const.Unsigned, FStar_Const.Int16)) -> begin
FStar_TypeChecker_Common.t_uint16
end
| FStar_Const.Const_int (_57_833, Some (FStar_Const.Signed, FStar_Const.Int16)) -> begin
FStar_TypeChecker_Common.t_int16
end
| FStar_Const.Const_int (_57_841, Some (FStar_Const.Unsigned, FStar_Const.Int32)) -> begin
FStar_TypeChecker_Common.t_uint32
end
| FStar_Const.Const_int (_57_849, Some (FStar_Const.Signed, FStar_Const.Int32)) -> begin
FStar_TypeChecker_Common.t_int32
end
| FStar_Const.Const_int (_57_857, Some (FStar_Const.Unsigned, FStar_Const.Int64)) -> begin
FStar_TypeChecker_Common.t_uint64
end
| FStar_Const.Const_int (_57_865, Some (FStar_Const.Signed, FStar_Const.Int64)) -> begin
FStar_TypeChecker_Common.t_int64
end
| FStar_Const.Const_string (_57_873) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_57_876) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_57_879) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_57_883) -> begin
FStar_TypeChecker_Common.t_range
end
| _57_886 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 545 "FStar.TypeChecker.Tc.fst"
let _57_893 = (FStar_Syntax_Util.type_u ())
in (match (_57_893) with
| (k, u) -> begin
(
# 546 "FStar.TypeChecker.Tc.fst"
let _57_898 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_898) with
| (t, _57_896, g) -> begin
(let _146_348 = (FStar_Syntax_Syntax.mk_Total t)
in (_146_348, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 550 "FStar.TypeChecker.Tc.fst"
let _57_903 = (FStar_Syntax_Util.type_u ())
in (match (_57_903) with
| (k, u) -> begin
(
# 551 "FStar.TypeChecker.Tc.fst"
let _57_908 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_908) with
| (t, _57_906, g) -> begin
(let _146_349 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_146_349, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 555 "FStar.TypeChecker.Tc.fst"
let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (
# 556 "FStar.TypeChecker.Tc.fst"
let tc = (let _146_351 = (let _146_350 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_146_350)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _146_351 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 557 "FStar.TypeChecker.Tc.fst"
let _57_917 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_57_917) with
| (tc, _57_915, f) -> begin
(
# 558 "FStar.TypeChecker.Tc.fst"
let _57_921 = (FStar_Syntax_Util.head_and_args tc)
in (match (_57_921) with
| (_57_919, args) -> begin
(
# 559 "FStar.TypeChecker.Tc.fst"
let _57_924 = (let _146_353 = (FStar_List.hd args)
in (let _146_352 = (FStar_List.tl args)
in (_146_353, _146_352)))
in (match (_57_924) with
| (res, args) -> begin
(
# 560 "FStar.TypeChecker.Tc.fst"
let _57_940 = (let _146_355 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _57_5 -> (match (_57_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(
# 562 "FStar.TypeChecker.Tc.fst"
let _57_931 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_931) with
| (env, _57_930) -> begin
(
# 563 "FStar.TypeChecker.Tc.fst"
let _57_936 = (tc_tot_or_gtot_term env e)
in (match (_57_936) with
| (e, _57_934, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _146_355 FStar_List.unzip))
in (match (_57_940) with
| (flags, guards) -> begin
(
# 566 "FStar.TypeChecker.Tc.fst"
let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| _57_945 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _146_357 = (FStar_Syntax_Syntax.mk_Comp (
# 569 "FStar.TypeChecker.Tc.fst"
let _57_947 = c
in {FStar_Syntax_Syntax.effect_name = _57_947.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _57_947.FStar_Syntax_Syntax.flags}))
in (let _146_356 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_146_357, u, _146_356))))
end))
end))
end))
end))))
end))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (
# 576 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun u -> (
# 577 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_57_955) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _146_362 = (aux u)
in FStar_Syntax_Syntax.U_succ (_146_362))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _146_363 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_146_363))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _146_367 = (let _146_366 = (let _146_365 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _146_364 = (FStar_TypeChecker_Env.get_range env)
in (_146_365, _146_364)))
in FStar_Syntax_Syntax.Error (_146_366))
in (Prims.raise _146_367))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _146_368 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_368 Prims.snd))
end
| _57_970 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (
# 599 "FStar.TypeChecker.Tc.fst"
let fail = (fun msg t -> (let _146_377 = (let _146_376 = (let _146_375 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_146_375, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_376))
in (Prims.raise _146_377)))
in (
# 608 "FStar.TypeChecker.Tc.fst"
let check_binders = (fun env bs bs_expected -> (
# 613 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun _57_988 bs bs_expected -> (match (_57_988) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| ((hd, imp)::bs, (hd_expected, imp')::bs_expected) -> begin
(
# 617 "FStar.TypeChecker.Tc.fst"
let _57_1019 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _146_394 = (let _146_393 = (let _146_392 = (let _146_390 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _146_390))
in (let _146_391 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_146_392, _146_391)))
in FStar_Syntax_Syntax.Error (_146_393))
in (Prims.raise _146_394))
end
| _57_1018 -> begin
()
end)
in (
# 624 "FStar.TypeChecker.Tc.fst"
let expected_t = (FStar_Syntax_Subst.subst (FStar_Syntax_Syntax.Renaming (subst)) hd_expected.FStar_Syntax_Syntax.sort)
in (
# 625 "FStar.TypeChecker.Tc.fst"
let _57_1036 = (match ((let _146_395 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _146_395.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _57_1024 -> begin
(
# 628 "FStar.TypeChecker.Tc.fst"
let _57_1025 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_396 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _146_396))
end else begin
()
end
in (
# 629 "FStar.TypeChecker.Tc.fst"
let _57_1031 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_57_1031) with
| (t, _57_1029, g1) -> begin
(
# 630 "FStar.TypeChecker.Tc.fst"
let g2 = (let _146_398 = (FStar_TypeChecker_Env.get_range env)
in (let _146_397 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _146_398 "Type annotation on parameter incompatible with the expected type" _146_397)))
in (
# 634 "FStar.TypeChecker.Tc.fst"
let g = (let _146_399 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _146_399))
in (t, g)))
end)))
end)
in (match (_57_1036) with
| (t, g) -> begin
(
# 636 "FStar.TypeChecker.Tc.fst"
let hd = (
# 636 "FStar.TypeChecker.Tc.fst"
let _57_1037 = hd
in {FStar_Syntax_Syntax.ppname = _57_1037.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1037.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 637 "FStar.TypeChecker.Tc.fst"
let b = (hd, imp)
in (
# 638 "FStar.TypeChecker.Tc.fst"
let b_expected = (hd_expected, imp')
in (
# 639 "FStar.TypeChecker.Tc.fst"
let env = (maybe_push_binding env b)
in (
# 640 "FStar.TypeChecker.Tc.fst"
let subst = (maybe_extend_renaming subst b_expected hd)
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
# 650 "FStar.TypeChecker.Tc.fst"
let rec expected_function_typ = (fun env t0 body -> (match (t0) with
| None -> begin
(
# 661 "FStar.TypeChecker.Tc.fst"
let _57_1058 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1057 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (
# 664 "FStar.TypeChecker.Tc.fst"
let _57_1065 = (tc_binders env bs)
in (match (_57_1065) with
| (bs, envbody, g, _57_1064) -> begin
(
# 665 "FStar.TypeChecker.Tc.fst"
let _57_1083 = (match ((let _146_406 = (FStar_Syntax_Subst.compress body)
in _146_406.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _57_1070) -> begin
(
# 667 "FStar.TypeChecker.Tc.fst"
let _57_1077 = (tc_comp envbody c)
in (match (_57_1077) with
| (c, _57_1075, g') -> begin
(let _146_407 = (FStar_TypeChecker_Rel.conj_guard g g')
in (Some (c), body, _146_407))
end))
end
| _57_1079 -> begin
(None, body, g)
end)
in (match (_57_1083) with
| (copt, body, g) -> begin
(None, bs, [], copt, envbody, body, g)
end))
end)))
end
| Some (t) -> begin
(
# 673 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 674 "FStar.TypeChecker.Tc.fst"
let rec as_function_typ = (fun norm t -> (match ((let _146_412 = (FStar_Syntax_Subst.compress t)
in _146_412.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 678 "FStar.TypeChecker.Tc.fst"
let _57_1110 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1109 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 679 "FStar.TypeChecker.Tc.fst"
let _57_1117 = (tc_binders env bs)
in (match (_57_1117) with
| (bs, envbody, g, _57_1116) -> begin
(
# 680 "FStar.TypeChecker.Tc.fst"
let _57_1121 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_57_1121) with
| (envbody, _57_1120) -> begin
(Some ((t, true)), bs, [], None, envbody, body, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _57_1124) -> begin
(
# 686 "FStar.TypeChecker.Tc.fst"
let _57_1135 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_57_1135) with
| (_57_1128, bs, bs', copt, env, body, g) -> begin
(Some ((t, false)), bs, bs', copt, env, body, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 690 "FStar.TypeChecker.Tc.fst"
let _57_1142 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_57_1142) with
| (bs_expected, c_expected) -> begin
(
# 697 "FStar.TypeChecker.Tc.fst"
let check_actuals_against_formals = (fun env bs bs_expected -> (
# 698 "FStar.TypeChecker.Tc.fst"
let rec handle_more = (fun _57_1153 c_expected -> (match (_57_1153) with
| (env, bs, more, guard, renaming) -> begin
(match (more) with
| None -> begin
(let _146_423 = (FStar_Syntax_Subst.subst_comp (FStar_Syntax_Syntax.Renaming (renaming)) c_expected)
in (env, bs, guard, _146_423))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(
# 703 "FStar.TypeChecker.Tc.fst"
let c = (let _146_424 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _146_424))
in (let _146_425 = (FStar_Syntax_Subst.subst_comp (FStar_Syntax_Syntax.Renaming (renaming)) c)
in (env, bs, guard, _146_425)))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(
# 707 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.subst_comp (FStar_Syntax_Syntax.Renaming (renaming)) c_expected)
in if (FStar_Syntax_Util.is_total_comp c) then begin
(
# 710 "FStar.TypeChecker.Tc.fst"
let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 713 "FStar.TypeChecker.Tc.fst"
let _57_1174 = (check_binders env more_bs bs_expected)
in (match (_57_1174) with
| (env, bs', more, guard', subst) -> begin
(let _146_427 = (let _146_426 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _146_426, subst))
in (handle_more _146_427 c_expected))
end))
end
| _57_1176 -> begin
(let _146_429 = (let _146_428 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _146_428))
in (fail _146_429 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _146_430 = (check_binders env bs bs_expected)
in (handle_more _146_430 c_expected))))
in (
# 720 "FStar.TypeChecker.Tc.fst"
let mk_letrec_env = (fun envbody bs c -> (
# 721 "FStar.TypeChecker.Tc.fst"
let letrecs = (guard_letrecs envbody bs c)
in (
# 722 "FStar.TypeChecker.Tc.fst"
let envbody = (
# 722 "FStar.TypeChecker.Tc.fst"
let _57_1182 = envbody
in {FStar_TypeChecker_Env.solver = _57_1182.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1182.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1182.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1182.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1182.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1182.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1182.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1182.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1182.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1182.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1182.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1182.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_1182.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1182.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1182.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1182.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1182.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1182.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1182.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1182.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _57_1187 _57_1190 -> (match ((_57_1187, _57_1190)) with
| ((env, letrec_binders), (l, t)) -> begin
(
# 726 "FStar.TypeChecker.Tc.fst"
let _57_1196 = (let _146_440 = (let _146_439 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_439 Prims.fst))
in (tc_term _146_440 t))
in (match (_57_1196) with
| (t, _57_1193, _57_1195) -> begin
(
# 727 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (
# 728 "FStar.TypeChecker.Tc.fst"
let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _146_441 = (FStar_Syntax_Syntax.mk_binder (
# 729 "FStar.TypeChecker.Tc.fst"
let _57_1200 = x
in {FStar_Syntax_Syntax.ppname = _57_1200.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1200.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_146_441)::letrec_binders)
end
| _57_1203 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (
# 734 "FStar.TypeChecker.Tc.fst"
let _57_1209 = (check_actuals_against_formals env bs bs_expected)
in (match (_57_1209) with
| (envbody, bs, g, c) -> begin
(
# 735 "FStar.TypeChecker.Tc.fst"
let _57_1212 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_57_1212) with
| (envbody, letrecs) -> begin
(
# 736 "FStar.TypeChecker.Tc.fst"
let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, body, g))
end))
end))))
end))
end
| _57_1215 -> begin
if (not (norm)) then begin
(let _146_442 = (unfold_whnf env t)
in (as_function_typ true _146_442))
end else begin
(
# 744 "FStar.TypeChecker.Tc.fst"
let _57_1225 = (expected_function_typ env None body)
in (match (_57_1225) with
| (_57_1217, bs, _57_1220, c_opt, envbody, body, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, body, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (
# 748 "FStar.TypeChecker.Tc.fst"
let use_eq = env.FStar_TypeChecker_Env.use_eq
in (
# 749 "FStar.TypeChecker.Tc.fst"
let _57_1229 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1229) with
| (env, topt) -> begin
(
# 751 "FStar.TypeChecker.Tc.fst"
let _57_1233 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_443 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _146_443 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (
# 756 "FStar.TypeChecker.Tc.fst"
let _57_1242 = (expected_function_typ env topt body)
in (match (_57_1242) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(
# 757 "FStar.TypeChecker.Tc.fst"
let _57_1248 = (tc_term (
# 757 "FStar.TypeChecker.Tc.fst"
let _57_1243 = envbody
in {FStar_TypeChecker_Env.solver = _57_1243.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1243.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1243.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1243.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1243.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1243.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1243.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1243.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1243.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1243.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1243.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1243.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1243.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1243.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1243.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1243.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1243.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1243.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1243.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_57_1248) with
| (body, cbody, guard_body) -> begin
(
# 759 "FStar.TypeChecker.Tc.fst"
let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (
# 762 "FStar.TypeChecker.Tc.fst"
let _57_1250 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _146_446 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _146_445 = (let _146_444 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _146_444))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _146_446 _146_445)))
end else begin
()
end
in (
# 767 "FStar.TypeChecker.Tc.fst"
let _57_1257 = (let _146_448 = (let _146_447 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _146_447))
in (check_expected_effect (
# 767 "FStar.TypeChecker.Tc.fst"
let _57_1252 = envbody
in {FStar_TypeChecker_Env.solver = _57_1252.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1252.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1252.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1252.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1252.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1252.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1252.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1252.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1252.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1252.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1252.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1252.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1252.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1252.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1252.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1252.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1252.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1252.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1252.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1252.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _146_448))
in (match (_57_1257) with
| (body, cbody, guard) -> begin
(
# 768 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (
# 769 "FStar.TypeChecker.Tc.fst"
let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _146_449 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _146_449))
end else begin
(
# 771 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (
# 774 "FStar.TypeChecker.Tc.fst"
let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (
# 775 "FStar.TypeChecker.Tc.fst"
let e = (let _146_452 = (let _146_451 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _146_450 -> FStar_Util.Inl (_146_450)))
in Some (_146_451))
in (FStar_Syntax_Util.abs bs body _146_452))
in (
# 776 "FStar.TypeChecker.Tc.fst"
let _57_1280 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(
# 778 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_1269) -> begin
(e, t, guard)
end
| _57_1272 -> begin
(
# 785 "FStar.TypeChecker.Tc.fst"
let _57_1275 = if use_teq then begin
(let _146_453 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _146_453))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_57_1275) with
| (e, guard') -> begin
(let _146_454 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _146_454))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_57_1280) with
| (e, tfun, guard) -> begin
(
# 794 "FStar.TypeChecker.Tc.fst"
let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (
# 795 "FStar.TypeChecker.Tc.fst"
let _57_1284 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_57_1284) with
| (c, g) -> begin
(e, c, g)
end)))
end))))))
end))))
end))
end)))
end)))))))
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead ghead args expected_topt -> (
# 803 "FStar.TypeChecker.Tc.fst"
let n_args = (FStar_List.length args)
in (
# 804 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 805 "FStar.TypeChecker.Tc.fst"
let thead = chead.FStar_Syntax_Syntax.res_typ
in (
# 806 "FStar.TypeChecker.Tc.fst"
let _57_1294 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_463 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _146_462 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _146_463 _146_462)))
end else begin
()
end
in (
# 807 "FStar.TypeChecker.Tc.fst"
let rec check_function_app = (fun norm tf -> (match ((let _146_468 = (FStar_Syntax_Util.unrefine tf)
in _146_468.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 811 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| (e, imp)::tl -> begin
(
# 814 "FStar.TypeChecker.Tc.fst"
let _57_1328 = (tc_term env e)
in (match (_57_1328) with
| (e, c, g_e) -> begin
(
# 815 "FStar.TypeChecker.Tc.fst"
let _57_1332 = (tc_args env tl)
in (match (_57_1332) with
| (args, comps, g_rest) -> begin
(let _146_473 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, ((e.FStar_Syntax_Syntax.pos, c))::comps, _146_473))
end))
end))
end))
in (
# 823 "FStar.TypeChecker.Tc.fst"
let _57_1336 = (tc_args env args)
in (match (_57_1336) with
| (args, comps, g_args) -> begin
(
# 824 "FStar.TypeChecker.Tc.fst"
let bs = (let _146_475 = (FStar_All.pipe_right comps (FStar_List.map (fun _57_1340 -> (match (_57_1340) with
| (_57_1338, c) -> begin
(c.FStar_Syntax_Syntax.res_typ, None)
end))))
in (FStar_Syntax_Util.null_binders_of_tks _146_475))
in (
# 825 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _57_1346 -> begin
FStar_Syntax_Util.ml_comp
end)
in (
# 828 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _146_490 = (FStar_Syntax_Subst.compress t)
in _146_490.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_1352) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _57_1357 -> begin
ml_or_tot
end)
end)
in (
# 835 "FStar.TypeChecker.Tc.fst"
let cres = (let _146_495 = (let _146_494 = (let _146_493 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_493 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _146_494))
in (ml_or_tot _146_495 r))
in (
# 836 "FStar.TypeChecker.Tc.fst"
let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (
# 837 "FStar.TypeChecker.Tc.fst"
let _57_1361 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_498 = (FStar_Syntax_Print.term_to_string head)
in (let _146_497 = (FStar_Syntax_Print.term_to_string tf)
in (let _146_496 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _146_498 _146_497 _146_496))))
end else begin
()
end
in (
# 842 "FStar.TypeChecker.Tc.fst"
let _57_1363 = (let _146_499 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _146_499))
in (
# 843 "FStar.TypeChecker.Tc.fst"
let comp = (let _146_502 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _57_1367 out -> (match (_57_1367) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c (None, out))
end)) (((head.FStar_Syntax_Syntax.pos, chead))::comps) _146_502))
in (let _146_504 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _146_503 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_146_504, comp, _146_503)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 851 "FStar.TypeChecker.Tc.fst"
let _57_1376 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_1376) with
| (bs, c) -> begin
(
# 853 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun _57_1384 bs cres args -> (match (_57_1384) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (_57_1391)))::rest, (_57_1399, None)::_57_1397) -> begin
(
# 864 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.subst (FStar_Syntax_Syntax.Instantiation (subst)) x.FStar_Syntax_Syntax.sort)
in (
# 865 "FStar.TypeChecker.Tc.fst"
let _57_1405 = (check_no_escape (Some (head)) env fvs t)
in (
# 866 "FStar.TypeChecker.Tc.fst"
let _57_1411 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_57_1411) with
| (varg, _57_1409, implicits) -> begin
(
# 867 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_Syntax_Syntax.Name2Term ((x, varg)))::subst
in (
# 868 "FStar.TypeChecker.Tc.fst"
let arg = (let _146_513 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _146_513))
in (let _146_515 = (let _146_514 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _146_514, fvs))
in (tc_args _146_515 rest cres args))))
end))))
end
| ((x, aqual)::rest, (e, aq)::rest') -> begin
(
# 872 "FStar.TypeChecker.Tc.fst"
let _57_1443 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _57_1442 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (
# 877 "FStar.TypeChecker.Tc.fst"
let targ = (FStar_Syntax_Subst.subst (FStar_Syntax_Syntax.Instantiation (subst)) x.FStar_Syntax_Syntax.sort)
in (
# 878 "FStar.TypeChecker.Tc.fst"
let x = (
# 878 "FStar.TypeChecker.Tc.fst"
let _57_1446 = x
in {FStar_Syntax_Syntax.ppname = _57_1446.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1446.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (
# 879 "FStar.TypeChecker.Tc.fst"
let _57_1449 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_516 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _146_516))
end else begin
()
end
in (
# 880 "FStar.TypeChecker.Tc.fst"
let _57_1451 = (check_no_escape (Some (head)) env fvs targ)
in (
# 881 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (
# 882 "FStar.TypeChecker.Tc.fst"
let env = (
# 882 "FStar.TypeChecker.Tc.fst"
let _57_1454 = env
in {FStar_TypeChecker_Env.solver = _57_1454.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1454.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1454.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1454.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1454.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1454.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1454.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1454.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1454.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1454.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1454.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1454.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1454.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1454.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1454.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _57_1454.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1454.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1454.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1454.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1454.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 883 "FStar.TypeChecker.Tc.fst"
let _57_1457 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_519 = (FStar_Syntax_Print.tag_of_term e)
in (let _146_518 = (FStar_Syntax_Print.term_to_string e)
in (let _146_517 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _146_519 _146_518 _146_517))))
end else begin
()
end
in (
# 884 "FStar.TypeChecker.Tc.fst"
let _57_1462 = (tc_term env e)
in (match (_57_1462) with
| (e, c, g_e) -> begin
(
# 885 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (
# 887 "FStar.TypeChecker.Tc.fst"
let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(
# 889 "FStar.TypeChecker.Tc.fst"
let subst = (let _146_520 = (FStar_List.hd bs)
in (maybe_extend_subst subst _146_520 e))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(
# 892 "FStar.TypeChecker.Tc.fst"
let subst = (let _146_521 = (FStar_List.hd bs)
in (maybe_extend_subst subst _146_521 e))
in (
# 893 "FStar.TypeChecker.Tc.fst"
let _57_1469 = (((e.FStar_Syntax_Syntax.pos, Some (x), c))::comps, g)
in (match (_57_1469) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _146_522 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _146_522)) then begin
(
# 897 "FStar.TypeChecker.Tc.fst"
let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (
# 898 "FStar.TypeChecker.Tc.fst"
let arg' = (let _146_523 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _146_523))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((e.FStar_Syntax_Syntax.pos, Some (newx), c))::comps, g, fvs) rest cres rest')))
end else begin
(let _146_527 = (let _146_526 = (let _146_525 = (let _146_524 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _146_524))
in (_146_525)::arg_rets)
in (subst, (arg)::outargs, _146_526, ((e.FStar_Syntax_Syntax.pos, Some (x), c))::comps, g, (x)::fvs))
in (tc_args _146_527 rest cres rest'))
end
end
end))
end))))))))))
end
| (_57_1473, []) -> begin
(
# 907 "FStar.TypeChecker.Tc.fst"
let _57_1476 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (
# 908 "FStar.TypeChecker.Tc.fst"
let _57_1496 = (match (bs) with
| [] -> begin
(
# 911 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.subst_lcomp (FStar_Syntax_Syntax.Instantiation (subst)) cres)
in (
# 917 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (
# 919 "FStar.TypeChecker.Tc.fst"
let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _57_1486 -> (match (_57_1486) with
| (_57_1482, _57_1484, c) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (
# 926 "FStar.TypeChecker.Tc.fst"
let cres = if refine_with_equality then begin
(let _146_529 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _146_529 cres))
end else begin
(
# 932 "FStar.TypeChecker.Tc.fst"
let _57_1488 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_532 = (FStar_Syntax_Print.term_to_string head)
in (let _146_531 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _146_530 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _146_532 _146_531 _146_530))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _57_1492 -> begin
(
# 941 "FStar.TypeChecker.Tc.fst"
let g = (let _146_533 = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (FStar_All.pipe_right _146_533 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _146_538 = (let _146_537 = (let _146_536 = (let _146_535 = (let _146_534 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _146_534))
in (FStar_Syntax_Subst.subst (FStar_Syntax_Syntax.Instantiation (subst)) _146_535))
in (FStar_Syntax_Syntax.mk_Total _146_536))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_537))
in (_146_538, g)))
end)
in (match (_57_1496) with
| (cres, g) -> begin
(
# 944 "FStar.TypeChecker.Tc.fst"
let _57_1497 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_539 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _146_539))
end else begin
()
end
in (
# 945 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_List.fold_left (fun out _57_1503 -> (match (_57_1503) with
| (r1, x, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c (x, out))
end)) cres comps)
in (
# 946 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.bind head.FStar_Syntax_Syntax.pos env None chead (None, comp))
in (
# 947 "FStar.TypeChecker.Tc.fst"
let app = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev outargs) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (
# 948 "FStar.TypeChecker.Tc.fst"
let _57_1509 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp g)
in (match (_57_1509) with
| (comp, g) -> begin
(app, comp, g)
end))))))
end)))
end
| ([], arg::_57_1512) -> begin
(
# 953 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun norm tres -> (
# 954 "FStar.TypeChecker.Tc.fst"
let tres = (let _146_547 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _146_547 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(
# 957 "FStar.TypeChecker.Tc.fst"
let _57_1524 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_548 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _146_548))
end else begin
()
end
in (let _146_552 = (let _146_551 = (let _146_550 = (let _146_549 = (FStar_TypeChecker_Env.get_range env)
in (_146_549, None, cres))
in (_146_550)::comps)
in (subst, outargs, arg_rets, _146_551, g, fvs))
in (tc_args _146_552 bs (FStar_Syntax_Util.lcomp_of_comp cres') args)))
end
| _57_1527 when (not (norm)) -> begin
(let _146_553 = (unfold_whnf env tres)
in (aux true _146_553))
end
| _57_1529 -> begin
(let _146_559 = (let _146_558 = (let _146_557 = (let _146_555 = (FStar_TypeChecker_Normalize.term_to_string env tf)
in (let _146_554 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _146_555 _146_554)))
in (let _146_556 = (FStar_Syntax_Syntax.argpos arg)
in (_146_557, _146_556)))
in FStar_Syntax_Syntax.Error (_146_558))
in (Prims.raise _146_559))
end)))
in (aux false cres.FStar_Syntax_Syntax.res_typ))
end)
end))
in (tc_args ([], [], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs (FStar_Syntax_Util.lcomp_of_comp c) args))
end))
end
| _57_1531 -> begin
if (not (norm)) then begin
(let _146_560 = (unfold_whnf env tf)
in (check_function_app true _146_560))
end else begin
(let _146_563 = (let _146_562 = (let _146_561 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_146_561, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_562))
in (Prims.raise _146_563))
end
end))
in (let _146_565 = (let _146_564 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _146_564))
in (check_function_app false _146_565))))))))
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
let _57_1567 = (FStar_List.fold_left2 (fun _57_1548 _57_1551 _57_1554 -> (match ((_57_1548, _57_1551, _57_1554)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(
# 989 "FStar.TypeChecker.Tc.fst"
let _57_1555 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 990 "FStar.TypeChecker.Tc.fst"
let _57_1560 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_57_1560) with
| (e, c, g) -> begin
(
# 991 "FStar.TypeChecker.Tc.fst"
let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (
# 992 "FStar.TypeChecker.Tc.fst"
let g = (let _146_575 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _146_575 g))
in (
# 993 "FStar.TypeChecker.Tc.fst"
let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _146_579 = (let _146_577 = (let _146_576 = (FStar_Syntax_Syntax.as_arg e)
in (_146_576)::[])
in (FStar_List.append seen _146_577))
in (let _146_578 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_146_579, _146_578, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_57_1567) with
| (args, guard, ghost) -> begin
(
# 997 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (
# 998 "FStar.TypeChecker.Tc.fst"
let c = if ghost then begin
(let _146_580 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _146_580 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (
# 999 "FStar.TypeChecker.Tc.fst"
let _57_1572 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_57_1572) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _57_1574 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (
# 1019 "FStar.TypeChecker.Tc.fst"
let _57_1581 = (FStar_Syntax_Subst.open_branch branch)
in (match (_57_1581) with
| (pattern, when_clause, branch_exp) -> begin
(
# 1020 "FStar.TypeChecker.Tc.fst"
let _57_1586 = branch
in (match (_57_1586) with
| (cpat, _57_1584, cbr) -> begin
(
# 1023 "FStar.TypeChecker.Tc.fst"
let tc_pat = (fun allow_implicits pat_t p0 -> (
# 1030 "FStar.TypeChecker.Tc.fst"
let _57_1594 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_57_1594) with
| (pat_bvs, exps, p) -> begin
(
# 1031 "FStar.TypeChecker.Tc.fst"
let _57_1595 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_592 = (FStar_Syntax_Print.pat_to_string p0)
in (let _146_591 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _146_592 _146_591)))
end else begin
()
end
in (
# 1033 "FStar.TypeChecker.Tc.fst"
let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (
# 1034 "FStar.TypeChecker.Tc.fst"
let _57_1601 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_57_1601) with
| (env1, _57_1600) -> begin
(
# 1035 "FStar.TypeChecker.Tc.fst"
let env1 = (
# 1035 "FStar.TypeChecker.Tc.fst"
let _57_1602 = env1
in {FStar_TypeChecker_Env.solver = _57_1602.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1602.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1602.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1602.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1602.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1602.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1602.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1602.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _57_1602.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1602.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1602.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1602.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1602.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1602.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1602.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1602.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1602.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1602.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1602.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1602.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1036 "FStar.TypeChecker.Tc.fst"
let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (
# 1037 "FStar.TypeChecker.Tc.fst"
let _57_1641 = (let _146_615 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (
# 1038 "FStar.TypeChecker.Tc.fst"
let _57_1607 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_595 = (FStar_Syntax_Print.term_to_string e)
in (let _146_594 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _146_595 _146_594)))
end else begin
()
end
in (
# 1041 "FStar.TypeChecker.Tc.fst"
let _57_1612 = (tc_term env1 e)
in (match (_57_1612) with
| (e, lc, g) -> begin
(
# 1043 "FStar.TypeChecker.Tc.fst"
let _57_1613 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_597 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _146_596 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _146_597 _146_596)))
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
let _57_1619 = (let _146_598 = (FStar_TypeChecker_Rel.discharge_guard env (
# 1048 "FStar.TypeChecker.Tc.fst"
let _57_1617 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_1617.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_1617.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_1617.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _146_598 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1049 "FStar.TypeChecker.Tc.fst"
let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (
# 1050 "FStar.TypeChecker.Tc.fst"
let uvars_to_string = (fun uvs -> (let _146_603 = (let _146_602 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _146_602 (FStar_List.map (fun _57_1627 -> (match (_57_1627) with
| (u, _57_1626) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _146_603 (FStar_String.concat ", "))))
in (
# 1051 "FStar.TypeChecker.Tc.fst"
let uvs1 = (FStar_Syntax_Free.uvars e')
in (
# 1052 "FStar.TypeChecker.Tc.fst"
let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (
# 1053 "FStar.TypeChecker.Tc.fst"
let _57_1635 = if (let _146_604 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _146_604)) then begin
(
# 1054 "FStar.TypeChecker.Tc.fst"
let unresolved = (let _146_605 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _146_605 FStar_Util.set_elements))
in (let _146_613 = (let _146_612 = (let _146_611 = (let _146_610 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _146_609 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _146_608 = (let _146_607 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _57_1634 -> (match (_57_1634) with
| (u, _57_1633) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _146_607 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _146_610 _146_609 _146_608))))
in (_146_611, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_146_612))
in (Prims.raise _146_613)))
end else begin
()
end
in (
# 1061 "FStar.TypeChecker.Tc.fst"
let _57_1637 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_614 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _146_614))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _146_615 FStar_List.unzip))
in (match (_57_1641) with
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
let _57_1648 = (let _146_616 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _146_616 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_57_1648) with
| (scrutinee_env, _57_1647) -> begin
(
# 1075 "FStar.TypeChecker.Tc.fst"
let _57_1654 = (tc_pat true pat_t pattern)
in (match (_57_1654) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(
# 1078 "FStar.TypeChecker.Tc.fst"
let _57_1664 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(
# 1085 "FStar.TypeChecker.Tc.fst"
let _57_1661 = (let _146_617 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _146_617 e))
in (match (_57_1661) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_57_1664) with
| (when_clause, g_when) -> begin
(
# 1089 "FStar.TypeChecker.Tc.fst"
let _57_1668 = (tc_term pat_env branch_exp)
in (match (_57_1668) with
| (branch_exp, c, g_branch) -> begin
(
# 1093 "FStar.TypeChecker.Tc.fst"
let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _146_619 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _146_618 -> Some (_146_618)) _146_619))
end)
in (
# 1100 "FStar.TypeChecker.Tc.fst"
let _57_1724 = (
# 1103 "FStar.TypeChecker.Tc.fst"
let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (
# 1104 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _57_1686 -> begin
(
# 1110 "FStar.TypeChecker.Tc.fst"
let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _146_623 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _146_622 -> Some (_146_622)) _146_623))
end))
end))) None))
in (
# 1115 "FStar.TypeChecker.Tc.fst"
let _57_1694 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_57_1694) with
| (c, g_branch) -> begin
(
# 1119 "FStar.TypeChecker.Tc.fst"
let _57_1719 = (match ((eqs, when_condition)) with
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
in (let _146_626 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _146_625 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_146_626, _146_625)))))
end
| (Some (f), Some (w)) -> begin
(
# 1131 "FStar.TypeChecker.Tc.fst"
let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1132 "FStar.TypeChecker.Tc.fst"
let g_fw = (let _146_627 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_146_627))
in (let _146_630 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _146_629 = (let _146_628 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _146_628 g_when))
in (_146_630, _146_629)))))
end
| (None, Some (w)) -> begin
(
# 1137 "FStar.TypeChecker.Tc.fst"
let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (
# 1138 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _146_631 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_146_631, g_when))))
end)
in (match (_57_1719) with
| (c_weak, g_when_weak) -> begin
(
# 1143 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _146_633 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _146_632 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_146_633, _146_632, g_branch))))
end))
end)))
in (match (_57_1724) with
| (c, g_when, g_branch) -> begin
(
# 1161 "FStar.TypeChecker.Tc.fst"
let branch_guard = (
# 1163 "FStar.TypeChecker.Tc.fst"
let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (
# 1164 "FStar.TypeChecker.Tc.fst"
let discriminate = (fun scrutinee_tm f -> if ((let _146_643 = (let _146_642 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _146_642))
in (FStar_List.length _146_643)) > 1) then begin
(
# 1167 "FStar.TypeChecker.Tc.fst"
let disc = (let _146_644 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _146_644 FStar_Syntax_Syntax.Delta_equational None))
in (
# 1168 "FStar.TypeChecker.Tc.fst"
let disc = (let _146_646 = (let _146_645 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_146_645)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _146_646 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _146_647 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_146_647)::[])))
end else begin
[]
end)
in (
# 1172 "FStar.TypeChecker.Tc.fst"
let fail = (fun _57_1734 -> (match (()) with
| () -> begin
(let _146_653 = (let _146_652 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _146_651 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _146_650 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _146_652 _146_651 _146_650))))
in (FStar_All.failwith _146_653))
end))
in (
# 1178 "FStar.TypeChecker.Tc.fst"
let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _57_1741) -> begin
(head_constructor t)
end
| _57_1745 -> begin
(fail ())
end))
in (
# 1183 "FStar.TypeChecker.Tc.fst"
let pat_exp = (let _146_656 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _146_656 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_57_1770) -> begin
(let _146_661 = (let _146_660 = (let _146_659 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _146_658 = (let _146_657 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_146_657)::[])
in (_146_659)::_146_658))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _146_660 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_146_661)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 1192 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _146_662 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _146_662))
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
let sub_term_guards = (let _146_669 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _57_1788 -> (match (_57_1788) with
| (ei, _57_1787) -> begin
(
# 1201 "FStar.TypeChecker.Tc.fst"
let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _57_1792 -> begin
(
# 1205 "FStar.TypeChecker.Tc.fst"
let sub_term = (let _146_668 = (let _146_665 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _146_665 FStar_Syntax_Syntax.Delta_equational None))
in (let _146_667 = (let _146_666 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_146_666)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _146_668 _146_667 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _146_669 FStar_List.flatten))
in (let _146_670 = (discriminate scrutinee_tm f)
in (FStar_List.append _146_670 sub_term_guards)))
end)
end
| _57_1796 -> begin
[]
end))))))
in (
# 1211 "FStar.TypeChecker.Tc.fst"
let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(
# 1214 "FStar.TypeChecker.Tc.fst"
let t = (let _146_675 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _146_675))
in (
# 1215 "FStar.TypeChecker.Tc.fst"
let _57_1804 = (FStar_Syntax_Util.type_u ())
in (match (_57_1804) with
| (k, _57_1803) -> begin
(
# 1216 "FStar.TypeChecker.Tc.fst"
let _57_1810 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_57_1810) with
| (t, _57_1807, _57_1809) -> begin
t
end))
end)))
end)
in (
# 1220 "FStar.TypeChecker.Tc.fst"
let branch_guard = (let _146_676 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _146_676 FStar_Syntax_Util.mk_disj_l))
in (
# 1223 "FStar.TypeChecker.Tc.fst"
let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
in (
# 1229 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (
# 1231 "FStar.TypeChecker.Tc.fst"
let _57_1818 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_677 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _146_677))
end else begin
()
end
in (let _146_678 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_146_678, branch_guard, c, guard)))))
end)))
end))
end))
end))
end)))))
end))
end)))
and check_top_level_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1245 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1248 "FStar.TypeChecker.Tc.fst"
let _57_1835 = (check_let_bound_def true env lb)
in (match (_57_1835) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(
# 1250 "FStar.TypeChecker.Tc.fst"
let _57_1847 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(
# 1253 "FStar.TypeChecker.Tc.fst"
let g1 = (let _146_681 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _146_681 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1254 "FStar.TypeChecker.Tc.fst"
let _57_1842 = (let _146_685 = (let _146_684 = (let _146_683 = (let _146_682 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _146_682))
in (_146_683)::[])
in (FStar_TypeChecker_Util.generalize env _146_684))
in (FStar_List.hd _146_685))
in (match (_57_1842) with
| (_57_1838, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_57_1847) with
| (g1, e1, univ_vars, c1) -> begin
(
# 1258 "FStar.TypeChecker.Tc.fst"
let _57_1857 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(
# 1260 "FStar.TypeChecker.Tc.fst"
let _57_1850 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_57_1850) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(
# 1263 "FStar.TypeChecker.Tc.fst"
let _57_1851 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _146_686 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _146_686 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _146_687 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_146_687, c1)))
end
end))
end else begin
(
# 1267 "FStar.TypeChecker.Tc.fst"
let _57_1853 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _146_688 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _146_688)))
end
in (match (_57_1857) with
| (e2, c1) -> begin
(
# 1272 "FStar.TypeChecker.Tc.fst"
let cres = (let _146_689 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_689))
in (
# 1273 "FStar.TypeChecker.Tc.fst"
let _57_1859 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1275 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _146_690 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_146_690, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _57_1863 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1292 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1295 "FStar.TypeChecker.Tc.fst"
let env = (
# 1295 "FStar.TypeChecker.Tc.fst"
let _57_1874 = env
in {FStar_TypeChecker_Env.solver = _57_1874.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1874.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1874.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1874.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1874.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1874.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1874.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1874.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1874.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1874.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1874.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1874.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1874.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1874.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1874.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1874.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1874.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1874.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1874.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1874.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1296 "FStar.TypeChecker.Tc.fst"
let _57_1883 = (let _146_694 = (let _146_693 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_693 Prims.fst))
in (check_let_bound_def false _146_694 lb))
in (match (_57_1883) with
| (e1, _57_1879, c1, g1, annotated) -> begin
(
# 1297 "FStar.TypeChecker.Tc.fst"
let x = (
# 1297 "FStar.TypeChecker.Tc.fst"
let _57_1884 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1884.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1884.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (
# 1298 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (
# 1299 "FStar.TypeChecker.Tc.fst"
let _57_1890 = (let _146_696 = (let _146_695 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_695)::[])
in (FStar_Syntax_Subst.open_term _146_696 e2))
in (match (_57_1890) with
| (xb, e2) -> begin
(
# 1300 "FStar.TypeChecker.Tc.fst"
let xbinder = (FStar_List.hd xb)
in (
# 1301 "FStar.TypeChecker.Tc.fst"
let x = (Prims.fst xbinder)
in (
# 1302 "FStar.TypeChecker.Tc.fst"
let _57_1896 = (let _146_697 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _146_697 e2))
in (match (_57_1896) with
| (e2, c2, g2) -> begin
(
# 1303 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (Some (x), c2))
in (
# 1304 "FStar.TypeChecker.Tc.fst"
let e = (let _146_700 = (let _146_699 = (let _146_698 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _146_698))
in FStar_Syntax_Syntax.Tm_let (_146_699))
in (FStar_Syntax_Syntax.mk _146_700 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 1305 "FStar.TypeChecker.Tc.fst"
let x_eq_e1 = (let _146_703 = (let _146_702 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _146_702 e1))
in (FStar_All.pipe_left (fun _146_701 -> FStar_TypeChecker_Common.NonTrivial (_146_701)) _146_703))
in (
# 1306 "FStar.TypeChecker.Tc.fst"
let g2 = (let _146_705 = (let _146_704 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _146_704 g2))
in (FStar_TypeChecker_Rel.close_guard xb _146_705))
in (
# 1308 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if annotated then begin
(e, cres, guard)
end else begin
(
# 1312 "FStar.TypeChecker.Tc.fst"
let _57_1902 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end)))))
end))))
end))))
end)))
end
| _57_1905 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1321 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1324 "FStar.TypeChecker.Tc.fst"
let _57_1917 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1917) with
| (lbs, e2) -> begin
(
# 1326 "FStar.TypeChecker.Tc.fst"
let _57_1920 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1920) with
| (env0, topt) -> begin
(
# 1327 "FStar.TypeChecker.Tc.fst"
let _57_1923 = (build_let_rec_env true env0 lbs)
in (match (_57_1923) with
| (lbs, rec_env) -> begin
(
# 1328 "FStar.TypeChecker.Tc.fst"
let _57_1926 = (check_let_recs rec_env lbs)
in (match (_57_1926) with
| (lbs, g_lbs) -> begin
(
# 1329 "FStar.TypeChecker.Tc.fst"
let g_lbs = (let _146_708 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _146_708 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1331 "FStar.TypeChecker.Tc.fst"
let all_lb_names = (let _146_711 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _146_711 (fun _146_710 -> Some (_146_710))))
in (
# 1333 "FStar.TypeChecker.Tc.fst"
let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(
# 1339 "FStar.TypeChecker.Tc.fst"
let ecs = (let _146_715 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _146_714 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _146_714)))))
in (FStar_TypeChecker_Util.generalize env _146_715))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _57_1937 -> (match (_57_1937) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (
# 1346 "FStar.TypeChecker.Tc.fst"
let cres = (let _146_717 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_717))
in (
# 1347 "FStar.TypeChecker.Tc.fst"
let _57_1940 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1349 "FStar.TypeChecker.Tc.fst"
let _57_1944 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1944) with
| (lbs, e2) -> begin
(let _146_719 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_718 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_146_719, cres, _146_718)))
end)))))))
end))
end))
end))
end))
end
| _57_1946 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1360 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1363 "FStar.TypeChecker.Tc.fst"
let _57_1958 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1958) with
| (lbs, e2) -> begin
(
# 1365 "FStar.TypeChecker.Tc.fst"
let _57_1961 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1961) with
| (env0, topt) -> begin
(
# 1366 "FStar.TypeChecker.Tc.fst"
let _57_1964 = (build_let_rec_env false env0 lbs)
in (match (_57_1964) with
| (lbs, rec_env) -> begin
(
# 1367 "FStar.TypeChecker.Tc.fst"
let _57_1967 = (check_let_recs rec_env lbs)
in (match (_57_1967) with
| (lbs, g_lbs) -> begin
(
# 1369 "FStar.TypeChecker.Tc.fst"
let _57_1979 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (
# 1370 "FStar.TypeChecker.Tc.fst"
let x = (
# 1370 "FStar.TypeChecker.Tc.fst"
let _57_1970 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1970.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1970.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (
# 1371 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1371 "FStar.TypeChecker.Tc.fst"
let _57_1973 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _57_1973.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1973.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1973.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _57_1973.FStar_Syntax_Syntax.lbdef})
in (
# 1372 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], lb.FStar_Syntax_Syntax.lbtyp))
in (env, lb))))) env))
in (match (_57_1979) with
| (env, lbs) -> begin
(
# 1375 "FStar.TypeChecker.Tc.fst"
let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (
# 1377 "FStar.TypeChecker.Tc.fst"
let _57_1985 = (tc_term env e2)
in (match (_57_1985) with
| (e2, cres, g2) -> begin
(
# 1378 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (
# 1379 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (
# 1380 "FStar.TypeChecker.Tc.fst"
let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (
# 1381 "FStar.TypeChecker.Tc.fst"
let cres = (
# 1381 "FStar.TypeChecker.Tc.fst"
let _57_1989 = cres
in {FStar_Syntax_Syntax.eff_name = _57_1989.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _57_1989.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_1989.FStar_Syntax_Syntax.comp})
in (
# 1383 "FStar.TypeChecker.Tc.fst"
let _57_1994 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1994) with
| (lbs, e2) -> begin
(
# 1384 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_57_1997) -> begin
(e, cres, guard)
end
| None -> begin
(
# 1388 "FStar.TypeChecker.Tc.fst"
let _57_2000 = (check_no_escape None env bvs tres)
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
| _57_2003 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (
# 1399 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1400 "FStar.TypeChecker.Tc.fst"
let _57_2036 = (FStar_List.fold_left (fun _57_2010 lb -> (match (_57_2010) with
| (lbs, env) -> begin
(
# 1401 "FStar.TypeChecker.Tc.fst"
let _57_2015 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_57_2015) with
| (univ_vars, t, check_t) -> begin
(
# 1402 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (
# 1403 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (
# 1404 "FStar.TypeChecker.Tc.fst"
let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(
# 1409 "FStar.TypeChecker.Tc.fst"
let _57_2024 = (let _146_731 = (let _146_730 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _146_730))
in (tc_check_tot_or_gtot_term (
# 1409 "FStar.TypeChecker.Tc.fst"
let _57_2018 = env0
in {FStar_TypeChecker_Env.solver = _57_2018.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2018.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2018.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2018.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2018.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2018.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2018.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2018.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2018.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2018.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2018.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2018.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2018.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2018.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _57_2018.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2018.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2018.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2018.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2018.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2018.FStar_TypeChecker_Env.use_bv_sorts}) t _146_731))
in (match (_57_2024) with
| (t, _57_2022, g) -> begin
(
# 1410 "FStar.TypeChecker.Tc.fst"
let _57_2025 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (
# 1412 "FStar.TypeChecker.Tc.fst"
let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(
# 1414 "FStar.TypeChecker.Tc.fst"
let _57_2028 = env
in {FStar_TypeChecker_Env.solver = _57_2028.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2028.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2028.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2028.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2028.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2028.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2028.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2028.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2028.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2028.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2028.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2028.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2028.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_2028.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2028.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2028.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2028.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2028.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2028.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2028.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (
# 1416 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1416 "FStar.TypeChecker.Tc.fst"
let _57_2031 = lb
in {FStar_Syntax_Syntax.lbname = _57_2031.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _57_2031.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_57_2036) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (
# 1423 "FStar.TypeChecker.Tc.fst"
let _57_2049 = (let _146_736 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 1424 "FStar.TypeChecker.Tc.fst"
let _57_2043 = (let _146_735 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _146_735 lb.FStar_Syntax_Syntax.lbdef))
in (match (_57_2043) with
| (e, c, g) -> begin
(
# 1425 "FStar.TypeChecker.Tc.fst"
let _57_2044 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1427 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _146_736 FStar_List.unzip))
in (match (_57_2049) with
| (lbs, gs) -> begin
(
# 1429 "FStar.TypeChecker.Tc.fst"
let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (
# 1443 "FStar.TypeChecker.Tc.fst"
let _57_2057 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_2057) with
| (env1, _57_2056) -> begin
(
# 1444 "FStar.TypeChecker.Tc.fst"
let e1 = lb.FStar_Syntax_Syntax.lbdef
in (
# 1447 "FStar.TypeChecker.Tc.fst"
let _57_2063 = (check_lbtyp top_level env lb)
in (match (_57_2063) with
| (topt, wf_annot, univ_vars, env1) -> begin
(
# 1449 "FStar.TypeChecker.Tc.fst"
let _57_2064 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1453 "FStar.TypeChecker.Tc.fst"
let _57_2071 = (tc_maybe_toplevel_term (
# 1453 "FStar.TypeChecker.Tc.fst"
let _57_2066 = env1
in {FStar_TypeChecker_Env.solver = _57_2066.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2066.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2066.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2066.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2066.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2066.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2066.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2066.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2066.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2066.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2066.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2066.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2066.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _57_2066.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2066.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2066.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2066.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2066.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2066.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2066.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_57_2071) with
| (e1, c1, g1) -> begin
(
# 1456 "FStar.TypeChecker.Tc.fst"
let _57_2075 = (let _146_743 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_2072 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _146_743 e1 c1 wf_annot))
in (match (_57_2075) with
| (c1, guard_f) -> begin
(
# 1459 "FStar.TypeChecker.Tc.fst"
let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (
# 1461 "FStar.TypeChecker.Tc.fst"
let _57_2077 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_744 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _146_744))
end else begin
()
end
in (let _146_745 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _146_745))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (
# 1473 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 1476 "FStar.TypeChecker.Tc.fst"
let _57_2084 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _57_2087 -> begin
(
# 1480 "FStar.TypeChecker.Tc.fst"
let _57_2090 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_57_2090) with
| (univ_vars, t) -> begin
(
# 1481 "FStar.TypeChecker.Tc.fst"
let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _146_749 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _146_749))
end else begin
(
# 1488 "FStar.TypeChecker.Tc.fst"
let _57_2095 = (FStar_Syntax_Util.type_u ())
in (match (_57_2095) with
| (k, _57_2094) -> begin
(
# 1489 "FStar.TypeChecker.Tc.fst"
let _57_2100 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_57_2100) with
| (t, _57_2098, g) -> begin
(
# 1490 "FStar.TypeChecker.Tc.fst"
let _57_2101 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _146_752 = (let _146_750 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _146_750))
in (let _146_751 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _146_752 _146_751)))
end else begin
()
end
in (
# 1494 "FStar.TypeChecker.Tc.fst"
let t = (norm env1 t)
in (let _146_753 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _146_753))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _57_2107 -> (match (_57_2107) with
| (x, imp) -> begin
(
# 1499 "FStar.TypeChecker.Tc.fst"
let _57_2110 = (FStar_Syntax_Util.type_u ())
in (match (_57_2110) with
| (tu, u) -> begin
(
# 1500 "FStar.TypeChecker.Tc.fst"
let _57_2115 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_57_2115) with
| (t, _57_2113, g) -> begin
(
# 1501 "FStar.TypeChecker.Tc.fst"
let x = ((
# 1501 "FStar.TypeChecker.Tc.fst"
let _57_2116 = x
in {FStar_Syntax_Syntax.ppname = _57_2116.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2116.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (
# 1502 "FStar.TypeChecker.Tc.fst"
let _57_2119 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_757 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _146_756 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _146_757 _146_756)))
end else begin
()
end
in (let _146_758 = (maybe_push_binding env x)
in (x, _146_758, g, u))))
end))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe Prims.list) = (fun env bs -> (
# 1507 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_TypeChecker_Rel.trivial_guard, [])
end
| b::bs -> begin
(
# 1510 "FStar.TypeChecker.Tc.fst"
let _57_2134 = (tc_binder env b)
in (match (_57_2134) with
| (b, env', g, u) -> begin
(
# 1511 "FStar.TypeChecker.Tc.fst"
let _57_2139 = (aux env' bs)
in (match (_57_2139) with
| (bs, env', g', us) -> begin
(let _146_766 = (let _146_765 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _146_765))
in ((b)::bs, env', _146_766, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (
# 1516 "FStar.TypeChecker.Tc.fst"
let tc_args = (fun env args -> (FStar_List.fold_right (fun _57_2147 _57_2150 -> (match ((_57_2147, _57_2150)) with
| ((t, imp), (args, g)) -> begin
(
# 1520 "FStar.TypeChecker.Tc.fst"
let _57_2155 = (tc_term env t)
in (match (_57_2155) with
| (t, _57_2153, g') -> begin
(let _146_775 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _146_775))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _57_2159 -> (match (_57_2159) with
| (pats, g) -> begin
(
# 1523 "FStar.TypeChecker.Tc.fst"
let _57_2162 = (tc_args env p)
in (match (_57_2162) with
| (args, g') -> begin
(let _146_778 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _146_778))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1528 "FStar.TypeChecker.Tc.fst"
let _57_2168 = (tc_maybe_toplevel_term env e)
in (match (_57_2168) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(
# 1531 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (
# 1532 "FStar.TypeChecker.Tc.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 1533 "FStar.TypeChecker.Tc.fst"
let _57_2171 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_781 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _146_781))
end else begin
()
end
in (
# 1534 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 1535 "FStar.TypeChecker.Tc.fst"
let _57_2176 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _146_782 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_146_782, false))
end else begin
(let _146_783 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_146_783, true))
end
in (match (_57_2176) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _146_784 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _146_784))
end
| _57_2180 -> begin
if allow_ghost then begin
(let _146_787 = (let _146_786 = (let _146_785 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_146_785, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_786))
in (Prims.raise _146_787))
end else begin
(let _146_790 = (let _146_789 = (let _146_788 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_146_788, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_789))
in (Prims.raise _146_790))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 1549 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))

# 1553 "FStar.TypeChecker.Tc.fst"
let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (
# 1554 "FStar.TypeChecker.Tc.fst"
let _57_2190 = (tc_tot_or_gtot_term env t)
in (match (_57_2190) with
| (t, c, g) -> begin
(
# 1555 "FStar.TypeChecker.Tc.fst"
let _57_2191 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))

# 1558 "FStar.TypeChecker.Tc.fst"
let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (
# 1559 "FStar.TypeChecker.Tc.fst"
let _57_2199 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_2199) with
| (t, c, g) -> begin
(
# 1560 "FStar.TypeChecker.Tc.fst"
let _57_2200 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))

# 1563 "FStar.TypeChecker.Tc.fst"
let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _146_810 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _146_810)))

# 1568 "FStar.TypeChecker.Tc.fst"
let check_nogen = (fun env t k -> (
# 1569 "FStar.TypeChecker.Tc.fst"
let t = (tc_check_trivial_guard env t k)
in (let _146_814 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _146_814))))

# 1572 "FStar.TypeChecker.Tc.fst"
let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (
# 1573 "FStar.TypeChecker.Tc.fst"
let _57_2215 = (tc_binders env tps)
in (match (_57_2215) with
| (tps, env, g, us) -> begin
(
# 1574 "FStar.TypeChecker.Tc.fst"
let _57_2216 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))

# 1577 "FStar.TypeChecker.Tc.fst"
let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (
# 1578 "FStar.TypeChecker.Tc.fst"
let fail = (fun _57_2222 -> (match (()) with
| () -> begin
(let _146_829 = (let _146_828 = (let _146_827 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_146_827, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_146_828))
in (Prims.raise _146_829))
end))
in (
# 1579 "FStar.TypeChecker.Tc.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1582 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _57_2239)::(wp, _57_2235)::(_wlp, _57_2231)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2243 -> begin
(fail ())
end))
end
| _57_2245 -> begin
(fail ())
end))))

# 1589 "FStar.TypeChecker.Tc.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 1592 "FStar.TypeChecker.Tc.fst"
let _57_2252 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_57_2252) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _57_2254 -> begin
(
# 1595 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow binders c)
in (
# 1596 "FStar.TypeChecker.Tc.fst"
let _57_2258 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_57_2258) with
| (uvs, t') -> begin
(match ((let _146_836 = (FStar_Syntax_Subst.compress t')
in _146_836.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _57_2264 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 1601 "FStar.TypeChecker.Tc.fst"
let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (
# 1602 "FStar.TypeChecker.Tc.fst"
let fail = (fun t -> (let _146_847 = (let _146_846 = (let _146_845 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_146_845, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_146_846))
in (Prims.raise _146_847)))
in (match ((let _146_848 = (FStar_Syntax_Subst.compress signature)
in _146_848.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1605 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _57_2285)::(wp, _57_2281)::(_wlp, _57_2277)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2289 -> begin
(fail signature)
end))
end
| _57_2291 -> begin
(fail signature)
end)))

# 1612 "FStar.TypeChecker.Tc.fst"
let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (
# 1613 "FStar.TypeChecker.Tc.fst"
let _57_2296 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_57_2296) with
| (a, wp) -> begin
(
# 1614 "FStar.TypeChecker.Tc.fst"
let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _57_2299 -> begin
(
# 1618 "FStar.TypeChecker.Tc.fst"
let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (
# 1619 "FStar.TypeChecker.Tc.fst"
let op = (fun ts -> (
# 1620 "FStar.TypeChecker.Tc.fst"
let _57_2303 = ()
in (
# 1621 "FStar.TypeChecker.Tc.fst"
let t0 = (Prims.snd ts)
in (
# 1622 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (
# 1624 "FStar.TypeChecker.Tc.fst"
let _57_2307 = ed
in (let _146_867 = (op ed.FStar_Syntax_Syntax.ret)
in (let _146_866 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _146_865 = (op ed.FStar_Syntax_Syntax.bind_wlp)
in (let _146_864 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _146_863 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _146_862 = (op ed.FStar_Syntax_Syntax.ite_wlp)
in (let _146_861 = (op ed.FStar_Syntax_Syntax.wp_binop)
in (let _146_860 = (op ed.FStar_Syntax_Syntax.wp_as_type)
in (let _146_859 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _146_858 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _146_857 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _146_856 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _146_855 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _57_2307.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2307.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2307.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2307.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2307.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _146_867; FStar_Syntax_Syntax.bind_wp = _146_866; FStar_Syntax_Syntax.bind_wlp = _146_865; FStar_Syntax_Syntax.if_then_else = _146_864; FStar_Syntax_Syntax.ite_wp = _146_863; FStar_Syntax_Syntax.ite_wlp = _146_862; FStar_Syntax_Syntax.wp_binop = _146_861; FStar_Syntax_Syntax.wp_as_type = _146_860; FStar_Syntax_Syntax.close_wp = _146_859; FStar_Syntax_Syntax.assert_p = _146_858; FStar_Syntax_Syntax.assume_p = _146_857; FStar_Syntax_Syntax.null_wp = _146_856; FStar_Syntax_Syntax.trivial = _146_855}))))))))))))))))
end)
in (ed, a, wp))
end)))

# 1640 "FStar.TypeChecker.Tc.fst"
let gen_wps_for_free : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env binders a wp_a ed -> (
# 1645 "FStar.TypeChecker.Tc.fst"
let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env)
in (
# 1647 "FStar.TypeChecker.Tc.fst"
let d = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))
in (
# 1648 "FStar.TypeChecker.Tc.fst"
let normalize_and_make_binders_explicit = (fun tm -> (
# 1649 "FStar.TypeChecker.Tc.fst"
let tm = (normalize tm)
in (
# 1650 "FStar.TypeChecker.Tc.fst"
let rec visit_term = (fun tm -> (
# 1651 "FStar.TypeChecker.Tc.fst"
let n = (match ((let _146_889 = (FStar_Syntax_Subst.compress tm)
in _146_889.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(
# 1653 "FStar.TypeChecker.Tc.fst"
let comp = (visit_comp comp)
in (
# 1654 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map visit_binder binders)
in FStar_Syntax_Syntax.Tm_arrow ((binders, comp))))
end
| FStar_Syntax_Syntax.Tm_abs (binders, term, comp) -> begin
(
# 1657 "FStar.TypeChecker.Tc.fst"
let comp = (visit_maybe_lcomp comp)
in (
# 1658 "FStar.TypeChecker.Tc.fst"
let term = (visit_term term)
in (
# 1659 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map visit_binder binders)
in FStar_Syntax_Syntax.Tm_abs ((binders, term, comp)))))
end
| _57_2342 -> begin
tm.FStar_Syntax_Syntax.n
end)
in (
# 1664 "FStar.TypeChecker.Tc.fst"
let _57_2344 = tm
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2344.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2344.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2344.FStar_Syntax_Syntax.vars})))
and visit_binder = (fun _57_2348 -> (match (_57_2348) with
| (bv, a) -> begin
(let _146_893 = (
# 1666 "FStar.TypeChecker.Tc.fst"
let _57_2349 = bv
in (let _146_891 = (visit_term bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_2349.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2349.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_891}))
in (let _146_892 = (FStar_Syntax_Syntax.as_implicit false)
in (_146_893, _146_892)))
end))
and visit_maybe_lcomp = (fun lcomp -> (match (lcomp) with
| Some (FStar_Util.Inl (lcomp)) -> begin
(let _146_898 = (let _146_897 = (let _146_896 = (let _146_895 = (lcomp.FStar_Syntax_Syntax.comp ())
in (visit_comp _146_895))
in (FStar_Syntax_Util.lcomp_of_comp _146_896))
in FStar_Util.Inl (_146_897))
in Some (_146_898))
end
| comp -> begin
comp
end))
and visit_comp = (fun comp -> (
# 1674 "FStar.TypeChecker.Tc.fst"
let n = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tm) -> begin
(let _146_900 = (visit_term tm)
in FStar_Syntax_Syntax.Total (_146_900))
end
| FStar_Syntax_Syntax.GTotal (tm) -> begin
(let _146_901 = (visit_term tm)
in FStar_Syntax_Syntax.GTotal (_146_901))
end
| comp -> begin
comp
end)
in (
# 1682 "FStar.TypeChecker.Tc.fst"
let _57_2363 = comp
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2363.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2363.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2363.FStar_Syntax_Syntax.vars})))
and visit_args = (fun args -> (FStar_List.map (fun _57_2368 -> (match (_57_2368) with
| (tm, q) -> begin
(let _146_904 = (visit_term tm)
in (_146_904, q))
end)) args))
in (visit_term tm))))
in (
# 1690 "FStar.TypeChecker.Tc.fst"
let check = (fun str t -> if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(
# 1692 "FStar.TypeChecker.Tc.fst"
let _57_2372 = (let _146_909 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Generated term for %s: %s\n" str _146_909))
in (
# 1693 "FStar.TypeChecker.Tc.fst"
let t = (normalize t)
in (
# 1694 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 1695 "FStar.TypeChecker.Tc.fst"
let _57_2387 = (tc_term env t)
in (match (_57_2387) with
| (e, {FStar_Syntax_Syntax.eff_name = _57_2383; FStar_Syntax_Syntax.res_typ = res_typ; FStar_Syntax_Syntax.cflags = _57_2380; FStar_Syntax_Syntax.comp = _57_2378}, _57_2386) -> begin
(
# 1696 "FStar.TypeChecker.Tc.fst"
let _57_2388 = (let _146_912 = (let _146_911 = (normalize res_typ)
in (FStar_Syntax_Print.term_to_string _146_911))
in (FStar_Util.print2 "Inferred type for %s: %s\n" str _146_912))
in (let _146_914 = (let _146_913 = (normalize e)
in (FStar_Syntax_Print.term_to_string _146_913))
in (FStar_Util.print2 "Elaborated term for %s: %s\n" str _146_914)))
end)))))
end else begin
()
end)
in (
# 1712 "FStar.TypeChecker.Tc.fst"
let rec collect_binders = (fun t -> (match ((let _146_917 = (FStar_Syntax_Subst.compress t)
in _146_917.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(
# 1715 "FStar.TypeChecker.Tc.fst"
let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
t
end
| _57_2399 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _146_918 = (collect_binders rest)
in (FStar_List.append bs _146_918)))
end
| FStar_Syntax_Syntax.Tm_type (_57_2402) -> begin
[]
end
| _57_2405 -> begin
(FStar_All.failwith "wp_a doesn\'t end in Type0")
end))
in (
# 1724 "FStar.TypeChecker.Tc.fst"
let _57_2420 = (
# 1725 "FStar.TypeChecker.Tc.fst"
let i = (FStar_ST.alloc 0)
in (
# 1726 "FStar.TypeChecker.Tc.fst"
let wp_binders = (let _146_925 = (normalize wp_a)
in (collect_binders _146_925))
in ((fun t -> (let _146_931 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow wp_binders _146_931))), (fun t -> (let _146_934 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow wp_binders _146_934))), (fun _57_2410 -> (match (()) with
| () -> begin
(FStar_List.map (fun _57_2414 -> (match (_57_2414) with
| (bv, _57_2413) -> begin
(
# 1735 "FStar.TypeChecker.Tc.fst"
let _57_2415 = (let _146_938 = ((FStar_ST.read i) + 1)
in (FStar_ST.op_Colon_Equals i _146_938))
in (let _146_941 = (let _146_940 = (let _146_939 = (FStar_ST.read i)
in (FStar_Util.string_of_int _146_939))
in (Prims.strcat "g" _146_940))
in (FStar_Syntax_Syntax.gen_bv _146_941 None bv.FStar_Syntax_Syntax.sort)))
end)) wp_binders)
end)))))
in (match (_57_2420) with
| (mk_ctx, mk_gctx, mk_gamma) -> begin
(
# 1741 "FStar.TypeChecker.Tc.fst"
let binders_of_list = (FStar_List.map (fun _57_2423 -> (match (_57_2423) with
| (t, b) -> begin
(let _146_947 = (FStar_Syntax_Syntax.as_implicit b)
in (t, _146_947))
end)))
in (
# 1743 "FStar.TypeChecker.Tc.fst"
let implicit_binders_of_list = (FStar_List.map (fun t -> (let _146_950 = (FStar_Syntax_Syntax.as_implicit true)
in (t, _146_950))))
in (
# 1745 "FStar.TypeChecker.Tc.fst"
let args_of_bv = (FStar_List.map (fun bv -> (let _146_953 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_Syntax_Syntax.as_arg _146_953))))
in (
# 1750 "FStar.TypeChecker.Tc.fst"
let c_pure = (
# 1751 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (
# 1752 "FStar.TypeChecker.Tc.fst"
let x = (let _146_954 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _146_954))
in (
# 1753 "FStar.TypeChecker.Tc.fst"
let ret = (let _146_959 = (let _146_958 = (let _146_957 = (let _146_956 = (let _146_955 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx _146_955))
in (FStar_Syntax_Syntax.mk_Total _146_956))
in (FStar_Syntax_Util.lcomp_of_comp _146_957))
in FStar_Util.Inl (_146_958))
in Some (_146_959))
in (
# 1754 "FStar.TypeChecker.Tc.fst"
let gamma = (mk_gamma ())
in (
# 1755 "FStar.TypeChecker.Tc.fst"
let body = (let _146_961 = (implicit_binders_of_list gamma)
in (let _146_960 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs _146_961 _146_960 ret)))
in (let _146_962 = (binders_of_list (((t, true))::((x, false))::[]))
in (FStar_Syntax_Util.abs _146_962 body ret)))))))
in (
# 1758 "FStar.TypeChecker.Tc.fst"
let _57_2435 = (let _146_966 = (let _146_965 = (let _146_964 = (let _146_963 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_963)::[])
in (FStar_List.append binders _146_964))
in (FStar_Syntax_Util.abs _146_965 c_pure None))
in (check "pure" _146_966))
in (
# 1765 "FStar.TypeChecker.Tc.fst"
let c_app = (
# 1766 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (
# 1767 "FStar.TypeChecker.Tc.fst"
let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (
# 1768 "FStar.TypeChecker.Tc.fst"
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
# 1771 "FStar.TypeChecker.Tc.fst"
let r = (let _146_976 = (let _146_975 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _146_975))
in (FStar_Syntax_Syntax.gen_bv "r" None _146_976))
in (
# 1772 "FStar.TypeChecker.Tc.fst"
let ret = (let _146_981 = (let _146_980 = (let _146_979 = (let _146_978 = (let _146_977 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_977))
in (FStar_Syntax_Syntax.mk_Total _146_978))
in (FStar_Syntax_Util.lcomp_of_comp _146_979))
in FStar_Util.Inl (_146_980))
in Some (_146_981))
in (
# 1773 "FStar.TypeChecker.Tc.fst"
let outer_body = (
# 1774 "FStar.TypeChecker.Tc.fst"
let gamma = (mk_gamma ())
in (
# 1775 "FStar.TypeChecker.Tc.fst"
let gamma_as_args = (args_of_bv gamma)
in (
# 1776 "FStar.TypeChecker.Tc.fst"
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
# 1785 "FStar.TypeChecker.Tc.fst"
let _57_2447 = (let _146_993 = (let _146_992 = (let _146_991 = (let _146_990 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_990)::[])
in (FStar_List.append binders _146_991))
in (FStar_Syntax_Util.abs _146_992 c_app None))
in (check "app" _146_993))
in (
# 1794 "FStar.TypeChecker.Tc.fst"
let unknown = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (
# 1795 "FStar.TypeChecker.Tc.fst"
let c_lift1 = (
# 1796 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (
# 1797 "FStar.TypeChecker.Tc.fst"
let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (
# 1798 "FStar.TypeChecker.Tc.fst"
let t_f = (let _146_998 = (let _146_995 = (let _146_994 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_994))
in (_146_995)::[])
in (let _146_997 = (let _146_996 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _146_996))
in (FStar_Syntax_Util.arrow _146_998 _146_997)))
in (
# 1799 "FStar.TypeChecker.Tc.fst"
let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (
# 1800 "FStar.TypeChecker.Tc.fst"
let a1 = (let _146_1000 = (let _146_999 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _146_999))
in (FStar_Syntax_Syntax.gen_bv "a1" None _146_1000))
in (
# 1801 "FStar.TypeChecker.Tc.fst"
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
# 1809 "FStar.TypeChecker.Tc.fst"
let _57_2457 = (let _146_1022 = (let _146_1021 = (let _146_1020 = (let _146_1019 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1019)::[])
in (FStar_List.append binders _146_1020))
in (FStar_Syntax_Util.abs _146_1021 c_lift1 None))
in (check "lift1" _146_1022))
in (
# 1820 "FStar.TypeChecker.Tc.fst"
let c_lift2 = (
# 1821 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (
# 1822 "FStar.TypeChecker.Tc.fst"
let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (
# 1823 "FStar.TypeChecker.Tc.fst"
let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (
# 1824 "FStar.TypeChecker.Tc.fst"
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
# 1828 "FStar.TypeChecker.Tc.fst"
let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (
# 1829 "FStar.TypeChecker.Tc.fst"
let a1 = (let _146_1032 = (let _146_1031 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _146_1031))
in (FStar_Syntax_Syntax.gen_bv "a1" None _146_1032))
in (
# 1830 "FStar.TypeChecker.Tc.fst"
let a2 = (let _146_1034 = (let _146_1033 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_1033))
in (FStar_Syntax_Syntax.gen_bv "a2" None _146_1034))
in (
# 1831 "FStar.TypeChecker.Tc.fst"
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
# 1842 "FStar.TypeChecker.Tc.fst"
let _57_2468 = (let _146_1063 = (let _146_1062 = (let _146_1061 = (let _146_1060 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1060)::[])
in (FStar_List.append binders _146_1061))
in (FStar_Syntax_Util.abs _146_1062 c_lift2 None))
in (check "lift2" _146_1063))
in (
# 1848 "FStar.TypeChecker.Tc.fst"
let c_push = (
# 1849 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (
# 1850 "FStar.TypeChecker.Tc.fst"
let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (
# 1851 "FStar.TypeChecker.Tc.fst"
let t_f = (let _146_1069 = (let _146_1065 = (let _146_1064 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_1064))
in (_146_1065)::[])
in (let _146_1068 = (let _146_1067 = (let _146_1066 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_1066))
in (FStar_Syntax_Syntax.mk_Total _146_1067))
in (FStar_Syntax_Util.arrow _146_1069 _146_1068)))
in (
# 1855 "FStar.TypeChecker.Tc.fst"
let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (
# 1856 "FStar.TypeChecker.Tc.fst"
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
# 1859 "FStar.TypeChecker.Tc.fst"
let e1 = (let _146_1080 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _146_1080))
in (
# 1860 "FStar.TypeChecker.Tc.fst"
let gamma = (mk_gamma ())
in (
# 1861 "FStar.TypeChecker.Tc.fst"
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
# 1866 "FStar.TypeChecker.Tc.fst"
let _57_2479 = (let _146_1095 = (let _146_1094 = (let _146_1093 = (let _146_1092 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1092)::[])
in (FStar_List.append binders _146_1093))
in (FStar_Syntax_Util.abs _146_1094 c_push None))
in (check "push" _146_1095))
in (
# 1868 "FStar.TypeChecker.Tc.fst"
let ret_tot_wp_a = (let _146_1098 = (let _146_1097 = (let _146_1096 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _146_1096))
in FStar_Util.Inl (_146_1097))
in Some (_146_1098))
in (
# 1874 "FStar.TypeChecker.Tc.fst"
let wp_if_then_else = (
# 1875 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _146_1109 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (let _146_1108 = (
# 1880 "FStar.TypeChecker.Tc.fst"
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
# 1888 "FStar.TypeChecker.Tc.fst"
let wp_if_then_else = (normalize_and_make_binders_explicit wp_if_then_else)
in (
# 1889 "FStar.TypeChecker.Tc.fst"
let _57_2486 = (let _146_1110 = (FStar_Syntax_Util.abs binders wp_if_then_else None)
in (check "wp_if_then_else" _146_1110))
in (
# 1895 "FStar.TypeChecker.Tc.fst"
let wp_binop = (
# 1896 "FStar.TypeChecker.Tc.fst"
let l = (FStar_Syntax_Syntax.gen_bv "l" None wp_a)
in (
# 1897 "FStar.TypeChecker.Tc.fst"
let op = (let _146_1116 = (let _146_1115 = (let _146_1113 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Util.ktype0)
in (let _146_1112 = (let _146_1111 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Util.ktype0)
in (_146_1111)::[])
in (_146_1113)::_146_1112))
in (let _146_1114 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _146_1115 _146_1114)))
in (FStar_Syntax_Syntax.gen_bv "op" None _146_1116))
in (
# 1900 "FStar.TypeChecker.Tc.fst"
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
# 1908 "FStar.TypeChecker.Tc.fst"
let wp_binop = (normalize_and_make_binders_explicit wp_binop)
in (
# 1909 "FStar.TypeChecker.Tc.fst"
let _57_2493 = (let _146_1129 = (FStar_Syntax_Util.abs binders wp_binop None)
in (check "wp_binop" _146_1129))
in (
# 1914 "FStar.TypeChecker.Tc.fst"
let wp_assert = (
# 1915 "FStar.TypeChecker.Tc.fst"
let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (
# 1916 "FStar.TypeChecker.Tc.fst"
let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (
# 1917 "FStar.TypeChecker.Tc.fst"
let l_and = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (
# 1918 "FStar.TypeChecker.Tc.fst"
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
# 1928 "FStar.TypeChecker.Tc.fst"
let wp_assert = (normalize_and_make_binders_explicit wp_assert)
in (
# 1929 "FStar.TypeChecker.Tc.fst"
let _57_2501 = (let _146_1145 = (FStar_Syntax_Util.abs binders wp_assert None)
in (check "wp_assert" _146_1145))
in (
# 1934 "FStar.TypeChecker.Tc.fst"
let wp_assume = (
# 1935 "FStar.TypeChecker.Tc.fst"
let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (
# 1936 "FStar.TypeChecker.Tc.fst"
let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (
# 1937 "FStar.TypeChecker.Tc.fst"
let l_imp = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (
# 1938 "FStar.TypeChecker.Tc.fst"
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
# 1948 "FStar.TypeChecker.Tc.fst"
let wp_assume = (normalize_and_make_binders_explicit wp_assume)
in (
# 1949 "FStar.TypeChecker.Tc.fst"
let _57_2509 = (let _146_1161 = (FStar_Syntax_Util.abs binders wp_assume None)
in (check "wp_assume" _146_1161))
in (
# 1951 "FStar.TypeChecker.Tc.fst"
let tforall = (let _146_1164 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _146_1163 = (let _146_1162 = (FStar_Syntax_Syntax.as_arg unknown)
in (_146_1162)::[])
in (FStar_Syntax_Util.mk_app _146_1164 _146_1163)))
in (
# 1957 "FStar.TypeChecker.Tc.fst"
let wp_close = (
# 1958 "FStar.TypeChecker.Tc.fst"
let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (
# 1959 "FStar.TypeChecker.Tc.fst"
let t_f = (let _146_1168 = (let _146_1166 = (let _146_1165 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _146_1165))
in (_146_1166)::[])
in (let _146_1167 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1168 _146_1167)))
in (
# 1960 "FStar.TypeChecker.Tc.fst"
let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (
# 1961 "FStar.TypeChecker.Tc.fst"
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
# 1973 "FStar.TypeChecker.Tc.fst"
let wp_close = (normalize_and_make_binders_explicit wp_close)
in (
# 1974 "FStar.TypeChecker.Tc.fst"
let _57_2518 = (let _146_1183 = (FStar_Syntax_Util.abs binders wp_close None)
in (check "wp_close" _146_1183))
in (
# 1976 "FStar.TypeChecker.Tc.fst"
let ret_tot_type0 = (let _146_1186 = (let _146_1185 = (let _146_1184 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_1184))
in FStar_Util.Inl (_146_1185))
in Some (_146_1186))
in (
# 1977 "FStar.TypeChecker.Tc.fst"
let mk_forall = (fun x body -> (
# 1978 "FStar.TypeChecker.Tc.fst"
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
# 1989 "FStar.TypeChecker.Tc.fst"
let rec mk_leq = (fun t x y -> (match ((let _146_1208 = (let _146_1207 = (FStar_Syntax_Subst.compress t)
in (normalize _146_1207))
in _146_1208.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_2530) -> begin
(FStar_Syntax_Util.mk_imp x y)
end
| (FStar_Syntax_Syntax.Tm_arrow (binder::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow (binder::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) when (FStar_Syntax_Syntax.is_null_binder binder) -> begin
(
# 1996 "FStar.TypeChecker.Tc.fst"
let a = (Prims.fst binder).FStar_Syntax_Syntax.sort
in (
# 1998 "FStar.TypeChecker.Tc.fst"
let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (
# 1999 "FStar.TypeChecker.Tc.fst"
let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (
# 2000 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1220 = (let _146_1210 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _146_1209 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_leq a _146_1210 _146_1209)))
in (let _146_1219 = (let _146_1218 = (let _146_1213 = (let _146_1212 = (let _146_1211 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _146_1211))
in (_146_1212)::[])
in (FStar_Syntax_Util.mk_app x _146_1213))
in (let _146_1217 = (let _146_1216 = (let _146_1215 = (let _146_1214 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _146_1214))
in (_146_1215)::[])
in (FStar_Syntax_Util.mk_app y _146_1216))
in (mk_leq b _146_1218 _146_1217)))
in (FStar_Syntax_Util.mk_imp _146_1220 _146_1219)))
in (let _146_1221 = (mk_forall a2 body)
in (mk_forall a1 _146_1221))))))
end
| FStar_Syntax_Syntax.Tm_arrow (binder::binders, comp) -> begin
(
# 2008 "FStar.TypeChecker.Tc.fst"
let t = (
# 2008 "FStar.TypeChecker.Tc.fst"
let _57_2566 = t
in (let _146_1225 = (let _146_1224 = (let _146_1223 = (let _146_1222 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _146_1222))
in ((binder)::[], _146_1223))
in FStar_Syntax_Syntax.Tm_arrow (_146_1224))
in {FStar_Syntax_Syntax.n = _146_1225; FStar_Syntax_Syntax.tk = _57_2566.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2566.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2566.FStar_Syntax_Syntax.vars}))
in (mk_leq t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_57_2570) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _57_2573 -> begin
(FStar_Syntax_Util.mk_eq t t x y)
end))
in (
# 2017 "FStar.TypeChecker.Tc.fst"
let stronger = (
# 2018 "FStar.TypeChecker.Tc.fst"
let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (
# 2019 "FStar.TypeChecker.Tc.fst"
let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (
# 2020 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1227 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _146_1226 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_leq wp_a _146_1227 _146_1226)))
in (let _146_1228 = (FStar_Syntax_Syntax.binders_of_list ((wp1)::(wp2)::[]))
in (FStar_Syntax_Util.abs _146_1228 body ret_tot_type0)))))
in (
# 2023 "FStar.TypeChecker.Tc.fst"
let _57_2578 = (let _146_1232 = (let _146_1231 = (let _146_1230 = (let _146_1229 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1229)::[])
in (FStar_List.append binders _146_1230))
in (FStar_Syntax_Util.abs _146_1231 stronger None))
in (check "stronger" _146_1232))
in (
# 2025 "FStar.TypeChecker.Tc.fst"
let null_wp = (Prims.snd ed.FStar_Syntax_Syntax.null_wp)
in (
# 2029 "FStar.TypeChecker.Tc.fst"
let wp_trivial = (
# 2030 "FStar.TypeChecker.Tc.fst"
let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (
# 2031 "FStar.TypeChecker.Tc.fst"
let body = (let _146_1240 = (let _146_1239 = (let _146_1238 = (let _146_1235 = (let _146_1234 = (let _146_1233 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _146_1233))
in (_146_1234)::[])
in (FStar_Syntax_Util.mk_app null_wp _146_1235))
in (let _146_1237 = (let _146_1236 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_146_1236)::[])
in (_146_1238)::_146_1237))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1239))
in (FStar_Syntax_Util.mk_app stronger _146_1240))
in (let _146_1241 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_Syntax_Util.abs _146_1241 body ret_tot_type0))))
in (
# 2037 "FStar.TypeChecker.Tc.fst"
let wp_trivial = (normalize_and_make_binders_explicit wp_trivial)
in (
# 2038 "FStar.TypeChecker.Tc.fst"
let _57_2585 = (let _146_1242 = (FStar_Syntax_Util.abs binders wp_trivial None)
in (check "wp_trivial" _146_1242))
in (
# 2040 "FStar.TypeChecker.Tc.fst"
let _57_2587 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2587.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2587.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2587.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2587.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2587.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _57_2587.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2587.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _57_2587.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = ([], wp_if_then_else); FStar_Syntax_Syntax.ite_wp = _57_2587.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _57_2587.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = ([], wp_binop); FStar_Syntax_Syntax.wp_as_type = _57_2587.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = ([], wp_close); FStar_Syntax_Syntax.assert_p = ([], wp_assert); FStar_Syntax_Syntax.assume_p = ([], wp_assume); FStar_Syntax_Syntax.null_wp = _57_2587.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = ([], wp_trivial)})))))))))))))))))))))))))))))))))))))))))
end))))))))

# 2050 "FStar.TypeChecker.Tc.fst"
let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  effect_cost  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed is_for_free -> (
# 2051 "FStar.TypeChecker.Tc.fst"
let _57_2592 = ()
in (
# 2052 "FStar.TypeChecker.Tc.fst"
let _57_2596 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_57_2596) with
| (binders_un, signature_un) -> begin
(
# 2053 "FStar.TypeChecker.Tc.fst"
let _57_2601 = (tc_tparams env0 binders_un)
in (match (_57_2601) with
| (binders, env, _57_2600) -> begin
(
# 2054 "FStar.TypeChecker.Tc.fst"
let _57_2605 = (tc_trivial_guard env signature_un)
in (match (_57_2605) with
| (signature, _57_2604) -> begin
(
# 2055 "FStar.TypeChecker.Tc.fst"
let ed = (
# 2055 "FStar.TypeChecker.Tc.fst"
let _57_2606 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2606.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2606.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2606.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _57_2606.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2606.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _57_2606.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = _57_2606.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _57_2606.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _57_2606.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = _57_2606.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _57_2606.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _57_2606.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _57_2606.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _57_2606.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _57_2606.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _57_2606.FStar_Syntax_Syntax.trivial})
in (
# 2058 "FStar.TypeChecker.Tc.fst"
let _57_2612 = (open_effect_decl env ed)
in (match (_57_2612) with
| (ed, a, wp_a) -> begin
(
# 2059 "FStar.TypeChecker.Tc.fst"
let get_effect_signature = (fun _57_2614 -> (match (()) with
| () -> begin
(
# 2060 "FStar.TypeChecker.Tc.fst"
let _57_2618 = (tc_trivial_guard env signature_un)
in (match (_57_2618) with
| (signature, _57_2617) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (
# 2064 "FStar.TypeChecker.Tc.fst"
let env = (let _146_1251 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _146_1251))
in (
# 2066 "FStar.TypeChecker.Tc.fst"
let _57_2620 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _146_1254 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _146_1253 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _146_1252 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checking effect signature: %s %s : %s\n" _146_1254 _146_1253 _146_1252))))
end else begin
()
end
in (
# 2072 "FStar.TypeChecker.Tc.fst"
let check_and_gen' = (fun env _57_2627 k -> (match (_57_2627) with
| (_57_2625, t) -> begin
(check_and_gen env t k)
end))
in (
# 2076 "FStar.TypeChecker.Tc.fst"
let ed = (match (is_for_free) with
| NotForFree -> begin
ed
end
| ForFree -> begin
(gen_wps_for_free env binders a wp_a ed)
end)
in (
# 2081 "FStar.TypeChecker.Tc.fst"
let ret = (
# 2082 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1266 = (let _146_1264 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1263 = (let _146_1262 = (let _146_1261 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_1261))
in (_146_1262)::[])
in (_146_1264)::_146_1263))
in (let _146_1265 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _146_1266 _146_1265)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (
# 2085 "FStar.TypeChecker.Tc.fst"
let bind_wp = (
# 2086 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 2087 "FStar.TypeChecker.Tc.fst"
let _57_2637 = (get_effect_signature ())
in (match (_57_2637) with
| (b, wp_b) -> begin
(
# 2088 "FStar.TypeChecker.Tc.fst"
let a_wp_b = (let _146_1270 = (let _146_1268 = (let _146_1267 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_1267))
in (_146_1268)::[])
in (let _146_1269 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _146_1270 _146_1269)))
in (
# 2089 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = a_wp_b
in (
# 2090 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1285 = (let _146_1283 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _146_1282 = (let _146_1281 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1280 = (let _146_1279 = (FStar_Syntax_Syntax.mk_binder b)
in (let _146_1278 = (let _146_1277 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_1276 = (let _146_1275 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _146_1274 = (let _146_1273 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (let _146_1272 = (let _146_1271 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_146_1271)::[])
in (_146_1273)::_146_1272))
in (_146_1275)::_146_1274))
in (_146_1277)::_146_1276))
in (_146_1279)::_146_1278))
in (_146_1281)::_146_1280))
in (_146_1283)::_146_1282))
in (let _146_1284 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _146_1285 _146_1284)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k))))
end)))
in (
# 2097 "FStar.TypeChecker.Tc.fst"
let bind_wlp = (
# 2098 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 2099 "FStar.TypeChecker.Tc.fst"
let _57_2645 = (get_effect_signature ())
in (match (_57_2645) with
| (b, wlp_b) -> begin
(
# 2100 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = (let _146_1289 = (let _146_1287 = (let _146_1286 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_1286))
in (_146_1287)::[])
in (let _146_1288 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _146_1289 _146_1288)))
in (
# 2101 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1300 = (let _146_1298 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _146_1297 = (let _146_1296 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1295 = (let _146_1294 = (FStar_Syntax_Syntax.mk_binder b)
in (let _146_1293 = (let _146_1292 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _146_1291 = (let _146_1290 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_146_1290)::[])
in (_146_1292)::_146_1291))
in (_146_1294)::_146_1293))
in (_146_1296)::_146_1295))
in (_146_1298)::_146_1297))
in (let _146_1299 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _146_1300 _146_1299)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wlp expected_k)))
end)))
in (
# 2108 "FStar.TypeChecker.Tc.fst"
let if_then_else = (
# 2109 "FStar.TypeChecker.Tc.fst"
let p = (let _146_1302 = (let _146_1301 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1301 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _146_1302))
in (
# 2110 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1311 = (let _146_1309 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1308 = (let _146_1307 = (FStar_Syntax_Syntax.mk_binder p)
in (let _146_1306 = (let _146_1305 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_1304 = (let _146_1303 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1303)::[])
in (_146_1305)::_146_1304))
in (_146_1307)::_146_1306))
in (_146_1309)::_146_1308))
in (let _146_1310 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1311 _146_1310)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (
# 2116 "FStar.TypeChecker.Tc.fst"
let ite_wp = (
# 2117 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 2118 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1318 = (let _146_1316 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1315 = (let _146_1314 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _146_1313 = (let _146_1312 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1312)::[])
in (_146_1314)::_146_1313))
in (_146_1316)::_146_1315))
in (let _146_1317 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1318 _146_1317)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k)))
in (
# 2124 "FStar.TypeChecker.Tc.fst"
let ite_wlp = (
# 2125 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 2126 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1323 = (let _146_1321 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1320 = (let _146_1319 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (_146_1319)::[])
in (_146_1321)::_146_1320))
in (let _146_1322 = (FStar_Syntax_Syntax.mk_Total wlp_a)
in (FStar_Syntax_Util.arrow _146_1323 _146_1322)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wlp expected_k)))
in (
# 2131 "FStar.TypeChecker.Tc.fst"
let wp_binop = (
# 2132 "FStar.TypeChecker.Tc.fst"
let bin_op = (
# 2133 "FStar.TypeChecker.Tc.fst"
let _57_2660 = (FStar_Syntax_Util.type_u ())
in (match (_57_2660) with
| (t1, u1) -> begin
(
# 2134 "FStar.TypeChecker.Tc.fst"
let _57_2663 = (FStar_Syntax_Util.type_u ())
in (match (_57_2663) with
| (t2, u2) -> begin
(
# 2135 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1324 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_max ((u1)::(u2)::[]))) None _146_1324))
in (let _146_1329 = (let _146_1327 = (FStar_Syntax_Syntax.null_binder t1)
in (let _146_1326 = (let _146_1325 = (FStar_Syntax_Syntax.null_binder t2)
in (_146_1325)::[])
in (_146_1327)::_146_1326))
in (let _146_1328 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _146_1329 _146_1328))))
end))
end))
in (
# 2137 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1338 = (let _146_1336 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1335 = (let _146_1334 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_1333 = (let _146_1332 = (FStar_Syntax_Syntax.null_binder bin_op)
in (let _146_1331 = (let _146_1330 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1330)::[])
in (_146_1332)::_146_1331))
in (_146_1334)::_146_1333))
in (_146_1336)::_146_1335))
in (let _146_1337 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1338 _146_1337)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_binop expected_k)))
in (
# 2144 "FStar.TypeChecker.Tc.fst"
let wp_as_type = (
# 2145 "FStar.TypeChecker.Tc.fst"
let _57_2671 = (FStar_Syntax_Util.type_u ())
in (match (_57_2671) with
| (t, _57_2670) -> begin
(
# 2146 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1343 = (let _146_1341 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1340 = (let _146_1339 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1339)::[])
in (_146_1341)::_146_1340))
in (let _146_1342 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _146_1343 _146_1342)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (
# 2151 "FStar.TypeChecker.Tc.fst"
let close_wp = (
# 2152 "FStar.TypeChecker.Tc.fst"
let b = (let _146_1345 = (let _146_1344 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1344 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _146_1345))
in (
# 2153 "FStar.TypeChecker.Tc.fst"
let b_wp_a = (let _146_1349 = (let _146_1347 = (let _146_1346 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _146_1346))
in (_146_1347)::[])
in (let _146_1348 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1349 _146_1348)))
in (
# 2154 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1356 = (let _146_1354 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1353 = (let _146_1352 = (FStar_Syntax_Syntax.mk_binder b)
in (let _146_1351 = (let _146_1350 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_146_1350)::[])
in (_146_1352)::_146_1351))
in (_146_1354)::_146_1353))
in (let _146_1355 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1356 _146_1355)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (
# 2158 "FStar.TypeChecker.Tc.fst"
let assert_p = (
# 2159 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1365 = (let _146_1363 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1362 = (let _146_1361 = (let _146_1358 = (let _146_1357 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1357 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _146_1358))
in (let _146_1360 = (let _146_1359 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1359)::[])
in (_146_1361)::_146_1360))
in (_146_1363)::_146_1362))
in (let _146_1364 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1365 _146_1364)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (
# 2165 "FStar.TypeChecker.Tc.fst"
let assume_p = (
# 2166 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1374 = (let _146_1372 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1371 = (let _146_1370 = (let _146_1367 = (let _146_1366 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1366 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _146_1367))
in (let _146_1369 = (let _146_1368 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1368)::[])
in (_146_1370)::_146_1369))
in (_146_1372)::_146_1371))
in (let _146_1373 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1374 _146_1373)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (
# 2172 "FStar.TypeChecker.Tc.fst"
let null_wp = (
# 2173 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1377 = (let _146_1375 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1375)::[])
in (let _146_1376 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1377 _146_1376)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (
# 2177 "FStar.TypeChecker.Tc.fst"
let trivial_wp = (
# 2178 "FStar.TypeChecker.Tc.fst"
let _57_2687 = (FStar_Syntax_Util.type_u ())
in (match (_57_2687) with
| (t, _57_2686) -> begin
(
# 2179 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1382 = (let _146_1380 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1379 = (let _146_1378 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1378)::[])
in (_146_1380)::_146_1379))
in (let _146_1381 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _146_1382 _146_1381)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (
# 2185 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1383 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _146_1383))
in (
# 2186 "FStar.TypeChecker.Tc.fst"
let _57_2693 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_57_2693) with
| (univs, t) -> begin
(
# 2187 "FStar.TypeChecker.Tc.fst"
let _57_2709 = (match ((let _146_1385 = (let _146_1384 = (FStar_Syntax_Subst.compress t)
in _146_1384.FStar_Syntax_Syntax.n)
in (binders, _146_1385))) with
| ([], _57_2696) -> begin
([], t)
end
| (_57_2699, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _57_2706 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_2709) with
| (binders, signature) -> begin
(
# 2191 "FStar.TypeChecker.Tc.fst"
let close = (fun n ts -> (
# 2192 "FStar.TypeChecker.Tc.fst"
let ts = (let _146_1390 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _146_1390))
in (
# 2193 "FStar.TypeChecker.Tc.fst"
let _57_2714 = ()
in ts)))
in (
# 2195 "FStar.TypeChecker.Tc.fst"
let ed = (
# 2195 "FStar.TypeChecker.Tc.fst"
let _57_2716 = ed
in (let _146_1403 = (close 0 ret)
in (let _146_1402 = (close 1 bind_wp)
in (let _146_1401 = (close 1 bind_wlp)
in (let _146_1400 = (close 0 if_then_else)
in (let _146_1399 = (close 0 ite_wp)
in (let _146_1398 = (close 0 ite_wlp)
in (let _146_1397 = (close 0 wp_binop)
in (let _146_1396 = (close 0 wp_as_type)
in (let _146_1395 = (close 1 close_wp)
in (let _146_1394 = (close 0 assert_p)
in (let _146_1393 = (close 0 assume_p)
in (let _146_1392 = (close 0 null_wp)
in (let _146_1391 = (close 0 trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _57_2716.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2716.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _146_1403; FStar_Syntax_Syntax.bind_wp = _146_1402; FStar_Syntax_Syntax.bind_wlp = _146_1401; FStar_Syntax_Syntax.if_then_else = _146_1400; FStar_Syntax_Syntax.ite_wp = _146_1399; FStar_Syntax_Syntax.ite_wlp = _146_1398; FStar_Syntax_Syntax.wp_binop = _146_1397; FStar_Syntax_Syntax.wp_as_type = _146_1396; FStar_Syntax_Syntax.close_wp = _146_1395; FStar_Syntax_Syntax.assert_p = _146_1394; FStar_Syntax_Syntax.assume_p = _146_1393; FStar_Syntax_Syntax.null_wp = _146_1392; FStar_Syntax_Syntax.trivial = _146_1391}))))))))))))))
in (
# 2213 "FStar.TypeChecker.Tc.fst"
let _57_2719 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1404 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _146_1404))
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

# 2217 "FStar.TypeChecker.Tc.fst"
let tc_lex_t = (fun env ses quals lids -> (
# 2224 "FStar.TypeChecker.Tc.fst"
let _57_2725 = ()
in (
# 2225 "FStar.TypeChecker.Tc.fst"
let _57_2733 = ()
in (match (ses) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _57_2762, _57_2764, [], r)::FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _57_2753, r1)::FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _57_2742, r2)::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(
# 2240 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (
# 2241 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (
# 2242 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (
# 2243 "FStar.TypeChecker.Tc.fst"
let tc = FStar_Syntax_Syntax.Sig_inductive_typ ((lex_t, (u)::[], [], t, [], (FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[], [], r))
in (
# 2245 "FStar.TypeChecker.Tc.fst"
let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (
# 2246 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (let _146_1412 = (let _146_1411 = (let _146_1410 = (let _146_1409 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _146_1409 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1410, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1411))
in (FStar_Syntax_Syntax.mk _146_1412 None r1))
in (
# 2247 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (
# 2248 "FStar.TypeChecker.Tc.fst"
let dc_lextop = FStar_Syntax_Syntax.Sig_datacon ((lex_top, (utop)::[], lex_top_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r1))
in (
# 2250 "FStar.TypeChecker.Tc.fst"
let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 2251 "FStar.TypeChecker.Tc.fst"
let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 2252 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (
# 2253 "FStar.TypeChecker.Tc.fst"
let a = (let _146_1413 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1413))
in (
# 2254 "FStar.TypeChecker.Tc.fst"
let hd = (let _146_1414 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1414))
in (
# 2255 "FStar.TypeChecker.Tc.fst"
let tl = (let _146_1419 = (let _146_1418 = (let _146_1417 = (let _146_1416 = (let _146_1415 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _146_1415 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1416, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1417))
in (FStar_Syntax_Syntax.mk _146_1418 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1419))
in (
# 2256 "FStar.TypeChecker.Tc.fst"
let res = (let _146_1423 = (let _146_1422 = (let _146_1421 = (let _146_1420 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _146_1420 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1421, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1422))
in (FStar_Syntax_Syntax.mk _146_1423 None r2))
in (let _146_1424 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _146_1424))))))
in (
# 2258 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (
# 2259 "FStar.TypeChecker.Tc.fst"
let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _146_1426 = (let _146_1425 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _146_1425))
in FStar_Syntax_Syntax.Sig_bundle (_146_1426)))))))))))))))
end
| _57_2788 -> begin
(let _146_1428 = (let _146_1427 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _146_1427))
in (FStar_All.failwith _146_1428))
end))))

# 2265 "FStar.TypeChecker.Tc.fst"
let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (
# 2328 "FStar.TypeChecker.Tc.fst"
let warn_positivity = (fun l r -> (let _146_1442 = (let _146_1441 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _146_1441))
in (FStar_TypeChecker_Errors.diag r _146_1442)))
in (
# 2330 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2333 "FStar.TypeChecker.Tc.fst"
let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(
# 2338 "FStar.TypeChecker.Tc.fst"
let _57_2810 = ()
in (
# 2339 "FStar.TypeChecker.Tc.fst"
let _57_2812 = (warn_positivity tc r)
in (
# 2340 "FStar.TypeChecker.Tc.fst"
let _57_2816 = (FStar_Syntax_Subst.open_term tps k)
in (match (_57_2816) with
| (tps, k) -> begin
(
# 2341 "FStar.TypeChecker.Tc.fst"
let _57_2820 = (tc_tparams env tps)
in (match (_57_2820) with
| (tps, env_tps, us) -> begin
(
# 2342 "FStar.TypeChecker.Tc.fst"
let _57_2823 = (FStar_Syntax_Util.arrow_formals k)
in (match (_57_2823) with
| (indices, t) -> begin
(
# 2343 "FStar.TypeChecker.Tc.fst"
let _57_2827 = (tc_tparams env_tps indices)
in (match (_57_2827) with
| (indices, env', us') -> begin
(
# 2344 "FStar.TypeChecker.Tc.fst"
let _57_2831 = (tc_trivial_guard env' t)
in (match (_57_2831) with
| (t, _57_2830) -> begin
(
# 2345 "FStar.TypeChecker.Tc.fst"
let k = (let _146_1447 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _146_1447))
in (
# 2346 "FStar.TypeChecker.Tc.fst"
let _57_2835 = (FStar_Syntax_Util.type_u ())
in (match (_57_2835) with
| (t_type, u) -> begin
(
# 2347 "FStar.TypeChecker.Tc.fst"
let _57_2836 = (let _146_1448 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _146_1448))
in (
# 2349 "FStar.TypeChecker.Tc.fst"
let t_tc = (let _146_1449 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _146_1449))
in (
# 2350 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 2351 "FStar.TypeChecker.Tc.fst"
let k = (FStar_Syntax_Subst.close tps k)
in (
# 2352 "FStar.TypeChecker.Tc.fst"
let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _146_1450 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) ([], t_tc))
in (_146_1450, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u)))))))
end)))
end))
end))
end))
end))
end))))
end
| _57_2843 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 2359 "FStar.TypeChecker.Tc.fst"
let positive_if_pure = (fun _57_2845 l -> ())
in (
# 2362 "FStar.TypeChecker.Tc.fst"
let tc_data = (fun env tcs _57_6 -> (match (_57_6) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(
# 2364 "FStar.TypeChecker.Tc.fst"
let _57_2862 = ()
in (
# 2366 "FStar.TypeChecker.Tc.fst"
let _57_2897 = (
# 2367 "FStar.TypeChecker.Tc.fst"
let tps_u_opt = (FStar_Util.find_map tcs (fun _57_2866 -> (match (_57_2866) with
| (se, u_tc) -> begin
if (let _146_1463 = (let _146_1462 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _146_1462))
in (FStar_Ident.lid_equals tc_lid _146_1463)) then begin
(
# 2369 "FStar.TypeChecker.Tc.fst"
let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2868, _57_2870, tps, _57_2873, _57_2875, _57_2877, _57_2879, _57_2881) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _57_2887 -> (match (_57_2887) with
| (x, _57_2886) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _57_2889 -> begin
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
in (match (_57_2897) with
| (tps, u_tc) -> begin
(
# 2382 "FStar.TypeChecker.Tc.fst"
let _57_2917 = (match ((let _146_1465 = (FStar_Syntax_Subst.compress t)
in _146_1465.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(
# 2387 "FStar.TypeChecker.Tc.fst"
let _57_2905 = (FStar_Util.first_N ntps bs)
in (match (_57_2905) with
| (_57_2903, bs') -> begin
(
# 2388 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (
# 2389 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _57_2911 -> (match (_57_2911) with
| (x, _57_2910) -> begin
FStar_Syntax_Syntax.Index2Name (((ntps - (1 + i)), x))
end))))
in (let _146_1468 = (FStar_Syntax_Subst.subst (FStar_Syntax_Syntax.Renaming (subst)) t)
in (FStar_Syntax_Util.arrow_formals _146_1468))))
end))
end
| _57_2914 -> begin
([], t)
end)
in (match (_57_2917) with
| (arguments, result) -> begin
(
# 2393 "FStar.TypeChecker.Tc.fst"
let _57_2918 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1471 = (FStar_Syntax_Print.lid_to_string c)
in (let _146_1470 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _146_1469 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _146_1471 _146_1470 _146_1469))))
end else begin
()
end
in (
# 2399 "FStar.TypeChecker.Tc.fst"
let _57_2923 = (tc_tparams env arguments)
in (match (_57_2923) with
| (arguments, env', us) -> begin
(
# 2400 "FStar.TypeChecker.Tc.fst"
let _57_2927 = (tc_trivial_guard env' result)
in (match (_57_2927) with
| (result, _57_2926) -> begin
(
# 2401 "FStar.TypeChecker.Tc.fst"
let _57_2931 = (FStar_Syntax_Util.head_and_args result)
in (match (_57_2931) with
| (head, _57_2930) -> begin
(
# 2402 "FStar.TypeChecker.Tc.fst"
let _57_2936 = (match ((let _146_1472 = (FStar_Syntax_Subst.compress head)
in _146_1472.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _57_2935 -> begin
(let _146_1476 = (let _146_1475 = (let _146_1474 = (let _146_1473 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _146_1473))
in (_146_1474, r))
in FStar_Syntax_Syntax.Error (_146_1475))
in (Prims.raise _146_1476))
end)
in (
# 2405 "FStar.TypeChecker.Tc.fst"
let g = (FStar_List.fold_left2 (fun g _57_2942 u_x -> (match (_57_2942) with
| (x, _57_2941) -> begin
(
# 2406 "FStar.TypeChecker.Tc.fst"
let _57_2944 = ()
in (let _146_1480 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _146_1480)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (
# 2412 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1484 = (let _146_1482 = (FStar_All.pipe_right tps (FStar_List.map (fun _57_2950 -> (match (_57_2950) with
| (x, _57_2949) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _146_1482 arguments))
in (let _146_1483 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _146_1484 _146_1483)))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _57_2953 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 2420 "FStar.TypeChecker.Tc.fst"
let generalize_and_inst_within = (fun env g tcs datas -> (
# 2421 "FStar.TypeChecker.Tc.fst"
let _57_2959 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2422 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_7 -> (match (_57_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2963, _57_2965, tps, k, _57_2969, _57_2971, _57_2973, _57_2975) -> begin
(let _146_1495 = (let _146_1494 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _146_1494))
in (FStar_Syntax_Syntax.null_binder _146_1495))
end
| _57_2979 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2425 "FStar.TypeChecker.Tc.fst"
let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _57_8 -> (match (_57_8) with
| FStar_Syntax_Syntax.Sig_datacon (_57_2983, _57_2985, t, _57_2988, _57_2990, _57_2992, _57_2994, _57_2996) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _57_3000 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2428 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1497 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _146_1497))
in (
# 2429 "FStar.TypeChecker.Tc.fst"
let _57_3003 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1498 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _146_1498))
end else begin
()
end
in (
# 2430 "FStar.TypeChecker.Tc.fst"
let _57_3007 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_57_3007) with
| (uvs, t) -> begin
(
# 2431 "FStar.TypeChecker.Tc.fst"
let _57_3009 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1502 = (let _146_1500 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _146_1500 (FStar_String.concat ", ")))
in (let _146_1501 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _146_1502 _146_1501)))
end else begin
()
end
in (
# 2434 "FStar.TypeChecker.Tc.fst"
let _57_3013 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_57_3013) with
| (uvs, t) -> begin
(
# 2435 "FStar.TypeChecker.Tc.fst"
let _57_3017 = (FStar_Syntax_Util.arrow_formals t)
in (match (_57_3017) with
| (args, _57_3016) -> begin
(
# 2436 "FStar.TypeChecker.Tc.fst"
let _57_3020 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_57_3020) with
| (tc_types, data_types) -> begin
(
# 2437 "FStar.TypeChecker.Tc.fst"
let tcs = (FStar_List.map2 (fun _57_3024 se -> (match (_57_3024) with
| (x, _57_3023) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3028, tps, _57_3031, mutuals, datas, quals, r) -> begin
(
# 2439 "FStar.TypeChecker.Tc.fst"
let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (
# 2440 "FStar.TypeChecker.Tc.fst"
let _57_3054 = (match ((let _146_1505 = (FStar_Syntax_Subst.compress ty)
in _146_1505.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 2442 "FStar.TypeChecker.Tc.fst"
let _57_3045 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_57_3045) with
| (tps, rest) -> begin
(
# 2443 "FStar.TypeChecker.Tc.fst"
let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _57_3048 -> begin
(let _146_1506 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _146_1506 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _57_3051 -> begin
([], ty)
end)
in (match (_57_3054) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _57_3056 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (
# 2453 "FStar.TypeChecker.Tc.fst"
let datas = (match (uvs) with
| [] -> begin
datas
end
| _57_3060 -> begin
(
# 2456 "FStar.TypeChecker.Tc.fst"
let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _146_1507 -> FStar_Syntax_Syntax.U_name (_146_1507))))
in (
# 2457 "FStar.TypeChecker.Tc.fst"
let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_9 -> (match (_57_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3065, _57_3067, _57_3069, _57_3071, _57_3073, _57_3075, _57_3077) -> begin
(tc, uvs_universes)
end
| _57_3081 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _57_3086 d -> (match (_57_3086) with
| (t, _57_3085) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _57_3090, _57_3092, tc, ntps, quals, mutuals, r) -> begin
(
# 2461 "FStar.TypeChecker.Tc.fst"
let ty = (let _146_1511 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _146_1511 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _57_3102 -> begin
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
# 2467 "FStar.TypeChecker.Tc.fst"
let _57_3112 = (FStar_All.pipe_right ses (FStar_List.partition (fun _57_10 -> (match (_57_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_3106) -> begin
true
end
| _57_3109 -> begin
false
end))))
in (match (_57_3112) with
| (tys, datas) -> begin
(
# 2469 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2472 "FStar.TypeChecker.Tc.fst"
let _57_3129 = (FStar_List.fold_right (fun tc _57_3118 -> (match (_57_3118) with
| (env, all_tcs, g) -> begin
(
# 2473 "FStar.TypeChecker.Tc.fst"
let _57_3122 = (tc_tycon env tc)
in (match (_57_3122) with
| (env, tc, tc_u) -> begin
(
# 2474 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (
# 2475 "FStar.TypeChecker.Tc.fst"
let _57_3124 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1515 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _146_1515))
end else begin
()
end
in (let _146_1516 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _146_1516))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_3129) with
| (env, tcs, g) -> begin
(
# 2482 "FStar.TypeChecker.Tc.fst"
let _57_3139 = (FStar_List.fold_right (fun se _57_3133 -> (match (_57_3133) with
| (datas, g) -> begin
(
# 2483 "FStar.TypeChecker.Tc.fst"
let _57_3136 = (tc_data env tcs se)
in (match (_57_3136) with
| (data, g') -> begin
(let _146_1519 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _146_1519))
end))
end)) datas ([], g))
in (match (_57_3139) with
| (datas, g) -> begin
(
# 2488 "FStar.TypeChecker.Tc.fst"
let _57_3142 = (let _146_1520 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _146_1520 datas))
in (match (_57_3142) with
| (tcs, datas) -> begin
(let _146_1522 = (let _146_1521 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _146_1521))
in FStar_Syntax_Syntax.Sig_bundle (_146_1522))
end))
end))
end)))
end)))))))))

# 2491 "FStar.TypeChecker.Tc.fst"
let rec tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.env) = (fun env se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(
# 2504 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2505 "FStar.TypeChecker.Tc.fst"
let se = (tc_lex_t env ses quals lids)
in (let _146_1527 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _146_1527))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(
# 2509 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2510 "FStar.TypeChecker.Tc.fst"
let se = (tc_inductive env ses quals lids)
in (let _146_1528 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _146_1528))))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(
# 2514 "FStar.TypeChecker.Tc.fst"
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
# 2520 "FStar.TypeChecker.Tc.fst"
let _57_3180 = (set_options FStar_Options.Set o)
in (se, env))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(
# 2523 "FStar.TypeChecker.Tc.fst"
let _57_3184 = (let _146_1533 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _146_1533 Prims.ignore))
in (
# 2524 "FStar.TypeChecker.Tc.fst"
let _57_3189 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (
# 2527 "FStar.TypeChecker.Tc.fst"
let _57_3191 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (se, env))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(
# 2532 "FStar.TypeChecker.Tc.fst"
let ne = (tc_eff_decl env ne ForFree)
in (
# 2534 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (
# 2535 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(
# 2539 "FStar.TypeChecker.Tc.fst"
let ne = (tc_eff_decl env ne NotForFree)
in (
# 2540 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (
# 2541 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(
# 2545 "FStar.TypeChecker.Tc.fst"
let _57_3213 = (let _146_1534 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _146_1534))
in (match (_57_3213) with
| (a, wp_a_src) -> begin
(
# 2546 "FStar.TypeChecker.Tc.fst"
let _57_3216 = (let _146_1535 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _146_1535))
in (match (_57_3216) with
| (b, wp_b_tgt) -> begin
(
# 2547 "FStar.TypeChecker.Tc.fst"
let wp_a_tgt = (FStar_Syntax_Subst.subst (FStar_Syntax_Syntax.Renaming ((FStar_Syntax_Syntax.Name2Name ((b, a)))::[])) wp_b_tgt)
in (
# 2548 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1540 = (let _146_1538 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1537 = (let _146_1536 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_146_1536)::[])
in (_146_1538)::_146_1537))
in (let _146_1539 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _146_1540 _146_1539)))
in (
# 2549 "FStar.TypeChecker.Tc.fst"
let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (
# 2550 "FStar.TypeChecker.Tc.fst"
let sub = (
# 2550 "FStar.TypeChecker.Tc.fst"
let _57_3220 = sub
in {FStar_Syntax_Syntax.source = _57_3220.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _57_3220.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
in (
# 2551 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect ((sub, r))
in (
# 2552 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(
# 2556 "FStar.TypeChecker.Tc.fst"
let _57_3233 = ()
in (
# 2557 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2558 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2559 "FStar.TypeChecker.Tc.fst"
let _57_3239 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_57_3239) with
| (tps, c) -> begin
(
# 2560 "FStar.TypeChecker.Tc.fst"
let _57_3243 = (tc_tparams env tps)
in (match (_57_3243) with
| (tps, env, us) -> begin
(
# 2561 "FStar.TypeChecker.Tc.fst"
let _57_3247 = (tc_comp env c)
in (match (_57_3247) with
| (c, u, g) -> begin
(
# 2562 "FStar.TypeChecker.Tc.fst"
let _57_3248 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2563 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 2564 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.close_comp tps c)
in (
# 2565 "FStar.TypeChecker.Tc.fst"
let _57_3254 = (let _146_1541 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _146_1541))
in (match (_57_3254) with
| (uvs, t) -> begin
(
# 2566 "FStar.TypeChecker.Tc.fst"
let _57_3273 = (match ((let _146_1543 = (let _146_1542 = (FStar_Syntax_Subst.compress t)
in _146_1542.FStar_Syntax_Syntax.n)
in (tps, _146_1543))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_57_3257, c)) -> begin
([], c)
end
| (_57_3263, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _57_3270 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_3273) with
| (tps, c) -> begin
(
# 2570 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_effect_abbrev ((lid, uvs, tps, c, tags, r))
in (
# 2571 "FStar.TypeChecker.Tc.fst"
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
# 2575 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2576 "FStar.TypeChecker.Tc.fst"
let _57_3284 = ()
in (
# 2577 "FStar.TypeChecker.Tc.fst"
let _57_3288 = (let _146_1545 = (let _146_1544 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _146_1544))
in (check_and_gen env t _146_1545))
in (match (_57_3288) with
| (uvs, t) -> begin
(
# 2578 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (
# 2579 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(
# 2583 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2584 "FStar.TypeChecker.Tc.fst"
let _57_3301 = (FStar_Syntax_Util.type_u ())
in (match (_57_3301) with
| (k, _57_3300) -> begin
(
# 2585 "FStar.TypeChecker.Tc.fst"
let phi = (let _146_1546 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _146_1546 (norm env)))
in (
# 2586 "FStar.TypeChecker.Tc.fst"
let _57_3303 = (FStar_TypeChecker_Util.check_uvars r phi)
in (
# 2587 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))
in (
# 2588 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(
# 2592 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2593 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (
# 2594 "FStar.TypeChecker.Tc.fst"
let _57_3316 = (tc_term env e)
in (match (_57_3316) with
| (e, c, g1) -> begin
(
# 2595 "FStar.TypeChecker.Tc.fst"
let _57_3321 = (let _146_1550 = (let _146_1547 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_146_1547))
in (let _146_1549 = (let _146_1548 = (c.FStar_Syntax_Syntax.comp ())
in (e, _146_1548))
in (check_expected_effect env _146_1550 _146_1549)))
in (match (_57_3321) with
| (e, _57_3319, g) -> begin
(
# 2596 "FStar.TypeChecker.Tc.fst"
let _57_3322 = (let _146_1551 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _146_1551))
in (
# 2597 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, r))
in (
# 2598 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(
# 2602 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2603 "FStar.TypeChecker.Tc.fst"
let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
if (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q')) then begin
Some (q)
end else begin
(let _146_1563 = (let _146_1562 = (let _146_1561 = (let _146_1560 = (FStar_Syntax_Print.lid_to_string l)
in (let _146_1559 = (FStar_Syntax_Print.quals_to_string q)
in (let _146_1558 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _146_1560 _146_1559 _146_1558))))
in (_146_1561, r))
in FStar_Syntax_Syntax.Error (_146_1562))
in (Prims.raise _146_1563))
end
end))
in (
# 2617 "FStar.TypeChecker.Tc.fst"
let _57_3366 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _57_3343 lb -> (match (_57_3343) with
| (gen, lbs, quals_opt) -> begin
(
# 2618 "FStar.TypeChecker.Tc.fst"
let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2619 "FStar.TypeChecker.Tc.fst"
let _57_3362 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(
# 2623 "FStar.TypeChecker.Tc.fst"
let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (
# 2624 "FStar.TypeChecker.Tc.fst"
let _57_3357 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _57_3356 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _146_1566 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _146_1566, quals_opt))))
end)
in (match (_57_3362) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_57_3366) with
| (should_generalize, lbs', quals_opt) -> begin
(
# 2633 "FStar.TypeChecker.Tc.fst"
let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _57_11 -> (match (_57_11) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _57_3375 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (
# 2640 "FStar.TypeChecker.Tc.fst"
let lbs' = (FStar_List.rev lbs')
in (
# 2643 "FStar.TypeChecker.Tc.fst"
let e = (let _146_1570 = (let _146_1569 = (let _146_1568 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _146_1568))
in FStar_Syntax_Syntax.Tm_let (_146_1569))
in (FStar_Syntax_Syntax.mk _146_1570 None r))
in (
# 2646 "FStar.TypeChecker.Tc.fst"
let _57_3409 = (match ((tc_maybe_toplevel_term (
# 2646 "FStar.TypeChecker.Tc.fst"
let _57_3379 = env
in {FStar_TypeChecker_Env.solver = _57_3379.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3379.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3379.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3379.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3379.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3379.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3379.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3379.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3379.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3379.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3379.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _57_3379.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _57_3379.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3379.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3379.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3379.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3379.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3379.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3379.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _57_3386; FStar_Syntax_Syntax.pos = _57_3384; FStar_Syntax_Syntax.vars = _57_3382}, _57_3393, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(
# 2649 "FStar.TypeChecker.Tc.fst"
let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_57_3397, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _57_3403 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _57_3406 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_57_3409) with
| (se, lbs) -> begin
(
# 2656 "FStar.TypeChecker.Tc.fst"
let _57_3415 = if (log env) then begin
(let _146_1578 = (let _146_1577 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 2658 "FStar.TypeChecker.Tc.fst"
let should_log = (match ((let _146_1574 = (let _146_1573 = (let _146_1572 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _146_1572.FStar_Syntax_Syntax.fv_name)
in _146_1573.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _146_1574))) with
| None -> begin
true
end
| _57_3413 -> begin
false
end)
in if should_log then begin
(let _146_1576 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _146_1575 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _146_1576 _146_1575)))
end else begin
""
end))))
in (FStar_All.pipe_right _146_1577 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _146_1578))
end else begin
()
end
in (
# 2665 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end))))
end))

# 2669 "FStar.TypeChecker.Tc.fst"
let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (
# 2693 "FStar.TypeChecker.Tc.fst"
let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _57_12 -> (match (_57_12) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _57_3425 -> begin
false
end)))))
in (
# 2694 "FStar.TypeChecker.Tc.fst"
let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _57_3435 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_57_3437) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _57_3448, _57_3450) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _57_3456 -> (match (_57_3456) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _57_3462, _57_3464, quals, r) -> begin
(
# 2708 "FStar.TypeChecker.Tc.fst"
let dec = (let _146_1594 = (let _146_1593 = (let _146_1592 = (let _146_1591 = (let _146_1590 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _146_1590))
in FStar_Syntax_Syntax.Tm_arrow (_146_1591))
in (FStar_Syntax_Syntax.mk _146_1592 None r))
in (l, us, _146_1593, (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_146_1594))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _57_3474, _57_3476, _57_3478, _57_3480, r) -> begin
(
# 2711 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _57_3486 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_57_3488, _57_3490, quals, _57_3493) -> begin
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
| _57_3512 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_57_3514) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _57_3533, _57_3535, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(
# 2742 "FStar.TypeChecker.Tc.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2743 "FStar.TypeChecker.Tc.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))) then begin
([], hidden)
end else begin
(
# 2746 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::[], (FStar_Ident.range_of_lid lid)))
in ((dec)::[], (lid)::hidden))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (is_abstract quals) then begin
(let _146_1601 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _146_1600 = (let _146_1599 = (let _146_1598 = (let _146_1597 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _146_1597.FStar_Syntax_Syntax.fv_name)
in _146_1598.FStar_Syntax_Syntax.v)
in (_146_1599, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_146_1600)))))
in (_146_1601, hidden))
end else begin
((se)::[], hidden)
end
end))))

# 2755 "FStar.TypeChecker.Tc.fst"
let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (
# 2756 "FStar.TypeChecker.Tc.fst"
let _57_3574 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _57_3555 se -> (match (_57_3555) with
| (ses, exports, env, hidden) -> begin
(
# 2758 "FStar.TypeChecker.Tc.fst"
let _57_3557 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1608 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _146_1608))
end else begin
()
end
in (
# 2761 "FStar.TypeChecker.Tc.fst"
let _57_3561 = (tc_decl env se)
in (match (_57_3561) with
| (se, env) -> begin
(
# 2763 "FStar.TypeChecker.Tc.fst"
let _57_3562 = if ((FStar_ST.read FStar_Options.log_types) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _146_1609 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _146_1609))
end else begin
()
end
in (
# 2766 "FStar.TypeChecker.Tc.fst"
let _57_3564 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (
# 2768 "FStar.TypeChecker.Tc.fst"
let _57_3568 = (for_export hidden se)
in (match (_57_3568) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_57_3574) with
| (ses, exports, env, _57_3573) -> begin
(let _146_1610 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _146_1610, env))
end)))

# 2773 "FStar.TypeChecker.Tc.fst"
let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2774 "FStar.TypeChecker.Tc.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 2775 "FStar.TypeChecker.Tc.fst"
let msg = (Prims.strcat "Internals for " name)
in (
# 2776 "FStar.TypeChecker.Tc.fst"
let env = (
# 2776 "FStar.TypeChecker.Tc.fst"
let _57_3579 = env
in (let _146_1615 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _57_3579.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3579.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3579.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3579.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3579.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3579.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3579.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3579.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3579.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3579.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3579.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3579.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3579.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_3579.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_3579.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3579.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _146_1615; FStar_TypeChecker_Env.type_of = _57_3579.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3579.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3579.FStar_TypeChecker_Env.use_bv_sorts}))
in (
# 2777 "FStar.TypeChecker.Tc.fst"
let _57_3582 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (
# 2778 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (
# 2779 "FStar.TypeChecker.Tc.fst"
let _57_3588 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_57_3588) with
| (ses, exports, env) -> begin
((
# 2780 "FStar.TypeChecker.Tc.fst"
let _57_3589 = modul
in {FStar_Syntax_Syntax.name = _57_3589.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _57_3589.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3589.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))

# 2782 "FStar.TypeChecker.Tc.fst"
let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (
# 2783 "FStar.TypeChecker.Tc.fst"
let _57_3597 = (tc_decls env decls)
in (match (_57_3597) with
| (ses, exports, env) -> begin
(
# 2784 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2784 "FStar.TypeChecker.Tc.fst"
let _57_3598 = modul
in {FStar_Syntax_Syntax.name = _57_3598.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _57_3598.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3598.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))

# 2787 "FStar.TypeChecker.Tc.fst"
let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (
# 2788 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2788 "FStar.TypeChecker.Tc.fst"
let _57_3604 = modul
in {FStar_Syntax_Syntax.name = _57_3604.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _57_3604.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (
# 2789 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.finish_module env modul)
in (
# 2790 "FStar.TypeChecker.Tc.fst"
let _57_3614 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(
# 2792 "FStar.TypeChecker.Tc.fst"
let _57_3608 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (
# 2793 "FStar.TypeChecker.Tc.fst"
let _57_3610 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (
# 2794 "FStar.TypeChecker.Tc.fst"
let _57_3612 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _146_1628 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _146_1628 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))

# 2799 "FStar.TypeChecker.Tc.fst"
let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2800 "FStar.TypeChecker.Tc.fst"
let _57_3621 = (tc_partial_modul env modul)
in (match (_57_3621) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

# 2803 "FStar.TypeChecker.Tc.fst"
let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 2804 "FStar.TypeChecker.Tc.fst"
let _57_3624 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _146_1637 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _146_1637))
end else begin
()
end
in (
# 2806 "FStar.TypeChecker.Tc.fst"
let env = (
# 2806 "FStar.TypeChecker.Tc.fst"
let _57_3626 = env
in {FStar_TypeChecker_Env.solver = _57_3626.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3626.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3626.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3626.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3626.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3626.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3626.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3626.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3626.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3626.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3626.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3626.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3626.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_3626.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3626.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3626.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3626.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3626.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3626.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3626.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 2807 "FStar.TypeChecker.Tc.fst"
let _57_3642 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _57_3634) -> begin
(let _146_1642 = (let _146_1641 = (let _146_1640 = (FStar_TypeChecker_Env.get_range env)
in ((Prims.strcat "Implicit argument: " msg), _146_1640))
in FStar_Syntax_Syntax.Error (_146_1641))
in (Prims.raise _146_1642))
end
in (match (_57_3642) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(t, c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(let _146_1647 = (let _146_1646 = (let _146_1645 = (let _146_1643 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _146_1643))
in (let _146_1644 = (FStar_TypeChecker_Env.get_range env)
in (_146_1645, _146_1644)))
in FStar_Syntax_Syntax.Error (_146_1646))
in (Prims.raise _146_1647))
end
end)))))

# 2814 "FStar.TypeChecker.Tc.fst"
let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (
# 2815 "FStar.TypeChecker.Tc.fst"
let _57_3645 = if ((let _146_1652 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _146_1652)) <> 0) then begin
(let _146_1653 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _146_1653))
end else begin
()
end
in (
# 2817 "FStar.TypeChecker.Tc.fst"
let _57_3649 = (tc_modul env m)
in (match (_57_3649) with
| (m, env) -> begin
(
# 2818 "FStar.TypeChecker.Tc.fst"
let _57_3650 = if (FStar_Options.should_dump m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _146_1654 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _146_1654))
end else begin
()
end
in (m, env))
end))))




