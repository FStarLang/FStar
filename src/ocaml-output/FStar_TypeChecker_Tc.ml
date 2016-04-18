
open Prims
# 42 "FStar.TypeChecker.Tc.fst"
let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_ST.read FStar_Options.log_types) && (not ((let _146_3 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _146_3))))))

# 43 "FStar.TypeChecker.Tc.fst"
let rng : FStar_TypeChecker_Env.env  ->  FStar_Range.range = (fun env -> (FStar_TypeChecker_Env.get_range env))

# 44 "FStar.TypeChecker.Tc.fst"
let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (
# 44 "FStar.TypeChecker.Tc.fst"
let _57_17 = env
in {FStar_TypeChecker_Env.solver = _57_17.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_17.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_17.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_17.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_17.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_17.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_17.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_17.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_17.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _57_17.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_17.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_17.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_17.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_17.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_17.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_17.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_17.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_17.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_17.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_17.FStar_TypeChecker_Env.use_bv_sorts}))

# 45 "FStar.TypeChecker.Tc.fst"
let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (
# 45 "FStar.TypeChecker.Tc.fst"
let _57_20 = env
in {FStar_TypeChecker_Env.solver = _57_20.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_20.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_20.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_20.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_20.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_20.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_20.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_20.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_20.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _57_20.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_20.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_20.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_20.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_20.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_20.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_20.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_20.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_20.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_20.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_20.FStar_TypeChecker_Env.use_bv_sorts}))

# 46 "FStar.TypeChecker.Tc.fst"
let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (
# 48 "FStar.TypeChecker.Tc.fst"
let r = if (tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
v.FStar_Syntax_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos tl.FStar_Syntax_Syntax.pos)
end
in (let _146_17 = (let _146_16 = (FStar_Syntax_Syntax.as_arg v)
in (let _146_15 = (let _146_14 = (FStar_Syntax_Syntax.as_arg tl)
in (_146_14)::[])
in (_146_16)::_146_15))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _146_17 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))

# 51 "FStar.TypeChecker.Tc.fst"
let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _57_1 -> (match (_57_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _57_30 -> begin
false
end))

# 54 "FStar.TypeChecker.Tc.fst"
let steps : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Normalize.step Prims.list = (fun env -> if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::[]
end else begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]
end)

# 58 "FStar.TypeChecker.Tc.fst"
let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Beta)::[]) env t))

# 59 "FStar.TypeChecker.Tc.fst"
let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _146_30 = (steps env)
in (FStar_TypeChecker_Normalize.normalize _146_30 env t)))

# 60 "FStar.TypeChecker.Tc.fst"
let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _146_35 = (steps env)
in (FStar_TypeChecker_Normalize.normalize_comp _146_35 env c)))

# 61 "FStar.TypeChecker.Tc.fst"
let check_no_escape : FStar_Syntax_Syntax.term Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun head_opt env fvs kt -> (
# 62 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
()
end
| _57_47 -> begin
(
# 65 "FStar.TypeChecker.Tc.fst"
let fvs' = (let _146_48 = if try_norm then begin
(norm env t)
end else begin
t
end
in (FStar_Syntax_Free.names _146_48))
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
let fail = (fun _57_54 -> (match (()) with
| () -> begin
(
# 72 "FStar.TypeChecker.Tc.fst"
let msg = (match (head_opt) with
| None -> begin
(let _146_52 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _146_52))
end
| Some (head) -> begin
(let _146_54 = (FStar_Syntax_Print.bv_to_string x)
in (let _146_53 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _146_54 _146_53)))
end)
in (let _146_57 = (let _146_56 = (let _146_55 = (FStar_TypeChecker_Env.get_range env)
in (msg, _146_55))
in FStar_Syntax_Syntax.Error (_146_56))
in (Prims.raise _146_57)))
end))
in (
# 77 "FStar.TypeChecker.Tc.fst"
let s = (let _146_59 = (let _146_58 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _146_58))
in (FStar_TypeChecker_Util.new_uvar env _146_59))
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

# 84 "FStar.TypeChecker.Tc.fst"
let maybe_push_binding : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder  ->  FStar_TypeChecker_Env.env = (fun env b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
env
end else begin
(
# 86 "FStar.TypeChecker.Tc.fst"
let _57_66 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_65 = (FStar_Syntax_Print.bv_to_string (Prims.fst b))
in (let _146_64 = (FStar_Syntax_Print.term_to_string (Prims.fst b).FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _146_65 _146_64)))
end else begin
()
end
in (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))
end)

# 90 "FStar.TypeChecker.Tc.fst"
let maybe_make_subst = (fun _57_2 -> (match (_57_2) with
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Syntax_Syntax.NT ((x, e)))::[]
end
| _57_75 -> begin
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
let _57_81 = lc
in {FStar_Syntax_Syntax.eff_name = _57_81.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _57_81.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _57_83 -> (match (()) with
| () -> begin
(let _146_78 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _146_78 t))
end))}))

# 101 "FStar.TypeChecker.Tc.fst"
let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (
# 102 "FStar.TypeChecker.Tc.fst"
let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _146_87 = if (not ((FStar_Syntax_Util.is_pure_or_ghost_function t))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _146_87))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (
# 107 "FStar.TypeChecker.Tc.fst"
let t = lc.FStar_Syntax_Syntax.res_typ
in (
# 108 "FStar.TypeChecker.Tc.fst"
let _57_115 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, guard)
end
| Some (t') -> begin
(
# 111 "FStar.TypeChecker.Tc.fst"
let _57_97 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_89 = (FStar_Syntax_Print.term_to_string t)
in (let _146_88 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _146_89 _146_88)))
end else begin
()
end
in (
# 113 "FStar.TypeChecker.Tc.fst"
let _57_101 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_57_101) with
| (e, lc) -> begin
(
# 114 "FStar.TypeChecker.Tc.fst"
let t = lc.FStar_Syntax_Syntax.res_typ
in (
# 115 "FStar.TypeChecker.Tc.fst"
let _57_105 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_57_105) with
| (e, g) -> begin
(
# 116 "FStar.TypeChecker.Tc.fst"
let _57_106 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_91 = (FStar_Syntax_Print.term_to_string t)
in (let _146_90 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _146_91 _146_90)))
end else begin
()
end
in (
# 118 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (
# 119 "FStar.TypeChecker.Tc.fst"
let _57_111 = (let _146_97 = (FStar_All.pipe_left (fun _146_96 -> Some (_146_96)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _146_97 env e lc g))
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
# 121 "FStar.TypeChecker.Tc.fst"
let _57_116 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_98 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _146_98))
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
let _57_126 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_57_126) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))

# 132 "FStar.TypeChecker.Tc.fst"
let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _57_131 -> (match (_57_131) with
| (e, c) -> begin
(
# 133 "FStar.TypeChecker.Tc.fst"
let expected_c_opt = (match (copt) with
| Some (_57_133) -> begin
copt
end
| None -> begin
if ((FStar_ST.read FStar_Options.ml_ish) && (FStar_Ident.lid_equals FStar_Syntax_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) then begin
(let _146_111 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (_146_111))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
if (FStar_Syntax_Util.is_pure_comp c) then begin
(let _146_112 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (_146_112))
end else begin
if (FStar_Syntax_Util.is_pure_or_ghost_comp c) then begin
(let _146_113 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (_146_113))
end else begin
None
end
end
end
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _146_114 = (norm_c env c)
in (e, _146_114, FStar_TypeChecker_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(
# 149 "FStar.TypeChecker.Tc.fst"
let _57_140 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_117 = (FStar_Syntax_Print.term_to_string e)
in (let _146_116 = (FStar_Syntax_Print.comp_to_string c)
in (let _146_115 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _146_117 _146_116 _146_115))))
end else begin
()
end
in (
# 152 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 153 "FStar.TypeChecker.Tc.fst"
let _57_143 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_120 = (FStar_Syntax_Print.term_to_string e)
in (let _146_119 = (FStar_Syntax_Print.comp_to_string c)
in (let _146_118 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _146_120 _146_119 _146_118))))
end else begin
()
end
in (
# 158 "FStar.TypeChecker.Tc.fst"
let _57_149 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_57_149) with
| (e, _57_147, g) -> begin
(
# 159 "FStar.TypeChecker.Tc.fst"
let g = (let _146_121 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _146_121 "could not prove post-condition" g))
in (
# 160 "FStar.TypeChecker.Tc.fst"
let _57_151 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_123 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _146_122 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _146_123 _146_122)))
end else begin
()
end
in (e, expected_c, g)))
end)))))
end))
end))

# 163 "FStar.TypeChecker.Tc.fst"
let no_logical_guard = (fun env _57_157 -> (match (_57_157) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
(te, kt, f)
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _146_129 = (let _146_128 = (let _146_127 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _146_126 = (FStar_TypeChecker_Env.get_range env)
in (_146_127, _146_126)))
in FStar_Syntax_Syntax.Error (_146_128))
in (Prims.raise _146_129))
end)
end))

# 168 "FStar.TypeChecker.Tc.fst"
let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _146_132 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _146_132))
end))

# 175 "FStar.TypeChecker.Tc.fst"
let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _57_181; FStar_Syntax_Syntax.result_typ = _57_179; FStar_Syntax_Syntax.effect_args = _pre::_post::(pats, _57_173)::[]; FStar_Syntax_Syntax.flags = _57_170}) -> begin
(
# 179 "FStar.TypeChecker.Tc.fst"
let pat_vars = (FStar_Syntax_Free.names pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _57_188 -> (match (_57_188) with
| (b, _57_187) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _57_192) -> begin
(let _146_139 = (let _146_138 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _146_138))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _146_139))
end))
end
| _57_196 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end)

# 190 "FStar.TypeChecker.Tc.fst"
let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun env actuals expected_c -> (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(
# 194 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 195 "FStar.TypeChecker.Tc.fst"
let env = (
# 195 "FStar.TypeChecker.Tc.fst"
let _57_203 = env
in {FStar_TypeChecker_Env.solver = _57_203.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_203.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_203.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_203.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_203.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_203.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_203.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_203.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_203.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_203.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_203.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_203.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_203.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_203.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_203.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_203.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_203.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_203.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_203.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_203.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 196 "FStar.TypeChecker.Tc.fst"
let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (
# 198 "FStar.TypeChecker.Tc.fst"
let decreases_clause = (fun bs c -> (
# 200 "FStar.TypeChecker.Tc.fst"
let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _57_215 -> (match (_57_215) with
| (b, _57_214) -> begin
(
# 202 "FStar.TypeChecker.Tc.fst"
let t = (let _146_153 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _146_153))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _57_224 -> begin
(let _146_154 = (FStar_Syntax_Syntax.bv_to_name b)
in (_146_154)::[])
end))
end)))))
in (
# 207 "FStar.TypeChecker.Tc.fst"
let as_lex_list = (fun dec -> (
# 208 "FStar.TypeChecker.Tc.fst"
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
# 212 "FStar.TypeChecker.Tc.fst"
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
# 216 "FStar.TypeChecker.Tc.fst"
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
# 221 "FStar.TypeChecker.Tc.fst"
let previous_dec = (decreases_clause actuals expected_c)
in (
# 222 "FStar.TypeChecker.Tc.fst"
let guard_one_letrec = (fun _57_256 -> (match (_57_256) with
| (l, t) -> begin
(match ((let _146_160 = (FStar_Syntax_Subst.compress t)
in _146_160.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 226 "FStar.TypeChecker.Tc.fst"
let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _57_263 -> (match (_57_263) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _146_164 = (let _146_163 = (let _146_162 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_146_162))
in (FStar_Syntax_Syntax.new_bv _146_163 x.FStar_Syntax_Syntax.sort))
in (_146_164, imp))
end else begin
(x, imp)
end
end))))
in (
# 227 "FStar.TypeChecker.Tc.fst"
let _57_267 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_57_267) with
| (formals, c) -> begin
(
# 228 "FStar.TypeChecker.Tc.fst"
let dec = (decreases_clause formals c)
in (
# 229 "FStar.TypeChecker.Tc.fst"
let precedes = (let _146_168 = (let _146_167 = (FStar_Syntax_Syntax.as_arg dec)
in (let _146_166 = (let _146_165 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_146_165)::[])
in (_146_167)::_146_166))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _146_168 None r))
in (
# 230 "FStar.TypeChecker.Tc.fst"
let _57_274 = (FStar_Util.prefix formals)
in (match (_57_274) with
| (bs, (last, imp)) -> begin
(
# 231 "FStar.TypeChecker.Tc.fst"
let last = (
# 231 "FStar.TypeChecker.Tc.fst"
let _57_275 = last
in (let _146_169 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _57_275.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_275.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_169}))
in (
# 232 "FStar.TypeChecker.Tc.fst"
let refined_formals = (FStar_List.append bs (((last, imp))::[]))
in (
# 233 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (
# 234 "FStar.TypeChecker.Tc.fst"
let _57_280 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_172 = (FStar_Syntax_Print.lbname_to_string l)
in (let _146_171 = (FStar_Syntax_Print.term_to_string t)
in (let _146_170 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _146_172 _146_171 _146_170))))
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

# 246 "FStar.TypeChecker.Tc.fst"
let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (
# 246 "FStar.TypeChecker.Tc.fst"
let _57_286 = env
in {FStar_TypeChecker_Env.solver = _57_286.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_286.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_286.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_286.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_286.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_286.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_286.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_286.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_286.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_286.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_286.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_286.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_286.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_286.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_286.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_286.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_286.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_286.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_286.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_286.FStar_TypeChecker_Env.use_bv_sorts}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 251 "FStar.TypeChecker.Tc.fst"
let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (
# 252 "FStar.TypeChecker.Tc.fst"
let _57_291 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_241 = (let _146_239 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _146_239))
in (let _146_240 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _146_241 _146_240)))
end else begin
()
end
in (
# 253 "FStar.TypeChecker.Tc.fst"
let top = e
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_57_295) -> begin
(let _146_245 = (FStar_Syntax_Subst.compress e)
in (tc_term env _146_245))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(
# 270 "FStar.TypeChecker.Tc.fst"
let _57_336 = (tc_tot_or_gtot_term env e)
in (match (_57_336) with
| (e, c, g) -> begin
(
# 271 "FStar.TypeChecker.Tc.fst"
let g = (
# 271 "FStar.TypeChecker.Tc.fst"
let _57_337 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_337.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_337.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_337.FStar_TypeChecker_Env.implicits})
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(
# 275 "FStar.TypeChecker.Tc.fst"
let _57_347 = (FStar_Syntax_Util.type_u ())
in (match (_57_347) with
| (t, u) -> begin
(
# 276 "FStar.TypeChecker.Tc.fst"
let _57_351 = (tc_check_tot_or_gtot_term env e t)
in (match (_57_351) with
| (e, c, g) -> begin
(
# 277 "FStar.TypeChecker.Tc.fst"
let _57_358 = (
# 278 "FStar.TypeChecker.Tc.fst"
let _57_355 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_355) with
| (env, _57_354) -> begin
(tc_pats env pats)
end))
in (match (_57_358) with
| (pats, g') -> begin
(
# 280 "FStar.TypeChecker.Tc.fst"
let g' = (
# 280 "FStar.TypeChecker.Tc.fst"
let _57_359 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_359.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_359.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_359.FStar_TypeChecker_Env.implicits})
in (let _146_247 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_pattern (pats)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_246 = (FStar_TypeChecker_Rel.conj_guard g g')
in (_146_247, c, _146_246))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _146_248 = (FStar_Syntax_Subst.compress e)
in _146_248.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_57_368, {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _57_375; FStar_Syntax_Syntax.lbtyp = _57_373; FStar_Syntax_Syntax.lbeff = _57_371; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 288 "FStar.TypeChecker.Tc.fst"
let _57_386 = (let _146_249 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _146_249 e1))
in (match (_57_386) with
| (e1, c1, g1) -> begin
(
# 289 "FStar.TypeChecker.Tc.fst"
let _57_390 = (tc_term env e2)
in (match (_57_390) with
| (e2, c2, g2) -> begin
(
# 290 "FStar.TypeChecker.Tc.fst"
let c = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (None, c2))
in (
# 291 "FStar.TypeChecker.Tc.fst"
let e = (let _146_254 = (let _146_253 = (let _146_252 = (let _146_251 = (let _146_250 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Common.t_unit, e1))
in (_146_250)::[])
in (false, _146_251))
in (_146_252, e2))
in FStar_Syntax_Syntax.Tm_let (_146_253))
in (FStar_Syntax_Syntax.mk _146_254 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 292 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_255 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _146_255)))))
end))
end))
end
| _57_395 -> begin
(
# 295 "FStar.TypeChecker.Tc.fst"
let _57_399 = (tc_term env e)
in (match (_57_399) with
| (e, c, g) -> begin
(
# 296 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(
# 301 "FStar.TypeChecker.Tc.fst"
let _57_408 = (tc_term env e)
in (match (_57_408) with
| (e, c, g) -> begin
(
# 302 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, m))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _57_414) -> begin
(
# 306 "FStar.TypeChecker.Tc.fst"
let _57_421 = (tc_comp env expected_c)
in (match (_57_421) with
| (expected_c, _57_419, g) -> begin
(
# 307 "FStar.TypeChecker.Tc.fst"
let _57_425 = (tc_term env e)
in (match (_57_425) with
| (e, c', g') -> begin
(
# 308 "FStar.TypeChecker.Tc.fst"
let _57_429 = (let _146_257 = (let _146_256 = (c'.FStar_Syntax_Syntax.comp ())
in (e, _146_256))
in (check_expected_effect env (Some (expected_c)) _146_257))
in (match (_57_429) with
| (e, expected_c, g'') -> begin
(
# 309 "FStar.TypeChecker.Tc.fst"
let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (let _146_260 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t_res), Some ((FStar_Syntax_Util.comp_effect_name expected_c))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_259 = (let _146_258 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _146_258))
in (_146_260, (FStar_Syntax_Util.lcomp_of_comp expected_c), _146_259))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _57_435) -> begin
(
# 315 "FStar.TypeChecker.Tc.fst"
let _57_440 = (FStar_Syntax_Util.type_u ())
in (match (_57_440) with
| (k, u) -> begin
(
# 316 "FStar.TypeChecker.Tc.fst"
let _57_445 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_445) with
| (t, _57_443, f) -> begin
(
# 317 "FStar.TypeChecker.Tc.fst"
let _57_449 = (let _146_261 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _146_261 e))
in (match (_57_449) with
| (e, c, g) -> begin
(
# 318 "FStar.TypeChecker.Tc.fst"
let _57_453 = (let _146_265 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_450 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _146_265 e c f))
in (match (_57_453) with
| (c, f) -> begin
(
# 319 "FStar.TypeChecker.Tc.fst"
let _57_457 = (let _146_266 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t), Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _146_266 c))
in (match (_57_457) with
| (e, c, f2) -> begin
(let _146_268 = (let _146_267 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _146_267))
in (e, c, _146_268))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 323 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 324 "FStar.TypeChecker.Tc.fst"
let env = (let _146_270 = (let _146_269 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_269 Prims.fst))
in (FStar_All.pipe_right _146_270 instantiate_both))
in (
# 325 "FStar.TypeChecker.Tc.fst"
let _57_464 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_272 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _146_271 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _146_272 _146_271)))
end else begin
()
end
in (
# 329 "FStar.TypeChecker.Tc.fst"
let _57_469 = (tc_term (no_inst env) head)
in (match (_57_469) with
| (head, chead, g_head) -> begin
(
# 330 "FStar.TypeChecker.Tc.fst"
let _57_473 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _146_273 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _146_273))
end else begin
(let _146_274 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _146_274))
end
in (match (_57_473) with
| (e, c, g) -> begin
(
# 333 "FStar.TypeChecker.Tc.fst"
let _57_474 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_275 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _146_275))
end else begin
()
end
in (
# 335 "FStar.TypeChecker.Tc.fst"
let c = if (((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) && (not ((FStar_Syntax_Util.is_lcomp_partial_return c)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)) then begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e c)
end else begin
c
end
in (
# 340 "FStar.TypeChecker.Tc.fst"
let _57_481 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_281 = (FStar_Syntax_Print.term_to_string e)
in (let _146_280 = (let _146_276 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _146_276))
in (let _146_279 = (let _146_278 = (FStar_TypeChecker_Env.expected_typ env0)
in (FStar_All.pipe_right _146_278 (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end))))
in (FStar_Util.print3 "(%s) About to check %s against expected typ %s\n" _146_281 _146_280 _146_279))))
end else begin
()
end
in (
# 345 "FStar.TypeChecker.Tc.fst"
let _57_486 = (comp_check_expected_typ env0 e c)
in (match (_57_486) with
| (e, c, g') -> begin
(
# 346 "FStar.TypeChecker.Tc.fst"
let _57_487 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_284 = (FStar_Syntax_Print.term_to_string e)
in (let _146_283 = (let _146_282 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _146_282))
in (FStar_Util.print2 "(%s) checked ... got %s\n" _146_284 _146_283)))
end else begin
()
end
in (
# 350 "FStar.TypeChecker.Tc.fst"
let gimp = (match ((let _146_285 = (FStar_Syntax_Subst.compress head)
in _146_285.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _57_491) -> begin
(
# 353 "FStar.TypeChecker.Tc.fst"
let imp = ("head of application is a uvar", env0, u, e, c.FStar_Syntax_Syntax.res_typ, head.FStar_Syntax_Syntax.pos)
in (
# 354 "FStar.TypeChecker.Tc.fst"
let _57_495 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_495.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_495.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_495.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _57_498 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (
# 356 "FStar.TypeChecker.Tc.fst"
let gres = (let _146_286 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _146_286))
in (
# 357 "FStar.TypeChecker.Tc.fst"
let _57_501 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_287 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print1 "Guard from application node is %s\n" _146_287))
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
# 362 "FStar.TypeChecker.Tc.fst"
let _57_509 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_509) with
| (env1, topt) -> begin
(
# 363 "FStar.TypeChecker.Tc.fst"
let env1 = (instantiate_both env1)
in (
# 364 "FStar.TypeChecker.Tc.fst"
let _57_514 = (tc_term env1 e1)
in (match (_57_514) with
| (e1, c1, g1) -> begin
(
# 365 "FStar.TypeChecker.Tc.fst"
let _57_525 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(
# 368 "FStar.TypeChecker.Tc.fst"
let _57_521 = (FStar_Syntax_Util.type_u ())
in (match (_57_521) with
| (k, _57_520) -> begin
(
# 369 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _146_288 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_146_288, res_t)))
end))
end)
in (match (_57_525) with
| (env_branches, res_t) -> begin
(
# 372 "FStar.TypeChecker.Tc.fst"
let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (
# 373 "FStar.TypeChecker.Tc.fst"
let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (
# 374 "FStar.TypeChecker.Tc.fst"
let _57_542 = (
# 375 "FStar.TypeChecker.Tc.fst"
let _57_539 = (FStar_List.fold_right (fun _57_533 _57_536 -> (match ((_57_533, _57_536)) with
| ((_57_529, f, c, g), (caccum, gaccum)) -> begin
(let _146_291 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _146_291))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_539) with
| (cases, g) -> begin
(let _146_292 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_146_292, g))
end))
in (match (_57_542) with
| (c_branches, g_branches) -> begin
(
# 379 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (guard_x), c_branches))
in (
# 380 "FStar.TypeChecker.Tc.fst"
let e = (let _146_296 = (let _146_295 = (let _146_294 = (FStar_List.map (fun _57_551 -> (match (_57_551) with
| (f, _57_546, _57_548, _57_550) -> begin
f
end)) t_eqns)
in (e1, _146_294))
in FStar_Syntax_Syntax.Tm_match (_146_295))
in (FStar_Syntax_Syntax.mk _146_296 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (
# 382 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ), Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (
# 383 "FStar.TypeChecker.Tc.fst"
let _57_554 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_299 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _146_298 = (let _146_297 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _146_297))
in (FStar_Util.print2 "(%s) comp type = %s\n" _146_299 _146_298)))
end else begin
()
end
in (let _146_300 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _146_300))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_566); FStar_Syntax_Syntax.lbunivs = _57_564; FStar_Syntax_Syntax.lbtyp = _57_562; FStar_Syntax_Syntax.lbeff = _57_560; FStar_Syntax_Syntax.lbdef = _57_558}::[]), _57_572) -> begin
(
# 390 "FStar.TypeChecker.Tc.fst"
let _57_575 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_301 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _146_301))
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
# 397 "FStar.TypeChecker.Tc.fst"
let _57_606 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_302 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _146_302))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _57_610), _57_613) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 410 "FStar.TypeChecker.Tc.fst"
let check_instantiated_fvar = (fun env v dc e t -> (
# 411 "FStar.TypeChecker.Tc.fst"
let _57_627 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_627) with
| (e, t, implicits) -> begin
(
# 413 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _146_316 = (let _146_315 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_315))
in FStar_Util.Inr (_146_316))
end
in (
# 414 "FStar.TypeChecker.Tc.fst"
let is_data_ctor = (fun _57_4 -> (match (_57_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _57_637 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _146_322 = (let _146_321 = (let _146_320 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _146_319 = (FStar_TypeChecker_Env.get_range env)
in (_146_320, _146_319)))
in FStar_Syntax_Syntax.Error (_146_321))
in (Prims.raise _146_322))
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
let g = (match ((let _146_323 = (FStar_Syntax_Subst.compress t1)
in _146_323.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_648) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _57_651 -> begin
(
# 433 "FStar.TypeChecker.Tc.fst"
let imp = ("uvar in term", env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (
# 434 "FStar.TypeChecker.Tc.fst"
let _57_653 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_653.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_653.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_653.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 439 "FStar.TypeChecker.Tc.fst"
let _57_659 = (FStar_Syntax_Util.type_u ())
in (match (_57_659) with
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
let _57_664 = x
in {FStar_Syntax_Syntax.ppname = _57_664.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_664.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (
# 446 "FStar.TypeChecker.Tc.fst"
let _57_670 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_670) with
| (e, t, implicits) -> begin
(
# 447 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _146_325 = (let _146_324 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_324))
in FStar_Util.Inr (_146_325))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _57_677; FStar_Syntax_Syntax.pos = _57_675; FStar_Syntax_Syntax.vars = _57_673}, us) -> begin
(
# 451 "FStar.TypeChecker.Tc.fst"
let us = (FStar_List.map (tc_universe env) us)
in (
# 452 "FStar.TypeChecker.Tc.fst"
let _57_687 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_687) with
| (us', t) -> begin
(
# 453 "FStar.TypeChecker.Tc.fst"
let _57_694 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _146_328 = (let _146_327 = (let _146_326 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _146_326))
in FStar_Syntax_Syntax.Error (_146_327))
in (Prims.raise _146_328))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _57_693 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (
# 458 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 458 "FStar.TypeChecker.Tc.fst"
let _57_696 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 458 "FStar.TypeChecker.Tc.fst"
let _57_698 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_698.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_698.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_696.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_696.FStar_Syntax_Syntax.fv_qual})
in (
# 459 "FStar.TypeChecker.Tc.fst"
let e = (let _146_331 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_331 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(
# 463 "FStar.TypeChecker.Tc.fst"
let _57_706 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_706) with
| (us, t) -> begin
(
# 464 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 464 "FStar.TypeChecker.Tc.fst"
let _57_707 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 464 "FStar.TypeChecker.Tc.fst"
let _57_709 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_709.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_709.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_707.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_707.FStar_Syntax_Syntax.fv_qual})
in (
# 465 "FStar.TypeChecker.Tc.fst"
let e = (let _146_332 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_332 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t)))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(
# 469 "FStar.TypeChecker.Tc.fst"
let t = (tc_constant env top.FStar_Syntax_Syntax.pos c)
in (
# 470 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 474 "FStar.TypeChecker.Tc.fst"
let _57_723 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_723) with
| (bs, c) -> begin
(
# 475 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 476 "FStar.TypeChecker.Tc.fst"
let _57_728 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_728) with
| (env, _57_727) -> begin
(
# 477 "FStar.TypeChecker.Tc.fst"
let _57_733 = (tc_binders env bs)
in (match (_57_733) with
| (bs, env, g, us) -> begin
(
# 478 "FStar.TypeChecker.Tc.fst"
let _57_737 = (tc_comp env c)
in (match (_57_737) with
| (c, uc, f) -> begin
(
# 479 "FStar.TypeChecker.Tc.fst"
let e = (
# 479 "FStar.TypeChecker.Tc.fst"
let _57_738 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _57_738.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_738.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_738.FStar_Syntax_Syntax.vars})
in (
# 480 "FStar.TypeChecker.Tc.fst"
let _57_741 = (check_smt_pat env e bs c)
in (
# 481 "FStar.TypeChecker.Tc.fst"
let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (
# 482 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 483 "FStar.TypeChecker.Tc.fst"
let g = (let _146_333 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _146_333))
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
let _57_757 = (let _146_335 = (let _146_334 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_334)::[])
in (FStar_Syntax_Subst.open_term _146_335 phi))
in (match (_57_757) with
| (x, phi) -> begin
(
# 494 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 495 "FStar.TypeChecker.Tc.fst"
let _57_762 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_762) with
| (env, _57_761) -> begin
(
# 496 "FStar.TypeChecker.Tc.fst"
let _57_767 = (let _146_336 = (FStar_List.hd x)
in (tc_binder env _146_336))
in (match (_57_767) with
| (x, env, f1, u) -> begin
(
# 497 "FStar.TypeChecker.Tc.fst"
let _57_768 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_339 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _146_338 = (FStar_Syntax_Print.term_to_string phi)
in (let _146_337 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _146_339 _146_338 _146_337))))
end else begin
()
end
in (
# 500 "FStar.TypeChecker.Tc.fst"
let _57_773 = (FStar_Syntax_Util.type_u ())
in (match (_57_773) with
| (t_phi, _57_772) -> begin
(
# 501 "FStar.TypeChecker.Tc.fst"
let _57_778 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_57_778) with
| (phi, _57_776, f2) -> begin
(
# 502 "FStar.TypeChecker.Tc.fst"
let e = (
# 502 "FStar.TypeChecker.Tc.fst"
let _57_779 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _57_779.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_779.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_779.FStar_Syntax_Syntax.vars})
in (
# 503 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 504 "FStar.TypeChecker.Tc.fst"
let g = (let _146_340 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _146_340))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _57_787) -> begin
(
# 508 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (
# 509 "FStar.TypeChecker.Tc.fst"
let _57_793 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_341 = (FStar_Syntax_Print.term_to_string (
# 510 "FStar.TypeChecker.Tc.fst"
let _57_791 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _57_791.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_791.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_791.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _146_341))
end else begin
()
end
in (
# 511 "FStar.TypeChecker.Tc.fst"
let _57_797 = (FStar_Syntax_Subst.open_term bs body)
in (match (_57_797) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _57_799 -> begin
(let _146_343 = (let _146_342 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _146_342))
in (FStar_All.failwith _146_343))
end)))))
and tc_constant : FStar_TypeChecker_Env.env  ->  FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun env r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_57_805) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_57_808, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_57_813, Some (FStar_Const.Unsigned, FStar_Const.Int8)) -> begin
FStar_TypeChecker_Common.t_uint8
end
| FStar_Const.Const_int (_57_821, Some (FStar_Const.Signed, FStar_Const.Int8)) -> begin
FStar_TypeChecker_Common.t_int8
end
| FStar_Const.Const_int (_57_829, Some (FStar_Const.Unsigned, FStar_Const.Int16)) -> begin
FStar_TypeChecker_Common.t_uint16
end
| FStar_Const.Const_int (_57_837, Some (FStar_Const.Signed, FStar_Const.Int16)) -> begin
FStar_TypeChecker_Common.t_int16
end
| FStar_Const.Const_int (_57_845, Some (FStar_Const.Unsigned, FStar_Const.Int32)) -> begin
FStar_TypeChecker_Common.t_uint32
end
| FStar_Const.Const_int (_57_853, Some (FStar_Const.Signed, FStar_Const.Int32)) -> begin
FStar_TypeChecker_Common.t_int32
end
| FStar_Const.Const_int (_57_861, Some (FStar_Const.Unsigned, FStar_Const.Int64)) -> begin
FStar_TypeChecker_Common.t_uint64
end
| FStar_Const.Const_int (_57_869, Some (FStar_Const.Signed, FStar_Const.Int64)) -> begin
FStar_TypeChecker_Common.t_int64
end
| FStar_Const.Const_string (_57_877) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_57_880) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_57_883) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_57_887) -> begin
(
# 535 "FStar.TypeChecker.Tc.fst"
let fail = (fun _57_890 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Range constant cannot be checked in this context; expected an instance of \'range_of\'", r))))
end))
in (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(fail ())
end
| Some (t) -> begin
if (let _146_349 = (FStar_Syntax_Util.destruct t FStar_Syntax_Const.range_of_lid)
in (FStar_Option.isSome _146_349)) then begin
t
end else begin
(fail ())
end
end))
end
| _57_895 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 556 "FStar.TypeChecker.Tc.fst"
let _57_902 = (FStar_Syntax_Util.type_u ())
in (match (_57_902) with
| (k, u) -> begin
(
# 557 "FStar.TypeChecker.Tc.fst"
let _57_907 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_907) with
| (t, _57_905, g) -> begin
(let _146_352 = (FStar_Syntax_Syntax.mk_Total t)
in (_146_352, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 561 "FStar.TypeChecker.Tc.fst"
let _57_912 = (FStar_Syntax_Util.type_u ())
in (match (_57_912) with
| (k, u) -> begin
(
# 562 "FStar.TypeChecker.Tc.fst"
let _57_917 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_917) with
| (t, _57_915, g) -> begin
(let _146_353 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_146_353, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 566 "FStar.TypeChecker.Tc.fst"
let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (
# 567 "FStar.TypeChecker.Tc.fst"
let tc = (let _146_355 = (let _146_354 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_146_354)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _146_355 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 568 "FStar.TypeChecker.Tc.fst"
let _57_926 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_57_926) with
| (tc, _57_924, f) -> begin
(
# 569 "FStar.TypeChecker.Tc.fst"
let _57_930 = (FStar_Syntax_Util.head_and_args tc)
in (match (_57_930) with
| (_57_928, args) -> begin
(
# 570 "FStar.TypeChecker.Tc.fst"
let _57_933 = (let _146_357 = (FStar_List.hd args)
in (let _146_356 = (FStar_List.tl args)
in (_146_357, _146_356)))
in (match (_57_933) with
| (res, args) -> begin
(
# 571 "FStar.TypeChecker.Tc.fst"
let _57_949 = (let _146_359 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _57_5 -> (match (_57_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(
# 573 "FStar.TypeChecker.Tc.fst"
let _57_940 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_940) with
| (env, _57_939) -> begin
(
# 574 "FStar.TypeChecker.Tc.fst"
let _57_945 = (tc_tot_or_gtot_term env e)
in (match (_57_945) with
| (e, _57_943, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _146_359 FStar_List.unzip))
in (match (_57_949) with
| (flags, guards) -> begin
(
# 577 "FStar.TypeChecker.Tc.fst"
let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| _57_954 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _146_361 = (FStar_Syntax_Syntax.mk_Comp (
# 580 "FStar.TypeChecker.Tc.fst"
let _57_956 = c
in {FStar_Syntax_Syntax.effect_name = _57_956.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _57_956.FStar_Syntax_Syntax.flags}))
in (let _146_360 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_146_361, u, _146_360))))
end))
end))
end))
end))))
end))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (
# 587 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun u -> (
# 588 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_57_964) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _146_366 = (aux u)
in FStar_Syntax_Syntax.U_succ (_146_366))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _146_367 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_146_367))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _146_371 = (let _146_370 = (let _146_369 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _146_368 = (FStar_TypeChecker_Env.get_range env)
in (_146_369, _146_368)))
in FStar_Syntax_Syntax.Error (_146_370))
in (Prims.raise _146_371))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _146_372 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_372 Prims.snd))
end
| _57_979 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (
# 610 "FStar.TypeChecker.Tc.fst"
let fail = (fun msg t -> (let _146_381 = (let _146_380 = (let _146_379 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_146_379, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_380))
in (Prims.raise _146_381)))
in (
# 619 "FStar.TypeChecker.Tc.fst"
let check_binders = (fun env bs bs_expected -> (
# 624 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun _57_997 bs bs_expected -> (match (_57_997) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| ((hd, imp)::bs, (hd_expected, imp')::bs_expected) -> begin
(
# 628 "FStar.TypeChecker.Tc.fst"
let _57_1028 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _146_398 = (let _146_397 = (let _146_396 = (let _146_394 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _146_394))
in (let _146_395 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_146_396, _146_395)))
in FStar_Syntax_Syntax.Error (_146_397))
in (Prims.raise _146_398))
end
| _57_1027 -> begin
()
end)
in (
# 635 "FStar.TypeChecker.Tc.fst"
let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (
# 636 "FStar.TypeChecker.Tc.fst"
let _57_1045 = (match ((let _146_399 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _146_399.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _57_1033 -> begin
(
# 639 "FStar.TypeChecker.Tc.fst"
let _57_1034 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_400 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _146_400))
end else begin
()
end
in (
# 640 "FStar.TypeChecker.Tc.fst"
let _57_1040 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_57_1040) with
| (t, _57_1038, g1) -> begin
(
# 641 "FStar.TypeChecker.Tc.fst"
let g2 = (let _146_402 = (FStar_TypeChecker_Env.get_range env)
in (let _146_401 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _146_402 "Type annotation on parameter incompatible with the expected type" _146_401)))
in (
# 645 "FStar.TypeChecker.Tc.fst"
let g = (let _146_403 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _146_403))
in (t, g)))
end)))
end)
in (match (_57_1045) with
| (t, g) -> begin
(
# 647 "FStar.TypeChecker.Tc.fst"
let hd = (
# 647 "FStar.TypeChecker.Tc.fst"
let _57_1046 = hd
in {FStar_Syntax_Syntax.ppname = _57_1046.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1046.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 648 "FStar.TypeChecker.Tc.fst"
let b = (hd, imp)
in (
# 649 "FStar.TypeChecker.Tc.fst"
let b_expected = (hd_expected, imp')
in (
# 650 "FStar.TypeChecker.Tc.fst"
let env = (maybe_push_binding env b)
in (
# 651 "FStar.TypeChecker.Tc.fst"
let subst = (let _146_404 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _146_404))
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
# 661 "FStar.TypeChecker.Tc.fst"
let rec expected_function_typ = (fun env t0 body -> (match (t0) with
| None -> begin
(
# 672 "FStar.TypeChecker.Tc.fst"
let _57_1067 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1066 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (
# 675 "FStar.TypeChecker.Tc.fst"
let _57_1074 = (tc_binders env bs)
in (match (_57_1074) with
| (bs, envbody, g, _57_1073) -> begin
(
# 676 "FStar.TypeChecker.Tc.fst"
let _57_1092 = (match ((let _146_411 = (FStar_Syntax_Subst.compress body)
in _146_411.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _57_1079) -> begin
(
# 678 "FStar.TypeChecker.Tc.fst"
let _57_1086 = (tc_comp envbody c)
in (match (_57_1086) with
| (c, _57_1084, g') -> begin
(let _146_412 = (FStar_TypeChecker_Rel.conj_guard g g')
in (Some (c), body, _146_412))
end))
end
| _57_1088 -> begin
(None, body, g)
end)
in (match (_57_1092) with
| (copt, body, g) -> begin
(None, bs, [], copt, envbody, body, g)
end))
end)))
end
| Some (t) -> begin
(
# 684 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 685 "FStar.TypeChecker.Tc.fst"
let rec as_function_typ = (fun norm t -> (match ((let _146_417 = (FStar_Syntax_Subst.compress t)
in _146_417.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 689 "FStar.TypeChecker.Tc.fst"
let _57_1119 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1118 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 690 "FStar.TypeChecker.Tc.fst"
let _57_1126 = (tc_binders env bs)
in (match (_57_1126) with
| (bs, envbody, g, _57_1125) -> begin
(
# 691 "FStar.TypeChecker.Tc.fst"
let _57_1130 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_57_1130) with
| (envbody, _57_1129) -> begin
(Some ((t, true)), bs, [], None, envbody, body, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _57_1133) -> begin
(
# 697 "FStar.TypeChecker.Tc.fst"
let _57_1144 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_57_1144) with
| (_57_1137, bs, bs', copt, env, body, g) -> begin
(Some ((t, false)), bs, bs', copt, env, body, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 701 "FStar.TypeChecker.Tc.fst"
let _57_1151 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_57_1151) with
| (bs_expected, c_expected) -> begin
(
# 708 "FStar.TypeChecker.Tc.fst"
let check_actuals_against_formals = (fun env bs bs_expected -> (
# 709 "FStar.TypeChecker.Tc.fst"
let rec handle_more = (fun _57_1162 c_expected -> (match (_57_1162) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _146_428 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _146_428))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(
# 714 "FStar.TypeChecker.Tc.fst"
let c = (let _146_429 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _146_429))
in (let _146_430 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _146_430)))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(
# 718 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.subst_comp subst c_expected)
in if (FStar_Syntax_Util.is_total_comp c) then begin
(
# 721 "FStar.TypeChecker.Tc.fst"
let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 724 "FStar.TypeChecker.Tc.fst"
let _57_1183 = (check_binders env more_bs bs_expected)
in (match (_57_1183) with
| (env, bs', more, guard', subst) -> begin
(let _146_432 = (let _146_431 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _146_431, subst))
in (handle_more _146_432 c_expected))
end))
end
| _57_1185 -> begin
(let _146_434 = (let _146_433 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _146_433))
in (fail _146_434 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _146_435 = (check_binders env bs bs_expected)
in (handle_more _146_435 c_expected))))
in (
# 731 "FStar.TypeChecker.Tc.fst"
let mk_letrec_env = (fun envbody bs c -> (
# 732 "FStar.TypeChecker.Tc.fst"
let letrecs = (guard_letrecs envbody bs c)
in (
# 733 "FStar.TypeChecker.Tc.fst"
let envbody = (
# 733 "FStar.TypeChecker.Tc.fst"
let _57_1191 = envbody
in {FStar_TypeChecker_Env.solver = _57_1191.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1191.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1191.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1191.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1191.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1191.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1191.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1191.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1191.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1191.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1191.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1191.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_1191.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1191.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1191.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1191.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1191.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1191.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1191.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1191.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _57_1196 _57_1199 -> (match ((_57_1196, _57_1199)) with
| ((env, letrec_binders), (l, t)) -> begin
(
# 737 "FStar.TypeChecker.Tc.fst"
let _57_1205 = (let _146_445 = (let _146_444 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_444 Prims.fst))
in (tc_term _146_445 t))
in (match (_57_1205) with
| (t, _57_1202, _57_1204) -> begin
(
# 738 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (
# 739 "FStar.TypeChecker.Tc.fst"
let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _146_446 = (FStar_Syntax_Syntax.mk_binder (
# 740 "FStar.TypeChecker.Tc.fst"
let _57_1209 = x
in {FStar_Syntax_Syntax.ppname = _57_1209.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1209.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_146_446)::letrec_binders)
end
| _57_1212 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (
# 745 "FStar.TypeChecker.Tc.fst"
let _57_1218 = (check_actuals_against_formals env bs bs_expected)
in (match (_57_1218) with
| (envbody, bs, g, c) -> begin
(
# 746 "FStar.TypeChecker.Tc.fst"
let _57_1221 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_57_1221) with
| (envbody, letrecs) -> begin
(
# 747 "FStar.TypeChecker.Tc.fst"
let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, body, g))
end))
end))))
end))
end
| _57_1224 -> begin
if (not (norm)) then begin
(let _146_447 = (unfold_whnf env t)
in (as_function_typ true _146_447))
end else begin
(
# 755 "FStar.TypeChecker.Tc.fst"
let _57_1234 = (expected_function_typ env None body)
in (match (_57_1234) with
| (_57_1226, bs, _57_1229, c_opt, envbody, body, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, body, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (
# 759 "FStar.TypeChecker.Tc.fst"
let use_eq = env.FStar_TypeChecker_Env.use_eq
in (
# 760 "FStar.TypeChecker.Tc.fst"
let _57_1238 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1238) with
| (env, topt) -> begin
(
# 762 "FStar.TypeChecker.Tc.fst"
let _57_1242 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_448 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _146_448 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (
# 767 "FStar.TypeChecker.Tc.fst"
let _57_1251 = (expected_function_typ env topt body)
in (match (_57_1251) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(
# 768 "FStar.TypeChecker.Tc.fst"
let _57_1257 = (tc_term (
# 768 "FStar.TypeChecker.Tc.fst"
let _57_1252 = envbody
in {FStar_TypeChecker_Env.solver = _57_1252.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1252.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1252.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1252.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1252.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1252.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1252.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1252.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1252.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1252.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1252.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1252.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1252.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1252.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1252.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1252.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1252.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1252.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1252.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_57_1257) with
| (body, cbody, guard_body) -> begin
(
# 770 "FStar.TypeChecker.Tc.fst"
let _57_1258 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_452 = (FStar_Syntax_Print.term_to_string body)
in (let _146_451 = (let _146_449 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _146_449))
in (let _146_450 = (FStar_TypeChecker_Rel.guard_to_string env guard_body)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _146_452 _146_451 _146_450))))
end else begin
()
end
in (
# 776 "FStar.TypeChecker.Tc.fst"
let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (
# 779 "FStar.TypeChecker.Tc.fst"
let _57_1261 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _146_455 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _146_454 = (let _146_453 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _146_453))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _146_455 _146_454)))
end else begin
()
end
in (
# 784 "FStar.TypeChecker.Tc.fst"
let _57_1268 = (let _146_457 = (let _146_456 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _146_456))
in (check_expected_effect (
# 784 "FStar.TypeChecker.Tc.fst"
let _57_1263 = envbody
in {FStar_TypeChecker_Env.solver = _57_1263.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1263.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1263.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1263.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1263.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1263.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1263.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1263.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1263.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1263.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1263.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1263.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1263.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1263.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1263.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1263.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1263.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1263.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1263.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1263.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _146_457))
in (match (_57_1268) with
| (body, cbody, guard) -> begin
(
# 785 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (
# 786 "FStar.TypeChecker.Tc.fst"
let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _146_458 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _146_458))
end else begin
(
# 788 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (
# 791 "FStar.TypeChecker.Tc.fst"
let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (
# 792 "FStar.TypeChecker.Tc.fst"
let e = (let _146_461 = (let _146_460 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _146_459 -> FStar_Util.Inl (_146_459)))
in Some (_146_460))
in (FStar_Syntax_Util.abs bs body _146_461))
in (
# 793 "FStar.TypeChecker.Tc.fst"
let _57_1291 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(
# 795 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_1280) -> begin
(e, t, guard)
end
| _57_1283 -> begin
(
# 802 "FStar.TypeChecker.Tc.fst"
let _57_1286 = if use_teq then begin
(let _146_462 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _146_462))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_57_1286) with
| (e, guard') -> begin
(let _146_463 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _146_463))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_57_1291) with
| (e, tfun, guard) -> begin
(
# 811 "FStar.TypeChecker.Tc.fst"
let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (
# 812 "FStar.TypeChecker.Tc.fst"
let _57_1295 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_57_1295) with
| (c, g) -> begin
(e, c, g)
end)))
end))))))
end)))))
end))
end)))
end)))))))
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead ghead args expected_topt -> (
# 820 "FStar.TypeChecker.Tc.fst"
let n_args = (FStar_List.length args)
in (
# 821 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 822 "FStar.TypeChecker.Tc.fst"
let thead = chead.FStar_Syntax_Syntax.res_typ
in (
# 823 "FStar.TypeChecker.Tc.fst"
let _57_1305 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_472 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _146_471 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _146_472 _146_471)))
end else begin
()
end
in (
# 824 "FStar.TypeChecker.Tc.fst"
let rec check_function_app = (fun norm tf -> (match ((let _146_477 = (FStar_Syntax_Util.unrefine tf)
in _146_477.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 828 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| (e, imp)::tl -> begin
(
# 831 "FStar.TypeChecker.Tc.fst"
let _57_1339 = (tc_term env e)
in (match (_57_1339) with
| (e, c, g_e) -> begin
(
# 832 "FStar.TypeChecker.Tc.fst"
let _57_1343 = (tc_args env tl)
in (match (_57_1343) with
| (args, comps, g_rest) -> begin
(let _146_482 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, (c)::comps, _146_482))
end))
end))
end))
in (
# 840 "FStar.TypeChecker.Tc.fst"
let _57_1347 = (tc_args env args)
in (match (_57_1347) with
| (args, comps, g_args) -> begin
(
# 841 "FStar.TypeChecker.Tc.fst"
let bs = (let _146_484 = (FStar_All.pipe_right comps (FStar_List.map (fun c -> (c.FStar_Syntax_Syntax.res_typ, None))))
in (FStar_Syntax_Util.null_binders_of_tks _146_484))
in (
# 842 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _57_1354 -> begin
FStar_Syntax_Util.ml_comp
end)
in (
# 845 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _146_499 = (FStar_Syntax_Subst.compress t)
in _146_499.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_1360) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _57_1365 -> begin
ml_or_tot
end)
end)
in (
# 852 "FStar.TypeChecker.Tc.fst"
let cres = (let _146_504 = (let _146_503 = (let _146_502 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_502 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _146_503))
in (ml_or_tot _146_504 r))
in (
# 853 "FStar.TypeChecker.Tc.fst"
let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (
# 854 "FStar.TypeChecker.Tc.fst"
let _57_1369 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_507 = (FStar_Syntax_Print.term_to_string head)
in (let _146_506 = (FStar_Syntax_Print.term_to_string tf)
in (let _146_505 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _146_507 _146_506 _146_505))))
end else begin
()
end
in (
# 859 "FStar.TypeChecker.Tc.fst"
let _57_1371 = (let _146_508 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _146_508))
in (
# 860 "FStar.TypeChecker.Tc.fst"
let comp = (let _146_511 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_TypeChecker_Util.bind env None c (None, out))) ((chead)::comps) _146_511))
in (let _146_513 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _146_512 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_146_513, comp, _146_512)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 864 "FStar.TypeChecker.Tc.fst"
let _57_1382 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_1382) with
| (bs, c) -> begin
(
# 866 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun _57_1390 bs cres args -> (match (_57_1390) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (_57_1397)))::rest, (_57_1405, None)::_57_1403) -> begin
(
# 877 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 878 "FStar.TypeChecker.Tc.fst"
let _57_1411 = (check_no_escape (Some (head)) env fvs t)
in (
# 879 "FStar.TypeChecker.Tc.fst"
let _57_1417 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_57_1417) with
| (varg, _57_1415, implicits) -> begin
(
# 880 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (
# 881 "FStar.TypeChecker.Tc.fst"
let arg = (let _146_522 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _146_522))
in (let _146_524 = (let _146_523 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _146_523, fvs))
in (tc_args _146_524 rest cres args))))
end))))
end
| ((x, aqual)::rest, (e, aq)::rest') -> begin
(
# 885 "FStar.TypeChecker.Tc.fst"
let _57_1449 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _57_1448 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (
# 890 "FStar.TypeChecker.Tc.fst"
let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 891 "FStar.TypeChecker.Tc.fst"
let x = (
# 891 "FStar.TypeChecker.Tc.fst"
let _57_1452 = x
in {FStar_Syntax_Syntax.ppname = _57_1452.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1452.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (
# 892 "FStar.TypeChecker.Tc.fst"
let _57_1455 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_525 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _146_525))
end else begin
()
end
in (
# 893 "FStar.TypeChecker.Tc.fst"
let _57_1457 = (check_no_escape (Some (head)) env fvs targ)
in (
# 894 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (
# 895 "FStar.TypeChecker.Tc.fst"
let env = (
# 895 "FStar.TypeChecker.Tc.fst"
let _57_1460 = env
in {FStar_TypeChecker_Env.solver = _57_1460.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1460.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1460.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1460.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1460.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1460.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1460.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1460.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1460.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1460.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1460.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1460.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1460.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1460.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1460.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _57_1460.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1460.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1460.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1460.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1460.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 896 "FStar.TypeChecker.Tc.fst"
let _57_1463 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_528 = (FStar_Syntax_Print.tag_of_term e)
in (let _146_527 = (FStar_Syntax_Print.term_to_string e)
in (let _146_526 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _146_528 _146_527 _146_526))))
end else begin
()
end
in (
# 897 "FStar.TypeChecker.Tc.fst"
let _57_1468 = (tc_term env e)
in (match (_57_1468) with
| (e, c, g_e) -> begin
(
# 898 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (
# 900 "FStar.TypeChecker.Tc.fst"
let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(
# 902 "FStar.TypeChecker.Tc.fst"
let subst = (let _146_529 = (FStar_List.hd bs)
in (maybe_extend_subst subst _146_529 e))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(
# 905 "FStar.TypeChecker.Tc.fst"
let subst = (let _146_530 = (FStar_List.hd bs)
in (maybe_extend_subst subst _146_530 e))
in (
# 906 "FStar.TypeChecker.Tc.fst"
let _57_1475 = (((Some (x), c))::comps, g)
in (match (_57_1475) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _146_531 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _146_531)) then begin
(
# 910 "FStar.TypeChecker.Tc.fst"
let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (
# 911 "FStar.TypeChecker.Tc.fst"
let arg' = (let _146_532 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _146_532))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (newx), c))::comps, g, fvs) rest cres rest')))
end else begin
(let _146_536 = (let _146_535 = (let _146_534 = (let _146_533 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _146_533))
in (_146_534)::arg_rets)
in (subst, (arg)::outargs, _146_535, ((Some (x), c))::comps, g, (x)::fvs))
in (tc_args _146_536 rest cres rest'))
end
end
end))
end))))))))))
end
| (_57_1479, []) -> begin
(
# 920 "FStar.TypeChecker.Tc.fst"
let _57_1482 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (
# 921 "FStar.TypeChecker.Tc.fst"
let _57_1500 = (match (bs) with
| [] -> begin
(
# 924 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (
# 930 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (
# 932 "FStar.TypeChecker.Tc.fst"
let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _57_1490 -> (match (_57_1490) with
| (_57_1488, c) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (
# 939 "FStar.TypeChecker.Tc.fst"
let cres = if refine_with_equality then begin
(let _146_538 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _146_538 cres))
end else begin
(
# 945 "FStar.TypeChecker.Tc.fst"
let _57_1492 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_541 = (FStar_Syntax_Print.term_to_string head)
in (let _146_540 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _146_539 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _146_541 _146_540 _146_539))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _57_1496 -> begin
(
# 954 "FStar.TypeChecker.Tc.fst"
let g = (let _146_542 = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (FStar_All.pipe_right _146_542 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _146_547 = (let _146_546 = (let _146_545 = (let _146_544 = (let _146_543 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _146_543))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _146_544))
in (FStar_Syntax_Syntax.mk_Total _146_545))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_546))
in (_146_547, g)))
end)
in (match (_57_1500) with
| (cres, g) -> begin
(
# 957 "FStar.TypeChecker.Tc.fst"
let _57_1501 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_548 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _146_548))
end else begin
()
end
in (
# 958 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_List.fold_left (fun out c -> (FStar_TypeChecker_Util.bind env None (Prims.snd c) ((Prims.fst c), out))) cres comps)
in (
# 959 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.bind env None chead (None, comp))
in (
# 960 "FStar.TypeChecker.Tc.fst"
let app = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev outargs) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (
# 961 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.record_application_site env app comp)
in (
# 962 "FStar.TypeChecker.Tc.fst"
let _57_1511 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp g)
in (match (_57_1511) with
| (comp, g) -> begin
(
# 963 "FStar.TypeChecker.Tc.fst"
let _57_1512 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_554 = (FStar_TypeChecker_Normalize.term_to_string env app)
in (let _146_553 = (let _146_552 = (comp.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Print.comp_to_string _146_552))
in (FStar_Util.print2 "\t Type of app term %s is %s\n" _146_554 _146_553)))
end else begin
()
end
in (app, comp, g))
end)))))))
end)))
end
| ([], arg::_57_1516) -> begin
(
# 969 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun norm tres -> (
# 970 "FStar.TypeChecker.Tc.fst"
let tres = (let _146_559 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _146_559 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(
# 973 "FStar.TypeChecker.Tc.fst"
let _57_1528 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_560 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _146_560))
end else begin
()
end
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs (FStar_Syntax_Util.lcomp_of_comp cres') args))
end
| _57_1531 when (not (norm)) -> begin
(let _146_561 = (unfold_whnf env tres)
in (aux true _146_561))
end
| _57_1533 -> begin
(let _146_567 = (let _146_566 = (let _146_565 = (let _146_563 = (FStar_TypeChecker_Normalize.term_to_string env tf)
in (let _146_562 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _146_563 _146_562)))
in (let _146_564 = (FStar_Syntax_Syntax.argpos arg)
in (_146_565, _146_564)))
in FStar_Syntax_Syntax.Error (_146_566))
in (Prims.raise _146_567))
end)))
in (aux false cres.FStar_Syntax_Syntax.res_typ))
end)
end))
in (tc_args ([], [], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs (FStar_Syntax_Util.lcomp_of_comp c) args))
end))
end
| _57_1535 -> begin
if (not (norm)) then begin
(let _146_568 = (unfold_whnf env tf)
in (check_function_app true _146_568))
end else begin
(let _146_571 = (let _146_570 = (let _146_569 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_146_569, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_570))
in (Prims.raise _146_571))
end
end))
in (let _146_573 = (let _146_572 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _146_572))
in (check_function_app false _146_573))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (
# 999 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1000 "FStar.TypeChecker.Tc.fst"
let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(
# 1003 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in (
# 1004 "FStar.TypeChecker.Tc.fst"
let _57_1571 = (FStar_List.fold_left2 (fun _57_1552 _57_1555 _57_1558 -> (match ((_57_1552, _57_1555, _57_1558)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(
# 1005 "FStar.TypeChecker.Tc.fst"
let _57_1559 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1006 "FStar.TypeChecker.Tc.fst"
let _57_1564 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_57_1564) with
| (e, c, g) -> begin
(
# 1007 "FStar.TypeChecker.Tc.fst"
let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (
# 1008 "FStar.TypeChecker.Tc.fst"
let g = (let _146_583 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _146_583 g))
in (
# 1009 "FStar.TypeChecker.Tc.fst"
let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _146_587 = (let _146_585 = (let _146_584 = (FStar_Syntax_Syntax.as_arg e)
in (_146_584)::[])
in (FStar_List.append seen _146_585))
in (let _146_586 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_146_587, _146_586, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_57_1571) with
| (args, guard, ghost) -> begin
(
# 1013 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (
# 1014 "FStar.TypeChecker.Tc.fst"
let c = if ghost then begin
(let _146_588 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _146_588 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (
# 1015 "FStar.TypeChecker.Tc.fst"
let _57_1576 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_57_1576) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _57_1578 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (
# 1035 "FStar.TypeChecker.Tc.fst"
let _57_1585 = (FStar_Syntax_Subst.open_branch branch)
in (match (_57_1585) with
| (pattern, when_clause, branch_exp) -> begin
(
# 1036 "FStar.TypeChecker.Tc.fst"
let _57_1590 = branch
in (match (_57_1590) with
| (cpat, _57_1588, cbr) -> begin
(
# 1039 "FStar.TypeChecker.Tc.fst"
let tc_pat = (fun allow_implicits pat_t p0 -> (
# 1046 "FStar.TypeChecker.Tc.fst"
let _57_1598 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_57_1598) with
| (pat_bvs, exps, p) -> begin
(
# 1047 "FStar.TypeChecker.Tc.fst"
let _57_1599 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_600 = (FStar_Syntax_Print.pat_to_string p0)
in (let _146_599 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _146_600 _146_599)))
end else begin
()
end
in (
# 1049 "FStar.TypeChecker.Tc.fst"
let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (
# 1050 "FStar.TypeChecker.Tc.fst"
let _57_1605 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_57_1605) with
| (env1, _57_1604) -> begin
(
# 1051 "FStar.TypeChecker.Tc.fst"
let env1 = (
# 1051 "FStar.TypeChecker.Tc.fst"
let _57_1606 = env1
in {FStar_TypeChecker_Env.solver = _57_1606.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1606.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1606.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1606.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1606.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1606.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1606.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1606.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _57_1606.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1606.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1606.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1606.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1606.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1606.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1606.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1606.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1606.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1606.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1606.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1606.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1052 "FStar.TypeChecker.Tc.fst"
let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (
# 1053 "FStar.TypeChecker.Tc.fst"
let _57_1645 = (let _146_623 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (
# 1054 "FStar.TypeChecker.Tc.fst"
let _57_1611 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_603 = (FStar_Syntax_Print.term_to_string e)
in (let _146_602 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _146_603 _146_602)))
end else begin
()
end
in (
# 1057 "FStar.TypeChecker.Tc.fst"
let _57_1616 = (tc_term env1 e)
in (match (_57_1616) with
| (e, lc, g) -> begin
(
# 1059 "FStar.TypeChecker.Tc.fst"
let _57_1617 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_605 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _146_604 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _146_605 _146_604)))
end else begin
()
end
in (
# 1062 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (
# 1063 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (
# 1064 "FStar.TypeChecker.Tc.fst"
let _57_1623 = (let _146_606 = (FStar_TypeChecker_Rel.discharge_guard env (
# 1064 "FStar.TypeChecker.Tc.fst"
let _57_1621 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_1621.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_1621.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_1621.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _146_606 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1065 "FStar.TypeChecker.Tc.fst"
let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (
# 1066 "FStar.TypeChecker.Tc.fst"
let uvars_to_string = (fun uvs -> (let _146_611 = (let _146_610 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _146_610 (FStar_List.map (fun _57_1631 -> (match (_57_1631) with
| (u, _57_1630) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _146_611 (FStar_String.concat ", "))))
in (
# 1067 "FStar.TypeChecker.Tc.fst"
let uvs1 = (FStar_Syntax_Free.uvars e')
in (
# 1068 "FStar.TypeChecker.Tc.fst"
let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (
# 1069 "FStar.TypeChecker.Tc.fst"
let _57_1639 = if (let _146_612 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _146_612)) then begin
(
# 1070 "FStar.TypeChecker.Tc.fst"
let unresolved = (let _146_613 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _146_613 FStar_Util.set_elements))
in (let _146_621 = (let _146_620 = (let _146_619 = (let _146_618 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _146_617 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _146_616 = (let _146_615 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _57_1638 -> (match (_57_1638) with
| (u, _57_1637) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _146_615 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _146_618 _146_617 _146_616))))
in (_146_619, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_146_620))
in (Prims.raise _146_621)))
end else begin
()
end
in (
# 1077 "FStar.TypeChecker.Tc.fst"
let _57_1641 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_622 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _146_622))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _146_623 FStar_List.unzip))
in (match (_57_1645) with
| (exps, norm_exps) -> begin
(
# 1082 "FStar.TypeChecker.Tc.fst"
let p = (FStar_TypeChecker_Util.decorate_pattern env p exps)
in (p, pat_bvs, pat_env, exps, norm_exps))
end))))
end))))
end)))
in (
# 1086 "FStar.TypeChecker.Tc.fst"
let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (
# 1087 "FStar.TypeChecker.Tc.fst"
let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (
# 1088 "FStar.TypeChecker.Tc.fst"
let _57_1652 = (let _146_624 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _146_624 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_57_1652) with
| (scrutinee_env, _57_1651) -> begin
(
# 1091 "FStar.TypeChecker.Tc.fst"
let _57_1658 = (tc_pat true pat_t pattern)
in (match (_57_1658) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(
# 1094 "FStar.TypeChecker.Tc.fst"
let _57_1668 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(
# 1101 "FStar.TypeChecker.Tc.fst"
let _57_1665 = (let _146_625 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _146_625 e))
in (match (_57_1665) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_57_1668) with
| (when_clause, g_when) -> begin
(
# 1105 "FStar.TypeChecker.Tc.fst"
let _57_1672 = (tc_term pat_env branch_exp)
in (match (_57_1672) with
| (branch_exp, c, g_branch) -> begin
(
# 1109 "FStar.TypeChecker.Tc.fst"
let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _146_627 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _146_626 -> Some (_146_626)) _146_627))
end)
in (
# 1116 "FStar.TypeChecker.Tc.fst"
let _57_1728 = (
# 1119 "FStar.TypeChecker.Tc.fst"
let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (
# 1120 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _57_1690 -> begin
(
# 1126 "FStar.TypeChecker.Tc.fst"
let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _146_631 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _146_630 -> Some (_146_630)) _146_631))
end))
end))) None))
in (
# 1131 "FStar.TypeChecker.Tc.fst"
let _57_1698 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_57_1698) with
| (c, g_branch) -> begin
(
# 1135 "FStar.TypeChecker.Tc.fst"
let _57_1723 = (match ((eqs, when_condition)) with
| (None, None) -> begin
(c, g_when)
end
| (Some (f), None) -> begin
(
# 1141 "FStar.TypeChecker.Tc.fst"
let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1142 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _146_634 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _146_633 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_146_634, _146_633)))))
end
| (Some (f), Some (w)) -> begin
(
# 1147 "FStar.TypeChecker.Tc.fst"
let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1148 "FStar.TypeChecker.Tc.fst"
let g_fw = (let _146_635 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_146_635))
in (let _146_638 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _146_637 = (let _146_636 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _146_636 g_when))
in (_146_638, _146_637)))))
end
| (None, Some (w)) -> begin
(
# 1153 "FStar.TypeChecker.Tc.fst"
let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (
# 1154 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _146_639 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_146_639, g_when))))
end)
in (match (_57_1723) with
| (c_weak, g_when_weak) -> begin
(
# 1159 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _146_641 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _146_640 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_146_641, _146_640, g_branch))))
end))
end)))
in (match (_57_1728) with
| (c, g_when, g_branch) -> begin
(
# 1177 "FStar.TypeChecker.Tc.fst"
let branch_guard = (
# 1179 "FStar.TypeChecker.Tc.fst"
let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (
# 1180 "FStar.TypeChecker.Tc.fst"
let discriminate = (fun scrutinee_tm f -> if ((let _146_651 = (let _146_650 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _146_650))
in (FStar_List.length _146_651)) > 1) then begin
(
# 1183 "FStar.TypeChecker.Tc.fst"
let disc = (let _146_652 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _146_652 FStar_Syntax_Syntax.Delta_equational None))
in (
# 1184 "FStar.TypeChecker.Tc.fst"
let disc = (let _146_654 = (let _146_653 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_146_653)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _146_654 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _146_655 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_146_655)::[])))
end else begin
[]
end)
in (
# 1188 "FStar.TypeChecker.Tc.fst"
let fail = (fun _57_1738 -> (match (()) with
| () -> begin
(let _146_661 = (let _146_660 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _146_659 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _146_658 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _146_660 _146_659 _146_658))))
in (FStar_All.failwith _146_661))
end))
in (
# 1194 "FStar.TypeChecker.Tc.fst"
let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _57_1745) -> begin
(head_constructor t)
end
| _57_1749 -> begin
(fail ())
end))
in (
# 1199 "FStar.TypeChecker.Tc.fst"
let pat_exp = (let _146_664 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _146_664 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_57_1774) -> begin
(let _146_669 = (let _146_668 = (let _146_667 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _146_666 = (let _146_665 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_146_665)::[])
in (_146_667)::_146_666))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _146_668 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_146_669)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 1208 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _146_670 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _146_670))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 1213 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(
# 1216 "FStar.TypeChecker.Tc.fst"
let sub_term_guards = (let _146_677 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _57_1792 -> (match (_57_1792) with
| (ei, _57_1791) -> begin
(
# 1217 "FStar.TypeChecker.Tc.fst"
let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _57_1796 -> begin
(
# 1221 "FStar.TypeChecker.Tc.fst"
let sub_term = (let _146_676 = (let _146_673 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _146_673 FStar_Syntax_Syntax.Delta_equational None))
in (let _146_675 = (let _146_674 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_146_674)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _146_676 _146_675 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _146_677 FStar_List.flatten))
in (let _146_678 = (discriminate scrutinee_tm f)
in (FStar_List.append _146_678 sub_term_guards)))
end)
end
| _57_1800 -> begin
[]
end))))))
in (
# 1227 "FStar.TypeChecker.Tc.fst"
let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(
# 1230 "FStar.TypeChecker.Tc.fst"
let t = (let _146_683 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _146_683))
in (
# 1231 "FStar.TypeChecker.Tc.fst"
let _57_1808 = (FStar_Syntax_Util.type_u ())
in (match (_57_1808) with
| (k, _57_1807) -> begin
(
# 1232 "FStar.TypeChecker.Tc.fst"
let _57_1814 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_57_1814) with
| (t, _57_1811, _57_1813) -> begin
t
end))
end)))
end)
in (
# 1236 "FStar.TypeChecker.Tc.fst"
let branch_guard = (let _146_684 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _146_684 FStar_Syntax_Util.mk_disj_l))
in (
# 1239 "FStar.TypeChecker.Tc.fst"
let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
in (
# 1245 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (
# 1247 "FStar.TypeChecker.Tc.fst"
let _57_1822 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_685 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _146_685))
end else begin
()
end
in (let _146_686 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_146_686, branch_guard, c, guard)))))
end)))
end))
end))
end))
end)))))
end))
end)))
and check_top_level_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1261 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1264 "FStar.TypeChecker.Tc.fst"
let _57_1839 = (check_let_bound_def true env lb)
in (match (_57_1839) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(
# 1266 "FStar.TypeChecker.Tc.fst"
let _57_1851 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(
# 1269 "FStar.TypeChecker.Tc.fst"
let g1 = (let _146_689 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _146_689 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1270 "FStar.TypeChecker.Tc.fst"
let _57_1846 = (let _146_693 = (let _146_692 = (let _146_691 = (let _146_690 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _146_690))
in (_146_691)::[])
in (FStar_TypeChecker_Util.generalize env _146_692))
in (FStar_List.hd _146_693))
in (match (_57_1846) with
| (_57_1842, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_57_1851) with
| (g1, e1, univ_vars, c1) -> begin
(
# 1274 "FStar.TypeChecker.Tc.fst"
let _57_1861 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(
# 1276 "FStar.TypeChecker.Tc.fst"
let _57_1854 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_57_1854) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(
# 1279 "FStar.TypeChecker.Tc.fst"
let _57_1855 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _146_694 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _146_694 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _146_695 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_146_695, c1)))
end
end))
end else begin
(
# 1283 "FStar.TypeChecker.Tc.fst"
let _57_1857 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _146_696 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _146_696)))
end
in (match (_57_1861) with
| (e2, c1) -> begin
(
# 1288 "FStar.TypeChecker.Tc.fst"
let cres = (let _146_697 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_697))
in (
# 1289 "FStar.TypeChecker.Tc.fst"
let _57_1863 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1291 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _146_698 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_146_698, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _57_1867 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1308 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1311 "FStar.TypeChecker.Tc.fst"
let env = (
# 1311 "FStar.TypeChecker.Tc.fst"
let _57_1878 = env
in {FStar_TypeChecker_Env.solver = _57_1878.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1878.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1878.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1878.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1878.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1878.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1878.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1878.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1878.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1878.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1878.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1878.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1878.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1878.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1878.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1878.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1878.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1878.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1878.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1878.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1312 "FStar.TypeChecker.Tc.fst"
let _57_1887 = (let _146_702 = (let _146_701 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_701 Prims.fst))
in (check_let_bound_def false _146_702 lb))
in (match (_57_1887) with
| (e1, _57_1883, c1, g1, annotated) -> begin
(
# 1313 "FStar.TypeChecker.Tc.fst"
let x = (
# 1313 "FStar.TypeChecker.Tc.fst"
let _57_1888 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1888.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1888.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (
# 1314 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (
# 1315 "FStar.TypeChecker.Tc.fst"
let _57_1894 = (let _146_704 = (let _146_703 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_703)::[])
in (FStar_Syntax_Subst.open_term _146_704 e2))
in (match (_57_1894) with
| (xb, e2) -> begin
(
# 1316 "FStar.TypeChecker.Tc.fst"
let xbinder = (FStar_List.hd xb)
in (
# 1317 "FStar.TypeChecker.Tc.fst"
let x = (Prims.fst xbinder)
in (
# 1318 "FStar.TypeChecker.Tc.fst"
let _57_1900 = (let _146_705 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _146_705 e2))
in (match (_57_1900) with
| (e2, c2, g2) -> begin
(
# 1319 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (x), c2))
in (
# 1320 "FStar.TypeChecker.Tc.fst"
let e = (let _146_708 = (let _146_707 = (let _146_706 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _146_706))
in FStar_Syntax_Syntax.Tm_let (_146_707))
in (FStar_Syntax_Syntax.mk _146_708 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 1321 "FStar.TypeChecker.Tc.fst"
let x_eq_e1 = (let _146_711 = (let _146_710 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _146_710 e1))
in (FStar_All.pipe_left (fun _146_709 -> FStar_TypeChecker_Common.NonTrivial (_146_709)) _146_711))
in (
# 1322 "FStar.TypeChecker.Tc.fst"
let g2 = (let _146_713 = (let _146_712 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _146_712 g2))
in (FStar_TypeChecker_Rel.close_guard xb _146_713))
in (
# 1324 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if annotated then begin
(e, cres, guard)
end else begin
(
# 1328 "FStar.TypeChecker.Tc.fst"
let _57_1906 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end)))))
end))))
end))))
end)))
end
| _57_1909 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1337 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1340 "FStar.TypeChecker.Tc.fst"
let _57_1921 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1921) with
| (lbs, e2) -> begin
(
# 1342 "FStar.TypeChecker.Tc.fst"
let _57_1924 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1924) with
| (env0, topt) -> begin
(
# 1343 "FStar.TypeChecker.Tc.fst"
let _57_1927 = (build_let_rec_env true env0 lbs)
in (match (_57_1927) with
| (lbs, rec_env) -> begin
(
# 1344 "FStar.TypeChecker.Tc.fst"
let _57_1930 = (check_let_recs rec_env lbs)
in (match (_57_1930) with
| (lbs, g_lbs) -> begin
(
# 1345 "FStar.TypeChecker.Tc.fst"
let g_lbs = (let _146_716 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _146_716 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1347 "FStar.TypeChecker.Tc.fst"
let all_lb_names = (let _146_719 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _146_719 (fun _146_718 -> Some (_146_718))))
in (
# 1349 "FStar.TypeChecker.Tc.fst"
let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(
# 1355 "FStar.TypeChecker.Tc.fst"
let ecs = (let _146_723 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _146_722 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _146_722)))))
in (FStar_TypeChecker_Util.generalize env _146_723))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _57_1941 -> (match (_57_1941) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (
# 1362 "FStar.TypeChecker.Tc.fst"
let cres = (let _146_725 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_725))
in (
# 1363 "FStar.TypeChecker.Tc.fst"
let _57_1944 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1365 "FStar.TypeChecker.Tc.fst"
let _57_1948 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1948) with
| (lbs, e2) -> begin
(let _146_727 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_726 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_146_727, cres, _146_726)))
end)))))))
end))
end))
end))
end))
end
| _57_1950 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1376 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1379 "FStar.TypeChecker.Tc.fst"
let _57_1962 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1962) with
| (lbs, e2) -> begin
(
# 1381 "FStar.TypeChecker.Tc.fst"
let _57_1965 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1965) with
| (env0, topt) -> begin
(
# 1382 "FStar.TypeChecker.Tc.fst"
let _57_1968 = (build_let_rec_env false env0 lbs)
in (match (_57_1968) with
| (lbs, rec_env) -> begin
(
# 1383 "FStar.TypeChecker.Tc.fst"
let _57_1971 = (check_let_recs rec_env lbs)
in (match (_57_1971) with
| (lbs, g_lbs) -> begin
(
# 1385 "FStar.TypeChecker.Tc.fst"
let _57_1983 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (
# 1386 "FStar.TypeChecker.Tc.fst"
let x = (
# 1386 "FStar.TypeChecker.Tc.fst"
let _57_1974 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1974.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1974.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (
# 1387 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1387 "FStar.TypeChecker.Tc.fst"
let _57_1977 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _57_1977.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1977.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1977.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _57_1977.FStar_Syntax_Syntax.lbdef})
in (
# 1388 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], lb.FStar_Syntax_Syntax.lbtyp))
in (env, lb))))) env))
in (match (_57_1983) with
| (env, lbs) -> begin
(
# 1391 "FStar.TypeChecker.Tc.fst"
let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (
# 1393 "FStar.TypeChecker.Tc.fst"
let _57_1989 = (tc_term env e2)
in (match (_57_1989) with
| (e2, cres, g2) -> begin
(
# 1394 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (
# 1395 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (
# 1396 "FStar.TypeChecker.Tc.fst"
let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (
# 1397 "FStar.TypeChecker.Tc.fst"
let cres = (
# 1397 "FStar.TypeChecker.Tc.fst"
let _57_1993 = cres
in {FStar_Syntax_Syntax.eff_name = _57_1993.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _57_1993.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_1993.FStar_Syntax_Syntax.comp})
in (
# 1399 "FStar.TypeChecker.Tc.fst"
let _57_1998 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1998) with
| (lbs, e2) -> begin
(
# 1400 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_57_2001) -> begin
(e, cres, guard)
end
| None -> begin
(
# 1404 "FStar.TypeChecker.Tc.fst"
let _57_2004 = (check_no_escape None env bvs tres)
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
| _57_2007 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (
# 1415 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1416 "FStar.TypeChecker.Tc.fst"
let _57_2040 = (FStar_List.fold_left (fun _57_2014 lb -> (match (_57_2014) with
| (lbs, env) -> begin
(
# 1417 "FStar.TypeChecker.Tc.fst"
let _57_2019 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_57_2019) with
| (univ_vars, t, check_t) -> begin
(
# 1418 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (
# 1419 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (
# 1420 "FStar.TypeChecker.Tc.fst"
let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(
# 1425 "FStar.TypeChecker.Tc.fst"
let _57_2028 = (let _146_739 = (let _146_738 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _146_738))
in (tc_check_tot_or_gtot_term (
# 1425 "FStar.TypeChecker.Tc.fst"
let _57_2022 = env0
in {FStar_TypeChecker_Env.solver = _57_2022.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2022.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2022.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2022.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2022.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2022.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2022.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2022.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2022.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2022.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2022.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2022.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2022.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2022.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _57_2022.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2022.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2022.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2022.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2022.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2022.FStar_TypeChecker_Env.use_bv_sorts}) t _146_739))
in (match (_57_2028) with
| (t, _57_2026, g) -> begin
(
# 1426 "FStar.TypeChecker.Tc.fst"
let _57_2029 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (
# 1428 "FStar.TypeChecker.Tc.fst"
let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(
# 1430 "FStar.TypeChecker.Tc.fst"
let _57_2032 = env
in {FStar_TypeChecker_Env.solver = _57_2032.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2032.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2032.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2032.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2032.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2032.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2032.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2032.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2032.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2032.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2032.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2032.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2032.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_2032.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2032.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2032.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2032.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2032.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2032.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2032.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (
# 1432 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1432 "FStar.TypeChecker.Tc.fst"
let _57_2035 = lb
in {FStar_Syntax_Syntax.lbname = _57_2035.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _57_2035.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_57_2040) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (
# 1439 "FStar.TypeChecker.Tc.fst"
let _57_2053 = (let _146_744 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 1440 "FStar.TypeChecker.Tc.fst"
let _57_2047 = (let _146_743 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _146_743 lb.FStar_Syntax_Syntax.lbdef))
in (match (_57_2047) with
| (e, c, g) -> begin
(
# 1441 "FStar.TypeChecker.Tc.fst"
let _57_2048 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1443 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _146_744 FStar_List.unzip))
in (match (_57_2053) with
| (lbs, gs) -> begin
(
# 1445 "FStar.TypeChecker.Tc.fst"
let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (
# 1459 "FStar.TypeChecker.Tc.fst"
let _57_2061 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_2061) with
| (env1, _57_2060) -> begin
(
# 1460 "FStar.TypeChecker.Tc.fst"
let e1 = lb.FStar_Syntax_Syntax.lbdef
in (
# 1463 "FStar.TypeChecker.Tc.fst"
let _57_2067 = (check_lbtyp top_level env lb)
in (match (_57_2067) with
| (topt, wf_annot, univ_vars, env1) -> begin
(
# 1465 "FStar.TypeChecker.Tc.fst"
let _57_2068 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1469 "FStar.TypeChecker.Tc.fst"
let _57_2075 = (tc_maybe_toplevel_term (
# 1469 "FStar.TypeChecker.Tc.fst"
let _57_2070 = env1
in {FStar_TypeChecker_Env.solver = _57_2070.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2070.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2070.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2070.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2070.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2070.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2070.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2070.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2070.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2070.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2070.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2070.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2070.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _57_2070.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2070.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2070.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2070.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2070.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2070.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2070.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_57_2075) with
| (e1, c1, g1) -> begin
(
# 1472 "FStar.TypeChecker.Tc.fst"
let _57_2079 = (let _146_751 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_2076 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _146_751 e1 c1 wf_annot))
in (match (_57_2079) with
| (c1, guard_f) -> begin
(
# 1475 "FStar.TypeChecker.Tc.fst"
let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (
# 1477 "FStar.TypeChecker.Tc.fst"
let _57_2081 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_752 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _146_752))
end else begin
()
end
in (let _146_753 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _146_753))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (
# 1489 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 1492 "FStar.TypeChecker.Tc.fst"
let _57_2088 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _57_2091 -> begin
(
# 1496 "FStar.TypeChecker.Tc.fst"
let _57_2094 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_57_2094) with
| (univ_vars, t) -> begin
(
# 1497 "FStar.TypeChecker.Tc.fst"
let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _146_757 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _146_757))
end else begin
(
# 1504 "FStar.TypeChecker.Tc.fst"
let _57_2099 = (FStar_Syntax_Util.type_u ())
in (match (_57_2099) with
| (k, _57_2098) -> begin
(
# 1505 "FStar.TypeChecker.Tc.fst"
let _57_2104 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_57_2104) with
| (t, _57_2102, g) -> begin
(
# 1506 "FStar.TypeChecker.Tc.fst"
let _57_2105 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _146_760 = (let _146_758 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _146_758))
in (let _146_759 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _146_760 _146_759)))
end else begin
()
end
in (
# 1510 "FStar.TypeChecker.Tc.fst"
let t = (norm env1 t)
in (let _146_761 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _146_761))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _57_2111 -> (match (_57_2111) with
| (x, imp) -> begin
(
# 1515 "FStar.TypeChecker.Tc.fst"
let _57_2114 = (FStar_Syntax_Util.type_u ())
in (match (_57_2114) with
| (tu, u) -> begin
(
# 1516 "FStar.TypeChecker.Tc.fst"
let _57_2119 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_57_2119) with
| (t, _57_2117, g) -> begin
(
# 1517 "FStar.TypeChecker.Tc.fst"
let x = ((
# 1517 "FStar.TypeChecker.Tc.fst"
let _57_2120 = x
in {FStar_Syntax_Syntax.ppname = _57_2120.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2120.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (
# 1518 "FStar.TypeChecker.Tc.fst"
let _57_2123 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_765 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _146_764 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _146_765 _146_764)))
end else begin
()
end
in (let _146_766 = (maybe_push_binding env x)
in (x, _146_766, g, u))))
end))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe Prims.list) = (fun env bs -> (
# 1523 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_TypeChecker_Rel.trivial_guard, [])
end
| b::bs -> begin
(
# 1526 "FStar.TypeChecker.Tc.fst"
let _57_2138 = (tc_binder env b)
in (match (_57_2138) with
| (b, env', g, u) -> begin
(
# 1527 "FStar.TypeChecker.Tc.fst"
let _57_2143 = (aux env' bs)
in (match (_57_2143) with
| (bs, env', g', us) -> begin
(let _146_774 = (let _146_773 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _146_773))
in ((b)::bs, env', _146_774, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (
# 1532 "FStar.TypeChecker.Tc.fst"
let tc_args = (fun env args -> (FStar_List.fold_right (fun _57_2151 _57_2154 -> (match ((_57_2151, _57_2154)) with
| ((t, imp), (args, g)) -> begin
(
# 1536 "FStar.TypeChecker.Tc.fst"
let _57_2159 = (tc_term env t)
in (match (_57_2159) with
| (t, _57_2157, g') -> begin
(let _146_783 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _146_783))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _57_2163 -> (match (_57_2163) with
| (pats, g) -> begin
(
# 1539 "FStar.TypeChecker.Tc.fst"
let _57_2166 = (tc_args env p)
in (match (_57_2166) with
| (args, g') -> begin
(let _146_786 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _146_786))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1544 "FStar.TypeChecker.Tc.fst"
let _57_2172 = (tc_maybe_toplevel_term env e)
in (match (_57_2172) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(
# 1547 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (
# 1548 "FStar.TypeChecker.Tc.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 1549 "FStar.TypeChecker.Tc.fst"
let _57_2175 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_789 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _146_789))
end else begin
()
end
in (
# 1550 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 1551 "FStar.TypeChecker.Tc.fst"
let _57_2180 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _146_790 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_146_790, false))
end else begin
(let _146_791 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_146_791, true))
end
in (match (_57_2180) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _146_792 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _146_792))
end
| _57_2184 -> begin
if allow_ghost then begin
(let _146_795 = (let _146_794 = (let _146_793 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_146_793, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_794))
in (Prims.raise _146_795))
end else begin
(let _146_798 = (let _146_797 = (let _146_796 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_146_796, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_797))
in (Prims.raise _146_798))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 1565 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))

# 1569 "FStar.TypeChecker.Tc.fst"
let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (
# 1570 "FStar.TypeChecker.Tc.fst"
let _57_2194 = (tc_tot_or_gtot_term env t)
in (match (_57_2194) with
| (t, c, g) -> begin
(
# 1571 "FStar.TypeChecker.Tc.fst"
let _57_2195 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))

# 1574 "FStar.TypeChecker.Tc.fst"
let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (
# 1575 "FStar.TypeChecker.Tc.fst"
let _57_2203 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_2203) with
| (t, c, g) -> begin
(
# 1576 "FStar.TypeChecker.Tc.fst"
let _57_2204 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))

# 1579 "FStar.TypeChecker.Tc.fst"
let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _146_818 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _146_818)))

# 1582 "FStar.TypeChecker.Tc.fst"
let check_nogen = (fun env t k -> (
# 1583 "FStar.TypeChecker.Tc.fst"
let t = (tc_check_trivial_guard env t k)
in (let _146_822 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _146_822))))

# 1586 "FStar.TypeChecker.Tc.fst"
let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (
# 1587 "FStar.TypeChecker.Tc.fst"
let _57_2219 = (tc_binders env tps)
in (match (_57_2219) with
| (tps, env, g, us) -> begin
(
# 1588 "FStar.TypeChecker.Tc.fst"
let _57_2220 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))

# 1591 "FStar.TypeChecker.Tc.fst"
let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (
# 1592 "FStar.TypeChecker.Tc.fst"
let fail = (fun _57_2226 -> (match (()) with
| () -> begin
(let _146_837 = (let _146_836 = (let _146_835 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_146_835, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_146_836))
in (Prims.raise _146_837))
end))
in (
# 1593 "FStar.TypeChecker.Tc.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1596 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _57_2243)::(wp, _57_2239)::(_wlp, _57_2235)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2247 -> begin
(fail ())
end))
end
| _57_2249 -> begin
(fail ())
end))))

# 1603 "FStar.TypeChecker.Tc.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 1606 "FStar.TypeChecker.Tc.fst"
let _57_2256 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_57_2256) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _57_2258 -> begin
(
# 1609 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow binders c)
in (
# 1610 "FStar.TypeChecker.Tc.fst"
let _57_2262 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_57_2262) with
| (uvs, t') -> begin
(match ((let _146_844 = (FStar_Syntax_Subst.compress t')
in _146_844.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _57_2268 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 1615 "FStar.TypeChecker.Tc.fst"
let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (
# 1616 "FStar.TypeChecker.Tc.fst"
let fail = (fun t -> (let _146_855 = (let _146_854 = (let _146_853 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_146_853, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_146_854))
in (Prims.raise _146_855)))
in (match ((let _146_856 = (FStar_Syntax_Subst.compress signature)
in _146_856.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1619 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _57_2289)::(wp, _57_2285)::(_wlp, _57_2281)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2293 -> begin
(fail signature)
end))
end
| _57_2295 -> begin
(fail signature)
end)))

# 1626 "FStar.TypeChecker.Tc.fst"
let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (
# 1627 "FStar.TypeChecker.Tc.fst"
let _57_2300 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_57_2300) with
| (a, wp) -> begin
(
# 1628 "FStar.TypeChecker.Tc.fst"
let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _57_2303 -> begin
(
# 1632 "FStar.TypeChecker.Tc.fst"
let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (
# 1633 "FStar.TypeChecker.Tc.fst"
let op = (fun ts -> (
# 1634 "FStar.TypeChecker.Tc.fst"
let _57_2307 = ()
in (
# 1635 "FStar.TypeChecker.Tc.fst"
let t0 = (Prims.snd ts)
in (
# 1636 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (
# 1638 "FStar.TypeChecker.Tc.fst"
let _57_2311 = ed
in (let _146_875 = (op ed.FStar_Syntax_Syntax.ret)
in (let _146_874 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _146_873 = (op ed.FStar_Syntax_Syntax.bind_wlp)
in (let _146_872 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _146_871 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _146_870 = (op ed.FStar_Syntax_Syntax.ite_wlp)
in (let _146_869 = (op ed.FStar_Syntax_Syntax.wp_binop)
in (let _146_868 = (op ed.FStar_Syntax_Syntax.wp_as_type)
in (let _146_867 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _146_866 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _146_865 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _146_864 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _146_863 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _57_2311.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2311.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2311.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2311.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2311.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _146_875; FStar_Syntax_Syntax.bind_wp = _146_874; FStar_Syntax_Syntax.bind_wlp = _146_873; FStar_Syntax_Syntax.if_then_else = _146_872; FStar_Syntax_Syntax.ite_wp = _146_871; FStar_Syntax_Syntax.ite_wlp = _146_870; FStar_Syntax_Syntax.wp_binop = _146_869; FStar_Syntax_Syntax.wp_as_type = _146_868; FStar_Syntax_Syntax.close_wp = _146_867; FStar_Syntax_Syntax.assert_p = _146_866; FStar_Syntax_Syntax.assume_p = _146_865; FStar_Syntax_Syntax.null_wp = _146_864; FStar_Syntax_Syntax.trivial = _146_863}))))))))))))))))
end)
in (ed, a, wp))
end)))

# 1654 "FStar.TypeChecker.Tc.fst"
let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (
# 1655 "FStar.TypeChecker.Tc.fst"
let _57_2316 = ()
in (
# 1656 "FStar.TypeChecker.Tc.fst"
let _57_2320 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_57_2320) with
| (binders_un, signature_un) -> begin
(
# 1657 "FStar.TypeChecker.Tc.fst"
let _57_2325 = (tc_tparams env0 binders_un)
in (match (_57_2325) with
| (binders, env, _57_2324) -> begin
(
# 1658 "FStar.TypeChecker.Tc.fst"
let _57_2329 = (tc_trivial_guard env signature_un)
in (match (_57_2329) with
| (signature, _57_2328) -> begin
(
# 1659 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1659 "FStar.TypeChecker.Tc.fst"
let _57_2330 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2330.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2330.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2330.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _57_2330.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2330.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _57_2330.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = _57_2330.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _57_2330.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _57_2330.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = _57_2330.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _57_2330.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _57_2330.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _57_2330.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _57_2330.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _57_2330.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _57_2330.FStar_Syntax_Syntax.trivial})
in (
# 1662 "FStar.TypeChecker.Tc.fst"
let _57_2336 = (open_effect_decl env ed)
in (match (_57_2336) with
| (ed, a, wp_a) -> begin
(
# 1663 "FStar.TypeChecker.Tc.fst"
let get_effect_signature = (fun _57_2338 -> (match (()) with
| () -> begin
(
# 1664 "FStar.TypeChecker.Tc.fst"
let _57_2342 = (tc_trivial_guard env signature_un)
in (match (_57_2342) with
| (signature, _57_2341) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (
# 1668 "FStar.TypeChecker.Tc.fst"
let env = (let _146_882 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _146_882))
in (
# 1670 "FStar.TypeChecker.Tc.fst"
let _57_2344 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _146_885 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _146_884 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _146_883 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checked effect signature: %s %s : %s\n" _146_885 _146_884 _146_883))))
end else begin
()
end
in (
# 1676 "FStar.TypeChecker.Tc.fst"
let check_and_gen' = (fun env _57_2351 k -> (match (_57_2351) with
| (_57_2349, t) -> begin
(check_and_gen env t k)
end))
in (
# 1679 "FStar.TypeChecker.Tc.fst"
let ret = (
# 1680 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_897 = (let _146_895 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_894 = (let _146_893 = (let _146_892 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_892))
in (_146_893)::[])
in (_146_895)::_146_894))
in (let _146_896 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _146_897 _146_896)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (
# 1683 "FStar.TypeChecker.Tc.fst"
let bind_wp = (
# 1684 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1685 "FStar.TypeChecker.Tc.fst"
let _57_2358 = (get_effect_signature ())
in (match (_57_2358) with
| (b, wp_b) -> begin
(
# 1686 "FStar.TypeChecker.Tc.fst"
let a_wp_b = (let _146_901 = (let _146_899 = (let _146_898 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_898))
in (_146_899)::[])
in (let _146_900 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _146_901 _146_900)))
in (
# 1687 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = a_wp_b
in (
# 1688 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_914 = (let _146_912 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_911 = (let _146_910 = (FStar_Syntax_Syntax.mk_binder b)
in (let _146_909 = (let _146_908 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_907 = (let _146_906 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _146_905 = (let _146_904 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (let _146_903 = (let _146_902 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_146_902)::[])
in (_146_904)::_146_903))
in (_146_906)::_146_905))
in (_146_908)::_146_907))
in (_146_910)::_146_909))
in (_146_912)::_146_911))
in (let _146_913 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _146_914 _146_913)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k))))
end)))
in (
# 1694 "FStar.TypeChecker.Tc.fst"
let bind_wlp = (
# 1695 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1696 "FStar.TypeChecker.Tc.fst"
let _57_2366 = (get_effect_signature ())
in (match (_57_2366) with
| (b, wlp_b) -> begin
(
# 1697 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = (let _146_918 = (let _146_916 = (let _146_915 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_915))
in (_146_916)::[])
in (let _146_917 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _146_918 _146_917)))
in (
# 1698 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_927 = (let _146_925 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_924 = (let _146_923 = (FStar_Syntax_Syntax.mk_binder b)
in (let _146_922 = (let _146_921 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _146_920 = (let _146_919 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_146_919)::[])
in (_146_921)::_146_920))
in (_146_923)::_146_922))
in (_146_925)::_146_924))
in (let _146_926 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _146_927 _146_926)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wlp expected_k)))
end)))
in (
# 1704 "FStar.TypeChecker.Tc.fst"
let if_then_else = (
# 1705 "FStar.TypeChecker.Tc.fst"
let p = (let _146_929 = (let _146_928 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_928 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _146_929))
in (
# 1706 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_938 = (let _146_936 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_935 = (let _146_934 = (FStar_Syntax_Syntax.mk_binder p)
in (let _146_933 = (let _146_932 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_931 = (let _146_930 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_930)::[])
in (_146_932)::_146_931))
in (_146_934)::_146_933))
in (_146_936)::_146_935))
in (let _146_937 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_938 _146_937)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (
# 1712 "FStar.TypeChecker.Tc.fst"
let ite_wp = (
# 1713 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1714 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_945 = (let _146_943 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_942 = (let _146_941 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _146_940 = (let _146_939 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_939)::[])
in (_146_941)::_146_940))
in (_146_943)::_146_942))
in (let _146_944 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_945 _146_944)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k)))
in (
# 1720 "FStar.TypeChecker.Tc.fst"
let ite_wlp = (
# 1721 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1722 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_950 = (let _146_948 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_947 = (let _146_946 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (_146_946)::[])
in (_146_948)::_146_947))
in (let _146_949 = (FStar_Syntax_Syntax.mk_Total wlp_a)
in (FStar_Syntax_Util.arrow _146_950 _146_949)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wlp expected_k)))
in (
# 1727 "FStar.TypeChecker.Tc.fst"
let wp_binop = (
# 1728 "FStar.TypeChecker.Tc.fst"
let bin_op = (
# 1729 "FStar.TypeChecker.Tc.fst"
let _57_2381 = (FStar_Syntax_Util.type_u ())
in (match (_57_2381) with
| (t1, u1) -> begin
(
# 1730 "FStar.TypeChecker.Tc.fst"
let _57_2384 = (FStar_Syntax_Util.type_u ())
in (match (_57_2384) with
| (t2, u2) -> begin
(
# 1731 "FStar.TypeChecker.Tc.fst"
let t = (let _146_951 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_max ((u1)::(u2)::[]))) None _146_951))
in (let _146_956 = (let _146_954 = (FStar_Syntax_Syntax.null_binder t1)
in (let _146_953 = (let _146_952 = (FStar_Syntax_Syntax.null_binder t2)
in (_146_952)::[])
in (_146_954)::_146_953))
in (let _146_955 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _146_956 _146_955))))
end))
end))
in (
# 1733 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_965 = (let _146_963 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_962 = (let _146_961 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_960 = (let _146_959 = (FStar_Syntax_Syntax.null_binder bin_op)
in (let _146_958 = (let _146_957 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_957)::[])
in (_146_959)::_146_958))
in (_146_961)::_146_960))
in (_146_963)::_146_962))
in (let _146_964 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_965 _146_964)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_binop expected_k)))
in (
# 1740 "FStar.TypeChecker.Tc.fst"
let wp_as_type = (
# 1741 "FStar.TypeChecker.Tc.fst"
let _57_2392 = (FStar_Syntax_Util.type_u ())
in (match (_57_2392) with
| (t, _57_2391) -> begin
(
# 1742 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_970 = (let _146_968 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_967 = (let _146_966 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_966)::[])
in (_146_968)::_146_967))
in (let _146_969 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _146_970 _146_969)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (
# 1747 "FStar.TypeChecker.Tc.fst"
let close_wp = (
# 1748 "FStar.TypeChecker.Tc.fst"
let b = (let _146_972 = (let _146_971 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_971 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _146_972))
in (
# 1749 "FStar.TypeChecker.Tc.fst"
let b_wp_a = (let _146_976 = (let _146_974 = (let _146_973 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _146_973))
in (_146_974)::[])
in (let _146_975 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_976 _146_975)))
in (
# 1750 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_983 = (let _146_981 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_980 = (let _146_979 = (FStar_Syntax_Syntax.mk_binder b)
in (let _146_978 = (let _146_977 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_146_977)::[])
in (_146_979)::_146_978))
in (_146_981)::_146_980))
in (let _146_982 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_983 _146_982)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (
# 1754 "FStar.TypeChecker.Tc.fst"
let assert_p = (
# 1755 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_992 = (let _146_990 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_989 = (let _146_988 = (let _146_985 = (let _146_984 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_984 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _146_985))
in (let _146_987 = (let _146_986 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_986)::[])
in (_146_988)::_146_987))
in (_146_990)::_146_989))
in (let _146_991 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_992 _146_991)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (
# 1761 "FStar.TypeChecker.Tc.fst"
let assume_p = (
# 1762 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1001 = (let _146_999 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_998 = (let _146_997 = (let _146_994 = (let _146_993 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_993 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _146_994))
in (let _146_996 = (let _146_995 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_995)::[])
in (_146_997)::_146_996))
in (_146_999)::_146_998))
in (let _146_1000 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1001 _146_1000)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (
# 1768 "FStar.TypeChecker.Tc.fst"
let null_wp = (
# 1769 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1004 = (let _146_1002 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1002)::[])
in (let _146_1003 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1004 _146_1003)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (
# 1773 "FStar.TypeChecker.Tc.fst"
let trivial_wp = (
# 1774 "FStar.TypeChecker.Tc.fst"
let _57_2408 = (FStar_Syntax_Util.type_u ())
in (match (_57_2408) with
| (t, _57_2407) -> begin
(
# 1775 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1009 = (let _146_1007 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1006 = (let _146_1005 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1005)::[])
in (_146_1007)::_146_1006))
in (let _146_1008 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _146_1009 _146_1008)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (
# 1781 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1010 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _146_1010))
in (
# 1782 "FStar.TypeChecker.Tc.fst"
let _57_2414 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_57_2414) with
| (univs, t) -> begin
(
# 1783 "FStar.TypeChecker.Tc.fst"
let _57_2430 = (match ((let _146_1012 = (let _146_1011 = (FStar_Syntax_Subst.compress t)
in _146_1011.FStar_Syntax_Syntax.n)
in (binders, _146_1012))) with
| ([], _57_2417) -> begin
([], t)
end
| (_57_2420, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _57_2427 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_2430) with
| (binders, signature) -> begin
(
# 1787 "FStar.TypeChecker.Tc.fst"
let close = (fun n ts -> (
# 1788 "FStar.TypeChecker.Tc.fst"
let ts = (let _146_1017 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _146_1017))
in (
# 1789 "FStar.TypeChecker.Tc.fst"
let _57_2435 = ()
in ts)))
in (
# 1791 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1791 "FStar.TypeChecker.Tc.fst"
let _57_2437 = ed
in (let _146_1030 = (close 0 ret)
in (let _146_1029 = (close 1 bind_wp)
in (let _146_1028 = (close 1 bind_wlp)
in (let _146_1027 = (close 0 if_then_else)
in (let _146_1026 = (close 0 ite_wp)
in (let _146_1025 = (close 0 ite_wlp)
in (let _146_1024 = (close 0 wp_binop)
in (let _146_1023 = (close 0 wp_as_type)
in (let _146_1022 = (close 1 close_wp)
in (let _146_1021 = (close 0 assert_p)
in (let _146_1020 = (close 0 assume_p)
in (let _146_1019 = (close 0 null_wp)
in (let _146_1018 = (close 0 trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _57_2437.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2437.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _146_1030; FStar_Syntax_Syntax.bind_wp = _146_1029; FStar_Syntax_Syntax.bind_wlp = _146_1028; FStar_Syntax_Syntax.if_then_else = _146_1027; FStar_Syntax_Syntax.ite_wp = _146_1026; FStar_Syntax_Syntax.ite_wlp = _146_1025; FStar_Syntax_Syntax.wp_binop = _146_1024; FStar_Syntax_Syntax.wp_as_type = _146_1023; FStar_Syntax_Syntax.close_wp = _146_1022; FStar_Syntax_Syntax.assert_p = _146_1021; FStar_Syntax_Syntax.assume_p = _146_1020; FStar_Syntax_Syntax.null_wp = _146_1019; FStar_Syntax_Syntax.trivial = _146_1018}))))))))))))))
in (
# 1809 "FStar.TypeChecker.Tc.fst"
let _57_2440 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1031 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _146_1031))
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

# 1813 "FStar.TypeChecker.Tc.fst"
let tc_lex_t = (fun env ses quals lids -> (
# 1820 "FStar.TypeChecker.Tc.fst"
let _57_2446 = ()
in (
# 1821 "FStar.TypeChecker.Tc.fst"
let _57_2454 = ()
in (match (ses) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _57_2483, _57_2485, [], r)::FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _57_2474, r1)::FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _57_2463, r2)::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(
# 1836 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (
# 1837 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (
# 1838 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (
# 1839 "FStar.TypeChecker.Tc.fst"
let tc = FStar_Syntax_Syntax.Sig_inductive_typ ((lex_t, (u)::[], [], t, [], (FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[], [], r))
in (
# 1841 "FStar.TypeChecker.Tc.fst"
let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (
# 1842 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (let _146_1039 = (let _146_1038 = (let _146_1037 = (let _146_1036 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _146_1036 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1037, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1038))
in (FStar_Syntax_Syntax.mk _146_1039 None r1))
in (
# 1843 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (
# 1844 "FStar.TypeChecker.Tc.fst"
let dc_lextop = FStar_Syntax_Syntax.Sig_datacon ((lex_top, (utop)::[], lex_top_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r1))
in (
# 1846 "FStar.TypeChecker.Tc.fst"
let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1847 "FStar.TypeChecker.Tc.fst"
let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1848 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (
# 1849 "FStar.TypeChecker.Tc.fst"
let a = (let _146_1040 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1040))
in (
# 1850 "FStar.TypeChecker.Tc.fst"
let hd = (let _146_1041 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1041))
in (
# 1851 "FStar.TypeChecker.Tc.fst"
let tl = (let _146_1046 = (let _146_1045 = (let _146_1044 = (let _146_1043 = (let _146_1042 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _146_1042 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1043, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1044))
in (FStar_Syntax_Syntax.mk _146_1045 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1046))
in (
# 1852 "FStar.TypeChecker.Tc.fst"
let res = (let _146_1050 = (let _146_1049 = (let _146_1048 = (let _146_1047 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _146_1047 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1048, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1049))
in (FStar_Syntax_Syntax.mk _146_1050 None r2))
in (let _146_1051 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _146_1051))))))
in (
# 1854 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (
# 1855 "FStar.TypeChecker.Tc.fst"
let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _146_1053 = (let _146_1052 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _146_1052))
in FStar_Syntax_Syntax.Sig_bundle (_146_1053)))))))))))))))
end
| _57_2509 -> begin
(let _146_1055 = (let _146_1054 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _146_1054))
in (FStar_All.failwith _146_1055))
end))))

# 1861 "FStar.TypeChecker.Tc.fst"
let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (
# 1924 "FStar.TypeChecker.Tc.fst"
let warn_positivity = (fun l r -> (let _146_1069 = (let _146_1068 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _146_1068))
in (FStar_TypeChecker_Errors.diag r _146_1069)))
in (
# 1926 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1929 "FStar.TypeChecker.Tc.fst"
let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(
# 1934 "FStar.TypeChecker.Tc.fst"
let _57_2531 = ()
in (
# 1935 "FStar.TypeChecker.Tc.fst"
let _57_2533 = (warn_positivity tc r)
in (
# 1936 "FStar.TypeChecker.Tc.fst"
let _57_2537 = (FStar_Syntax_Subst.open_term tps k)
in (match (_57_2537) with
| (tps, k) -> begin
(
# 1937 "FStar.TypeChecker.Tc.fst"
let _57_2541 = (tc_tparams env tps)
in (match (_57_2541) with
| (tps, env_tps, us) -> begin
(
# 1938 "FStar.TypeChecker.Tc.fst"
let _57_2544 = (FStar_Syntax_Util.arrow_formals k)
in (match (_57_2544) with
| (indices, t) -> begin
(
# 1939 "FStar.TypeChecker.Tc.fst"
let _57_2548 = (tc_tparams env_tps indices)
in (match (_57_2548) with
| (indices, env', us') -> begin
(
# 1940 "FStar.TypeChecker.Tc.fst"
let _57_2552 = (tc_trivial_guard env' t)
in (match (_57_2552) with
| (t, _57_2551) -> begin
(
# 1941 "FStar.TypeChecker.Tc.fst"
let k = (let _146_1074 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _146_1074))
in (
# 1942 "FStar.TypeChecker.Tc.fst"
let _57_2556 = (FStar_Syntax_Util.type_u ())
in (match (_57_2556) with
| (t_type, u) -> begin
(
# 1943 "FStar.TypeChecker.Tc.fst"
let _57_2557 = (let _146_1075 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _146_1075))
in (
# 1945 "FStar.TypeChecker.Tc.fst"
let t_tc = (let _146_1076 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _146_1076))
in (
# 1946 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 1947 "FStar.TypeChecker.Tc.fst"
let k = (FStar_Syntax_Subst.close tps k)
in (
# 1948 "FStar.TypeChecker.Tc.fst"
let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _146_1077 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) ([], t_tc))
in (_146_1077, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u)))))))
end)))
end))
end))
end))
end))
end))))
end
| _57_2564 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1955 "FStar.TypeChecker.Tc.fst"
let positive_if_pure = (fun _57_2566 l -> ())
in (
# 1958 "FStar.TypeChecker.Tc.fst"
let tc_data = (fun env tcs _57_6 -> (match (_57_6) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(
# 1960 "FStar.TypeChecker.Tc.fst"
let _57_2583 = ()
in (
# 1962 "FStar.TypeChecker.Tc.fst"
let _57_2618 = (
# 1963 "FStar.TypeChecker.Tc.fst"
let tps_u_opt = (FStar_Util.find_map tcs (fun _57_2587 -> (match (_57_2587) with
| (se, u_tc) -> begin
if (let _146_1090 = (let _146_1089 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _146_1089))
in (FStar_Ident.lid_equals tc_lid _146_1090)) then begin
(
# 1965 "FStar.TypeChecker.Tc.fst"
let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2589, _57_2591, tps, _57_2594, _57_2596, _57_2598, _57_2600, _57_2602) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _57_2608 -> (match (_57_2608) with
| (x, _57_2607) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _57_2610 -> begin
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
in (match (_57_2618) with
| (tps, u_tc) -> begin
(
# 1978 "FStar.TypeChecker.Tc.fst"
let _57_2638 = (match ((let _146_1092 = (FStar_Syntax_Subst.compress t)
in _146_1092.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(
# 1983 "FStar.TypeChecker.Tc.fst"
let _57_2626 = (FStar_Util.first_N ntps bs)
in (match (_57_2626) with
| (_57_2624, bs') -> begin
(
# 1984 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (
# 1985 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _57_2632 -> (match (_57_2632) with
| (x, _57_2631) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _146_1095 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _146_1095))))
end))
end
| _57_2635 -> begin
([], t)
end)
in (match (_57_2638) with
| (arguments, result) -> begin
(
# 1989 "FStar.TypeChecker.Tc.fst"
let _57_2639 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1098 = (FStar_Syntax_Print.lid_to_string c)
in (let _146_1097 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _146_1096 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _146_1098 _146_1097 _146_1096))))
end else begin
()
end
in (
# 1995 "FStar.TypeChecker.Tc.fst"
let _57_2644 = (tc_tparams env arguments)
in (match (_57_2644) with
| (arguments, env', us) -> begin
(
# 1996 "FStar.TypeChecker.Tc.fst"
let _57_2648 = (tc_trivial_guard env' result)
in (match (_57_2648) with
| (result, _57_2647) -> begin
(
# 1997 "FStar.TypeChecker.Tc.fst"
let _57_2652 = (FStar_Syntax_Util.head_and_args result)
in (match (_57_2652) with
| (head, _57_2651) -> begin
(
# 1998 "FStar.TypeChecker.Tc.fst"
let _57_2657 = (match ((let _146_1099 = (FStar_Syntax_Subst.compress head)
in _146_1099.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _57_2656 -> begin
(let _146_1103 = (let _146_1102 = (let _146_1101 = (let _146_1100 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _146_1100))
in (_146_1101, r))
in FStar_Syntax_Syntax.Error (_146_1102))
in (Prims.raise _146_1103))
end)
in (
# 2001 "FStar.TypeChecker.Tc.fst"
let g = (FStar_List.fold_left2 (fun g _57_2663 u_x -> (match (_57_2663) with
| (x, _57_2662) -> begin
(
# 2002 "FStar.TypeChecker.Tc.fst"
let _57_2665 = ()
in (let _146_1107 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _146_1107)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (
# 2008 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1111 = (let _146_1109 = (FStar_All.pipe_right tps (FStar_List.map (fun _57_2671 -> (match (_57_2671) with
| (x, _57_2670) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _146_1109 arguments))
in (let _146_1110 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _146_1111 _146_1110)))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _57_2674 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 2016 "FStar.TypeChecker.Tc.fst"
let generalize_and_inst_within = (fun env g tcs datas -> (
# 2017 "FStar.TypeChecker.Tc.fst"
let _57_2680 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2018 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_7 -> (match (_57_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2684, _57_2686, tps, k, _57_2690, _57_2692, _57_2694, _57_2696) -> begin
(let _146_1122 = (let _146_1121 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _146_1121))
in (FStar_Syntax_Syntax.null_binder _146_1122))
end
| _57_2700 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2021 "FStar.TypeChecker.Tc.fst"
let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _57_8 -> (match (_57_8) with
| FStar_Syntax_Syntax.Sig_datacon (_57_2704, _57_2706, t, _57_2709, _57_2711, _57_2713, _57_2715, _57_2717) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _57_2721 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2024 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1124 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _146_1124))
in (
# 2025 "FStar.TypeChecker.Tc.fst"
let _57_2724 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1125 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _146_1125))
end else begin
()
end
in (
# 2026 "FStar.TypeChecker.Tc.fst"
let _57_2728 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_57_2728) with
| (uvs, t) -> begin
(
# 2027 "FStar.TypeChecker.Tc.fst"
let _57_2730 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1129 = (let _146_1127 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _146_1127 (FStar_String.concat ", ")))
in (let _146_1128 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _146_1129 _146_1128)))
end else begin
()
end
in (
# 2030 "FStar.TypeChecker.Tc.fst"
let _57_2734 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_57_2734) with
| (uvs, t) -> begin
(
# 2031 "FStar.TypeChecker.Tc.fst"
let _57_2738 = (FStar_Syntax_Util.arrow_formals t)
in (match (_57_2738) with
| (args, _57_2737) -> begin
(
# 2032 "FStar.TypeChecker.Tc.fst"
let _57_2741 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_57_2741) with
| (tc_types, data_types) -> begin
(
# 2033 "FStar.TypeChecker.Tc.fst"
let tcs = (FStar_List.map2 (fun _57_2745 se -> (match (_57_2745) with
| (x, _57_2744) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_2749, tps, _57_2752, mutuals, datas, quals, r) -> begin
(
# 2035 "FStar.TypeChecker.Tc.fst"
let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (
# 2036 "FStar.TypeChecker.Tc.fst"
let _57_2775 = (match ((let _146_1132 = (FStar_Syntax_Subst.compress ty)
in _146_1132.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 2038 "FStar.TypeChecker.Tc.fst"
let _57_2766 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_57_2766) with
| (tps, rest) -> begin
(
# 2039 "FStar.TypeChecker.Tc.fst"
let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _57_2769 -> begin
(let _146_1133 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _146_1133 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _57_2772 -> begin
([], ty)
end)
in (match (_57_2775) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _57_2777 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (
# 2049 "FStar.TypeChecker.Tc.fst"
let datas = (match (uvs) with
| [] -> begin
datas
end
| _57_2781 -> begin
(
# 2052 "FStar.TypeChecker.Tc.fst"
let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _146_1134 -> FStar_Syntax_Syntax.U_name (_146_1134))))
in (
# 2053 "FStar.TypeChecker.Tc.fst"
let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_9 -> (match (_57_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_2786, _57_2788, _57_2790, _57_2792, _57_2794, _57_2796, _57_2798) -> begin
(tc, uvs_universes)
end
| _57_2802 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _57_2807 d -> (match (_57_2807) with
| (t, _57_2806) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _57_2811, _57_2813, tc, ntps, quals, mutuals, r) -> begin
(
# 2057 "FStar.TypeChecker.Tc.fst"
let ty = (let _146_1138 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _146_1138 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _57_2823 -> begin
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
# 2063 "FStar.TypeChecker.Tc.fst"
let _57_2833 = (FStar_All.pipe_right ses (FStar_List.partition (fun _57_10 -> (match (_57_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2827) -> begin
true
end
| _57_2830 -> begin
false
end))))
in (match (_57_2833) with
| (tys, datas) -> begin
(
# 2065 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2068 "FStar.TypeChecker.Tc.fst"
let _57_2850 = (FStar_List.fold_right (fun tc _57_2839 -> (match (_57_2839) with
| (env, all_tcs, g) -> begin
(
# 2069 "FStar.TypeChecker.Tc.fst"
let _57_2843 = (tc_tycon env tc)
in (match (_57_2843) with
| (env, tc, tc_u) -> begin
(
# 2070 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (
# 2071 "FStar.TypeChecker.Tc.fst"
let _57_2845 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1142 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _146_1142))
end else begin
()
end
in (let _146_1143 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _146_1143))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_2850) with
| (env, tcs, g) -> begin
(
# 2078 "FStar.TypeChecker.Tc.fst"
let _57_2860 = (FStar_List.fold_right (fun se _57_2854 -> (match (_57_2854) with
| (datas, g) -> begin
(
# 2079 "FStar.TypeChecker.Tc.fst"
let _57_2857 = (tc_data env tcs se)
in (match (_57_2857) with
| (data, g') -> begin
(let _146_1146 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _146_1146))
end))
end)) datas ([], g))
in (match (_57_2860) with
| (datas, g) -> begin
(
# 2084 "FStar.TypeChecker.Tc.fst"
let _57_2863 = (let _146_1147 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _146_1147 datas))
in (match (_57_2863) with
| (tcs, datas) -> begin
(let _146_1149 = (let _146_1148 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _146_1148))
in FStar_Syntax_Syntax.Sig_bundle (_146_1149))
end))
end))
end)))
end)))))))))

# 2087 "FStar.TypeChecker.Tc.fst"
let rec tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.env) = (fun env se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(
# 2100 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2101 "FStar.TypeChecker.Tc.fst"
let se = (tc_lex_t env ses quals lids)
in (let _146_1154 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _146_1154))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(
# 2105 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2106 "FStar.TypeChecker.Tc.fst"
let se = (tc_inductive env ses quals lids)
in (let _146_1155 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _146_1155))))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(
# 2110 "FStar.TypeChecker.Tc.fst"
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
# 2116 "FStar.TypeChecker.Tc.fst"
let _57_2901 = (set_options FStar_Options.Set o)
in (se, env))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(
# 2119 "FStar.TypeChecker.Tc.fst"
let _57_2905 = (let _146_1160 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _146_1160 Prims.ignore))
in (
# 2120 "FStar.TypeChecker.Tc.fst"
let _57_2910 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (
# 2123 "FStar.TypeChecker.Tc.fst"
let _57_2912 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (se, env))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(
# 2128 "FStar.TypeChecker.Tc.fst"
let ne = (tc_eff_decl env ne)
in (
# 2129 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (
# 2130 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(
# 2134 "FStar.TypeChecker.Tc.fst"
let _57_2927 = (let _146_1161 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _146_1161))
in (match (_57_2927) with
| (a, wp_a_src) -> begin
(
# 2135 "FStar.TypeChecker.Tc.fst"
let _57_2930 = (let _146_1162 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _146_1162))
in (match (_57_2930) with
| (b, wp_b_tgt) -> begin
(
# 2136 "FStar.TypeChecker.Tc.fst"
let wp_a_tgt = (let _146_1166 = (let _146_1165 = (let _146_1164 = (let _146_1163 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _146_1163))
in FStar_Syntax_Syntax.NT (_146_1164))
in (_146_1165)::[])
in (FStar_Syntax_Subst.subst _146_1166 wp_b_tgt))
in (
# 2137 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1171 = (let _146_1169 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1168 = (let _146_1167 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_146_1167)::[])
in (_146_1169)::_146_1168))
in (let _146_1170 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _146_1171 _146_1170)))
in (
# 2138 "FStar.TypeChecker.Tc.fst"
let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (
# 2139 "FStar.TypeChecker.Tc.fst"
let sub = (
# 2139 "FStar.TypeChecker.Tc.fst"
let _57_2934 = sub
in {FStar_Syntax_Syntax.source = _57_2934.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _57_2934.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
in (
# 2140 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect ((sub, r))
in (
# 2141 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(
# 2145 "FStar.TypeChecker.Tc.fst"
let _57_2947 = ()
in (
# 2146 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2147 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2148 "FStar.TypeChecker.Tc.fst"
let _57_2953 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_57_2953) with
| (tps, c) -> begin
(
# 2149 "FStar.TypeChecker.Tc.fst"
let _57_2957 = (tc_tparams env tps)
in (match (_57_2957) with
| (tps, env, us) -> begin
(
# 2150 "FStar.TypeChecker.Tc.fst"
let _57_2961 = (tc_comp env c)
in (match (_57_2961) with
| (c, u, g) -> begin
(
# 2151 "FStar.TypeChecker.Tc.fst"
let _57_2962 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2152 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 2153 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.close_comp tps c)
in (
# 2154 "FStar.TypeChecker.Tc.fst"
let _57_2968 = (let _146_1172 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _146_1172))
in (match (_57_2968) with
| (uvs, t) -> begin
(
# 2155 "FStar.TypeChecker.Tc.fst"
let _57_2987 = (match ((let _146_1174 = (let _146_1173 = (FStar_Syntax_Subst.compress t)
in _146_1173.FStar_Syntax_Syntax.n)
in (tps, _146_1174))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_57_2971, c)) -> begin
([], c)
end
| (_57_2977, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _57_2984 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_2987) with
| (tps, c) -> begin
(
# 2159 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_effect_abbrev ((lid, uvs, tps, c, tags, r))
in (
# 2160 "FStar.TypeChecker.Tc.fst"
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
# 2164 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2165 "FStar.TypeChecker.Tc.fst"
let _57_2998 = ()
in (
# 2166 "FStar.TypeChecker.Tc.fst"
let _57_3002 = (let _146_1176 = (let _146_1175 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _146_1175))
in (check_and_gen env t _146_1176))
in (match (_57_3002) with
| (uvs, t) -> begin
(
# 2167 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (
# 2168 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(
# 2172 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2173 "FStar.TypeChecker.Tc.fst"
let _57_3015 = (FStar_Syntax_Util.type_u ())
in (match (_57_3015) with
| (k, _57_3014) -> begin
(
# 2174 "FStar.TypeChecker.Tc.fst"
let phi = (let _146_1177 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _146_1177 (norm env)))
in (
# 2175 "FStar.TypeChecker.Tc.fst"
let _57_3017 = (FStar_TypeChecker_Util.check_uvars r phi)
in (
# 2176 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))
in (
# 2177 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(
# 2181 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2182 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (
# 2183 "FStar.TypeChecker.Tc.fst"
let _57_3030 = (tc_term env e)
in (match (_57_3030) with
| (e, c, g1) -> begin
(
# 2184 "FStar.TypeChecker.Tc.fst"
let _57_3035 = (let _146_1181 = (let _146_1178 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_146_1178))
in (let _146_1180 = (let _146_1179 = (c.FStar_Syntax_Syntax.comp ())
in (e, _146_1179))
in (check_expected_effect env _146_1181 _146_1180)))
in (match (_57_3035) with
| (e, _57_3033, g) -> begin
(
# 2185 "FStar.TypeChecker.Tc.fst"
let _57_3036 = (let _146_1182 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _146_1182))
in (
# 2186 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, r))
in (
# 2187 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(
# 2191 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2192 "FStar.TypeChecker.Tc.fst"
let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
if (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q')) then begin
Some (q)
end else begin
(let _146_1194 = (let _146_1193 = (let _146_1192 = (let _146_1191 = (FStar_Syntax_Print.lid_to_string l)
in (let _146_1190 = (FStar_Syntax_Print.quals_to_string q)
in (let _146_1189 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _146_1191 _146_1190 _146_1189))))
in (_146_1192, r))
in FStar_Syntax_Syntax.Error (_146_1193))
in (Prims.raise _146_1194))
end
end))
in (
# 2206 "FStar.TypeChecker.Tc.fst"
let _57_3080 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _57_3057 lb -> (match (_57_3057) with
| (gen, lbs, quals_opt) -> begin
(
# 2207 "FStar.TypeChecker.Tc.fst"
let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2208 "FStar.TypeChecker.Tc.fst"
let _57_3076 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(
# 2212 "FStar.TypeChecker.Tc.fst"
let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (
# 2213 "FStar.TypeChecker.Tc.fst"
let _57_3071 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _57_3070 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _146_1197 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _146_1197, quals_opt))))
end)
in (match (_57_3076) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_57_3080) with
| (should_generalize, lbs', quals_opt) -> begin
(
# 2222 "FStar.TypeChecker.Tc.fst"
let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _57_11 -> (match (_57_11) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _57_3089 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (
# 2229 "FStar.TypeChecker.Tc.fst"
let lbs' = (FStar_List.rev lbs')
in (
# 2232 "FStar.TypeChecker.Tc.fst"
let e = (let _146_1201 = (let _146_1200 = (let _146_1199 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _146_1199))
in FStar_Syntax_Syntax.Tm_let (_146_1200))
in (FStar_Syntax_Syntax.mk _146_1201 None r))
in (
# 2235 "FStar.TypeChecker.Tc.fst"
let _57_3123 = (match ((tc_maybe_toplevel_term (
# 2235 "FStar.TypeChecker.Tc.fst"
let _57_3093 = env
in {FStar_TypeChecker_Env.solver = _57_3093.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3093.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3093.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3093.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3093.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3093.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3093.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3093.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3093.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3093.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3093.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _57_3093.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _57_3093.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3093.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3093.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3093.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3093.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3093.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3093.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _57_3100; FStar_Syntax_Syntax.pos = _57_3098; FStar_Syntax_Syntax.vars = _57_3096}, _57_3107, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(
# 2238 "FStar.TypeChecker.Tc.fst"
let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_57_3111, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _57_3117 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _57_3120 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_57_3123) with
| (se, lbs) -> begin
(
# 2245 "FStar.TypeChecker.Tc.fst"
let _57_3129 = if (log env) then begin
(let _146_1209 = (let _146_1208 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 2247 "FStar.TypeChecker.Tc.fst"
let should_log = (match ((let _146_1205 = (let _146_1204 = (let _146_1203 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _146_1203.FStar_Syntax_Syntax.fv_name)
in _146_1204.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _146_1205))) with
| None -> begin
true
end
| _57_3127 -> begin
false
end)
in if should_log then begin
(let _146_1207 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _146_1206 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _146_1207 _146_1206)))
end else begin
""
end))))
in (FStar_All.pipe_right _146_1208 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _146_1209))
end else begin
()
end
in (
# 2254 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end))))
end))

# 2258 "FStar.TypeChecker.Tc.fst"
let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (
# 2282 "FStar.TypeChecker.Tc.fst"
let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _57_12 -> (match (_57_12) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _57_3139 -> begin
false
end)))))
in (
# 2283 "FStar.TypeChecker.Tc.fst"
let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _57_3149 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_57_3151) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _57_3162, _57_3164) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _57_3170 -> (match (_57_3170) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _57_3176, _57_3178, quals, r) -> begin
(
# 2297 "FStar.TypeChecker.Tc.fst"
let dec = (let _146_1225 = (let _146_1224 = (let _146_1223 = (let _146_1222 = (let _146_1221 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _146_1221))
in FStar_Syntax_Syntax.Tm_arrow (_146_1222))
in (FStar_Syntax_Syntax.mk _146_1223 None r))
in (l, us, _146_1224, (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_146_1225))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _57_3188, _57_3190, _57_3192, _57_3194, r) -> begin
(
# 2300 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _57_3200 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_57_3202, _57_3204, quals, _57_3207) -> begin
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
| _57_3226 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_57_3228) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _57_3244, _57_3246, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(
# 2330 "FStar.TypeChecker.Tc.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2331 "FStar.TypeChecker.Tc.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))) then begin
([], hidden)
end else begin
(
# 2334 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::[], (FStar_Ident.range_of_lid lid)))
in ((dec)::[], (lid)::hidden))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (is_abstract quals) then begin
(let _146_1232 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _146_1231 = (let _146_1230 = (let _146_1229 = (let _146_1228 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _146_1228.FStar_Syntax_Syntax.fv_name)
in _146_1229.FStar_Syntax_Syntax.v)
in (_146_1230, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_146_1231)))))
in (_146_1232, hidden))
end else begin
((se)::[], hidden)
end
end))))

# 2343 "FStar.TypeChecker.Tc.fst"
let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (
# 2344 "FStar.TypeChecker.Tc.fst"
let _57_3285 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _57_3266 se -> (match (_57_3266) with
| (ses, exports, env, hidden) -> begin
(
# 2346 "FStar.TypeChecker.Tc.fst"
let _57_3268 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1239 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _146_1239))
end else begin
()
end
in (
# 2349 "FStar.TypeChecker.Tc.fst"
let _57_3272 = (tc_decl env se)
in (match (_57_3272) with
| (se, env) -> begin
(
# 2351 "FStar.TypeChecker.Tc.fst"
let _57_3273 = if ((FStar_ST.read FStar_Options.log_types) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _146_1240 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _146_1240))
end else begin
()
end
in (
# 2354 "FStar.TypeChecker.Tc.fst"
let _57_3275 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (
# 2356 "FStar.TypeChecker.Tc.fst"
let _57_3279 = (for_export hidden se)
in (match (_57_3279) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_57_3285) with
| (ses, exports, env, _57_3284) -> begin
(let _146_1241 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _146_1241, env))
end)))

# 2361 "FStar.TypeChecker.Tc.fst"
let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2362 "FStar.TypeChecker.Tc.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 2363 "FStar.TypeChecker.Tc.fst"
let msg = (Prims.strcat "Internals for " name)
in (
# 2364 "FStar.TypeChecker.Tc.fst"
let env = (
# 2364 "FStar.TypeChecker.Tc.fst"
let _57_3290 = env
in (let _146_1246 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _57_3290.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3290.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3290.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3290.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3290.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3290.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3290.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3290.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3290.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3290.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3290.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3290.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3290.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_3290.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_3290.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3290.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _146_1246; FStar_TypeChecker_Env.type_of = _57_3290.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3290.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3290.FStar_TypeChecker_Env.use_bv_sorts}))
in (
# 2365 "FStar.TypeChecker.Tc.fst"
let _57_3293 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (
# 2366 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (
# 2367 "FStar.TypeChecker.Tc.fst"
let _57_3299 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_57_3299) with
| (ses, exports, env) -> begin
((
# 2368 "FStar.TypeChecker.Tc.fst"
let _57_3300 = modul
in {FStar_Syntax_Syntax.name = _57_3300.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _57_3300.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3300.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))

# 2370 "FStar.TypeChecker.Tc.fst"
let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (
# 2371 "FStar.TypeChecker.Tc.fst"
let _57_3308 = (tc_decls env decls)
in (match (_57_3308) with
| (ses, exports, env) -> begin
(
# 2372 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2372 "FStar.TypeChecker.Tc.fst"
let _57_3309 = modul
in {FStar_Syntax_Syntax.name = _57_3309.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _57_3309.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3309.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))

# 2375 "FStar.TypeChecker.Tc.fst"
let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (
# 2376 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2376 "FStar.TypeChecker.Tc.fst"
let _57_3315 = modul
in {FStar_Syntax_Syntax.name = _57_3315.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _57_3315.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (
# 2377 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.finish_module env modul)
in (
# 2378 "FStar.TypeChecker.Tc.fst"
let _57_3325 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(
# 2380 "FStar.TypeChecker.Tc.fst"
let _57_3319 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (
# 2381 "FStar.TypeChecker.Tc.fst"
let _57_3321 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (
# 2382 "FStar.TypeChecker.Tc.fst"
let _57_3323 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _146_1259 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _146_1259 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))

# 2387 "FStar.TypeChecker.Tc.fst"
let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2388 "FStar.TypeChecker.Tc.fst"
let _57_3332 = (tc_partial_modul env modul)
in (match (_57_3332) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

# 2391 "FStar.TypeChecker.Tc.fst"
let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 2392 "FStar.TypeChecker.Tc.fst"
let _57_3335 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _146_1268 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _146_1268))
end else begin
()
end
in (
# 2394 "FStar.TypeChecker.Tc.fst"
let env = (
# 2394 "FStar.TypeChecker.Tc.fst"
let _57_3337 = env
in {FStar_TypeChecker_Env.solver = _57_3337.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3337.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3337.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3337.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3337.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3337.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3337.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3337.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3337.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3337.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3337.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3337.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3337.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_3337.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3337.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3337.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3337.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3337.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3337.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3337.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 2395 "FStar.TypeChecker.Tc.fst"
let _57_3353 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _57_3345) -> begin
(let _146_1273 = (let _146_1272 = (let _146_1271 = (FStar_TypeChecker_Env.get_range env)
in ((Prims.strcat "Implicit argument: " msg), _146_1271))
in FStar_Syntax_Syntax.Error (_146_1272))
in (Prims.raise _146_1273))
end
in (match (_57_3353) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(t, c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(let _146_1278 = (let _146_1277 = (let _146_1276 = (let _146_1274 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _146_1274))
in (let _146_1275 = (FStar_TypeChecker_Env.get_range env)
in (_146_1276, _146_1275)))
in FStar_Syntax_Syntax.Error (_146_1277))
in (Prims.raise _146_1278))
end
end)))))

# 2402 "FStar.TypeChecker.Tc.fst"
let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (
# 2403 "FStar.TypeChecker.Tc.fst"
let _57_3356 = if ((let _146_1283 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _146_1283)) <> 0) then begin
(let _146_1284 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _146_1284))
end else begin
()
end
in (
# 2405 "FStar.TypeChecker.Tc.fst"
let _57_3360 = (tc_modul env m)
in (match (_57_3360) with
| (m, env) -> begin
(
# 2406 "FStar.TypeChecker.Tc.fst"
let _57_3361 = if (FStar_Options.should_dump m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _146_1285 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _146_1285))
end else begin
()
end
in (m, env))
end))))




