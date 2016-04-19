
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
| (k, u) -> begin
(
# 440 "FStar.TypeChecker.Tc.fst"
let t = (FStar_TypeChecker_Util.new_uvar env k)
in (
# 441 "FStar.TypeChecker.Tc.fst"
let e = (FStar_TypeChecker_Util.new_uvar env t)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 445 "FStar.TypeChecker.Tc.fst"
let t = if env.FStar_TypeChecker_Env.use_bv_sorts then begin
x.FStar_Syntax_Syntax.sort
end else begin
(FStar_TypeChecker_Env.lookup_bv env x)
end
in (
# 446 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.bv_to_name (
# 446 "FStar.TypeChecker.Tc.fst"
let _57_665 = x
in {FStar_Syntax_Syntax.ppname = _57_665.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_665.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (
# 447 "FStar.TypeChecker.Tc.fst"
let _57_671 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_671) with
| (e, t, implicits) -> begin
(
# 448 "FStar.TypeChecker.Tc.fst"
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
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _57_678; FStar_Syntax_Syntax.pos = _57_676; FStar_Syntax_Syntax.vars = _57_674}, us) -> begin
(
# 452 "FStar.TypeChecker.Tc.fst"
let us = (FStar_List.map (tc_universe env) us)
in (
# 453 "FStar.TypeChecker.Tc.fst"
let _57_688 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_688) with
| (us', t) -> begin
(
# 454 "FStar.TypeChecker.Tc.fst"
let _57_695 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _146_328 = (let _146_327 = (let _146_326 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _146_326))
in FStar_Syntax_Syntax.Error (_146_327))
in (Prims.raise _146_328))
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
# 459 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 459 "FStar.TypeChecker.Tc.fst"
let _57_697 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 459 "FStar.TypeChecker.Tc.fst"
let _57_699 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_699.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_699.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_697.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_697.FStar_Syntax_Syntax.fv_qual})
in (
# 460 "FStar.TypeChecker.Tc.fst"
let e = (let _146_331 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_331 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(
# 464 "FStar.TypeChecker.Tc.fst"
let _57_707 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_707) with
| (us, t) -> begin
(
# 465 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 465 "FStar.TypeChecker.Tc.fst"
let _57_708 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 465 "FStar.TypeChecker.Tc.fst"
let _57_710 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_710.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_710.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_708.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_708.FStar_Syntax_Syntax.fv_qual})
in (
# 466 "FStar.TypeChecker.Tc.fst"
let e = (let _146_332 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_332 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t)))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(
# 470 "FStar.TypeChecker.Tc.fst"
let t = (tc_constant env top.FStar_Syntax_Syntax.pos c)
in (
# 471 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 475 "FStar.TypeChecker.Tc.fst"
let _57_724 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_724) with
| (bs, c) -> begin
(
# 476 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 477 "FStar.TypeChecker.Tc.fst"
let _57_729 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_729) with
| (env, _57_728) -> begin
(
# 478 "FStar.TypeChecker.Tc.fst"
let _57_734 = (tc_binders env bs)
in (match (_57_734) with
| (bs, env, g, us) -> begin
(
# 479 "FStar.TypeChecker.Tc.fst"
let _57_738 = (tc_comp env c)
in (match (_57_738) with
| (c, uc, f) -> begin
(
# 480 "FStar.TypeChecker.Tc.fst"
let e = (
# 480 "FStar.TypeChecker.Tc.fst"
let _57_739 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _57_739.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_739.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_739.FStar_Syntax_Syntax.vars})
in (
# 481 "FStar.TypeChecker.Tc.fst"
let _57_742 = (check_smt_pat env e bs c)
in (
# 482 "FStar.TypeChecker.Tc.fst"
let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (
# 483 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 484 "FStar.TypeChecker.Tc.fst"
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
# 488 "FStar.TypeChecker.Tc.fst"
let u = (tc_universe env u)
in (
# 489 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) None top.FStar_Syntax_Syntax.pos)
in (
# 490 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 494 "FStar.TypeChecker.Tc.fst"
let _57_758 = (let _146_335 = (let _146_334 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_334)::[])
in (FStar_Syntax_Subst.open_term _146_335 phi))
in (match (_57_758) with
| (x, phi) -> begin
(
# 495 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 496 "FStar.TypeChecker.Tc.fst"
let _57_763 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_763) with
| (env, _57_762) -> begin
(
# 497 "FStar.TypeChecker.Tc.fst"
let _57_768 = (let _146_336 = (FStar_List.hd x)
in (tc_binder env _146_336))
in (match (_57_768) with
| (x, env, f1, u) -> begin
(
# 498 "FStar.TypeChecker.Tc.fst"
let _57_769 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_339 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _146_338 = (FStar_Syntax_Print.term_to_string phi)
in (let _146_337 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _146_339 _146_338 _146_337))))
end else begin
()
end
in (
# 501 "FStar.TypeChecker.Tc.fst"
let _57_774 = (FStar_Syntax_Util.type_u ())
in (match (_57_774) with
| (t_phi, _57_773) -> begin
(
# 502 "FStar.TypeChecker.Tc.fst"
let _57_779 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_57_779) with
| (phi, _57_777, f2) -> begin
(
# 503 "FStar.TypeChecker.Tc.fst"
let e = (
# 503 "FStar.TypeChecker.Tc.fst"
let _57_780 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _57_780.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_780.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_780.FStar_Syntax_Syntax.vars})
in (
# 504 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 505 "FStar.TypeChecker.Tc.fst"
let g = (let _146_340 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _146_340))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _57_788) -> begin
(
# 509 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (
# 510 "FStar.TypeChecker.Tc.fst"
let _57_794 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_341 = (FStar_Syntax_Print.term_to_string (
# 511 "FStar.TypeChecker.Tc.fst"
let _57_792 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _57_792.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_792.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_792.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _146_341))
end else begin
()
end
in (
# 512 "FStar.TypeChecker.Tc.fst"
let _57_798 = (FStar_Syntax_Subst.open_term bs body)
in (match (_57_798) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _57_800 -> begin
(let _146_343 = (let _146_342 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _146_342))
in (FStar_All.failwith _146_343))
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
# 536 "FStar.TypeChecker.Tc.fst"
let fail = (fun _57_891 -> (match (()) with
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
| _57_896 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 557 "FStar.TypeChecker.Tc.fst"
let _57_903 = (FStar_Syntax_Util.type_u ())
in (match (_57_903) with
| (k, u) -> begin
(
# 558 "FStar.TypeChecker.Tc.fst"
let _57_908 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_908) with
| (t, _57_906, g) -> begin
(let _146_352 = (FStar_Syntax_Syntax.mk_Total t)
in (_146_352, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 562 "FStar.TypeChecker.Tc.fst"
let _57_913 = (FStar_Syntax_Util.type_u ())
in (match (_57_913) with
| (k, u) -> begin
(
# 563 "FStar.TypeChecker.Tc.fst"
let _57_918 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_918) with
| (t, _57_916, g) -> begin
(let _146_353 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_146_353, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 567 "FStar.TypeChecker.Tc.fst"
let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (
# 568 "FStar.TypeChecker.Tc.fst"
let tc = (let _146_355 = (let _146_354 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_146_354)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _146_355 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 569 "FStar.TypeChecker.Tc.fst"
let _57_927 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_57_927) with
| (tc, _57_925, f) -> begin
(
# 570 "FStar.TypeChecker.Tc.fst"
let _57_931 = (FStar_Syntax_Util.head_and_args tc)
in (match (_57_931) with
| (_57_929, args) -> begin
(
# 571 "FStar.TypeChecker.Tc.fst"
let _57_934 = (let _146_357 = (FStar_List.hd args)
in (let _146_356 = (FStar_List.tl args)
in (_146_357, _146_356)))
in (match (_57_934) with
| (res, args) -> begin
(
# 572 "FStar.TypeChecker.Tc.fst"
let _57_950 = (let _146_359 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _57_5 -> (match (_57_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(
# 574 "FStar.TypeChecker.Tc.fst"
let _57_941 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_941) with
| (env, _57_940) -> begin
(
# 575 "FStar.TypeChecker.Tc.fst"
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
in (FStar_All.pipe_right _146_359 FStar_List.unzip))
in (match (_57_950) with
| (flags, guards) -> begin
(
# 578 "FStar.TypeChecker.Tc.fst"
let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| _57_955 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _146_361 = (FStar_Syntax_Syntax.mk_Comp (
# 581 "FStar.TypeChecker.Tc.fst"
let _57_957 = c
in {FStar_Syntax_Syntax.effect_name = _57_957.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _57_957.FStar_Syntax_Syntax.flags}))
in (let _146_360 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_146_361, u, _146_360))))
end))
end))
end))
end))))
end))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (
# 588 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun u -> (
# 589 "FStar.TypeChecker.Tc.fst"
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
| _57_980 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (
# 611 "FStar.TypeChecker.Tc.fst"
let fail = (fun msg t -> (let _146_381 = (let _146_380 = (let _146_379 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_146_379, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_380))
in (Prims.raise _146_381)))
in (
# 620 "FStar.TypeChecker.Tc.fst"
let check_binders = (fun env bs bs_expected -> (
# 625 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun _57_998 bs bs_expected -> (match (_57_998) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| ((hd, imp)::bs, (hd_expected, imp')::bs_expected) -> begin
(
# 629 "FStar.TypeChecker.Tc.fst"
let _57_1029 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _146_398 = (let _146_397 = (let _146_396 = (let _146_394 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _146_394))
in (let _146_395 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_146_396, _146_395)))
in FStar_Syntax_Syntax.Error (_146_397))
in (Prims.raise _146_398))
end
| _57_1028 -> begin
()
end)
in (
# 636 "FStar.TypeChecker.Tc.fst"
let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (
# 637 "FStar.TypeChecker.Tc.fst"
let _57_1046 = (match ((let _146_399 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _146_399.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _57_1034 -> begin
(
# 640 "FStar.TypeChecker.Tc.fst"
let _57_1035 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_400 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _146_400))
end else begin
()
end
in (
# 641 "FStar.TypeChecker.Tc.fst"
let _57_1041 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_57_1041) with
| (t, _57_1039, g1) -> begin
(
# 642 "FStar.TypeChecker.Tc.fst"
let g2 = (let _146_402 = (FStar_TypeChecker_Env.get_range env)
in (let _146_401 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _146_402 "Type annotation on parameter incompatible with the expected type" _146_401)))
in (
# 646 "FStar.TypeChecker.Tc.fst"
let g = (let _146_403 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _146_403))
in (t, g)))
end)))
end)
in (match (_57_1046) with
| (t, g) -> begin
(
# 648 "FStar.TypeChecker.Tc.fst"
let hd = (
# 648 "FStar.TypeChecker.Tc.fst"
let _57_1047 = hd
in {FStar_Syntax_Syntax.ppname = _57_1047.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1047.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 649 "FStar.TypeChecker.Tc.fst"
let b = (hd, imp)
in (
# 650 "FStar.TypeChecker.Tc.fst"
let b_expected = (hd_expected, imp')
in (
# 651 "FStar.TypeChecker.Tc.fst"
let env = (maybe_push_binding env b)
in (
# 652 "FStar.TypeChecker.Tc.fst"
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
# 662 "FStar.TypeChecker.Tc.fst"
let rec expected_function_typ = (fun env t0 body -> (match (t0) with
| None -> begin
(
# 673 "FStar.TypeChecker.Tc.fst"
let _57_1068 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1067 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (
# 676 "FStar.TypeChecker.Tc.fst"
let _57_1075 = (tc_binders env bs)
in (match (_57_1075) with
| (bs, envbody, g, _57_1074) -> begin
(
# 677 "FStar.TypeChecker.Tc.fst"
let _57_1093 = (match ((let _146_411 = (FStar_Syntax_Subst.compress body)
in _146_411.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _57_1080) -> begin
(
# 679 "FStar.TypeChecker.Tc.fst"
let _57_1087 = (tc_comp envbody c)
in (match (_57_1087) with
| (c, _57_1085, g') -> begin
(let _146_412 = (FStar_TypeChecker_Rel.conj_guard g g')
in (Some (c), body, _146_412))
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
# 685 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 686 "FStar.TypeChecker.Tc.fst"
let rec as_function_typ = (fun norm t -> (match ((let _146_417 = (FStar_Syntax_Subst.compress t)
in _146_417.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 690 "FStar.TypeChecker.Tc.fst"
let _57_1120 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1119 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 691 "FStar.TypeChecker.Tc.fst"
let _57_1127 = (tc_binders env bs)
in (match (_57_1127) with
| (bs, envbody, g, _57_1126) -> begin
(
# 692 "FStar.TypeChecker.Tc.fst"
let _57_1131 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_57_1131) with
| (envbody, _57_1130) -> begin
(Some ((t, true)), bs, [], None, envbody, body, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _57_1134) -> begin
(
# 698 "FStar.TypeChecker.Tc.fst"
let _57_1145 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_57_1145) with
| (_57_1138, bs, bs', copt, env, body, g) -> begin
(Some ((t, false)), bs, bs', copt, env, body, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 702 "FStar.TypeChecker.Tc.fst"
let _57_1152 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_57_1152) with
| (bs_expected, c_expected) -> begin
(
# 709 "FStar.TypeChecker.Tc.fst"
let check_actuals_against_formals = (fun env bs bs_expected -> (
# 710 "FStar.TypeChecker.Tc.fst"
let rec handle_more = (fun _57_1163 c_expected -> (match (_57_1163) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _146_428 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _146_428))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(
# 715 "FStar.TypeChecker.Tc.fst"
let c = (let _146_429 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _146_429))
in (let _146_430 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _146_430)))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(
# 719 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.subst_comp subst c_expected)
in if (FStar_Syntax_Util.is_total_comp c) then begin
(
# 722 "FStar.TypeChecker.Tc.fst"
let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 725 "FStar.TypeChecker.Tc.fst"
let _57_1184 = (check_binders env more_bs bs_expected)
in (match (_57_1184) with
| (env, bs', more, guard', subst) -> begin
(let _146_432 = (let _146_431 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _146_431, subst))
in (handle_more _146_432 c_expected))
end))
end
| _57_1186 -> begin
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
# 732 "FStar.TypeChecker.Tc.fst"
let mk_letrec_env = (fun envbody bs c -> (
# 733 "FStar.TypeChecker.Tc.fst"
let letrecs = (guard_letrecs envbody bs c)
in (
# 734 "FStar.TypeChecker.Tc.fst"
let envbody = (
# 734 "FStar.TypeChecker.Tc.fst"
let _57_1192 = envbody
in {FStar_TypeChecker_Env.solver = _57_1192.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1192.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1192.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1192.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1192.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1192.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1192.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1192.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1192.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1192.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1192.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1192.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_1192.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1192.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1192.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1192.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1192.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1192.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1192.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1192.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _57_1197 _57_1200 -> (match ((_57_1197, _57_1200)) with
| ((env, letrec_binders), (l, t)) -> begin
(
# 738 "FStar.TypeChecker.Tc.fst"
let _57_1206 = (let _146_445 = (let _146_444 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_444 Prims.fst))
in (tc_term _146_445 t))
in (match (_57_1206) with
| (t, _57_1203, _57_1205) -> begin
(
# 739 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (
# 740 "FStar.TypeChecker.Tc.fst"
let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _146_446 = (FStar_Syntax_Syntax.mk_binder (
# 741 "FStar.TypeChecker.Tc.fst"
let _57_1210 = x
in {FStar_Syntax_Syntax.ppname = _57_1210.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1210.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_146_446)::letrec_binders)
end
| _57_1213 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (
# 746 "FStar.TypeChecker.Tc.fst"
let _57_1219 = (check_actuals_against_formals env bs bs_expected)
in (match (_57_1219) with
| (envbody, bs, g, c) -> begin
(
# 747 "FStar.TypeChecker.Tc.fst"
let _57_1222 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_57_1222) with
| (envbody, letrecs) -> begin
(
# 748 "FStar.TypeChecker.Tc.fst"
let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, body, g))
end))
end))))
end))
end
| _57_1225 -> begin
if (not (norm)) then begin
(let _146_447 = (unfold_whnf env t)
in (as_function_typ true _146_447))
end else begin
(
# 756 "FStar.TypeChecker.Tc.fst"
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
# 760 "FStar.TypeChecker.Tc.fst"
let use_eq = env.FStar_TypeChecker_Env.use_eq
in (
# 761 "FStar.TypeChecker.Tc.fst"
let _57_1239 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1239) with
| (env, topt) -> begin
(
# 763 "FStar.TypeChecker.Tc.fst"
let _57_1243 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
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
# 768 "FStar.TypeChecker.Tc.fst"
let _57_1252 = (expected_function_typ env topt body)
in (match (_57_1252) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(
# 769 "FStar.TypeChecker.Tc.fst"
let _57_1258 = (tc_term (
# 769 "FStar.TypeChecker.Tc.fst"
let _57_1253 = envbody
in {FStar_TypeChecker_Env.solver = _57_1253.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1253.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1253.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1253.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1253.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1253.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1253.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1253.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1253.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1253.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1253.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1253.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1253.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1253.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1253.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1253.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1253.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1253.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1253.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_57_1258) with
| (body, cbody, guard_body) -> begin
(
# 771 "FStar.TypeChecker.Tc.fst"
let _57_1259 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_452 = (FStar_Syntax_Print.term_to_string body)
in (let _146_451 = (let _146_449 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _146_449))
in (let _146_450 = (FStar_TypeChecker_Rel.guard_to_string env guard_body)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _146_452 _146_451 _146_450))))
end else begin
()
end
in (
# 777 "FStar.TypeChecker.Tc.fst"
let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (
# 780 "FStar.TypeChecker.Tc.fst"
let _57_1262 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _146_455 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _146_454 = (let _146_453 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _146_453))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _146_455 _146_454)))
end else begin
()
end
in (
# 785 "FStar.TypeChecker.Tc.fst"
let _57_1269 = (let _146_457 = (let _146_456 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _146_456))
in (check_expected_effect (
# 785 "FStar.TypeChecker.Tc.fst"
let _57_1264 = envbody
in {FStar_TypeChecker_Env.solver = _57_1264.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1264.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1264.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1264.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1264.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1264.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1264.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1264.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1264.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1264.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1264.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1264.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1264.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1264.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1264.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1264.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1264.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1264.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1264.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1264.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _146_457))
in (match (_57_1269) with
| (body, cbody, guard) -> begin
(
# 786 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (
# 787 "FStar.TypeChecker.Tc.fst"
let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _146_458 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _146_458))
end else begin
(
# 789 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (
# 792 "FStar.TypeChecker.Tc.fst"
let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (
# 793 "FStar.TypeChecker.Tc.fst"
let e = (let _146_461 = (let _146_460 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _146_459 -> FStar_Util.Inl (_146_459)))
in Some (_146_460))
in (FStar_Syntax_Util.abs bs body _146_461))
in (
# 794 "FStar.TypeChecker.Tc.fst"
let _57_1292 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(
# 796 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_1281) -> begin
(e, t, guard)
end
| _57_1284 -> begin
(
# 803 "FStar.TypeChecker.Tc.fst"
let _57_1287 = if use_teq then begin
(let _146_462 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _146_462))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_57_1287) with
| (e, guard') -> begin
(let _146_463 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _146_463))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_57_1292) with
| (e, tfun, guard) -> begin
(
# 812 "FStar.TypeChecker.Tc.fst"
let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (
# 813 "FStar.TypeChecker.Tc.fst"
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
# 821 "FStar.TypeChecker.Tc.fst"
let n_args = (FStar_List.length args)
in (
# 822 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 823 "FStar.TypeChecker.Tc.fst"
let thead = chead.FStar_Syntax_Syntax.res_typ
in (
# 824 "FStar.TypeChecker.Tc.fst"
let _57_1306 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_472 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _146_471 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _146_472 _146_471)))
end else begin
()
end
in (
# 825 "FStar.TypeChecker.Tc.fst"
let rec check_function_app = (fun norm tf -> (match ((let _146_477 = (FStar_Syntax_Util.unrefine tf)
in _146_477.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 829 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| (e, imp)::tl -> begin
(
# 832 "FStar.TypeChecker.Tc.fst"
let _57_1340 = (tc_term env e)
in (match (_57_1340) with
| (e, c, g_e) -> begin
(
# 833 "FStar.TypeChecker.Tc.fst"
let _57_1344 = (tc_args env tl)
in (match (_57_1344) with
| (args, comps, g_rest) -> begin
(let _146_482 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, (c)::comps, _146_482))
end))
end))
end))
in (
# 841 "FStar.TypeChecker.Tc.fst"
let _57_1348 = (tc_args env args)
in (match (_57_1348) with
| (args, comps, g_args) -> begin
(
# 842 "FStar.TypeChecker.Tc.fst"
let bs = (let _146_484 = (FStar_All.pipe_right comps (FStar_List.map (fun c -> (c.FStar_Syntax_Syntax.res_typ, None))))
in (FStar_Syntax_Util.null_binders_of_tks _146_484))
in (
# 843 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _57_1355 -> begin
FStar_Syntax_Util.ml_comp
end)
in (
# 846 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _146_499 = (FStar_Syntax_Subst.compress t)
in _146_499.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_1361) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _57_1366 -> begin
ml_or_tot
end)
end)
in (
# 853 "FStar.TypeChecker.Tc.fst"
let cres = (let _146_504 = (let _146_503 = (let _146_502 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_502 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _146_503))
in (ml_or_tot _146_504 r))
in (
# 854 "FStar.TypeChecker.Tc.fst"
let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (
# 855 "FStar.TypeChecker.Tc.fst"
let _57_1370 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_507 = (FStar_Syntax_Print.term_to_string head)
in (let _146_506 = (FStar_Syntax_Print.term_to_string tf)
in (let _146_505 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _146_507 _146_506 _146_505))))
end else begin
()
end
in (
# 860 "FStar.TypeChecker.Tc.fst"
let _57_1372 = (let _146_508 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _146_508))
in (
# 861 "FStar.TypeChecker.Tc.fst"
let comp = (let _146_511 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_TypeChecker_Util.bind env None c (None, out))) ((chead)::comps) _146_511))
in (let _146_513 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _146_512 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_146_513, comp, _146_512)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 865 "FStar.TypeChecker.Tc.fst"
let _57_1383 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_1383) with
| (bs, c) -> begin
(
# 867 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun _57_1391 bs cres args -> (match (_57_1391) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (_57_1398)))::rest, (_57_1406, None)::_57_1404) -> begin
(
# 878 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 879 "FStar.TypeChecker.Tc.fst"
let _57_1412 = (check_no_escape (Some (head)) env fvs t)
in (
# 880 "FStar.TypeChecker.Tc.fst"
let _57_1418 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_57_1418) with
| (varg, _57_1416, implicits) -> begin
(
# 881 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (
# 882 "FStar.TypeChecker.Tc.fst"
let arg = (let _146_522 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _146_522))
in (let _146_524 = (let _146_523 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _146_523, fvs))
in (tc_args _146_524 rest cres args))))
end))))
end
| ((x, aqual)::rest, (e, aq)::rest') -> begin
(
# 886 "FStar.TypeChecker.Tc.fst"
let _57_1450 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _57_1449 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (
# 891 "FStar.TypeChecker.Tc.fst"
let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 892 "FStar.TypeChecker.Tc.fst"
let x = (
# 892 "FStar.TypeChecker.Tc.fst"
let _57_1453 = x
in {FStar_Syntax_Syntax.ppname = _57_1453.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1453.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (
# 893 "FStar.TypeChecker.Tc.fst"
let _57_1456 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_525 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _146_525))
end else begin
()
end
in (
# 894 "FStar.TypeChecker.Tc.fst"
let _57_1458 = (check_no_escape (Some (head)) env fvs targ)
in (
# 895 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (
# 896 "FStar.TypeChecker.Tc.fst"
let env = (
# 896 "FStar.TypeChecker.Tc.fst"
let _57_1461 = env
in {FStar_TypeChecker_Env.solver = _57_1461.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1461.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1461.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1461.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1461.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1461.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1461.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1461.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1461.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1461.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1461.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1461.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1461.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1461.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1461.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _57_1461.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1461.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1461.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1461.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1461.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 897 "FStar.TypeChecker.Tc.fst"
let _57_1464 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_528 = (FStar_Syntax_Print.tag_of_term e)
in (let _146_527 = (FStar_Syntax_Print.term_to_string e)
in (let _146_526 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _146_528 _146_527 _146_526))))
end else begin
()
end
in (
# 898 "FStar.TypeChecker.Tc.fst"
let _57_1469 = (tc_term env e)
in (match (_57_1469) with
| (e, c, g_e) -> begin
(
# 899 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (
# 901 "FStar.TypeChecker.Tc.fst"
let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(
# 903 "FStar.TypeChecker.Tc.fst"
let subst = (let _146_529 = (FStar_List.hd bs)
in (maybe_extend_subst subst _146_529 e))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(
# 906 "FStar.TypeChecker.Tc.fst"
let subst = (let _146_530 = (FStar_List.hd bs)
in (maybe_extend_subst subst _146_530 e))
in (
# 907 "FStar.TypeChecker.Tc.fst"
let _57_1476 = (((Some (x), c))::comps, g)
in (match (_57_1476) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _146_531 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _146_531)) then begin
(
# 911 "FStar.TypeChecker.Tc.fst"
let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (
# 912 "FStar.TypeChecker.Tc.fst"
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
| (_57_1480, []) -> begin
(
# 921 "FStar.TypeChecker.Tc.fst"
let _57_1483 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (
# 922 "FStar.TypeChecker.Tc.fst"
let _57_1501 = (match (bs) with
| [] -> begin
(
# 925 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (
# 931 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (
# 933 "FStar.TypeChecker.Tc.fst"
let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _57_1491 -> (match (_57_1491) with
| (_57_1489, c) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (
# 940 "FStar.TypeChecker.Tc.fst"
let cres = if refine_with_equality then begin
(let _146_538 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _146_538 cres))
end else begin
(
# 946 "FStar.TypeChecker.Tc.fst"
let _57_1493 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
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
| _57_1497 -> begin
(
# 955 "FStar.TypeChecker.Tc.fst"
let g = (let _146_542 = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (FStar_All.pipe_right _146_542 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _146_547 = (let _146_546 = (let _146_545 = (let _146_544 = (let _146_543 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _146_543))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _146_544))
in (FStar_Syntax_Syntax.mk_Total _146_545))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_546))
in (_146_547, g)))
end)
in (match (_57_1501) with
| (cres, g) -> begin
(
# 958 "FStar.TypeChecker.Tc.fst"
let _57_1502 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_548 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _146_548))
end else begin
()
end
in (
# 959 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_List.fold_left (fun out c -> (FStar_TypeChecker_Util.bind env None (Prims.snd c) ((Prims.fst c), out))) cres comps)
in (
# 960 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.bind env None chead (None, comp))
in (
# 961 "FStar.TypeChecker.Tc.fst"
let app = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev outargs) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (
# 962 "FStar.TypeChecker.Tc.fst"
let comp = (FStar_TypeChecker_Util.record_application_site env app comp)
in (
# 963 "FStar.TypeChecker.Tc.fst"
let _57_1512 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp g)
in (match (_57_1512) with
| (comp, g) -> begin
(
# 964 "FStar.TypeChecker.Tc.fst"
let _57_1513 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
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
| ([], arg::_57_1517) -> begin
(
# 970 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun norm tres -> (
# 971 "FStar.TypeChecker.Tc.fst"
let tres = (let _146_559 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _146_559 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(
# 974 "FStar.TypeChecker.Tc.fst"
let _57_1529 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_560 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _146_560))
end else begin
()
end
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs (FStar_Syntax_Util.lcomp_of_comp cres') args))
end
| _57_1532 when (not (norm)) -> begin
(let _146_561 = (unfold_whnf env tres)
in (aux true _146_561))
end
| _57_1534 -> begin
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
| _57_1536 -> begin
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
# 1000 "FStar.TypeChecker.Tc.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1001 "FStar.TypeChecker.Tc.fst"
let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(
# 1004 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in (
# 1005 "FStar.TypeChecker.Tc.fst"
let _57_1572 = (FStar_List.fold_left2 (fun _57_1553 _57_1556 _57_1559 -> (match ((_57_1553, _57_1556, _57_1559)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(
# 1006 "FStar.TypeChecker.Tc.fst"
let _57_1560 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1007 "FStar.TypeChecker.Tc.fst"
let _57_1565 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_57_1565) with
| (e, c, g) -> begin
(
# 1008 "FStar.TypeChecker.Tc.fst"
let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (
# 1009 "FStar.TypeChecker.Tc.fst"
let g = (let _146_583 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _146_583 g))
in (
# 1010 "FStar.TypeChecker.Tc.fst"
let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _146_587 = (let _146_585 = (let _146_584 = (FStar_Syntax_Syntax.as_arg e)
in (_146_584)::[])
in (FStar_List.append seen _146_585))
in (let _146_586 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_146_587, _146_586, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_57_1572) with
| (args, guard, ghost) -> begin
(
# 1014 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (
# 1015 "FStar.TypeChecker.Tc.fst"
let c = if ghost then begin
(let _146_588 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _146_588 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (
# 1016 "FStar.TypeChecker.Tc.fst"
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
# 1036 "FStar.TypeChecker.Tc.fst"
let _57_1586 = (FStar_Syntax_Subst.open_branch branch)
in (match (_57_1586) with
| (pattern, when_clause, branch_exp) -> begin
(
# 1037 "FStar.TypeChecker.Tc.fst"
let _57_1591 = branch
in (match (_57_1591) with
| (cpat, _57_1589, cbr) -> begin
(
# 1040 "FStar.TypeChecker.Tc.fst"
let tc_pat = (fun allow_implicits pat_t p0 -> (
# 1047 "FStar.TypeChecker.Tc.fst"
let _57_1599 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_57_1599) with
| (pat_bvs, exps, p) -> begin
(
# 1048 "FStar.TypeChecker.Tc.fst"
let _57_1600 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_600 = (FStar_Syntax_Print.pat_to_string p0)
in (let _146_599 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _146_600 _146_599)))
end else begin
()
end
in (
# 1050 "FStar.TypeChecker.Tc.fst"
let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (
# 1051 "FStar.TypeChecker.Tc.fst"
let _57_1606 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_57_1606) with
| (env1, _57_1605) -> begin
(
# 1052 "FStar.TypeChecker.Tc.fst"
let env1 = (
# 1052 "FStar.TypeChecker.Tc.fst"
let _57_1607 = env1
in {FStar_TypeChecker_Env.solver = _57_1607.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1607.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1607.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1607.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1607.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1607.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1607.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1607.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _57_1607.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1607.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1607.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1607.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1607.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1607.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1607.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1607.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1607.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1607.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1607.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1607.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1053 "FStar.TypeChecker.Tc.fst"
let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (
# 1054 "FStar.TypeChecker.Tc.fst"
let _57_1646 = (let _146_623 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (
# 1055 "FStar.TypeChecker.Tc.fst"
let _57_1612 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_603 = (FStar_Syntax_Print.term_to_string e)
in (let _146_602 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _146_603 _146_602)))
end else begin
()
end
in (
# 1058 "FStar.TypeChecker.Tc.fst"
let _57_1617 = (tc_term env1 e)
in (match (_57_1617) with
| (e, lc, g) -> begin
(
# 1060 "FStar.TypeChecker.Tc.fst"
let _57_1618 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_605 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _146_604 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _146_605 _146_604)))
end else begin
()
end
in (
# 1063 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (
# 1064 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (
# 1065 "FStar.TypeChecker.Tc.fst"
let _57_1624 = (let _146_606 = (FStar_TypeChecker_Rel.discharge_guard env (
# 1065 "FStar.TypeChecker.Tc.fst"
let _57_1622 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_1622.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_1622.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_1622.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _146_606 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1066 "FStar.TypeChecker.Tc.fst"
let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (
# 1067 "FStar.TypeChecker.Tc.fst"
let uvars_to_string = (fun uvs -> (let _146_611 = (let _146_610 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _146_610 (FStar_List.map (fun _57_1632 -> (match (_57_1632) with
| (u, _57_1631) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _146_611 (FStar_String.concat ", "))))
in (
# 1068 "FStar.TypeChecker.Tc.fst"
let uvs1 = (FStar_Syntax_Free.uvars e')
in (
# 1069 "FStar.TypeChecker.Tc.fst"
let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (
# 1070 "FStar.TypeChecker.Tc.fst"
let _57_1640 = if (let _146_612 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _146_612)) then begin
(
# 1071 "FStar.TypeChecker.Tc.fst"
let unresolved = (let _146_613 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _146_613 FStar_Util.set_elements))
in (let _146_621 = (let _146_620 = (let _146_619 = (let _146_618 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _146_617 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _146_616 = (let _146_615 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _57_1639 -> (match (_57_1639) with
| (u, _57_1638) -> begin
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
# 1078 "FStar.TypeChecker.Tc.fst"
let _57_1642 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_622 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _146_622))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _146_623 FStar_List.unzip))
in (match (_57_1646) with
| (exps, norm_exps) -> begin
(
# 1083 "FStar.TypeChecker.Tc.fst"
let p = (FStar_TypeChecker_Util.decorate_pattern env p exps)
in (p, pat_bvs, pat_env, exps, norm_exps))
end))))
end))))
end)))
in (
# 1087 "FStar.TypeChecker.Tc.fst"
let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (
# 1088 "FStar.TypeChecker.Tc.fst"
let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (
# 1089 "FStar.TypeChecker.Tc.fst"
let _57_1653 = (let _146_624 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _146_624 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_57_1653) with
| (scrutinee_env, _57_1652) -> begin
(
# 1092 "FStar.TypeChecker.Tc.fst"
let _57_1659 = (tc_pat true pat_t pattern)
in (match (_57_1659) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(
# 1095 "FStar.TypeChecker.Tc.fst"
let _57_1669 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(
# 1102 "FStar.TypeChecker.Tc.fst"
let _57_1666 = (let _146_625 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _146_625 e))
in (match (_57_1666) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_57_1669) with
| (when_clause, g_when) -> begin
(
# 1106 "FStar.TypeChecker.Tc.fst"
let _57_1673 = (tc_term pat_env branch_exp)
in (match (_57_1673) with
| (branch_exp, c, g_branch) -> begin
(
# 1110 "FStar.TypeChecker.Tc.fst"
let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _146_627 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _146_626 -> Some (_146_626)) _146_627))
end)
in (
# 1117 "FStar.TypeChecker.Tc.fst"
let _57_1729 = (
# 1120 "FStar.TypeChecker.Tc.fst"
let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (
# 1121 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _57_1691 -> begin
(
# 1127 "FStar.TypeChecker.Tc.fst"
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
# 1132 "FStar.TypeChecker.Tc.fst"
let _57_1699 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_57_1699) with
| (c, g_branch) -> begin
(
# 1136 "FStar.TypeChecker.Tc.fst"
let _57_1724 = (match ((eqs, when_condition)) with
| (None, None) -> begin
(c, g_when)
end
| (Some (f), None) -> begin
(
# 1142 "FStar.TypeChecker.Tc.fst"
let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1143 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _146_634 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _146_633 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_146_634, _146_633)))))
end
| (Some (f), Some (w)) -> begin
(
# 1148 "FStar.TypeChecker.Tc.fst"
let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1149 "FStar.TypeChecker.Tc.fst"
let g_fw = (let _146_635 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_146_635))
in (let _146_638 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _146_637 = (let _146_636 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _146_636 g_when))
in (_146_638, _146_637)))))
end
| (None, Some (w)) -> begin
(
# 1154 "FStar.TypeChecker.Tc.fst"
let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (
# 1155 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _146_639 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_146_639, g_when))))
end)
in (match (_57_1724) with
| (c_weak, g_when_weak) -> begin
(
# 1160 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _146_641 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _146_640 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_146_641, _146_640, g_branch))))
end))
end)))
in (match (_57_1729) with
| (c, g_when, g_branch) -> begin
(
# 1178 "FStar.TypeChecker.Tc.fst"
let branch_guard = (
# 1180 "FStar.TypeChecker.Tc.fst"
let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (
# 1181 "FStar.TypeChecker.Tc.fst"
let discriminate = (fun scrutinee_tm f -> if ((let _146_651 = (let _146_650 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _146_650))
in (FStar_List.length _146_651)) > 1) then begin
(
# 1184 "FStar.TypeChecker.Tc.fst"
let disc = (let _146_652 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _146_652 FStar_Syntax_Syntax.Delta_equational None))
in (
# 1185 "FStar.TypeChecker.Tc.fst"
let disc = (let _146_654 = (let _146_653 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_146_653)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _146_654 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _146_655 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_146_655)::[])))
end else begin
[]
end)
in (
# 1189 "FStar.TypeChecker.Tc.fst"
let fail = (fun _57_1739 -> (match (()) with
| () -> begin
(let _146_661 = (let _146_660 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _146_659 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _146_658 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _146_660 _146_659 _146_658))))
in (FStar_All.failwith _146_661))
end))
in (
# 1195 "FStar.TypeChecker.Tc.fst"
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
# 1200 "FStar.TypeChecker.Tc.fst"
let pat_exp = (let _146_664 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _146_664 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_57_1775) -> begin
(let _146_669 = (let _146_668 = (let _146_667 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _146_666 = (let _146_665 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_146_665)::[])
in (_146_667)::_146_666))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _146_668 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_146_669)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 1209 "FStar.TypeChecker.Tc.fst"
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
# 1214 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(
# 1217 "FStar.TypeChecker.Tc.fst"
let sub_term_guards = (let _146_677 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _57_1793 -> (match (_57_1793) with
| (ei, _57_1792) -> begin
(
# 1218 "FStar.TypeChecker.Tc.fst"
let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _57_1797 -> begin
(
# 1222 "FStar.TypeChecker.Tc.fst"
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
| _57_1801 -> begin
[]
end))))))
in (
# 1228 "FStar.TypeChecker.Tc.fst"
let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(
# 1231 "FStar.TypeChecker.Tc.fst"
let t = (let _146_683 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _146_683))
in (
# 1232 "FStar.TypeChecker.Tc.fst"
let _57_1809 = (FStar_Syntax_Util.type_u ())
in (match (_57_1809) with
| (k, _57_1808) -> begin
(
# 1233 "FStar.TypeChecker.Tc.fst"
let _57_1815 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_57_1815) with
| (t, _57_1812, _57_1814) -> begin
t
end))
end)))
end)
in (
# 1237 "FStar.TypeChecker.Tc.fst"
let branch_guard = (let _146_684 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _146_684 FStar_Syntax_Util.mk_disj_l))
in (
# 1240 "FStar.TypeChecker.Tc.fst"
let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
in (
# 1246 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (
# 1248 "FStar.TypeChecker.Tc.fst"
let _57_1823 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
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
# 1262 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1265 "FStar.TypeChecker.Tc.fst"
let _57_1840 = (check_let_bound_def true env lb)
in (match (_57_1840) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(
# 1267 "FStar.TypeChecker.Tc.fst"
let _57_1852 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(
# 1270 "FStar.TypeChecker.Tc.fst"
let g1 = (let _146_689 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _146_689 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1271 "FStar.TypeChecker.Tc.fst"
let _57_1847 = (let _146_693 = (let _146_692 = (let _146_691 = (let _146_690 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _146_690))
in (_146_691)::[])
in (FStar_TypeChecker_Util.generalize env _146_692))
in (FStar_List.hd _146_693))
in (match (_57_1847) with
| (_57_1843, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_57_1852) with
| (g1, e1, univ_vars, c1) -> begin
(
# 1275 "FStar.TypeChecker.Tc.fst"
let _57_1862 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(
# 1277 "FStar.TypeChecker.Tc.fst"
let _57_1855 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_57_1855) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(
# 1280 "FStar.TypeChecker.Tc.fst"
let _57_1856 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
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
# 1284 "FStar.TypeChecker.Tc.fst"
let _57_1858 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _146_696 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _146_696)))
end
in (match (_57_1862) with
| (e2, c1) -> begin
(
# 1289 "FStar.TypeChecker.Tc.fst"
let cres = (let _146_697 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_697))
in (
# 1290 "FStar.TypeChecker.Tc.fst"
let _57_1864 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1292 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _146_698 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_146_698, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _57_1868 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1309 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(
# 1312 "FStar.TypeChecker.Tc.fst"
let env = (
# 1312 "FStar.TypeChecker.Tc.fst"
let _57_1879 = env
in {FStar_TypeChecker_Env.solver = _57_1879.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1879.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1879.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1879.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1879.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1879.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1879.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1879.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1879.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1879.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1879.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1879.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1879.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1879.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1879.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1879.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1879.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1879.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1879.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1879.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1313 "FStar.TypeChecker.Tc.fst"
let _57_1888 = (let _146_702 = (let _146_701 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_701 Prims.fst))
in (check_let_bound_def false _146_702 lb))
in (match (_57_1888) with
| (e1, _57_1884, c1, g1, annotated) -> begin
(
# 1314 "FStar.TypeChecker.Tc.fst"
let x = (
# 1314 "FStar.TypeChecker.Tc.fst"
let _57_1889 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1889.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1889.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (
# 1315 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (
# 1316 "FStar.TypeChecker.Tc.fst"
let _57_1895 = (let _146_704 = (let _146_703 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_703)::[])
in (FStar_Syntax_Subst.open_term _146_704 e2))
in (match (_57_1895) with
| (xb, e2) -> begin
(
# 1317 "FStar.TypeChecker.Tc.fst"
let xbinder = (FStar_List.hd xb)
in (
# 1318 "FStar.TypeChecker.Tc.fst"
let x = (Prims.fst xbinder)
in (
# 1319 "FStar.TypeChecker.Tc.fst"
let _57_1901 = (let _146_705 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _146_705 e2))
in (match (_57_1901) with
| (e2, c2, g2) -> begin
(
# 1320 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (x), c2))
in (
# 1321 "FStar.TypeChecker.Tc.fst"
let e = (let _146_708 = (let _146_707 = (let _146_706 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _146_706))
in FStar_Syntax_Syntax.Tm_let (_146_707))
in (FStar_Syntax_Syntax.mk _146_708 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 1322 "FStar.TypeChecker.Tc.fst"
let x_eq_e1 = (let _146_711 = (let _146_710 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _146_710 e1))
in (FStar_All.pipe_left (fun _146_709 -> FStar_TypeChecker_Common.NonTrivial (_146_709)) _146_711))
in (
# 1323 "FStar.TypeChecker.Tc.fst"
let g2 = (let _146_713 = (let _146_712 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _146_712 g2))
in (FStar_TypeChecker_Rel.close_guard xb _146_713))
in (
# 1325 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if annotated then begin
(e, cres, guard)
end else begin
(
# 1329 "FStar.TypeChecker.Tc.fst"
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
# 1338 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1341 "FStar.TypeChecker.Tc.fst"
let _57_1922 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1922) with
| (lbs, e2) -> begin
(
# 1343 "FStar.TypeChecker.Tc.fst"
let _57_1925 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1925) with
| (env0, topt) -> begin
(
# 1344 "FStar.TypeChecker.Tc.fst"
let _57_1928 = (build_let_rec_env true env0 lbs)
in (match (_57_1928) with
| (lbs, rec_env) -> begin
(
# 1345 "FStar.TypeChecker.Tc.fst"
let _57_1931 = (check_let_recs rec_env lbs)
in (match (_57_1931) with
| (lbs, g_lbs) -> begin
(
# 1346 "FStar.TypeChecker.Tc.fst"
let g_lbs = (let _146_716 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _146_716 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1348 "FStar.TypeChecker.Tc.fst"
let all_lb_names = (let _146_719 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _146_719 (fun _146_718 -> Some (_146_718))))
in (
# 1350 "FStar.TypeChecker.Tc.fst"
let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(
# 1356 "FStar.TypeChecker.Tc.fst"
let ecs = (let _146_723 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _146_722 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _146_722)))))
in (FStar_TypeChecker_Util.generalize env _146_723))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _57_1942 -> (match (_57_1942) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (
# 1363 "FStar.TypeChecker.Tc.fst"
let cres = (let _146_725 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_725))
in (
# 1364 "FStar.TypeChecker.Tc.fst"
let _57_1945 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1366 "FStar.TypeChecker.Tc.fst"
let _57_1949 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1949) with
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
| _57_1951 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1377 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1380 "FStar.TypeChecker.Tc.fst"
let _57_1963 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1963) with
| (lbs, e2) -> begin
(
# 1382 "FStar.TypeChecker.Tc.fst"
let _57_1966 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1966) with
| (env0, topt) -> begin
(
# 1383 "FStar.TypeChecker.Tc.fst"
let _57_1969 = (build_let_rec_env false env0 lbs)
in (match (_57_1969) with
| (lbs, rec_env) -> begin
(
# 1384 "FStar.TypeChecker.Tc.fst"
let _57_1972 = (check_let_recs rec_env lbs)
in (match (_57_1972) with
| (lbs, g_lbs) -> begin
(
# 1386 "FStar.TypeChecker.Tc.fst"
let _57_1984 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (
# 1387 "FStar.TypeChecker.Tc.fst"
let x = (
# 1387 "FStar.TypeChecker.Tc.fst"
let _57_1975 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1975.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1975.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (
# 1388 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1388 "FStar.TypeChecker.Tc.fst"
let _57_1978 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _57_1978.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1978.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1978.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _57_1978.FStar_Syntax_Syntax.lbdef})
in (
# 1389 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], lb.FStar_Syntax_Syntax.lbtyp))
in (env, lb))))) env))
in (match (_57_1984) with
| (env, lbs) -> begin
(
# 1392 "FStar.TypeChecker.Tc.fst"
let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (
# 1394 "FStar.TypeChecker.Tc.fst"
let _57_1990 = (tc_term env e2)
in (match (_57_1990) with
| (e2, cres, g2) -> begin
(
# 1395 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (
# 1396 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (
# 1397 "FStar.TypeChecker.Tc.fst"
let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (
# 1398 "FStar.TypeChecker.Tc.fst"
let cres = (
# 1398 "FStar.TypeChecker.Tc.fst"
let _57_1994 = cres
in {FStar_Syntax_Syntax.eff_name = _57_1994.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _57_1994.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_1994.FStar_Syntax_Syntax.comp})
in (
# 1400 "FStar.TypeChecker.Tc.fst"
let _57_1999 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1999) with
| (lbs, e2) -> begin
(
# 1401 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_57_2002) -> begin
(e, cres, guard)
end
| None -> begin
(
# 1405 "FStar.TypeChecker.Tc.fst"
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
# 1416 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1417 "FStar.TypeChecker.Tc.fst"
let _57_2041 = (FStar_List.fold_left (fun _57_2015 lb -> (match (_57_2015) with
| (lbs, env) -> begin
(
# 1418 "FStar.TypeChecker.Tc.fst"
let _57_2020 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_57_2020) with
| (univ_vars, t, check_t) -> begin
(
# 1419 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (
# 1420 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (
# 1421 "FStar.TypeChecker.Tc.fst"
let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(
# 1426 "FStar.TypeChecker.Tc.fst"
let _57_2029 = (let _146_739 = (let _146_738 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _146_738))
in (tc_check_tot_or_gtot_term (
# 1426 "FStar.TypeChecker.Tc.fst"
let _57_2023 = env0
in {FStar_TypeChecker_Env.solver = _57_2023.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2023.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2023.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2023.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2023.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2023.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2023.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2023.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2023.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2023.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2023.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2023.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2023.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2023.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _57_2023.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2023.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2023.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2023.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2023.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2023.FStar_TypeChecker_Env.use_bv_sorts}) t _146_739))
in (match (_57_2029) with
| (t, _57_2027, g) -> begin
(
# 1427 "FStar.TypeChecker.Tc.fst"
let _57_2030 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (
# 1429 "FStar.TypeChecker.Tc.fst"
let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(
# 1431 "FStar.TypeChecker.Tc.fst"
let _57_2033 = env
in {FStar_TypeChecker_Env.solver = _57_2033.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2033.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2033.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2033.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2033.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2033.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2033.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2033.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2033.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2033.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2033.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2033.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2033.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_2033.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2033.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2033.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2033.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2033.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2033.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2033.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (
# 1433 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1433 "FStar.TypeChecker.Tc.fst"
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
# 1440 "FStar.TypeChecker.Tc.fst"
let _57_2054 = (let _146_744 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 1441 "FStar.TypeChecker.Tc.fst"
let _57_2048 = (let _146_743 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _146_743 lb.FStar_Syntax_Syntax.lbdef))
in (match (_57_2048) with
| (e, c, g) -> begin
(
# 1442 "FStar.TypeChecker.Tc.fst"
let _57_2049 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1444 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _146_744 FStar_List.unzip))
in (match (_57_2054) with
| (lbs, gs) -> begin
(
# 1446 "FStar.TypeChecker.Tc.fst"
let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (
# 1460 "FStar.TypeChecker.Tc.fst"
let _57_2062 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_2062) with
| (env1, _57_2061) -> begin
(
# 1461 "FStar.TypeChecker.Tc.fst"
let e1 = lb.FStar_Syntax_Syntax.lbdef
in (
# 1464 "FStar.TypeChecker.Tc.fst"
let _57_2068 = (check_lbtyp top_level env lb)
in (match (_57_2068) with
| (topt, wf_annot, univ_vars, env1) -> begin
(
# 1466 "FStar.TypeChecker.Tc.fst"
let _57_2069 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1470 "FStar.TypeChecker.Tc.fst"
let _57_2076 = (tc_maybe_toplevel_term (
# 1470 "FStar.TypeChecker.Tc.fst"
let _57_2071 = env1
in {FStar_TypeChecker_Env.solver = _57_2071.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2071.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2071.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2071.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2071.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2071.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2071.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2071.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2071.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2071.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2071.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2071.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2071.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _57_2071.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2071.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2071.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2071.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2071.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2071.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2071.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_57_2076) with
| (e1, c1, g1) -> begin
(
# 1473 "FStar.TypeChecker.Tc.fst"
let _57_2080 = (let _146_751 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_2077 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _146_751 e1 c1 wf_annot))
in (match (_57_2080) with
| (c1, guard_f) -> begin
(
# 1476 "FStar.TypeChecker.Tc.fst"
let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (
# 1478 "FStar.TypeChecker.Tc.fst"
let _57_2082 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
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
# 1490 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 1493 "FStar.TypeChecker.Tc.fst"
let _57_2089 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _57_2092 -> begin
(
# 1497 "FStar.TypeChecker.Tc.fst"
let _57_2095 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_57_2095) with
| (univ_vars, t) -> begin
(
# 1498 "FStar.TypeChecker.Tc.fst"
let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _146_757 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _146_757))
end else begin
(
# 1505 "FStar.TypeChecker.Tc.fst"
let _57_2100 = (FStar_Syntax_Util.type_u ())
in (match (_57_2100) with
| (k, _57_2099) -> begin
(
# 1506 "FStar.TypeChecker.Tc.fst"
let _57_2105 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_57_2105) with
| (t, _57_2103, g) -> begin
(
# 1507 "FStar.TypeChecker.Tc.fst"
let _57_2106 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _146_760 = (let _146_758 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _146_758))
in (let _146_759 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _146_760 _146_759)))
end else begin
()
end
in (
# 1511 "FStar.TypeChecker.Tc.fst"
let t = (norm env1 t)
in (let _146_761 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _146_761))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _57_2112 -> (match (_57_2112) with
| (x, imp) -> begin
(
# 1516 "FStar.TypeChecker.Tc.fst"
let _57_2115 = (FStar_Syntax_Util.type_u ())
in (match (_57_2115) with
| (tu, u) -> begin
(
# 1517 "FStar.TypeChecker.Tc.fst"
let _57_2120 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_57_2120) with
| (t, _57_2118, g) -> begin
(
# 1518 "FStar.TypeChecker.Tc.fst"
let x = ((
# 1518 "FStar.TypeChecker.Tc.fst"
let _57_2121 = x
in {FStar_Syntax_Syntax.ppname = _57_2121.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2121.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (
# 1519 "FStar.TypeChecker.Tc.fst"
let _57_2124 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
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
# 1524 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_TypeChecker_Rel.trivial_guard, [])
end
| b::bs -> begin
(
# 1527 "FStar.TypeChecker.Tc.fst"
let _57_2139 = (tc_binder env b)
in (match (_57_2139) with
| (b, env', g, u) -> begin
(
# 1528 "FStar.TypeChecker.Tc.fst"
let _57_2144 = (aux env' bs)
in (match (_57_2144) with
| (bs, env', g', us) -> begin
(let _146_774 = (let _146_773 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _146_773))
in ((b)::bs, env', _146_774, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (
# 1533 "FStar.TypeChecker.Tc.fst"
let tc_args = (fun env args -> (FStar_List.fold_right (fun _57_2152 _57_2155 -> (match ((_57_2152, _57_2155)) with
| ((t, imp), (args, g)) -> begin
(
# 1537 "FStar.TypeChecker.Tc.fst"
let _57_2160 = (tc_term env t)
in (match (_57_2160) with
| (t, _57_2158, g') -> begin
(let _146_783 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _146_783))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _57_2164 -> (match (_57_2164) with
| (pats, g) -> begin
(
# 1540 "FStar.TypeChecker.Tc.fst"
let _57_2167 = (tc_args env p)
in (match (_57_2167) with
| (args, g') -> begin
(let _146_786 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _146_786))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1545 "FStar.TypeChecker.Tc.fst"
let _57_2173 = (tc_maybe_toplevel_term env e)
in (match (_57_2173) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(
# 1548 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (
# 1549 "FStar.TypeChecker.Tc.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 1550 "FStar.TypeChecker.Tc.fst"
let _57_2176 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_789 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _146_789))
end else begin
()
end
in (
# 1551 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 1552 "FStar.TypeChecker.Tc.fst"
let _57_2181 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _146_790 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_146_790, false))
end else begin
(let _146_791 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_146_791, true))
end
in (match (_57_2181) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _146_792 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _146_792))
end
| _57_2185 -> begin
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
# 1566 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))

# 1570 "FStar.TypeChecker.Tc.fst"
let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (
# 1571 "FStar.TypeChecker.Tc.fst"
let _57_2195 = (tc_tot_or_gtot_term env t)
in (match (_57_2195) with
| (t, c, g) -> begin
(
# 1572 "FStar.TypeChecker.Tc.fst"
let _57_2196 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))

# 1575 "FStar.TypeChecker.Tc.fst"
let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (
# 1576 "FStar.TypeChecker.Tc.fst"
let _57_2204 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_2204) with
| (t, c, g) -> begin
(
# 1577 "FStar.TypeChecker.Tc.fst"
let _57_2205 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))

# 1580 "FStar.TypeChecker.Tc.fst"
let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _146_818 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _146_818)))

# 1583 "FStar.TypeChecker.Tc.fst"
let check_nogen = (fun env t k -> (
# 1584 "FStar.TypeChecker.Tc.fst"
let t = (tc_check_trivial_guard env t k)
in (let _146_822 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _146_822))))

# 1587 "FStar.TypeChecker.Tc.fst"
let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (
# 1588 "FStar.TypeChecker.Tc.fst"
let _57_2220 = (tc_binders env tps)
in (match (_57_2220) with
| (tps, env, g, us) -> begin
(
# 1589 "FStar.TypeChecker.Tc.fst"
let _57_2221 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))

# 1592 "FStar.TypeChecker.Tc.fst"
let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (
# 1593 "FStar.TypeChecker.Tc.fst"
let fail = (fun _57_2227 -> (match (()) with
| () -> begin
(let _146_837 = (let _146_836 = (let _146_835 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_146_835, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_146_836))
in (Prims.raise _146_837))
end))
in (
# 1594 "FStar.TypeChecker.Tc.fst"
let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1597 "FStar.TypeChecker.Tc.fst"
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

# 1604 "FStar.TypeChecker.Tc.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 1607 "FStar.TypeChecker.Tc.fst"
let _57_2257 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_57_2257) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _57_2259 -> begin
(
# 1610 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow binders c)
in (
# 1611 "FStar.TypeChecker.Tc.fst"
let _57_2263 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_57_2263) with
| (uvs, t') -> begin
(match ((let _146_844 = (FStar_Syntax_Subst.compress t')
in _146_844.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _57_2269 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 1616 "FStar.TypeChecker.Tc.fst"
let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (
# 1617 "FStar.TypeChecker.Tc.fst"
let fail = (fun t -> (let _146_855 = (let _146_854 = (let _146_853 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_146_853, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_146_854))
in (Prims.raise _146_855)))
in (match ((let _146_856 = (FStar_Syntax_Subst.compress signature)
in _146_856.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1620 "FStar.TypeChecker.Tc.fst"
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

# 1627 "FStar.TypeChecker.Tc.fst"
let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (
# 1628 "FStar.TypeChecker.Tc.fst"
let _57_2301 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_57_2301) with
| (a, wp) -> begin
(
# 1629 "FStar.TypeChecker.Tc.fst"
let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _57_2304 -> begin
(
# 1633 "FStar.TypeChecker.Tc.fst"
let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (
# 1634 "FStar.TypeChecker.Tc.fst"
let op = (fun ts -> (
# 1635 "FStar.TypeChecker.Tc.fst"
let _57_2308 = ()
in (
# 1636 "FStar.TypeChecker.Tc.fst"
let t0 = (Prims.snd ts)
in (
# 1637 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (
# 1639 "FStar.TypeChecker.Tc.fst"
let _57_2312 = ed
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
in {FStar_Syntax_Syntax.qualifiers = _57_2312.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2312.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2312.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2312.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2312.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _146_875; FStar_Syntax_Syntax.bind_wp = _146_874; FStar_Syntax_Syntax.bind_wlp = _146_873; FStar_Syntax_Syntax.if_then_else = _146_872; FStar_Syntax_Syntax.ite_wp = _146_871; FStar_Syntax_Syntax.ite_wlp = _146_870; FStar_Syntax_Syntax.wp_binop = _146_869; FStar_Syntax_Syntax.wp_as_type = _146_868; FStar_Syntax_Syntax.close_wp = _146_867; FStar_Syntax_Syntax.assert_p = _146_866; FStar_Syntax_Syntax.assume_p = _146_865; FStar_Syntax_Syntax.null_wp = _146_864; FStar_Syntax_Syntax.trivial = _146_863}))))))))))))))))
end)
in (ed, a, wp))
end)))

# 1655 "FStar.TypeChecker.Tc.fst"
let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (
# 1656 "FStar.TypeChecker.Tc.fst"
let _57_2317 = ()
in (
# 1657 "FStar.TypeChecker.Tc.fst"
let _57_2321 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_57_2321) with
| (binders_un, signature_un) -> begin
(
# 1658 "FStar.TypeChecker.Tc.fst"
let _57_2326 = (tc_tparams env0 binders_un)
in (match (_57_2326) with
| (binders, env, _57_2325) -> begin
(
# 1659 "FStar.TypeChecker.Tc.fst"
let _57_2330 = (tc_trivial_guard env signature_un)
in (match (_57_2330) with
| (signature, _57_2329) -> begin
(
# 1660 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1660 "FStar.TypeChecker.Tc.fst"
let _57_2331 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2331.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2331.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2331.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _57_2331.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2331.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _57_2331.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = _57_2331.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _57_2331.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _57_2331.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = _57_2331.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _57_2331.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _57_2331.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _57_2331.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _57_2331.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _57_2331.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _57_2331.FStar_Syntax_Syntax.trivial})
in (
# 1663 "FStar.TypeChecker.Tc.fst"
let _57_2337 = (open_effect_decl env ed)
in (match (_57_2337) with
| (ed, a, wp_a) -> begin
(
# 1664 "FStar.TypeChecker.Tc.fst"
let get_effect_signature = (fun _57_2339 -> (match (()) with
| () -> begin
(
# 1665 "FStar.TypeChecker.Tc.fst"
let _57_2343 = (tc_trivial_guard env signature_un)
in (match (_57_2343) with
| (signature, _57_2342) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (
# 1669 "FStar.TypeChecker.Tc.fst"
let env = (let _146_882 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _146_882))
in (
# 1671 "FStar.TypeChecker.Tc.fst"
let _57_2345 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _146_885 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _146_884 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _146_883 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checked effect signature: %s %s : %s\n" _146_885 _146_884 _146_883))))
end else begin
()
end
in (
# 1677 "FStar.TypeChecker.Tc.fst"
let check_and_gen' = (fun env _57_2352 k -> (match (_57_2352) with
| (_57_2350, t) -> begin
(check_and_gen env t k)
end))
in (
# 1680 "FStar.TypeChecker.Tc.fst"
let ret = (
# 1681 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_897 = (let _146_895 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_894 = (let _146_893 = (let _146_892 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_892))
in (_146_893)::[])
in (_146_895)::_146_894))
in (let _146_896 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _146_897 _146_896)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (
# 1684 "FStar.TypeChecker.Tc.fst"
let bind_wp = (
# 1685 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1686 "FStar.TypeChecker.Tc.fst"
let _57_2359 = (get_effect_signature ())
in (match (_57_2359) with
| (b, wp_b) -> begin
(
# 1687 "FStar.TypeChecker.Tc.fst"
let a_wp_b = (let _146_901 = (let _146_899 = (let _146_898 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_898))
in (_146_899)::[])
in (let _146_900 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _146_901 _146_900)))
in (
# 1688 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = a_wp_b
in (
# 1689 "FStar.TypeChecker.Tc.fst"
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
# 1695 "FStar.TypeChecker.Tc.fst"
let bind_wlp = (
# 1696 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1697 "FStar.TypeChecker.Tc.fst"
let _57_2367 = (get_effect_signature ())
in (match (_57_2367) with
| (b, wlp_b) -> begin
(
# 1698 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = (let _146_918 = (let _146_916 = (let _146_915 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_915))
in (_146_916)::[])
in (let _146_917 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _146_918 _146_917)))
in (
# 1699 "FStar.TypeChecker.Tc.fst"
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
# 1705 "FStar.TypeChecker.Tc.fst"
let if_then_else = (
# 1706 "FStar.TypeChecker.Tc.fst"
let p = (let _146_929 = (let _146_928 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_928 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _146_929))
in (
# 1707 "FStar.TypeChecker.Tc.fst"
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
# 1713 "FStar.TypeChecker.Tc.fst"
let ite_wp = (
# 1714 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1715 "FStar.TypeChecker.Tc.fst"
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
# 1721 "FStar.TypeChecker.Tc.fst"
let ite_wlp = (
# 1722 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1723 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_950 = (let _146_948 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_947 = (let _146_946 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (_146_946)::[])
in (_146_948)::_146_947))
in (let _146_949 = (FStar_Syntax_Syntax.mk_Total wlp_a)
in (FStar_Syntax_Util.arrow _146_950 _146_949)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wlp expected_k)))
in (
# 1728 "FStar.TypeChecker.Tc.fst"
let wp_binop = (
# 1729 "FStar.TypeChecker.Tc.fst"
let bin_op = (
# 1730 "FStar.TypeChecker.Tc.fst"
let _57_2382 = (FStar_Syntax_Util.type_u ())
in (match (_57_2382) with
| (t1, u1) -> begin
(
# 1731 "FStar.TypeChecker.Tc.fst"
let _57_2385 = (FStar_Syntax_Util.type_u ())
in (match (_57_2385) with
| (t2, u2) -> begin
(
# 1732 "FStar.TypeChecker.Tc.fst"
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
# 1734 "FStar.TypeChecker.Tc.fst"
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
# 1741 "FStar.TypeChecker.Tc.fst"
let wp_as_type = (
# 1742 "FStar.TypeChecker.Tc.fst"
let _57_2393 = (FStar_Syntax_Util.type_u ())
in (match (_57_2393) with
| (t, _57_2392) -> begin
(
# 1743 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_970 = (let _146_968 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_967 = (let _146_966 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_966)::[])
in (_146_968)::_146_967))
in (let _146_969 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _146_970 _146_969)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (
# 1748 "FStar.TypeChecker.Tc.fst"
let close_wp = (
# 1749 "FStar.TypeChecker.Tc.fst"
let b = (let _146_972 = (let _146_971 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_971 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _146_972))
in (
# 1750 "FStar.TypeChecker.Tc.fst"
let b_wp_a = (let _146_976 = (let _146_974 = (let _146_973 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _146_973))
in (_146_974)::[])
in (let _146_975 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_976 _146_975)))
in (
# 1751 "FStar.TypeChecker.Tc.fst"
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
# 1755 "FStar.TypeChecker.Tc.fst"
let assert_p = (
# 1756 "FStar.TypeChecker.Tc.fst"
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
# 1762 "FStar.TypeChecker.Tc.fst"
let assume_p = (
# 1763 "FStar.TypeChecker.Tc.fst"
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
# 1769 "FStar.TypeChecker.Tc.fst"
let null_wp = (
# 1770 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1004 = (let _146_1002 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1002)::[])
in (let _146_1003 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1004 _146_1003)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (
# 1774 "FStar.TypeChecker.Tc.fst"
let trivial_wp = (
# 1775 "FStar.TypeChecker.Tc.fst"
let _57_2409 = (FStar_Syntax_Util.type_u ())
in (match (_57_2409) with
| (t, _57_2408) -> begin
(
# 1776 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1009 = (let _146_1007 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1006 = (let _146_1005 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1005)::[])
in (_146_1007)::_146_1006))
in (let _146_1008 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _146_1009 _146_1008)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (
# 1782 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1010 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _146_1010))
in (
# 1783 "FStar.TypeChecker.Tc.fst"
let _57_2415 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_57_2415) with
| (univs, t) -> begin
(
# 1784 "FStar.TypeChecker.Tc.fst"
let _57_2431 = (match ((let _146_1012 = (let _146_1011 = (FStar_Syntax_Subst.compress t)
in _146_1011.FStar_Syntax_Syntax.n)
in (binders, _146_1012))) with
| ([], _57_2418) -> begin
([], t)
end
| (_57_2421, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _57_2428 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_2431) with
| (binders, signature) -> begin
(
# 1788 "FStar.TypeChecker.Tc.fst"
let close = (fun n ts -> (
# 1789 "FStar.TypeChecker.Tc.fst"
let ts = (let _146_1017 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _146_1017))
in (
# 1790 "FStar.TypeChecker.Tc.fst"
let _57_2436 = ()
in ts)))
in (
# 1792 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1792 "FStar.TypeChecker.Tc.fst"
let _57_2438 = ed
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
in {FStar_Syntax_Syntax.qualifiers = _57_2438.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2438.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _146_1030; FStar_Syntax_Syntax.bind_wp = _146_1029; FStar_Syntax_Syntax.bind_wlp = _146_1028; FStar_Syntax_Syntax.if_then_else = _146_1027; FStar_Syntax_Syntax.ite_wp = _146_1026; FStar_Syntax_Syntax.ite_wlp = _146_1025; FStar_Syntax_Syntax.wp_binop = _146_1024; FStar_Syntax_Syntax.wp_as_type = _146_1023; FStar_Syntax_Syntax.close_wp = _146_1022; FStar_Syntax_Syntax.assert_p = _146_1021; FStar_Syntax_Syntax.assume_p = _146_1020; FStar_Syntax_Syntax.null_wp = _146_1019; FStar_Syntax_Syntax.trivial = _146_1018}))))))))))))))
in (
# 1810 "FStar.TypeChecker.Tc.fst"
let _57_2441 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
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

# 1814 "FStar.TypeChecker.Tc.fst"
let tc_lex_t = (fun env ses quals lids -> (
# 1821 "FStar.TypeChecker.Tc.fst"
let _57_2447 = ()
in (
# 1822 "FStar.TypeChecker.Tc.fst"
let _57_2455 = ()
in (match (ses) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _57_2484, _57_2486, [], r)::FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _57_2475, r1)::FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _57_2464, r2)::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(
# 1837 "FStar.TypeChecker.Tc.fst"
let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (
# 1838 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (
# 1839 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (
# 1840 "FStar.TypeChecker.Tc.fst"
let tc = FStar_Syntax_Syntax.Sig_inductive_typ ((lex_t, (u)::[], [], t, [], (FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[], [], r))
in (
# 1842 "FStar.TypeChecker.Tc.fst"
let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (
# 1843 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (let _146_1039 = (let _146_1038 = (let _146_1037 = (let _146_1036 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _146_1036 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1037, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1038))
in (FStar_Syntax_Syntax.mk _146_1039 None r1))
in (
# 1844 "FStar.TypeChecker.Tc.fst"
let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (
# 1845 "FStar.TypeChecker.Tc.fst"
let dc_lextop = FStar_Syntax_Syntax.Sig_datacon ((lex_top, (utop)::[], lex_top_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r1))
in (
# 1847 "FStar.TypeChecker.Tc.fst"
let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1848 "FStar.TypeChecker.Tc.fst"
let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (
# 1849 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (
# 1850 "FStar.TypeChecker.Tc.fst"
let a = (let _146_1040 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1040))
in (
# 1851 "FStar.TypeChecker.Tc.fst"
let hd = (let _146_1041 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1041))
in (
# 1852 "FStar.TypeChecker.Tc.fst"
let tl = (let _146_1046 = (let _146_1045 = (let _146_1044 = (let _146_1043 = (let _146_1042 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _146_1042 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1043, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1044))
in (FStar_Syntax_Syntax.mk _146_1045 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1046))
in (
# 1853 "FStar.TypeChecker.Tc.fst"
let res = (let _146_1050 = (let _146_1049 = (let _146_1048 = (let _146_1047 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _146_1047 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1048, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1049))
in (FStar_Syntax_Syntax.mk _146_1050 None r2))
in (let _146_1051 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _146_1051))))))
in (
# 1855 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (
# 1856 "FStar.TypeChecker.Tc.fst"
let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _146_1053 = (let _146_1052 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _146_1052))
in FStar_Syntax_Syntax.Sig_bundle (_146_1053)))))))))))))))
end
| _57_2510 -> begin
(let _146_1055 = (let _146_1054 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _146_1054))
in (FStar_All.failwith _146_1055))
end))))

# 1862 "FStar.TypeChecker.Tc.fst"
let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (
# 1925 "FStar.TypeChecker.Tc.fst"
let warn_positivity = (fun l r -> (let _146_1069 = (let _146_1068 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _146_1068))
in (FStar_TypeChecker_Errors.diag r _146_1069)))
in (
# 1927 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1930 "FStar.TypeChecker.Tc.fst"
let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(
# 1935 "FStar.TypeChecker.Tc.fst"
let _57_2532 = ()
in (
# 1936 "FStar.TypeChecker.Tc.fst"
let _57_2534 = (warn_positivity tc r)
in (
# 1937 "FStar.TypeChecker.Tc.fst"
let _57_2538 = (FStar_Syntax_Subst.open_term tps k)
in (match (_57_2538) with
| (tps, k) -> begin
(
# 1938 "FStar.TypeChecker.Tc.fst"
let _57_2542 = (tc_tparams env tps)
in (match (_57_2542) with
| (tps, env_tps, us) -> begin
(
# 1939 "FStar.TypeChecker.Tc.fst"
let _57_2545 = (FStar_Syntax_Util.arrow_formals k)
in (match (_57_2545) with
| (indices, t) -> begin
(
# 1940 "FStar.TypeChecker.Tc.fst"
let _57_2549 = (tc_tparams env_tps indices)
in (match (_57_2549) with
| (indices, env', us') -> begin
(
# 1941 "FStar.TypeChecker.Tc.fst"
let _57_2553 = (tc_trivial_guard env' t)
in (match (_57_2553) with
| (t, _57_2552) -> begin
(
# 1942 "FStar.TypeChecker.Tc.fst"
let k = (let _146_1074 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _146_1074))
in (
# 1943 "FStar.TypeChecker.Tc.fst"
let _57_2557 = (FStar_Syntax_Util.type_u ())
in (match (_57_2557) with
| (t_type, u) -> begin
(
# 1944 "FStar.TypeChecker.Tc.fst"
let _57_2558 = (let _146_1075 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _146_1075))
in (
# 1946 "FStar.TypeChecker.Tc.fst"
let t_tc = (let _146_1076 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _146_1076))
in (
# 1947 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 1948 "FStar.TypeChecker.Tc.fst"
let k = (FStar_Syntax_Subst.close tps k)
in (
# 1949 "FStar.TypeChecker.Tc.fst"
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
| _57_2565 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1956 "FStar.TypeChecker.Tc.fst"
let positive_if_pure = (fun _57_2567 l -> ())
in (
# 1959 "FStar.TypeChecker.Tc.fst"
let tc_data = (fun env tcs _57_6 -> (match (_57_6) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(
# 1961 "FStar.TypeChecker.Tc.fst"
let _57_2584 = ()
in (
# 1963 "FStar.TypeChecker.Tc.fst"
let _57_2619 = (
# 1964 "FStar.TypeChecker.Tc.fst"
let tps_u_opt = (FStar_Util.find_map tcs (fun _57_2588 -> (match (_57_2588) with
| (se, u_tc) -> begin
if (let _146_1090 = (let _146_1089 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _146_1089))
in (FStar_Ident.lid_equals tc_lid _146_1090)) then begin
(
# 1966 "FStar.TypeChecker.Tc.fst"
let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2590, _57_2592, tps, _57_2595, _57_2597, _57_2599, _57_2601, _57_2603) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _57_2609 -> (match (_57_2609) with
| (x, _57_2608) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _57_2611 -> begin
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
in (match (_57_2619) with
| (tps, u_tc) -> begin
(
# 1979 "FStar.TypeChecker.Tc.fst"
let _57_2639 = (match ((let _146_1092 = (FStar_Syntax_Subst.compress t)
in _146_1092.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(
# 1984 "FStar.TypeChecker.Tc.fst"
let _57_2627 = (FStar_Util.first_N ntps bs)
in (match (_57_2627) with
| (_57_2625, bs') -> begin
(
# 1985 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (
# 1986 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _57_2633 -> (match (_57_2633) with
| (x, _57_2632) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _146_1095 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _146_1095))))
end))
end
| _57_2636 -> begin
([], t)
end)
in (match (_57_2639) with
| (arguments, result) -> begin
(
# 1990 "FStar.TypeChecker.Tc.fst"
let _57_2640 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1098 = (FStar_Syntax_Print.lid_to_string c)
in (let _146_1097 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _146_1096 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _146_1098 _146_1097 _146_1096))))
end else begin
()
end
in (
# 1996 "FStar.TypeChecker.Tc.fst"
let _57_2645 = (tc_tparams env arguments)
in (match (_57_2645) with
| (arguments, env', us) -> begin
(
# 1997 "FStar.TypeChecker.Tc.fst"
let _57_2649 = (tc_trivial_guard env' result)
in (match (_57_2649) with
| (result, _57_2648) -> begin
(
# 1998 "FStar.TypeChecker.Tc.fst"
let _57_2653 = (FStar_Syntax_Util.head_and_args result)
in (match (_57_2653) with
| (head, _57_2652) -> begin
(
# 1999 "FStar.TypeChecker.Tc.fst"
let _57_2658 = (match ((let _146_1099 = (FStar_Syntax_Subst.compress head)
in _146_1099.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _57_2657 -> begin
(let _146_1103 = (let _146_1102 = (let _146_1101 = (let _146_1100 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _146_1100))
in (_146_1101, r))
in FStar_Syntax_Syntax.Error (_146_1102))
in (Prims.raise _146_1103))
end)
in (
# 2002 "FStar.TypeChecker.Tc.fst"
let g = (FStar_List.fold_left2 (fun g _57_2664 u_x -> (match (_57_2664) with
| (x, _57_2663) -> begin
(
# 2003 "FStar.TypeChecker.Tc.fst"
let _57_2666 = ()
in (let _146_1107 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _146_1107)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (
# 2009 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1111 = (let _146_1109 = (FStar_All.pipe_right tps (FStar_List.map (fun _57_2672 -> (match (_57_2672) with
| (x, _57_2671) -> begin
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
| _57_2675 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 2017 "FStar.TypeChecker.Tc.fst"
let generalize_and_inst_within = (fun env g tcs datas -> (
# 2018 "FStar.TypeChecker.Tc.fst"
let _57_2681 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2019 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_7 -> (match (_57_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2685, _57_2687, tps, k, _57_2691, _57_2693, _57_2695, _57_2697) -> begin
(let _146_1122 = (let _146_1121 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _146_1121))
in (FStar_Syntax_Syntax.null_binder _146_1122))
end
| _57_2701 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2022 "FStar.TypeChecker.Tc.fst"
let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _57_8 -> (match (_57_8) with
| FStar_Syntax_Syntax.Sig_datacon (_57_2705, _57_2707, t, _57_2710, _57_2712, _57_2714, _57_2716, _57_2718) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _57_2722 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2025 "FStar.TypeChecker.Tc.fst"
let t = (let _146_1124 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _146_1124))
in (
# 2026 "FStar.TypeChecker.Tc.fst"
let _57_2725 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1125 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _146_1125))
end else begin
()
end
in (
# 2027 "FStar.TypeChecker.Tc.fst"
let _57_2729 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_57_2729) with
| (uvs, t) -> begin
(
# 2028 "FStar.TypeChecker.Tc.fst"
let _57_2731 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1129 = (let _146_1127 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _146_1127 (FStar_String.concat ", ")))
in (let _146_1128 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _146_1129 _146_1128)))
end else begin
()
end
in (
# 2031 "FStar.TypeChecker.Tc.fst"
let _57_2735 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_57_2735) with
| (uvs, t) -> begin
(
# 2032 "FStar.TypeChecker.Tc.fst"
let _57_2739 = (FStar_Syntax_Util.arrow_formals t)
in (match (_57_2739) with
| (args, _57_2738) -> begin
(
# 2033 "FStar.TypeChecker.Tc.fst"
let _57_2742 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_57_2742) with
| (tc_types, data_types) -> begin
(
# 2034 "FStar.TypeChecker.Tc.fst"
let tcs = (FStar_List.map2 (fun _57_2746 se -> (match (_57_2746) with
| (x, _57_2745) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_2750, tps, _57_2753, mutuals, datas, quals, r) -> begin
(
# 2036 "FStar.TypeChecker.Tc.fst"
let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (
# 2037 "FStar.TypeChecker.Tc.fst"
let _57_2776 = (match ((let _146_1132 = (FStar_Syntax_Subst.compress ty)
in _146_1132.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 2039 "FStar.TypeChecker.Tc.fst"
let _57_2767 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_57_2767) with
| (tps, rest) -> begin
(
# 2040 "FStar.TypeChecker.Tc.fst"
let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _57_2770 -> begin
(let _146_1133 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _146_1133 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _57_2773 -> begin
([], ty)
end)
in (match (_57_2776) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _57_2778 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (
# 2050 "FStar.TypeChecker.Tc.fst"
let datas = (match (uvs) with
| [] -> begin
datas
end
| _57_2782 -> begin
(
# 2053 "FStar.TypeChecker.Tc.fst"
let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _146_1134 -> FStar_Syntax_Syntax.U_name (_146_1134))))
in (
# 2054 "FStar.TypeChecker.Tc.fst"
let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_9 -> (match (_57_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_2787, _57_2789, _57_2791, _57_2793, _57_2795, _57_2797, _57_2799) -> begin
(tc, uvs_universes)
end
| _57_2803 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _57_2808 d -> (match (_57_2808) with
| (t, _57_2807) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _57_2812, _57_2814, tc, ntps, quals, mutuals, r) -> begin
(
# 2058 "FStar.TypeChecker.Tc.fst"
let ty = (let _146_1138 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _146_1138 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _57_2824 -> begin
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
# 2064 "FStar.TypeChecker.Tc.fst"
let _57_2834 = (FStar_All.pipe_right ses (FStar_List.partition (fun _57_10 -> (match (_57_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2828) -> begin
true
end
| _57_2831 -> begin
false
end))))
in (match (_57_2834) with
| (tys, datas) -> begin
(
# 2066 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2069 "FStar.TypeChecker.Tc.fst"
let _57_2851 = (FStar_List.fold_right (fun tc _57_2840 -> (match (_57_2840) with
| (env, all_tcs, g) -> begin
(
# 2070 "FStar.TypeChecker.Tc.fst"
let _57_2844 = (tc_tycon env tc)
in (match (_57_2844) with
| (env, tc, tc_u) -> begin
(
# 2071 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (
# 2072 "FStar.TypeChecker.Tc.fst"
let _57_2846 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1142 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _146_1142))
end else begin
()
end
in (let _146_1143 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _146_1143))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_2851) with
| (env, tcs, g) -> begin
(
# 2079 "FStar.TypeChecker.Tc.fst"
let _57_2861 = (FStar_List.fold_right (fun se _57_2855 -> (match (_57_2855) with
| (datas, g) -> begin
(
# 2080 "FStar.TypeChecker.Tc.fst"
let _57_2858 = (tc_data env tcs se)
in (match (_57_2858) with
| (data, g') -> begin
(let _146_1146 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _146_1146))
end))
end)) datas ([], g))
in (match (_57_2861) with
| (datas, g) -> begin
(
# 2085 "FStar.TypeChecker.Tc.fst"
let _57_2864 = (let _146_1147 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _146_1147 datas))
in (match (_57_2864) with
| (tcs, datas) -> begin
(let _146_1149 = (let _146_1148 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _146_1148))
in FStar_Syntax_Syntax.Sig_bundle (_146_1149))
end))
end))
end)))
end)))))))))

# 2088 "FStar.TypeChecker.Tc.fst"
let rec tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.env) = (fun env se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(
# 2101 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2102 "FStar.TypeChecker.Tc.fst"
let se = (tc_lex_t env ses quals lids)
in (let _146_1154 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _146_1154))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(
# 2106 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2107 "FStar.TypeChecker.Tc.fst"
let se = (tc_inductive env ses quals lids)
in (let _146_1155 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _146_1155))))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(
# 2111 "FStar.TypeChecker.Tc.fst"
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
# 2117 "FStar.TypeChecker.Tc.fst"
let _57_2902 = (set_options FStar_Options.Set o)
in (se, env))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(
# 2120 "FStar.TypeChecker.Tc.fst"
let _57_2906 = (let _146_1160 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _146_1160 Prims.ignore))
in (
# 2121 "FStar.TypeChecker.Tc.fst"
let _57_2911 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (
# 2124 "FStar.TypeChecker.Tc.fst"
let _57_2913 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (se, env))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(
# 2129 "FStar.TypeChecker.Tc.fst"
let ne = (tc_eff_decl env ne)
in (
# 2130 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (
# 2131 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(
# 2135 "FStar.TypeChecker.Tc.fst"
let _57_2928 = (let _146_1161 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _146_1161))
in (match (_57_2928) with
| (a, wp_a_src) -> begin
(
# 2136 "FStar.TypeChecker.Tc.fst"
let _57_2931 = (let _146_1162 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _146_1162))
in (match (_57_2931) with
| (b, wp_b_tgt) -> begin
(
# 2137 "FStar.TypeChecker.Tc.fst"
let wp_a_tgt = (let _146_1166 = (let _146_1165 = (let _146_1164 = (let _146_1163 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _146_1163))
in FStar_Syntax_Syntax.NT (_146_1164))
in (_146_1165)::[])
in (FStar_Syntax_Subst.subst _146_1166 wp_b_tgt))
in (
# 2138 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _146_1171 = (let _146_1169 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1168 = (let _146_1167 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_146_1167)::[])
in (_146_1169)::_146_1168))
in (let _146_1170 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _146_1171 _146_1170)))
in (
# 2139 "FStar.TypeChecker.Tc.fst"
let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (
# 2140 "FStar.TypeChecker.Tc.fst"
let sub = (
# 2140 "FStar.TypeChecker.Tc.fst"
let _57_2935 = sub
in {FStar_Syntax_Syntax.source = _57_2935.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _57_2935.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
in (
# 2141 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect ((sub, r))
in (
# 2142 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(
# 2146 "FStar.TypeChecker.Tc.fst"
let _57_2948 = ()
in (
# 2147 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2148 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2149 "FStar.TypeChecker.Tc.fst"
let _57_2954 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_57_2954) with
| (tps, c) -> begin
(
# 2150 "FStar.TypeChecker.Tc.fst"
let _57_2958 = (tc_tparams env tps)
in (match (_57_2958) with
| (tps, env, us) -> begin
(
# 2151 "FStar.TypeChecker.Tc.fst"
let _57_2962 = (tc_comp env c)
in (match (_57_2962) with
| (c, u, g) -> begin
(
# 2152 "FStar.TypeChecker.Tc.fst"
let _57_2963 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2153 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 2154 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.close_comp tps c)
in (
# 2155 "FStar.TypeChecker.Tc.fst"
let _57_2969 = (let _146_1172 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _146_1172))
in (match (_57_2969) with
| (uvs, t) -> begin
(
# 2156 "FStar.TypeChecker.Tc.fst"
let _57_2988 = (match ((let _146_1174 = (let _146_1173 = (FStar_Syntax_Subst.compress t)
in _146_1173.FStar_Syntax_Syntax.n)
in (tps, _146_1174))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_57_2972, c)) -> begin
([], c)
end
| (_57_2978, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _57_2985 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_2988) with
| (tps, c) -> begin
(
# 2160 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_effect_abbrev ((lid, uvs, tps, c, tags, r))
in (
# 2161 "FStar.TypeChecker.Tc.fst"
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
# 2165 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2166 "FStar.TypeChecker.Tc.fst"
let _57_2999 = ()
in (
# 2167 "FStar.TypeChecker.Tc.fst"
let _57_3003 = (let _146_1176 = (let _146_1175 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _146_1175))
in (check_and_gen env t _146_1176))
in (match (_57_3003) with
| (uvs, t) -> begin
(
# 2168 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (
# 2169 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(
# 2173 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2174 "FStar.TypeChecker.Tc.fst"
let _57_3016 = (FStar_Syntax_Util.type_u ())
in (match (_57_3016) with
| (k, _57_3015) -> begin
(
# 2175 "FStar.TypeChecker.Tc.fst"
let phi = (let _146_1177 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _146_1177 (norm env)))
in (
# 2176 "FStar.TypeChecker.Tc.fst"
let _57_3018 = (FStar_TypeChecker_Util.check_uvars r phi)
in (
# 2177 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))
in (
# 2178 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(
# 2182 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2183 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (
# 2184 "FStar.TypeChecker.Tc.fst"
let _57_3031 = (tc_term env e)
in (match (_57_3031) with
| (e, c, g1) -> begin
(
# 2185 "FStar.TypeChecker.Tc.fst"
let _57_3036 = (let _146_1181 = (let _146_1178 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_146_1178))
in (let _146_1180 = (let _146_1179 = (c.FStar_Syntax_Syntax.comp ())
in (e, _146_1179))
in (check_expected_effect env _146_1181 _146_1180)))
in (match (_57_3036) with
| (e, _57_3034, g) -> begin
(
# 2186 "FStar.TypeChecker.Tc.fst"
let _57_3037 = (let _146_1182 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _146_1182))
in (
# 2187 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, r))
in (
# 2188 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(
# 2192 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2193 "FStar.TypeChecker.Tc.fst"
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
# 2207 "FStar.TypeChecker.Tc.fst"
let _57_3081 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _57_3058 lb -> (match (_57_3058) with
| (gen, lbs, quals_opt) -> begin
(
# 2208 "FStar.TypeChecker.Tc.fst"
let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2209 "FStar.TypeChecker.Tc.fst"
let _57_3077 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(
# 2213 "FStar.TypeChecker.Tc.fst"
let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (
# 2214 "FStar.TypeChecker.Tc.fst"
let _57_3072 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _57_3071 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _146_1197 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _146_1197, quals_opt))))
end)
in (match (_57_3077) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_57_3081) with
| (should_generalize, lbs', quals_opt) -> begin
(
# 2223 "FStar.TypeChecker.Tc.fst"
let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _57_11 -> (match (_57_11) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _57_3090 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (
# 2230 "FStar.TypeChecker.Tc.fst"
let lbs' = (FStar_List.rev lbs')
in (
# 2233 "FStar.TypeChecker.Tc.fst"
let e = (let _146_1201 = (let _146_1200 = (let _146_1199 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _146_1199))
in FStar_Syntax_Syntax.Tm_let (_146_1200))
in (FStar_Syntax_Syntax.mk _146_1201 None r))
in (
# 2236 "FStar.TypeChecker.Tc.fst"
let _57_3124 = (match ((tc_maybe_toplevel_term (
# 2236 "FStar.TypeChecker.Tc.fst"
let _57_3094 = env
in {FStar_TypeChecker_Env.solver = _57_3094.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3094.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3094.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3094.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3094.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3094.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3094.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3094.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3094.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3094.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3094.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _57_3094.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _57_3094.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3094.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3094.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3094.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3094.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3094.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3094.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _57_3101; FStar_Syntax_Syntax.pos = _57_3099; FStar_Syntax_Syntax.vars = _57_3097}, _57_3108, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(
# 2239 "FStar.TypeChecker.Tc.fst"
let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_57_3112, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _57_3118 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _57_3121 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_57_3124) with
| (se, lbs) -> begin
(
# 2246 "FStar.TypeChecker.Tc.fst"
let _57_3130 = if (log env) then begin
(let _146_1209 = (let _146_1208 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 2248 "FStar.TypeChecker.Tc.fst"
let should_log = (match ((let _146_1205 = (let _146_1204 = (let _146_1203 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _146_1203.FStar_Syntax_Syntax.fv_name)
in _146_1204.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _146_1205))) with
| None -> begin
true
end
| _57_3128 -> begin
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
# 2255 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end))))
end))

# 2259 "FStar.TypeChecker.Tc.fst"
let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (
# 2283 "FStar.TypeChecker.Tc.fst"
let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _57_12 -> (match (_57_12) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _57_3140 -> begin
false
end)))))
in (
# 2284 "FStar.TypeChecker.Tc.fst"
let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _57_3150 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_57_3152) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _57_3163, _57_3165) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _57_3171 -> (match (_57_3171) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _57_3177, _57_3179, quals, r) -> begin
(
# 2298 "FStar.TypeChecker.Tc.fst"
let dec = (let _146_1225 = (let _146_1224 = (let _146_1223 = (let _146_1222 = (let _146_1221 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _146_1221))
in FStar_Syntax_Syntax.Tm_arrow (_146_1222))
in (FStar_Syntax_Syntax.mk _146_1223 None r))
in (l, us, _146_1224, (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_146_1225))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _57_3189, _57_3191, _57_3193, _57_3195, r) -> begin
(
# 2301 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _57_3201 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_57_3203, _57_3205, quals, _57_3208) -> begin
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
| _57_3227 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_57_3229) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _57_3245, _57_3247, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(
# 2331 "FStar.TypeChecker.Tc.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2332 "FStar.TypeChecker.Tc.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))) then begin
([], hidden)
end else begin
(
# 2335 "FStar.TypeChecker.Tc.fst"
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

# 2344 "FStar.TypeChecker.Tc.fst"
let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (
# 2345 "FStar.TypeChecker.Tc.fst"
let _57_3286 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _57_3267 se -> (match (_57_3267) with
| (ses, exports, env, hidden) -> begin
(
# 2347 "FStar.TypeChecker.Tc.fst"
let _57_3269 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1239 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _146_1239))
end else begin
()
end
in (
# 2350 "FStar.TypeChecker.Tc.fst"
let _57_3273 = (tc_decl env se)
in (match (_57_3273) with
| (se, env) -> begin
(
# 2352 "FStar.TypeChecker.Tc.fst"
let _57_3274 = if ((FStar_ST.read FStar_Options.log_types) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _146_1240 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _146_1240))
end else begin
()
end
in (
# 2355 "FStar.TypeChecker.Tc.fst"
let _57_3276 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (
# 2357 "FStar.TypeChecker.Tc.fst"
let _57_3280 = (for_export hidden se)
in (match (_57_3280) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_57_3286) with
| (ses, exports, env, _57_3285) -> begin
(let _146_1241 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _146_1241, env))
end)))

# 2362 "FStar.TypeChecker.Tc.fst"
let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2363 "FStar.TypeChecker.Tc.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 2364 "FStar.TypeChecker.Tc.fst"
let msg = (Prims.strcat "Internals for " name)
in (
# 2365 "FStar.TypeChecker.Tc.fst"
let env = (
# 2365 "FStar.TypeChecker.Tc.fst"
let _57_3291 = env
in (let _146_1246 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _57_3291.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3291.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3291.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3291.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3291.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3291.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3291.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3291.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3291.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3291.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3291.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3291.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3291.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_3291.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_3291.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3291.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _146_1246; FStar_TypeChecker_Env.type_of = _57_3291.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3291.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3291.FStar_TypeChecker_Env.use_bv_sorts}))
in (
# 2366 "FStar.TypeChecker.Tc.fst"
let _57_3294 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (
# 2367 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (
# 2368 "FStar.TypeChecker.Tc.fst"
let _57_3300 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_57_3300) with
| (ses, exports, env) -> begin
((
# 2369 "FStar.TypeChecker.Tc.fst"
let _57_3301 = modul
in {FStar_Syntax_Syntax.name = _57_3301.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _57_3301.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3301.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))

# 2371 "FStar.TypeChecker.Tc.fst"
let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (
# 2372 "FStar.TypeChecker.Tc.fst"
let _57_3309 = (tc_decls env decls)
in (match (_57_3309) with
| (ses, exports, env) -> begin
(
# 2373 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2373 "FStar.TypeChecker.Tc.fst"
let _57_3310 = modul
in {FStar_Syntax_Syntax.name = _57_3310.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _57_3310.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3310.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))

# 2376 "FStar.TypeChecker.Tc.fst"
let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (
# 2377 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2377 "FStar.TypeChecker.Tc.fst"
let _57_3316 = modul
in {FStar_Syntax_Syntax.name = _57_3316.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _57_3316.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (
# 2378 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.finish_module env modul)
in (
# 2379 "FStar.TypeChecker.Tc.fst"
let _57_3326 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(
# 2381 "FStar.TypeChecker.Tc.fst"
let _57_3320 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (
# 2382 "FStar.TypeChecker.Tc.fst"
let _57_3322 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (
# 2383 "FStar.TypeChecker.Tc.fst"
let _57_3324 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _146_1259 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _146_1259 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))

# 2388 "FStar.TypeChecker.Tc.fst"
let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2389 "FStar.TypeChecker.Tc.fst"
let _57_3333 = (tc_partial_modul env modul)
in (match (_57_3333) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

# 2392 "FStar.TypeChecker.Tc.fst"
let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 2393 "FStar.TypeChecker.Tc.fst"
let _57_3336 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _146_1268 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _146_1268))
end else begin
()
end
in (
# 2395 "FStar.TypeChecker.Tc.fst"
let env = (
# 2395 "FStar.TypeChecker.Tc.fst"
let _57_3338 = env
in {FStar_TypeChecker_Env.solver = _57_3338.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3338.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3338.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3338.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3338.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3338.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3338.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3338.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3338.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3338.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3338.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3338.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3338.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_3338.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3338.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3338.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3338.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3338.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3338.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3338.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 2396 "FStar.TypeChecker.Tc.fst"
let _57_3354 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _57_3346) -> begin
(let _146_1273 = (let _146_1272 = (let _146_1271 = (FStar_TypeChecker_Env.get_range env)
in ((Prims.strcat "Implicit argument: " msg), _146_1271))
in FStar_Syntax_Syntax.Error (_146_1272))
in (Prims.raise _146_1273))
end
in (match (_57_3354) with
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

# 2403 "FStar.TypeChecker.Tc.fst"
let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (
# 2404 "FStar.TypeChecker.Tc.fst"
let _57_3357 = if ((let _146_1283 = (FStar_ST.read FStar_Options.debug)
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
# 2406 "FStar.TypeChecker.Tc.fst"
let _57_3361 = (tc_modul env m)
in (match (_57_3361) with
| (m, env) -> begin
(
# 2407 "FStar.TypeChecker.Tc.fst"
let _57_3362 = if (FStar_Options.should_dump m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _146_1285 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _146_1285))
end else begin
()
end
in (m, env))
end))))




