
open Prims
# 42 "FStar.TypeChecker.Tc.fst"
let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_ST.read FStar_Options.log_types) && (not ((let _157_3 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _157_3))))))

# 43 "FStar.TypeChecker.Tc.fst"
let rng : FStar_TypeChecker_Env.env  ->  FStar_Range.range = (fun env -> (FStar_TypeChecker_Env.get_range env))

# 44 "FStar.TypeChecker.Tc.fst"
let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (
# 44 "FStar.TypeChecker.Tc.fst"
let _68_17 = env
in {FStar_TypeChecker_Env.solver = _68_17.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_17.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_17.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_17.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_17.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_17.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_17.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_17.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_17.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _68_17.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_17.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_17.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _68_17.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _68_17.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_17.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_17.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_17.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _68_17.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_17.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_17.FStar_TypeChecker_Env.use_bv_sorts}))

# 45 "FStar.TypeChecker.Tc.fst"
let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (
# 45 "FStar.TypeChecker.Tc.fst"
let _68_20 = env
in {FStar_TypeChecker_Env.solver = _68_20.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_20.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_20.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_20.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_20.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_20.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_20.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_20.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_20.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _68_20.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_20.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_20.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _68_20.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _68_20.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_20.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_20.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_20.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _68_20.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_20.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_20.FStar_TypeChecker_Env.use_bv_sorts}))

# 46 "FStar.TypeChecker.Tc.fst"
let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (
# 48 "FStar.TypeChecker.Tc.fst"
let r = if (tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
v.FStar_Syntax_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos tl.FStar_Syntax_Syntax.pos)
end
in (let _157_17 = (let _157_16 = (FStar_Syntax_Syntax.as_arg v)
in (let _157_15 = (let _157_14 = (FStar_Syntax_Syntax.as_arg tl)
in (_157_14)::[])
in (_157_16)::_157_15))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _157_17 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))

# 51 "FStar.TypeChecker.Tc.fst"
let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _68_1 -> (match (_68_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _68_30 -> begin
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
let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _157_30 = (steps env)
in (FStar_TypeChecker_Normalize.normalize _157_30 env t)))

# 60 "FStar.TypeChecker.Tc.fst"
let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _157_35 = (steps env)
in (FStar_TypeChecker_Normalize.normalize_comp _157_35 env c)))

# 61 "FStar.TypeChecker.Tc.fst"
let check_no_escape : FStar_Syntax_Syntax.term Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun head_opt env fvs kt -> (
# 62 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
()
end
| _68_47 -> begin
(
# 65 "FStar.TypeChecker.Tc.fst"
let fvs' = (let _157_48 = if try_norm then begin
(norm env t)
end else begin
t
end
in (FStar_Syntax_Free.names _157_48))
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
let fail = (fun _68_54 -> (match (()) with
| () -> begin
(
# 72 "FStar.TypeChecker.Tc.fst"
let msg = (match (head_opt) with
| None -> begin
(let _157_52 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _157_52))
end
| Some (head) -> begin
(let _157_54 = (FStar_Syntax_Print.bv_to_string x)
in (let _157_53 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _157_54 _157_53)))
end)
in (let _157_57 = (let _157_56 = (let _157_55 = (FStar_TypeChecker_Env.get_range env)
in (msg, _157_55))
in FStar_Syntax_Syntax.Error (_157_56))
in (Prims.raise _157_57)))
end))
in (
# 77 "FStar.TypeChecker.Tc.fst"
let s = (let _157_59 = (let _157_58 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _157_58))
in (FStar_TypeChecker_Util.new_uvar env _157_59))
in (match ((FStar_TypeChecker_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g)
end
| _68_63 -> begin
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
let _68_66 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_65 = (FStar_Syntax_Print.bv_to_string (Prims.fst b))
in (let _157_64 = (FStar_Syntax_Print.term_to_string (Prims.fst b).FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _157_65 _157_64)))
end else begin
()
end
in (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))
end)

# 90 "FStar.TypeChecker.Tc.fst"
let maybe_make_subst = (fun _68_2 -> (match (_68_2) with
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Syntax_Syntax.NT ((x, e)))::[]
end
| _68_75 -> begin
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
let _68_81 = lc
in {FStar_Syntax_Syntax.eff_name = _68_81.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _68_81.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _68_83 -> (match (()) with
| () -> begin
(let _157_78 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _157_78 t))
end))}))

# 101 "FStar.TypeChecker.Tc.fst"
let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (
# 102 "FStar.TypeChecker.Tc.fst"
let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _157_87 = if (not ((FStar_Syntax_Util.is_pure_or_ghost_function t))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _157_87))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (
# 107 "FStar.TypeChecker.Tc.fst"
let t = lc.FStar_Syntax_Syntax.res_typ
in (
# 108 "FStar.TypeChecker.Tc.fst"
let _68_115 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, guard)
end
| Some (t') -> begin
(
# 111 "FStar.TypeChecker.Tc.fst"
let _68_97 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_89 = (FStar_Syntax_Print.term_to_string t)
in (let _157_88 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _157_89 _157_88)))
end else begin
()
end
in (
# 113 "FStar.TypeChecker.Tc.fst"
let _68_101 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_68_101) with
| (e, lc) -> begin
(
# 114 "FStar.TypeChecker.Tc.fst"
let t = lc.FStar_Syntax_Syntax.res_typ
in (
# 115 "FStar.TypeChecker.Tc.fst"
let _68_105 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_68_105) with
| (e, g) -> begin
(
# 116 "FStar.TypeChecker.Tc.fst"
let _68_106 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_91 = (FStar_Syntax_Print.term_to_string t)
in (let _157_90 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _157_91 _157_90)))
end else begin
()
end
in (
# 118 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (
# 119 "FStar.TypeChecker.Tc.fst"
let _68_111 = (let _157_97 = (FStar_All.pipe_left (fun _157_96 -> Some (_157_96)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _157_97 env e lc g))
in (match (_68_111) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))))
end)))
end)))
end)
in (match (_68_115) with
| (e, lc, g) -> begin
(
# 121 "FStar.TypeChecker.Tc.fst"
let _68_116 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_98 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _157_98))
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
let _68_126 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_68_126) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))

# 132 "FStar.TypeChecker.Tc.fst"
let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _68_131 -> (match (_68_131) with
| (e, c) -> begin
(
# 133 "FStar.TypeChecker.Tc.fst"
let expected_c_opt = (match (copt) with
| Some (_68_133) -> begin
copt
end
| None -> begin
if ((FStar_ST.read FStar_Options.ml_ish) && (FStar_Ident.lid_equals FStar_Syntax_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) then begin
(let _157_111 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (_157_111))
end else begin
if (env.FStar_TypeChecker_Env.top_level || (FStar_Syntax_Util.is_tot_or_gtot_comp c)) then begin
None
end else begin
if (FStar_Syntax_Util.is_pure_comp c) then begin
(let _157_112 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (_157_112))
end else begin
if (FStar_Syntax_Util.is_pure_or_ghost_comp c) then begin
(let _157_113 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (_157_113))
end else begin
None
end
end
end
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _157_114 = (norm_c env c)
in (e, _157_114, FStar_TypeChecker_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(
# 149 "FStar.TypeChecker.Tc.fst"
let _68_140 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_117 = (FStar_Syntax_Print.term_to_string e)
in (let _157_116 = (FStar_Syntax_Print.comp_to_string c)
in (let _157_115 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _157_117 _157_116 _157_115))))
end else begin
()
end
in (
# 152 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 153 "FStar.TypeChecker.Tc.fst"
let _68_143 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_120 = (FStar_Syntax_Print.term_to_string e)
in (let _157_119 = (FStar_Syntax_Print.comp_to_string c)
in (let _157_118 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _157_120 _157_119 _157_118))))
end else begin
()
end
in (
# 158 "FStar.TypeChecker.Tc.fst"
let _68_149 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_68_149) with
| (e, _68_147, g) -> begin
(
# 159 "FStar.TypeChecker.Tc.fst"
let g = (let _157_121 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _157_121 "could not prove post-condition" g))
in (
# 160 "FStar.TypeChecker.Tc.fst"
let _68_151 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_123 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _157_122 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _157_123 _157_122)))
end else begin
()
end
in (e, expected_c, g)))
end)))))
end))
end))

# 163 "FStar.TypeChecker.Tc.fst"
let no_logical_guard = (fun env _68_157 -> (match (_68_157) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
(te, kt, f)
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _157_129 = (let _157_128 = (let _157_127 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _157_126 = (FStar_TypeChecker_Env.get_range env)
in (_157_127, _157_126)))
in FStar_Syntax_Syntax.Error (_157_128))
in (Prims.raise _157_129))
end)
end))

# 168 "FStar.TypeChecker.Tc.fst"
let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _157_132 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _157_132))
end))

# 175 "FStar.TypeChecker.Tc.fst"
let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _68_181; FStar_Syntax_Syntax.result_typ = _68_179; FStar_Syntax_Syntax.effect_args = _pre::_post::(pats, _68_173)::[]; FStar_Syntax_Syntax.flags = _68_170}) -> begin
(
# 179 "FStar.TypeChecker.Tc.fst"
let pat_vars = (FStar_Syntax_Free.names pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _68_188 -> (match (_68_188) with
| (b, _68_187) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _68_192) -> begin
(let _157_139 = (let _157_138 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _157_138))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _157_139))
end))
end
| _68_196 -> begin
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
let _68_203 = env
in {FStar_TypeChecker_Env.solver = _68_203.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_203.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_203.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_203.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_203.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_203.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_203.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_203.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_203.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_203.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_203.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_203.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _68_203.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _68_203.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_203.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_203.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_203.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _68_203.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_203.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_203.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 196 "FStar.TypeChecker.Tc.fst"
let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (
# 198 "FStar.TypeChecker.Tc.fst"
let decreases_clause = (fun bs c -> (
# 200 "FStar.TypeChecker.Tc.fst"
let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _68_215 -> (match (_68_215) with
| (b, _68_214) -> begin
(
# 202 "FStar.TypeChecker.Tc.fst"
let t = (let _157_153 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _157_153))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _68_224 -> begin
(let _157_154 = (FStar_Syntax_Syntax.bv_to_name b)
in (_157_154)::[])
end))
end)))))
in (
# 207 "FStar.TypeChecker.Tc.fst"
let as_lex_list = (fun dec -> (
# 208 "FStar.TypeChecker.Tc.fst"
let _68_230 = (FStar_Syntax_Util.head_and_args dec)
in (match (_68_230) with
| (head, _68_229) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _68_234 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (
# 212 "FStar.TypeChecker.Tc.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _68_3 -> (match (_68_3) with
| FStar_Syntax_Syntax.DECREASES (_68_238) -> begin
true
end
| _68_241 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _68_246 -> begin
(
# 216 "FStar.TypeChecker.Tc.fst"
let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| x::[] -> begin
x
end
| _68_251 -> begin
(mk_lex_list xs)
end))
end)))))
in (
# 221 "FStar.TypeChecker.Tc.fst"
let previous_dec = (decreases_clause actuals expected_c)
in (
# 222 "FStar.TypeChecker.Tc.fst"
let guard_one_letrec = (fun _68_256 -> (match (_68_256) with
| (l, t) -> begin
(match ((let _157_160 = (FStar_Syntax_Subst.compress t)
in _157_160.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 226 "FStar.TypeChecker.Tc.fst"
let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _68_263 -> (match (_68_263) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _157_164 = (let _157_163 = (let _157_162 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_157_162))
in (FStar_Syntax_Syntax.new_bv _157_163 x.FStar_Syntax_Syntax.sort))
in (_157_164, imp))
end else begin
(x, imp)
end
end))))
in (
# 227 "FStar.TypeChecker.Tc.fst"
let _68_267 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_68_267) with
| (formals, c) -> begin
(
# 228 "FStar.TypeChecker.Tc.fst"
let dec = (decreases_clause formals c)
in (
# 229 "FStar.TypeChecker.Tc.fst"
let precedes = (let _157_168 = (let _157_167 = (FStar_Syntax_Syntax.as_arg dec)
in (let _157_166 = (let _157_165 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_157_165)::[])
in (_157_167)::_157_166))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _157_168 None r))
in (
# 230 "FStar.TypeChecker.Tc.fst"
let _68_274 = (FStar_Util.prefix formals)
in (match (_68_274) with
| (bs, (last, imp)) -> begin
(
# 231 "FStar.TypeChecker.Tc.fst"
let last = (
# 231 "FStar.TypeChecker.Tc.fst"
let _68_275 = last
in (let _157_169 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _68_275.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_275.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _157_169}))
in (
# 232 "FStar.TypeChecker.Tc.fst"
let refined_formals = (FStar_List.append bs (((last, imp))::[]))
in (
# 233 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (
# 234 "FStar.TypeChecker.Tc.fst"
let _68_280 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_172 = (FStar_Syntax_Print.lbname_to_string l)
in (let _157_171 = (FStar_Syntax_Print.term_to_string t)
in (let _157_170 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _157_172 _157_171 _157_170))))
end else begin
()
end
in (l, t')))))
end))))
end)))
end
| _68_283 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end))

# 246 "FStar.TypeChecker.Tc.fst"
let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (
# 246 "FStar.TypeChecker.Tc.fst"
let _68_286 = env
in {FStar_TypeChecker_Env.solver = _68_286.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_286.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_286.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_286.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_286.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_286.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_286.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_286.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_286.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_286.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_286.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_286.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_286.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _68_286.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_286.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_286.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_286.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _68_286.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_286.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_286.FStar_TypeChecker_Env.use_bv_sorts}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 251 "FStar.TypeChecker.Tc.fst"
let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (
# 252 "FStar.TypeChecker.Tc.fst"
let _68_291 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_241 = (let _157_239 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _157_239))
in (let _157_240 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _157_241 _157_240)))
end else begin
()
end
in (
# 253 "FStar.TypeChecker.Tc.fst"
let top = e
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_68_295) -> begin
(let _157_245 = (FStar_Syntax_Subst.compress e)
in (tc_term env _157_245))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(
# 270 "FStar.TypeChecker.Tc.fst"
let _68_336 = (tc_tot_or_gtot_term env e)
in (match (_68_336) with
| (e, c, g) -> begin
(
# 271 "FStar.TypeChecker.Tc.fst"
let g = (
# 271 "FStar.TypeChecker.Tc.fst"
let _68_337 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _68_337.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_337.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_337.FStar_TypeChecker_Env.implicits})
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(
# 275 "FStar.TypeChecker.Tc.fst"
let _68_347 = (FStar_Syntax_Util.type_u ())
in (match (_68_347) with
| (t, u) -> begin
(
# 276 "FStar.TypeChecker.Tc.fst"
let _68_351 = (tc_check_tot_or_gtot_term env e t)
in (match (_68_351) with
| (e, c, g) -> begin
(
# 277 "FStar.TypeChecker.Tc.fst"
let _68_358 = (
# 278 "FStar.TypeChecker.Tc.fst"
let _68_355 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_68_355) with
| (env, _68_354) -> begin
(tc_pats env pats)
end))
in (match (_68_358) with
| (pats, g') -> begin
(
# 280 "FStar.TypeChecker.Tc.fst"
let g' = (
# 280 "FStar.TypeChecker.Tc.fst"
let _68_359 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _68_359.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_359.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_359.FStar_TypeChecker_Env.implicits})
in (let _157_247 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_pattern (pats)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _157_246 = (FStar_TypeChecker_Rel.conj_guard g g')
in (_157_247, c, _157_246))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _157_248 = (FStar_Syntax_Subst.compress e)
in _157_248.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_68_368, {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _68_375; FStar_Syntax_Syntax.lbtyp = _68_373; FStar_Syntax_Syntax.lbeff = _68_371; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 288 "FStar.TypeChecker.Tc.fst"
let _68_386 = (let _157_249 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _157_249 e1))
in (match (_68_386) with
| (e1, c1, g1) -> begin
(
# 289 "FStar.TypeChecker.Tc.fst"
let _68_390 = (tc_term env e2)
in (match (_68_390) with
| (e2, c2, g2) -> begin
(
# 290 "FStar.TypeChecker.Tc.fst"
let c = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (None, c2))
in (
# 291 "FStar.TypeChecker.Tc.fst"
let e = (let _157_254 = (let _157_253 = (let _157_252 = (let _157_251 = (let _157_250 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Common.t_unit, e1))
in (_157_250)::[])
in (false, _157_251))
in (_157_252, e2))
in FStar_Syntax_Syntax.Tm_let (_157_253))
in (FStar_Syntax_Syntax.mk _157_254 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 292 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _157_255 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _157_255)))))
end))
end))
end
| _68_395 -> begin
(
# 295 "FStar.TypeChecker.Tc.fst"
let _68_399 = (tc_term env e)
in (match (_68_399) with
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
let _68_408 = (tc_term env e)
in (match (_68_408) with
| (e, c, g) -> begin
(
# 302 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, m))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _68_414) -> begin
(
# 306 "FStar.TypeChecker.Tc.fst"
let _68_421 = (tc_comp env expected_c)
in (match (_68_421) with
| (expected_c, _68_419, g) -> begin
(
# 307 "FStar.TypeChecker.Tc.fst"
let _68_425 = (tc_term env e)
in (match (_68_425) with
| (e, c', g') -> begin
(
# 308 "FStar.TypeChecker.Tc.fst"
let _68_429 = (let _157_257 = (let _157_256 = (c'.FStar_Syntax_Syntax.comp ())
in (e, _157_256))
in (check_expected_effect env (Some (expected_c)) _157_257))
in (match (_68_429) with
| (e, expected_c, g'') -> begin
(
# 309 "FStar.TypeChecker.Tc.fst"
let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (let _157_260 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t_res), Some ((FStar_Syntax_Util.comp_effect_name expected_c))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _157_259 = (let _157_258 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _157_258))
in (_157_260, (FStar_Syntax_Util.lcomp_of_comp expected_c), _157_259))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _68_435) -> begin
(
# 315 "FStar.TypeChecker.Tc.fst"
let _68_440 = (FStar_Syntax_Util.type_u ())
in (match (_68_440) with
| (k, u) -> begin
(
# 316 "FStar.TypeChecker.Tc.fst"
let _68_445 = (tc_check_tot_or_gtot_term env t k)
in (match (_68_445) with
| (t, _68_443, f) -> begin
(
# 317 "FStar.TypeChecker.Tc.fst"
let _68_449 = (let _157_261 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _157_261 e))
in (match (_68_449) with
| (e, c, g) -> begin
(
# 318 "FStar.TypeChecker.Tc.fst"
let _68_453 = (let _157_265 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _68_450 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _157_265 e c f))
in (match (_68_453) with
| (c, f) -> begin
(
# 319 "FStar.TypeChecker.Tc.fst"
let _68_457 = (let _157_266 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t), Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _157_266 c))
in (match (_68_457) with
| (e, c, f2) -> begin
(let _157_268 = (let _157_267 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _157_267))
in (e, c, _157_268))
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
let env = (let _157_270 = (let _157_269 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _157_269 Prims.fst))
in (FStar_All.pipe_right _157_270 instantiate_both))
in (
# 325 "FStar.TypeChecker.Tc.fst"
let _68_464 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_272 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _157_271 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _157_272 _157_271)))
end else begin
()
end
in (
# 329 "FStar.TypeChecker.Tc.fst"
let _68_469 = (tc_term (no_inst env) head)
in (match (_68_469) with
| (head, chead, g_head) -> begin
(
# 330 "FStar.TypeChecker.Tc.fst"
let _68_473 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _157_273 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _157_273))
end else begin
(let _157_274 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _157_274))
end
in (match (_68_473) with
| (e, c, g) -> begin
(
# 333 "FStar.TypeChecker.Tc.fst"
let _68_474 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _157_275 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _157_275))
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
let _68_481 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_281 = (FStar_Syntax_Print.term_to_string e)
in (let _157_280 = (let _157_276 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _157_276))
in (let _157_279 = (let _157_278 = (FStar_TypeChecker_Env.expected_typ env0)
in (FStar_All.pipe_right _157_278 (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end))))
in (FStar_Util.print3 "(%s) About to check %s against expected typ %s\n" _157_281 _157_280 _157_279))))
end else begin
()
end
in (
# 345 "FStar.TypeChecker.Tc.fst"
let _68_486 = (comp_check_expected_typ env0 e c)
in (match (_68_486) with
| (e, c, g') -> begin
(
# 346 "FStar.TypeChecker.Tc.fst"
let _68_487 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_284 = (FStar_Syntax_Print.term_to_string e)
in (let _157_283 = (let _157_282 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _157_282))
in (FStar_Util.print2 "(%s) checked ... got %s\n" _157_284 _157_283)))
end else begin
()
end
in (
# 350 "FStar.TypeChecker.Tc.fst"
let gimp = (match ((let _157_285 = (FStar_Syntax_Subst.compress head)
in _157_285.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _68_491) -> begin
(
# 353 "FStar.TypeChecker.Tc.fst"
let imp = ("head of application is a uvar", env0, u, e, c.FStar_Syntax_Syntax.res_typ, head.FStar_Syntax_Syntax.pos)
in (
# 354 "FStar.TypeChecker.Tc.fst"
let _68_495 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _68_495.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _68_495.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_495.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _68_498 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (
# 356 "FStar.TypeChecker.Tc.fst"
let gres = (let _157_286 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _157_286))
in (
# 357 "FStar.TypeChecker.Tc.fst"
let _68_501 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _157_287 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print1 "Guard from application node is %s\n" _157_287))
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
let _68_509 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_68_509) with
| (env1, topt) -> begin
(
# 363 "FStar.TypeChecker.Tc.fst"
let env1 = (instantiate_both env1)
in (
# 364 "FStar.TypeChecker.Tc.fst"
let _68_514 = (tc_term env1 e1)
in (match (_68_514) with
| (e1, c1, g1) -> begin
(
# 365 "FStar.TypeChecker.Tc.fst"
let _68_525 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(
# 368 "FStar.TypeChecker.Tc.fst"
let _68_521 = (FStar_Syntax_Util.type_u ())
in (match (_68_521) with
| (k, _68_520) -> begin
(
# 369 "FStar.TypeChecker.Tc.fst"
let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _157_288 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_157_288, res_t)))
end))
end)
in (match (_68_525) with
| (env_branches, res_t) -> begin
(
# 372 "FStar.TypeChecker.Tc.fst"
let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (
# 373 "FStar.TypeChecker.Tc.fst"
let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (
# 374 "FStar.TypeChecker.Tc.fst"
let _68_542 = (
# 375 "FStar.TypeChecker.Tc.fst"
let _68_539 = (FStar_List.fold_right (fun _68_533 _68_536 -> (match ((_68_533, _68_536)) with
| ((_68_529, f, c, g), (caccum, gaccum)) -> begin
(let _157_291 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _157_291))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_68_539) with
| (cases, g) -> begin
(let _157_292 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_157_292, g))
end))
in (match (_68_542) with
| (c_branches, g_branches) -> begin
(
# 379 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (guard_x), c_branches))
in (
# 380 "FStar.TypeChecker.Tc.fst"
let e = (let _157_296 = (let _157_295 = (let _157_294 = (FStar_List.map (fun _68_551 -> (match (_68_551) with
| (f, _68_546, _68_548, _68_550) -> begin
f
end)) t_eqns)
in (e1, _157_294))
in FStar_Syntax_Syntax.Tm_match (_157_295))
in (FStar_Syntax_Syntax.mk _157_296 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (
# 382 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ), Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (
# 383 "FStar.TypeChecker.Tc.fst"
let _68_554 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _157_299 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _157_298 = (let _157_297 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _157_297))
in (FStar_Util.print2 "(%s) comp type = %s\n" _157_299 _157_298)))
end else begin
()
end
in (let _157_300 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _157_300))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_68_566); FStar_Syntax_Syntax.lbunivs = _68_564; FStar_Syntax_Syntax.lbtyp = _68_562; FStar_Syntax_Syntax.lbeff = _68_560; FStar_Syntax_Syntax.lbdef = _68_558}::[]), _68_572) -> begin
(
# 390 "FStar.TypeChecker.Tc.fst"
let _68_575 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_301 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _157_301))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _68_579), _68_582) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_68_597); FStar_Syntax_Syntax.lbunivs = _68_595; FStar_Syntax_Syntax.lbtyp = _68_593; FStar_Syntax_Syntax.lbeff = _68_591; FStar_Syntax_Syntax.lbdef = _68_589}::_68_587), _68_603) -> begin
(
# 397 "FStar.TypeChecker.Tc.fst"
let _68_606 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_302 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _157_302))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _68_610), _68_613) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 410 "FStar.TypeChecker.Tc.fst"
let check_instantiated_fvar = (fun env v dc e t -> (
# 411 "FStar.TypeChecker.Tc.fst"
let _68_627 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_68_627) with
| (e, t, implicits) -> begin
(
# 413 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _157_316 = (let _157_315 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _157_315))
in FStar_Util.Inr (_157_316))
end
in (
# 414 "FStar.TypeChecker.Tc.fst"
let is_data_ctor = (fun _68_4 -> (match (_68_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _68_637 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _157_322 = (let _157_321 = (let _157_320 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _157_319 = (FStar_TypeChecker_Env.get_range env)
in (_157_320, _157_319)))
in FStar_Syntax_Syntax.Error (_157_321))
in (Prims.raise _157_322))
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
let g = (match ((let _157_323 = (FStar_Syntax_Subst.compress t1)
in _157_323.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_68_648) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _68_651 -> begin
(
# 433 "FStar.TypeChecker.Tc.fst"
let imp = ("uvar in term", env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (
# 434 "FStar.TypeChecker.Tc.fst"
let _68_653 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _68_653.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _68_653.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_653.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 439 "FStar.TypeChecker.Tc.fst"
let _68_659 = (FStar_Syntax_Util.type_u ())
in (match (_68_659) with
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
let _68_664 = x
in {FStar_Syntax_Syntax.ppname = _68_664.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_664.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (
# 446 "FStar.TypeChecker.Tc.fst"
let _68_670 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_68_670) with
| (e, t, implicits) -> begin
(
# 447 "FStar.TypeChecker.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _157_325 = (let _157_324 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _157_324))
in FStar_Util.Inr (_157_325))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _68_677; FStar_Syntax_Syntax.pos = _68_675; FStar_Syntax_Syntax.vars = _68_673}, us) -> begin
(
# 451 "FStar.TypeChecker.Tc.fst"
let us = (FStar_List.map (tc_universe env) us)
in (
# 452 "FStar.TypeChecker.Tc.fst"
let _68_687 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_68_687) with
| (us', t) -> begin
(
# 453 "FStar.TypeChecker.Tc.fst"
let _68_694 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _157_328 = (let _157_327 = (let _157_326 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _157_326))
in FStar_Syntax_Syntax.Error (_157_327))
in (Prims.raise _157_328))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _68_693 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (
# 458 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 458 "FStar.TypeChecker.Tc.fst"
let _68_696 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 458 "FStar.TypeChecker.Tc.fst"
let _68_698 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _68_698.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _68_698.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _68_696.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _68_696.FStar_Syntax_Syntax.fv_qual})
in (
# 459 "FStar.TypeChecker.Tc.fst"
let e = (let _157_331 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _157_331 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(
# 463 "FStar.TypeChecker.Tc.fst"
let _68_706 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_68_706) with
| (us, t) -> begin
(
# 464 "FStar.TypeChecker.Tc.fst"
let fv' = (
# 464 "FStar.TypeChecker.Tc.fst"
let _68_707 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 464 "FStar.TypeChecker.Tc.fst"
let _68_709 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _68_709.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _68_709.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _68_707.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _68_707.FStar_Syntax_Syntax.fv_qual})
in (
# 465 "FStar.TypeChecker.Tc.fst"
let e = (let _157_332 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _157_332 us))
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
let _68_723 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_68_723) with
| (bs, c) -> begin
(
# 475 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 476 "FStar.TypeChecker.Tc.fst"
let _68_728 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_68_728) with
| (env, _68_727) -> begin
(
# 477 "FStar.TypeChecker.Tc.fst"
let _68_733 = (tc_binders env bs)
in (match (_68_733) with
| (bs, env, g, us) -> begin
(
# 478 "FStar.TypeChecker.Tc.fst"
let _68_737 = (tc_comp env c)
in (match (_68_737) with
| (c, uc, f) -> begin
(
# 479 "FStar.TypeChecker.Tc.fst"
let e = (
# 479 "FStar.TypeChecker.Tc.fst"
let _68_738 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _68_738.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _68_738.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _68_738.FStar_Syntax_Syntax.vars})
in (
# 480 "FStar.TypeChecker.Tc.fst"
let _68_741 = (check_smt_pat env e bs c)
in (
# 481 "FStar.TypeChecker.Tc.fst"
let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (
# 482 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 483 "FStar.TypeChecker.Tc.fst"
let g = (let _157_333 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _157_333))
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
let _68_757 = (let _157_335 = (let _157_334 = (FStar_Syntax_Syntax.mk_binder x)
in (_157_334)::[])
in (FStar_Syntax_Subst.open_term _157_335 phi))
in (match (_68_757) with
| (x, phi) -> begin
(
# 494 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 495 "FStar.TypeChecker.Tc.fst"
let _68_762 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_68_762) with
| (env, _68_761) -> begin
(
# 496 "FStar.TypeChecker.Tc.fst"
let _68_767 = (let _157_336 = (FStar_List.hd x)
in (tc_binder env _157_336))
in (match (_68_767) with
| (x, env, f1, u) -> begin
(
# 497 "FStar.TypeChecker.Tc.fst"
let _68_768 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_339 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _157_338 = (FStar_Syntax_Print.term_to_string phi)
in (let _157_337 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _157_339 _157_338 _157_337))))
end else begin
()
end
in (
# 500 "FStar.TypeChecker.Tc.fst"
let _68_773 = (FStar_Syntax_Util.type_u ())
in (match (_68_773) with
| (t_phi, _68_772) -> begin
(
# 501 "FStar.TypeChecker.Tc.fst"
let _68_778 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_68_778) with
| (phi, _68_776, f2) -> begin
(
# 502 "FStar.TypeChecker.Tc.fst"
let e = (
# 502 "FStar.TypeChecker.Tc.fst"
let _68_779 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _68_779.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _68_779.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _68_779.FStar_Syntax_Syntax.vars})
in (
# 503 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (
# 504 "FStar.TypeChecker.Tc.fst"
let g = (let _157_340 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _157_340))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _68_787) -> begin
(
# 508 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (
# 509 "FStar.TypeChecker.Tc.fst"
let _68_793 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_341 = (FStar_Syntax_Print.term_to_string (
# 510 "FStar.TypeChecker.Tc.fst"
let _68_791 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _68_791.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _68_791.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _68_791.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _157_341))
end else begin
()
end
in (
# 511 "FStar.TypeChecker.Tc.fst"
let _68_797 = (FStar_Syntax_Subst.open_term bs body)
in (match (_68_797) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _68_799 -> begin
(let _157_343 = (let _157_342 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _157_342))
in (FStar_All.failwith _157_343))
end)))))
and tc_constant : FStar_TypeChecker_Env.env  ->  FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun env r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_68_805) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_68_808, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_68_813, Some (FStar_Const.Unsigned, FStar_Const.Int8)) -> begin
FStar_TypeChecker_Common.t_uint8
end
| FStar_Const.Const_int (_68_821, Some (FStar_Const.Signed, FStar_Const.Int8)) -> begin
FStar_TypeChecker_Common.t_int8
end
| FStar_Const.Const_int (_68_829, Some (FStar_Const.Unsigned, FStar_Const.Int16)) -> begin
FStar_TypeChecker_Common.t_uint16
end
| FStar_Const.Const_int (_68_837, Some (FStar_Const.Signed, FStar_Const.Int16)) -> begin
FStar_TypeChecker_Common.t_int16
end
| FStar_Const.Const_int (_68_845, Some (FStar_Const.Unsigned, FStar_Const.Int32)) -> begin
FStar_TypeChecker_Common.t_uint32
end
| FStar_Const.Const_int (_68_853, Some (FStar_Const.Signed, FStar_Const.Int32)) -> begin
FStar_TypeChecker_Common.t_int32
end
| FStar_Const.Const_int (_68_861, Some (FStar_Const.Unsigned, FStar_Const.Int64)) -> begin
FStar_TypeChecker_Common.t_uint64
end
| FStar_Const.Const_int (_68_869, Some (FStar_Const.Signed, FStar_Const.Int64)) -> begin
FStar_TypeChecker_Common.t_int64
end
| FStar_Const.Const_string (_68_877) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_68_880) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_68_883) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_68_887) -> begin
(
# 535 "FStar.TypeChecker.Tc.fst"
let fail = (fun _68_890 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Range constant cannot be checked in this context; expected an instance of \'range_of\'", r))))
end))
in (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(fail ())
end
| Some (t) -> begin
if (let _157_349 = (FStar_Syntax_Util.destruct t FStar_Syntax_Const.range_of_lid)
in (FStar_Option.isSome _157_349)) then begin
t
end else begin
(fail ())
end
end))
end
| _68_895 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 556 "FStar.TypeChecker.Tc.fst"
let _68_902 = (FStar_Syntax_Util.type_u ())
in (match (_68_902) with
| (k, u) -> begin
(
# 557 "FStar.TypeChecker.Tc.fst"
let _68_907 = (tc_check_tot_or_gtot_term env t k)
in (match (_68_907) with
| (t, _68_905, g) -> begin
(let _157_352 = (FStar_Syntax_Syntax.mk_Total t)
in (_157_352, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 561 "FStar.TypeChecker.Tc.fst"
let _68_912 = (FStar_Syntax_Util.type_u ())
in (match (_68_912) with
| (k, u) -> begin
(
# 562 "FStar.TypeChecker.Tc.fst"
let _68_917 = (tc_check_tot_or_gtot_term env t k)
in (match (_68_917) with
| (t, _68_915, g) -> begin
(let _157_353 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_157_353, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 566 "FStar.TypeChecker.Tc.fst"
let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (
# 567 "FStar.TypeChecker.Tc.fst"
let tc = (let _157_355 = (let _157_354 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_157_354)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _157_355 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 568 "FStar.TypeChecker.Tc.fst"
let _68_926 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_68_926) with
| (tc, _68_924, f) -> begin
(
# 569 "FStar.TypeChecker.Tc.fst"
let _68_930 = (FStar_Syntax_Util.head_and_args tc)
in (match (_68_930) with
| (_68_928, args) -> begin
(
# 570 "FStar.TypeChecker.Tc.fst"
let _68_933 = (let _157_357 = (FStar_List.hd args)
in (let _157_356 = (FStar_List.tl args)
in (_157_357, _157_356)))
in (match (_68_933) with
| (res, args) -> begin
(
# 571 "FStar.TypeChecker.Tc.fst"
let _68_949 = (let _157_359 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _68_5 -> (match (_68_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(
# 573 "FStar.TypeChecker.Tc.fst"
let _68_940 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_68_940) with
| (env, _68_939) -> begin
(
# 574 "FStar.TypeChecker.Tc.fst"
let _68_945 = (tc_tot_or_gtot_term env e)
in (match (_68_945) with
| (e, _68_943, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _157_359 FStar_List.unzip))
in (match (_68_949) with
| (flags, guards) -> begin
(
# 577 "FStar.TypeChecker.Tc.fst"
let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| _68_954 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _157_361 = (FStar_Syntax_Syntax.mk_Comp (
# 580 "FStar.TypeChecker.Tc.fst"
let _68_956 = c
in {FStar_Syntax_Syntax.effect_name = _68_956.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _68_956.FStar_Syntax_Syntax.flags}))
in (let _157_360 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_157_361, u, _157_360))))
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
| FStar_Syntax_Syntax.U_bvar (_68_964) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _157_366 = (aux u)
in FStar_Syntax_Syntax.U_succ (_157_366))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _157_367 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_157_367))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _157_371 = (let _157_370 = (let _157_369 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _157_368 = (FStar_TypeChecker_Env.get_range env)
in (_157_369, _157_368)))
in FStar_Syntax_Syntax.Error (_157_370))
in (Prims.raise _157_371))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _157_372 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _157_372 Prims.snd))
end
| _68_979 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (
# 610 "FStar.TypeChecker.Tc.fst"
let fail = (fun msg t -> (let _157_381 = (let _157_380 = (let _157_379 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_157_379, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_157_380))
in (Prims.raise _157_381)))
in (
# 619 "FStar.TypeChecker.Tc.fst"
let check_binders = (fun env bs bs_expected -> (
# 624 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun _68_997 bs bs_expected -> (match (_68_997) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| ((hd, imp)::bs, (hd_expected, imp')::bs_expected) -> begin
(
# 628 "FStar.TypeChecker.Tc.fst"
let _68_1028 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _157_398 = (let _157_397 = (let _157_396 = (let _157_394 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _157_394))
in (let _157_395 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_157_396, _157_395)))
in FStar_Syntax_Syntax.Error (_157_397))
in (Prims.raise _157_398))
end
| _68_1027 -> begin
()
end)
in (
# 635 "FStar.TypeChecker.Tc.fst"
let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (
# 636 "FStar.TypeChecker.Tc.fst"
let _68_1045 = (match ((let _157_399 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _157_399.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _68_1033 -> begin
(
# 639 "FStar.TypeChecker.Tc.fst"
let _68_1034 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_400 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _157_400))
end else begin
()
end
in (
# 640 "FStar.TypeChecker.Tc.fst"
let _68_1040 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_68_1040) with
| (t, _68_1038, g1) -> begin
(
# 641 "FStar.TypeChecker.Tc.fst"
let g2 = (let _157_402 = (FStar_TypeChecker_Env.get_range env)
in (let _157_401 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _157_402 "Type annotation on parameter incompatible with the expected type" _157_401)))
in (
# 645 "FStar.TypeChecker.Tc.fst"
let g = (let _157_403 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _157_403))
in (t, g)))
end)))
end)
in (match (_68_1045) with
| (t, g) -> begin
(
# 647 "FStar.TypeChecker.Tc.fst"
let hd = (
# 647 "FStar.TypeChecker.Tc.fst"
let _68_1046 = hd
in {FStar_Syntax_Syntax.ppname = _68_1046.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_1046.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
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
let subst = (let _157_404 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _157_404))
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
let _68_1067 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _68_1066 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (
# 675 "FStar.TypeChecker.Tc.fst"
let _68_1074 = (tc_binders env bs)
in (match (_68_1074) with
| (bs, envbody, g, _68_1073) -> begin
(
# 676 "FStar.TypeChecker.Tc.fst"
let _68_1092 = (match ((let _157_411 = (FStar_Syntax_Subst.compress body)
in _157_411.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _68_1079) -> begin
(
# 678 "FStar.TypeChecker.Tc.fst"
let _68_1086 = (tc_comp envbody c)
in (match (_68_1086) with
| (c, _68_1084, g') -> begin
(let _157_412 = (FStar_TypeChecker_Rel.conj_guard g g')
in (Some (c), body, _157_412))
end))
end
| _68_1088 -> begin
(None, body, g)
end)
in (match (_68_1092) with
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
let rec as_function_typ = (fun norm t -> (match ((let _157_417 = (FStar_Syntax_Subst.compress t)
in _157_417.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(
# 689 "FStar.TypeChecker.Tc.fst"
let _68_1119 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _68_1118 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 690 "FStar.TypeChecker.Tc.fst"
let _68_1126 = (tc_binders env bs)
in (match (_68_1126) with
| (bs, envbody, g, _68_1125) -> begin
(
# 691 "FStar.TypeChecker.Tc.fst"
let _68_1130 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_68_1130) with
| (envbody, _68_1129) -> begin
(Some ((t, true)), bs, [], None, envbody, body, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _68_1133) -> begin
(
# 697 "FStar.TypeChecker.Tc.fst"
let _68_1144 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_68_1144) with
| (_68_1137, bs, bs', copt, env, body, g) -> begin
(Some ((t, false)), bs, bs', copt, env, body, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(
# 701 "FStar.TypeChecker.Tc.fst"
let _68_1151 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_68_1151) with
| (bs_expected, c_expected) -> begin
(
# 708 "FStar.TypeChecker.Tc.fst"
let check_actuals_against_formals = (fun env bs bs_expected -> (
# 709 "FStar.TypeChecker.Tc.fst"
let rec handle_more = (fun _68_1162 c_expected -> (match (_68_1162) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _157_428 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _157_428))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(
# 714 "FStar.TypeChecker.Tc.fst"
let c = (let _157_429 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _157_429))
in (let _157_430 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _157_430)))
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
let _68_1183 = (check_binders env more_bs bs_expected)
in (match (_68_1183) with
| (env, bs', more, guard', subst) -> begin
(let _157_432 = (let _157_431 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _157_431, subst))
in (handle_more _157_432 c_expected))
end))
end
| _68_1185 -> begin
(let _157_434 = (let _157_433 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _157_433))
in (fail _157_434 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _157_435 = (check_binders env bs bs_expected)
in (handle_more _157_435 c_expected))))
in (
# 731 "FStar.TypeChecker.Tc.fst"
let mk_letrec_env = (fun envbody bs c -> (
# 732 "FStar.TypeChecker.Tc.fst"
let letrecs = (guard_letrecs envbody bs c)
in (
# 733 "FStar.TypeChecker.Tc.fst"
let envbody = (
# 733 "FStar.TypeChecker.Tc.fst"
let _68_1191 = envbody
in {FStar_TypeChecker_Env.solver = _68_1191.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_1191.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_1191.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_1191.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_1191.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_1191.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_1191.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_1191.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_1191.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_1191.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_1191.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_1191.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _68_1191.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _68_1191.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_1191.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_1191.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_1191.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _68_1191.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_1191.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_1191.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _68_1196 _68_1199 -> (match ((_68_1196, _68_1199)) with
| ((env, letrec_binders), (l, t)) -> begin
(
# 737 "FStar.TypeChecker.Tc.fst"
let _68_1205 = (let _157_445 = (let _157_444 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _157_444 Prims.fst))
in (tc_term _157_445 t))
in (match (_68_1205) with
| (t, _68_1202, _68_1204) -> begin
(
# 738 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (
# 739 "FStar.TypeChecker.Tc.fst"
let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _157_446 = (FStar_Syntax_Syntax.mk_binder (
# 740 "FStar.TypeChecker.Tc.fst"
let _68_1209 = x
in {FStar_Syntax_Syntax.ppname = _68_1209.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_1209.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_157_446)::letrec_binders)
end
| _68_1212 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (
# 745 "FStar.TypeChecker.Tc.fst"
let _68_1218 = (check_actuals_against_formals env bs bs_expected)
in (match (_68_1218) with
| (envbody, bs, g, c) -> begin
(
# 746 "FStar.TypeChecker.Tc.fst"
let _68_1221 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_68_1221) with
| (envbody, letrecs) -> begin
(
# 747 "FStar.TypeChecker.Tc.fst"
let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, body, g))
end))
end))))
end))
end
| _68_1224 -> begin
if (not (norm)) then begin
(let _157_447 = (unfold_whnf env t)
in (as_function_typ true _157_447))
end else begin
(
# 755 "FStar.TypeChecker.Tc.fst"
let _68_1234 = (expected_function_typ env None body)
in (match (_68_1234) with
| (_68_1226, bs, _68_1229, c_opt, envbody, body, g) -> begin
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
let _68_1238 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_68_1238) with
| (env, topt) -> begin
(
# 762 "FStar.TypeChecker.Tc.fst"
let _68_1242 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_448 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _157_448 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (
# 767 "FStar.TypeChecker.Tc.fst"
let _68_1251 = (expected_function_typ env topt body)
in (match (_68_1251) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(
# 768 "FStar.TypeChecker.Tc.fst"
let _68_1257 = (tc_term (
# 768 "FStar.TypeChecker.Tc.fst"
let _68_1252 = envbody
in {FStar_TypeChecker_Env.solver = _68_1252.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_1252.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_1252.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_1252.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_1252.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_1252.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_1252.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_1252.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_1252.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_1252.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_1252.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_1252.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_1252.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _68_1252.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _68_1252.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_1252.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _68_1252.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_1252.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_1252.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_68_1257) with
| (body, cbody, guard_body) -> begin
(
# 770 "FStar.TypeChecker.Tc.fst"
let _68_1258 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_452 = (FStar_Syntax_Print.term_to_string body)
in (let _157_451 = (let _157_449 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _157_449))
in (let _157_450 = (FStar_TypeChecker_Rel.guard_to_string env guard_body)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _157_452 _157_451 _157_450))))
end else begin
()
end
in (
# 776 "FStar.TypeChecker.Tc.fst"
let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (
# 779 "FStar.TypeChecker.Tc.fst"
let _68_1261 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _157_455 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _157_454 = (let _157_453 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _157_453))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _157_455 _157_454)))
end else begin
()
end
in (
# 784 "FStar.TypeChecker.Tc.fst"
let _68_1268 = (let _157_457 = (let _157_456 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _157_456))
in (check_expected_effect (
# 784 "FStar.TypeChecker.Tc.fst"
let _68_1263 = envbody
in {FStar_TypeChecker_Env.solver = _68_1263.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_1263.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_1263.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_1263.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_1263.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_1263.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_1263.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_1263.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_1263.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_1263.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_1263.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_1263.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_1263.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _68_1263.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _68_1263.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _68_1263.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_1263.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _68_1263.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_1263.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_1263.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _157_457))
in (match (_68_1268) with
| (body, cbody, guard) -> begin
(
# 785 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (
# 786 "FStar.TypeChecker.Tc.fst"
let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _157_458 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _157_458))
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
let e = (FStar_Syntax_Util.abs bs body (Some ((FStar_Syntax_Util.lcomp_of_comp cbody))))
in (
# 793 "FStar.TypeChecker.Tc.fst"
let _68_1291 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(
# 795 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_68_1280) -> begin
(e, t, guard)
end
| _68_1283 -> begin
(
# 802 "FStar.TypeChecker.Tc.fst"
let _68_1286 = if use_teq then begin
(let _157_459 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _157_459))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_68_1286) with
| (e, guard') -> begin
(let _157_460 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _157_460))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_68_1291) with
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
let _68_1295 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_68_1295) with
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
let _68_1305 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_469 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _157_468 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _157_469 _157_468)))
end else begin
()
end
in (
# 824 "FStar.TypeChecker.Tc.fst"
let rec check_function_app = (fun norm tf -> (match ((let _157_474 = (FStar_Syntax_Util.unrefine tf)
in _157_474.FStar_Syntax_Syntax.n)) with
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
let _68_1339 = (tc_term env e)
in (match (_68_1339) with
| (e, c, g_e) -> begin
(
# 832 "FStar.TypeChecker.Tc.fst"
let _68_1343 = (tc_args env tl)
in (match (_68_1343) with
| (args, comps, g_rest) -> begin
(let _157_479 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, (c)::comps, _157_479))
end))
end))
end))
in (
# 840 "FStar.TypeChecker.Tc.fst"
let _68_1347 = (tc_args env args)
in (match (_68_1347) with
| (args, comps, g_args) -> begin
(
# 841 "FStar.TypeChecker.Tc.fst"
let bs = (let _157_481 = (FStar_All.pipe_right comps (FStar_List.map (fun c -> (c.FStar_Syntax_Syntax.res_typ, None))))
in (FStar_Syntax_Util.null_binders_of_tks _157_481))
in (
# 842 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _68_1354 -> begin
FStar_Syntax_Util.ml_comp
end)
in (
# 845 "FStar.TypeChecker.Tc.fst"
let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _157_496 = (FStar_Syntax_Subst.compress t)
in _157_496.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_68_1360) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _68_1365 -> begin
ml_or_tot
end)
end)
in (
# 852 "FStar.TypeChecker.Tc.fst"
let cres = (let _157_501 = (let _157_500 = (let _157_499 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _157_499 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _157_500))
in (ml_or_tot _157_501 r))
in (
# 853 "FStar.TypeChecker.Tc.fst"
let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (
# 854 "FStar.TypeChecker.Tc.fst"
let _68_1369 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _157_504 = (FStar_Syntax_Print.term_to_string head)
in (let _157_503 = (FStar_Syntax_Print.term_to_string tf)
in (let _157_502 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _157_504 _157_503 _157_502))))
end else begin
()
end
in (
# 859 "FStar.TypeChecker.Tc.fst"
let _68_1371 = (let _157_505 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _157_505))
in (
# 860 "FStar.TypeChecker.Tc.fst"
let comp = (let _157_508 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_TypeChecker_Util.bind env None c (None, out))) ((chead)::comps) _157_508))
in (let _157_510 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _157_509 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_157_510, comp, _157_509)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 864 "FStar.TypeChecker.Tc.fst"
let _68_1382 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_68_1382) with
| (bs, c) -> begin
(
# 866 "FStar.TypeChecker.Tc.fst"
let rec tc_args = (fun _68_1390 bs cres args -> (match (_68_1390) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (_68_1397)))::rest, (_68_1405, None)::_68_1403) -> begin
(
# 877 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 878 "FStar.TypeChecker.Tc.fst"
let _68_1411 = (check_no_escape (Some (head)) env fvs t)
in (
# 879 "FStar.TypeChecker.Tc.fst"
let _68_1417 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_68_1417) with
| (varg, _68_1415, implicits) -> begin
(
# 880 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (
# 881 "FStar.TypeChecker.Tc.fst"
let arg = (let _157_519 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _157_519))
in (let _157_521 = (let _157_520 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _157_520, fvs))
in (tc_args _157_521 rest cres args))))
end))))
end
| ((x, aqual)::rest, (e, aq)::rest') -> begin
(
# 885 "FStar.TypeChecker.Tc.fst"
let _68_1449 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _68_1448 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (
# 890 "FStar.TypeChecker.Tc.fst"
let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 891 "FStar.TypeChecker.Tc.fst"
let x = (
# 891 "FStar.TypeChecker.Tc.fst"
let _68_1452 = x
in {FStar_Syntax_Syntax.ppname = _68_1452.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_1452.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (
# 892 "FStar.TypeChecker.Tc.fst"
let _68_1455 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _157_522 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _157_522))
end else begin
()
end
in (
# 893 "FStar.TypeChecker.Tc.fst"
let _68_1457 = (check_no_escape (Some (head)) env fvs targ)
in (
# 894 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (
# 895 "FStar.TypeChecker.Tc.fst"
let env = (
# 895 "FStar.TypeChecker.Tc.fst"
let _68_1460 = env
in {FStar_TypeChecker_Env.solver = _68_1460.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_1460.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_1460.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_1460.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_1460.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_1460.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_1460.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_1460.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_1460.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_1460.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_1460.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_1460.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_1460.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _68_1460.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _68_1460.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _68_1460.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_1460.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _68_1460.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_1460.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_1460.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 896 "FStar.TypeChecker.Tc.fst"
let _68_1463 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_525 = (FStar_Syntax_Print.tag_of_term e)
in (let _157_524 = (FStar_Syntax_Print.term_to_string e)
in (let _157_523 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _157_525 _157_524 _157_523))))
end else begin
()
end
in (
# 897 "FStar.TypeChecker.Tc.fst"
let _68_1468 = (tc_term env e)
in (match (_68_1468) with
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
let subst = (let _157_526 = (FStar_List.hd bs)
in (maybe_extend_subst subst _157_526 e))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(
# 905 "FStar.TypeChecker.Tc.fst"
let subst = (let _157_527 = (FStar_List.hd bs)
in (maybe_extend_subst subst _157_527 e))
in (
# 906 "FStar.TypeChecker.Tc.fst"
let _68_1475 = (((Some (x), c))::comps, g)
in (match (_68_1475) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _157_528 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _157_528)) then begin
(
# 910 "FStar.TypeChecker.Tc.fst"
let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (
# 911 "FStar.TypeChecker.Tc.fst"
let arg' = (let _157_529 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _157_529))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (newx), c))::comps, g, fvs) rest cres rest')))
end else begin
(let _157_533 = (let _157_532 = (let _157_531 = (let _157_530 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _157_530))
in (_157_531)::arg_rets)
in (subst, (arg)::outargs, _157_532, ((Some (x), c))::comps, g, (x)::fvs))
in (tc_args _157_533 rest cres rest'))
end
end
end))
end))))))))))
end
| (_68_1479, []) -> begin
(
# 920 "FStar.TypeChecker.Tc.fst"
let _68_1482 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (
# 921 "FStar.TypeChecker.Tc.fst"
let _68_1500 = (match (bs) with
| [] -> begin
(
# 924 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (
# 930 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (
# 932 "FStar.TypeChecker.Tc.fst"
let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _68_1490 -> (match (_68_1490) with
| (_68_1488, c) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (
# 939 "FStar.TypeChecker.Tc.fst"
let cres = if refine_with_equality then begin
(let _157_535 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _157_535 cres))
end else begin
(
# 945 "FStar.TypeChecker.Tc.fst"
let _68_1492 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_538 = (FStar_Syntax_Print.term_to_string head)
in (let _157_537 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _157_536 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _157_538 _157_537 _157_536))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _68_1496 -> begin
(
# 954 "FStar.TypeChecker.Tc.fst"
let g = (let _157_539 = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (FStar_All.pipe_right _157_539 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _157_544 = (let _157_543 = (let _157_542 = (let _157_541 = (let _157_540 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _157_540))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _157_541))
in (FStar_Syntax_Syntax.mk_Total _157_542))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _157_543))
in (_157_544, g)))
end)
in (match (_68_1500) with
| (cres, g) -> begin
(
# 957 "FStar.TypeChecker.Tc.fst"
let _68_1501 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_545 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _157_545))
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
let _68_1511 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp g)
in (match (_68_1511) with
| (comp, g) -> begin
(
# 963 "FStar.TypeChecker.Tc.fst"
let _68_1512 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_551 = (FStar_TypeChecker_Normalize.term_to_string env app)
in (let _157_550 = (let _157_549 = (comp.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Print.comp_to_string _157_549))
in (FStar_Util.print2 "\t Type of app term %s is %s\n" _157_551 _157_550)))
end else begin
()
end
in (app, comp, g))
end)))))))
end)))
end
| ([], arg::_68_1516) -> begin
(
# 969 "FStar.TypeChecker.Tc.fst"
let rec aux = (fun norm tres -> (
# 970 "FStar.TypeChecker.Tc.fst"
let tres = (let _157_556 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _157_556 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(
# 973 "FStar.TypeChecker.Tc.fst"
let _68_1528 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_557 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _157_557))
end else begin
()
end
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs (FStar_Syntax_Util.lcomp_of_comp cres') args))
end
| _68_1531 when (not (norm)) -> begin
(let _157_558 = (unfold_whnf env tres)
in (aux true _157_558))
end
| _68_1533 -> begin
(let _157_564 = (let _157_563 = (let _157_562 = (let _157_560 = (FStar_TypeChecker_Normalize.term_to_string env tf)
in (let _157_559 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _157_560 _157_559)))
in (let _157_561 = (FStar_Syntax_Syntax.argpos arg)
in (_157_562, _157_561)))
in FStar_Syntax_Syntax.Error (_157_563))
in (Prims.raise _157_564))
end)))
in (aux false cres.FStar_Syntax_Syntax.res_typ))
end)
end))
in (tc_args ([], [], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs (FStar_Syntax_Util.lcomp_of_comp c) args))
end))
end
| _68_1535 -> begin
if (not (norm)) then begin
(let _157_565 = (unfold_whnf env tf)
in (check_function_app true _157_565))
end else begin
(let _157_568 = (let _157_567 = (let _157_566 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_157_566, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_157_567))
in (Prims.raise _157_568))
end
end))
in (let _157_570 = (let _157_569 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _157_569))
in (check_function_app false _157_570))))))))
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
let _68_1571 = (FStar_List.fold_left2 (fun _68_1552 _68_1555 _68_1558 -> (match ((_68_1552, _68_1555, _68_1558)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(
# 1005 "FStar.TypeChecker.Tc.fst"
let _68_1559 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1006 "FStar.TypeChecker.Tc.fst"
let _68_1564 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_68_1564) with
| (e, c, g) -> begin
(
# 1007 "FStar.TypeChecker.Tc.fst"
let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (
# 1008 "FStar.TypeChecker.Tc.fst"
let g = (let _157_580 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _157_580 g))
in (
# 1009 "FStar.TypeChecker.Tc.fst"
let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _157_584 = (let _157_582 = (let _157_581 = (FStar_Syntax_Syntax.as_arg e)
in (_157_581)::[])
in (FStar_List.append seen _157_582))
in (let _157_583 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_157_584, _157_583, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_68_1571) with
| (args, guard, ghost) -> begin
(
# 1013 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (
# 1014 "FStar.TypeChecker.Tc.fst"
let c = if ghost then begin
(let _157_585 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _157_585 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (
# 1015 "FStar.TypeChecker.Tc.fst"
let _68_1576 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_68_1576) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _68_1578 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (
# 1035 "FStar.TypeChecker.Tc.fst"
let _68_1585 = (FStar_Syntax_Subst.open_branch branch)
in (match (_68_1585) with
| (pattern, when_clause, branch_exp) -> begin
(
# 1036 "FStar.TypeChecker.Tc.fst"
let _68_1590 = branch
in (match (_68_1590) with
| (cpat, _68_1588, cbr) -> begin
(
# 1039 "FStar.TypeChecker.Tc.fst"
let tc_pat = (fun allow_implicits pat_t p0 -> (
# 1046 "FStar.TypeChecker.Tc.fst"
let _68_1598 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_68_1598) with
| (pat_bvs, exps, p) -> begin
(
# 1047 "FStar.TypeChecker.Tc.fst"
let _68_1599 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_597 = (FStar_Syntax_Print.pat_to_string p0)
in (let _157_596 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _157_597 _157_596)))
end else begin
()
end
in (
# 1049 "FStar.TypeChecker.Tc.fst"
let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (
# 1050 "FStar.TypeChecker.Tc.fst"
let _68_1605 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_68_1605) with
| (env1, _68_1604) -> begin
(
# 1051 "FStar.TypeChecker.Tc.fst"
let env1 = (
# 1051 "FStar.TypeChecker.Tc.fst"
let _68_1606 = env1
in {FStar_TypeChecker_Env.solver = _68_1606.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_1606.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_1606.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_1606.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_1606.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_1606.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_1606.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_1606.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _68_1606.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_1606.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_1606.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_1606.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _68_1606.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _68_1606.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_1606.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_1606.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_1606.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _68_1606.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_1606.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_1606.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1052 "FStar.TypeChecker.Tc.fst"
let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (
# 1053 "FStar.TypeChecker.Tc.fst"
let _68_1645 = (let _157_620 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (
# 1054 "FStar.TypeChecker.Tc.fst"
let _68_1611 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_600 = (FStar_Syntax_Print.term_to_string e)
in (let _157_599 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _157_600 _157_599)))
end else begin
()
end
in (
# 1057 "FStar.TypeChecker.Tc.fst"
let _68_1616 = (tc_term env1 e)
in (match (_68_1616) with
| (e, lc, g) -> begin
(
# 1059 "FStar.TypeChecker.Tc.fst"
let _68_1617 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_602 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _157_601 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _157_602 _157_601)))
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
let _68_1623 = (let _157_603 = (FStar_TypeChecker_Rel.discharge_guard env (
# 1064 "FStar.TypeChecker.Tc.fst"
let _68_1621 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _68_1621.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_1621.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_1621.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _157_603 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1065 "FStar.TypeChecker.Tc.fst"
let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (
# 1066 "FStar.TypeChecker.Tc.fst"
let uvars_to_string = (fun uvs -> (let _157_608 = (let _157_607 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _157_607 (FStar_List.map (fun _68_1631 -> (match (_68_1631) with
| (u, _68_1630) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _157_608 (FStar_String.concat ", "))))
in (
# 1067 "FStar.TypeChecker.Tc.fst"
let uvs1 = (FStar_Syntax_Free.uvars e')
in (
# 1068 "FStar.TypeChecker.Tc.fst"
let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (
# 1069 "FStar.TypeChecker.Tc.fst"
let _68_1639 = if (let _157_609 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _157_609)) then begin
(
# 1070 "FStar.TypeChecker.Tc.fst"
let unresolved = (let _157_610 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _157_610 FStar_Util.set_elements))
in (let _157_618 = (let _157_617 = (let _157_616 = (let _157_615 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _157_614 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _157_613 = (let _157_612 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _68_1638 -> (match (_68_1638) with
| (u, _68_1637) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _157_612 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _157_615 _157_614 _157_613))))
in (_157_616, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_157_617))
in (Prims.raise _157_618)))
end else begin
()
end
in (
# 1077 "FStar.TypeChecker.Tc.fst"
let _68_1641 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_619 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _157_619))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _157_620 FStar_List.unzip))
in (match (_68_1645) with
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
let _68_1652 = (let _157_621 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _157_621 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_68_1652) with
| (scrutinee_env, _68_1651) -> begin
(
# 1091 "FStar.TypeChecker.Tc.fst"
let _68_1658 = (tc_pat true pat_t pattern)
in (match (_68_1658) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(
# 1094 "FStar.TypeChecker.Tc.fst"
let _68_1668 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(
# 1101 "FStar.TypeChecker.Tc.fst"
let _68_1665 = (let _157_622 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _157_622 e))
in (match (_68_1665) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_68_1668) with
| (when_clause, g_when) -> begin
(
# 1105 "FStar.TypeChecker.Tc.fst"
let _68_1672 = (tc_term pat_env branch_exp)
in (match (_68_1672) with
| (branch_exp, c, g_branch) -> begin
(
# 1109 "FStar.TypeChecker.Tc.fst"
let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _157_624 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _157_623 -> Some (_157_623)) _157_624))
end)
in (
# 1116 "FStar.TypeChecker.Tc.fst"
let _68_1728 = (
# 1119 "FStar.TypeChecker.Tc.fst"
let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (
# 1120 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _68_1690 -> begin
(
# 1126 "FStar.TypeChecker.Tc.fst"
let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _157_628 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _157_627 -> Some (_157_627)) _157_628))
end))
end))) None))
in (
# 1131 "FStar.TypeChecker.Tc.fst"
let _68_1698 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_68_1698) with
| (c, g_branch) -> begin
(
# 1135 "FStar.TypeChecker.Tc.fst"
let _68_1723 = (match ((eqs, when_condition)) with
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
in (let _157_631 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _157_630 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_157_631, _157_630)))))
end
| (Some (f), Some (w)) -> begin
(
# 1147 "FStar.TypeChecker.Tc.fst"
let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (
# 1148 "FStar.TypeChecker.Tc.fst"
let g_fw = (let _157_632 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_157_632))
in (let _157_635 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _157_634 = (let _157_633 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _157_633 g_when))
in (_157_635, _157_634)))))
end
| (None, Some (w)) -> begin
(
# 1153 "FStar.TypeChecker.Tc.fst"
let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (
# 1154 "FStar.TypeChecker.Tc.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _157_636 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_157_636, g_when))))
end)
in (match (_68_1723) with
| (c_weak, g_when_weak) -> begin
(
# 1159 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _157_638 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _157_637 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_157_638, _157_637, g_branch))))
end))
end)))
in (match (_68_1728) with
| (c, g_when, g_branch) -> begin
(
# 1177 "FStar.TypeChecker.Tc.fst"
let branch_guard = (
# 1179 "FStar.TypeChecker.Tc.fst"
let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (
# 1180 "FStar.TypeChecker.Tc.fst"
let discriminate = (fun scrutinee_tm f -> if ((let _157_648 = (let _157_647 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _157_647))
in (FStar_List.length _157_648)) > 1) then begin
(
# 1183 "FStar.TypeChecker.Tc.fst"
let disc = (let _157_649 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _157_649 FStar_Syntax_Syntax.Delta_equational None))
in (
# 1184 "FStar.TypeChecker.Tc.fst"
let disc = (let _157_651 = (let _157_650 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_157_650)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _157_651 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _157_652 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_157_652)::[])))
end else begin
[]
end)
in (
# 1188 "FStar.TypeChecker.Tc.fst"
let fail = (fun _68_1738 -> (match (()) with
| () -> begin
(let _157_658 = (let _157_657 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _157_656 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _157_655 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _157_657 _157_656 _157_655))))
in (FStar_All.failwith _157_658))
end))
in (
# 1194 "FStar.TypeChecker.Tc.fst"
let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _68_1745) -> begin
(head_constructor t)
end
| _68_1749 -> begin
(fail ())
end))
in (
# 1199 "FStar.TypeChecker.Tc.fst"
let pat_exp = (let _157_661 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _157_661 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_68_1774) -> begin
(let _157_666 = (let _157_665 = (let _157_664 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _157_663 = (let _157_662 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_157_662)::[])
in (_157_664)::_157_663))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _157_665 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_157_666)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(
# 1208 "FStar.TypeChecker.Tc.fst"
let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _157_667 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _157_667))
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
let sub_term_guards = (let _157_674 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _68_1792 -> (match (_68_1792) with
| (ei, _68_1791) -> begin
(
# 1217 "FStar.TypeChecker.Tc.fst"
let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _68_1796 -> begin
(
# 1221 "FStar.TypeChecker.Tc.fst"
let sub_term = (let _157_673 = (let _157_670 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _157_670 FStar_Syntax_Syntax.Delta_equational None))
in (let _157_672 = (let _157_671 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_157_671)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _157_673 _157_672 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _157_674 FStar_List.flatten))
in (let _157_675 = (discriminate scrutinee_tm f)
in (FStar_List.append _157_675 sub_term_guards)))
end)
end
| _68_1800 -> begin
[]
end))))))
in (
# 1227 "FStar.TypeChecker.Tc.fst"
let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(
# 1230 "FStar.TypeChecker.Tc.fst"
let t = (let _157_680 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _157_680))
in (
# 1231 "FStar.TypeChecker.Tc.fst"
let _68_1808 = (FStar_Syntax_Util.type_u ())
in (match (_68_1808) with
| (k, _68_1807) -> begin
(
# 1232 "FStar.TypeChecker.Tc.fst"
let _68_1814 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_68_1814) with
| (t, _68_1811, _68_1813) -> begin
t
end))
end)))
end)
in (
# 1236 "FStar.TypeChecker.Tc.fst"
let branch_guard = (let _157_681 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _157_681 FStar_Syntax_Util.mk_disj_l))
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
let _68_1822 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_682 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _157_682))
end else begin
()
end
in (let _157_683 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_157_683, branch_guard, c, guard)))))
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
let _68_1839 = (check_let_bound_def true env lb)
in (match (_68_1839) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(
# 1266 "FStar.TypeChecker.Tc.fst"
let _68_1851 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(
# 1269 "FStar.TypeChecker.Tc.fst"
let g1 = (let _157_686 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _157_686 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1270 "FStar.TypeChecker.Tc.fst"
let _68_1846 = (let _157_690 = (let _157_689 = (let _157_688 = (let _157_687 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _157_687))
in (_157_688)::[])
in (FStar_TypeChecker_Util.generalize env _157_689))
in (FStar_List.hd _157_690))
in (match (_68_1846) with
| (_68_1842, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_68_1851) with
| (g1, e1, univ_vars, c1) -> begin
(
# 1274 "FStar.TypeChecker.Tc.fst"
let _68_1861 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(
# 1276 "FStar.TypeChecker.Tc.fst"
let _68_1854 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_68_1854) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(
# 1279 "FStar.TypeChecker.Tc.fst"
let _68_1855 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _157_691 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _157_691 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _157_692 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_157_692, c1)))
end
end))
end else begin
(
# 1283 "FStar.TypeChecker.Tc.fst"
let _68_1857 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _157_693 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _157_693)))
end
in (match (_68_1861) with
| (e2, c1) -> begin
(
# 1288 "FStar.TypeChecker.Tc.fst"
let cres = (let _157_694 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _157_694))
in (
# 1289 "FStar.TypeChecker.Tc.fst"
let _68_1863 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1291 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _157_695 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_157_695, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _68_1867 -> begin
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
let _68_1878 = env
in {FStar_TypeChecker_Env.solver = _68_1878.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_1878.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_1878.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_1878.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_1878.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_1878.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_1878.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_1878.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_1878.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_1878.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_1878.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_1878.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_1878.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _68_1878.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_1878.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_1878.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_1878.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _68_1878.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_1878.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_1878.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 1312 "FStar.TypeChecker.Tc.fst"
let _68_1887 = (let _157_699 = (let _157_698 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _157_698 Prims.fst))
in (check_let_bound_def false _157_699 lb))
in (match (_68_1887) with
| (e1, _68_1883, c1, g1, annotated) -> begin
(
# 1313 "FStar.TypeChecker.Tc.fst"
let x = (
# 1313 "FStar.TypeChecker.Tc.fst"
let _68_1888 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _68_1888.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_1888.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (
# 1314 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (
# 1315 "FStar.TypeChecker.Tc.fst"
let _68_1894 = (let _157_701 = (let _157_700 = (FStar_Syntax_Syntax.mk_binder x)
in (_157_700)::[])
in (FStar_Syntax_Subst.open_term _157_701 e2))
in (match (_68_1894) with
| (xb, e2) -> begin
(
# 1316 "FStar.TypeChecker.Tc.fst"
let xbinder = (FStar_List.hd xb)
in (
# 1317 "FStar.TypeChecker.Tc.fst"
let x = (Prims.fst xbinder)
in (
# 1318 "FStar.TypeChecker.Tc.fst"
let _68_1900 = (let _157_702 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _157_702 e2))
in (match (_68_1900) with
| (e2, c2, g2) -> begin
(
# 1319 "FStar.TypeChecker.Tc.fst"
let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (x), c2))
in (
# 1320 "FStar.TypeChecker.Tc.fst"
let e = (let _157_705 = (let _157_704 = (let _157_703 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _157_703))
in FStar_Syntax_Syntax.Tm_let (_157_704))
in (FStar_Syntax_Syntax.mk _157_705 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (
# 1321 "FStar.TypeChecker.Tc.fst"
let x_eq_e1 = (let _157_708 = (let _157_707 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _157_707 e1))
in (FStar_All.pipe_left (fun _157_706 -> FStar_TypeChecker_Common.NonTrivial (_157_706)) _157_708))
in (
# 1322 "FStar.TypeChecker.Tc.fst"
let g2 = (let _157_710 = (let _157_709 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _157_709 g2))
in (FStar_TypeChecker_Rel.close_guard xb _157_710))
in (
# 1324 "FStar.TypeChecker.Tc.fst"
let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if annotated then begin
(e, cres, guard)
end else begin
(
# 1328 "FStar.TypeChecker.Tc.fst"
let _68_1906 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end)))))
end))))
end))))
end)))
end
| _68_1909 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1337 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1340 "FStar.TypeChecker.Tc.fst"
let _68_1921 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_68_1921) with
| (lbs, e2) -> begin
(
# 1342 "FStar.TypeChecker.Tc.fst"
let _68_1924 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_68_1924) with
| (env0, topt) -> begin
(
# 1343 "FStar.TypeChecker.Tc.fst"
let _68_1927 = (build_let_rec_env true env0 lbs)
in (match (_68_1927) with
| (lbs, rec_env) -> begin
(
# 1344 "FStar.TypeChecker.Tc.fst"
let _68_1930 = (check_let_recs rec_env lbs)
in (match (_68_1930) with
| (lbs, g_lbs) -> begin
(
# 1345 "FStar.TypeChecker.Tc.fst"
let g_lbs = (let _157_713 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _157_713 FStar_TypeChecker_Rel.resolve_implicits))
in (
# 1347 "FStar.TypeChecker.Tc.fst"
let all_lb_names = (let _157_716 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _157_716 (fun _157_715 -> Some (_157_715))))
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
let ecs = (let _157_720 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _157_719 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _157_719)))))
in (FStar_TypeChecker_Util.generalize env _157_720))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _68_1941 -> (match (_68_1941) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (
# 1362 "FStar.TypeChecker.Tc.fst"
let cres = (let _157_722 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _157_722))
in (
# 1363 "FStar.TypeChecker.Tc.fst"
let _68_1944 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (
# 1365 "FStar.TypeChecker.Tc.fst"
let _68_1948 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_68_1948) with
| (lbs, e2) -> begin
(let _157_724 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _157_723 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_157_724, cres, _157_723)))
end)))))))
end))
end))
end))
end))
end
| _68_1950 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (
# 1376 "FStar.TypeChecker.Tc.fst"
let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(
# 1379 "FStar.TypeChecker.Tc.fst"
let _68_1962 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_68_1962) with
| (lbs, e2) -> begin
(
# 1381 "FStar.TypeChecker.Tc.fst"
let _68_1965 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_68_1965) with
| (env0, topt) -> begin
(
# 1382 "FStar.TypeChecker.Tc.fst"
let _68_1968 = (build_let_rec_env false env0 lbs)
in (match (_68_1968) with
| (lbs, rec_env) -> begin
(
# 1383 "FStar.TypeChecker.Tc.fst"
let _68_1971 = (check_let_recs rec_env lbs)
in (match (_68_1971) with
| (lbs, g_lbs) -> begin
(
# 1385 "FStar.TypeChecker.Tc.fst"
let _68_1983 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (
# 1386 "FStar.TypeChecker.Tc.fst"
let x = (
# 1386 "FStar.TypeChecker.Tc.fst"
let _68_1974 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _68_1974.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_1974.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (
# 1387 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1387 "FStar.TypeChecker.Tc.fst"
let _68_1977 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _68_1977.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _68_1977.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _68_1977.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _68_1977.FStar_Syntax_Syntax.lbdef})
in (
# 1388 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], lb.FStar_Syntax_Syntax.lbtyp))
in (env, lb))))) env))
in (match (_68_1983) with
| (env, lbs) -> begin
(
# 1391 "FStar.TypeChecker.Tc.fst"
let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (
# 1393 "FStar.TypeChecker.Tc.fst"
let _68_1989 = (tc_term env e2)
in (match (_68_1989) with
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
let _68_1993 = cres
in {FStar_Syntax_Syntax.eff_name = _68_1993.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _68_1993.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _68_1993.FStar_Syntax_Syntax.comp})
in (
# 1399 "FStar.TypeChecker.Tc.fst"
let _68_1998 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_68_1998) with
| (lbs, e2) -> begin
(
# 1400 "FStar.TypeChecker.Tc.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_68_2001) -> begin
(e, cres, guard)
end
| None -> begin
(
# 1404 "FStar.TypeChecker.Tc.fst"
let _68_2004 = (check_no_escape None env bvs tres)
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
| _68_2007 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (
# 1415 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1416 "FStar.TypeChecker.Tc.fst"
let _68_2040 = (FStar_List.fold_left (fun _68_2014 lb -> (match (_68_2014) with
| (lbs, env) -> begin
(
# 1417 "FStar.TypeChecker.Tc.fst"
let _68_2019 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_68_2019) with
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
let _68_2028 = (let _157_736 = (let _157_735 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _157_735))
in (tc_check_tot_or_gtot_term (
# 1425 "FStar.TypeChecker.Tc.fst"
let _68_2022 = env0
in {FStar_TypeChecker_Env.solver = _68_2022.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_2022.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_2022.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_2022.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_2022.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_2022.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_2022.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_2022.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_2022.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_2022.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_2022.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_2022.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_2022.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _68_2022.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _68_2022.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_2022.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_2022.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _68_2022.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_2022.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_2022.FStar_TypeChecker_Env.use_bv_sorts}) t _157_736))
in (match (_68_2028) with
| (t, _68_2026, g) -> begin
(
# 1426 "FStar.TypeChecker.Tc.fst"
let _68_2029 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (
# 1428 "FStar.TypeChecker.Tc.fst"
let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(
# 1430 "FStar.TypeChecker.Tc.fst"
let _68_2032 = env
in {FStar_TypeChecker_Env.solver = _68_2032.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_2032.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_2032.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_2032.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_2032.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_2032.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_2032.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_2032.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_2032.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_2032.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_2032.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_2032.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _68_2032.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _68_2032.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_2032.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_2032.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_2032.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _68_2032.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_2032.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_2032.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (
# 1432 "FStar.TypeChecker.Tc.fst"
let lb = (
# 1432 "FStar.TypeChecker.Tc.fst"
let _68_2035 = lb
in {FStar_Syntax_Syntax.lbname = _68_2035.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _68_2035.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_68_2040) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (
# 1439 "FStar.TypeChecker.Tc.fst"
let _68_2053 = (let _157_741 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 1440 "FStar.TypeChecker.Tc.fst"
let _68_2047 = (let _157_740 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _157_740 lb.FStar_Syntax_Syntax.lbdef))
in (match (_68_2047) with
| (e, c, g) -> begin
(
# 1441 "FStar.TypeChecker.Tc.fst"
let _68_2048 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1443 "FStar.TypeChecker.Tc.fst"
let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _157_741 FStar_List.unzip))
in (match (_68_2053) with
| (lbs, gs) -> begin
(
# 1445 "FStar.TypeChecker.Tc.fst"
let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (
# 1459 "FStar.TypeChecker.Tc.fst"
let _68_2061 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_68_2061) with
| (env1, _68_2060) -> begin
(
# 1460 "FStar.TypeChecker.Tc.fst"
let e1 = lb.FStar_Syntax_Syntax.lbdef
in (
# 1463 "FStar.TypeChecker.Tc.fst"
let _68_2067 = (check_lbtyp top_level env lb)
in (match (_68_2067) with
| (topt, wf_annot, univ_vars, env1) -> begin
(
# 1465 "FStar.TypeChecker.Tc.fst"
let _68_2068 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (
# 1469 "FStar.TypeChecker.Tc.fst"
let _68_2075 = (tc_maybe_toplevel_term (
# 1469 "FStar.TypeChecker.Tc.fst"
let _68_2070 = env1
in {FStar_TypeChecker_Env.solver = _68_2070.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_2070.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_2070.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_2070.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_2070.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_2070.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_2070.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_2070.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_2070.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_2070.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_2070.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_2070.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_2070.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _68_2070.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_2070.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_2070.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_2070.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _68_2070.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_2070.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_2070.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_68_2075) with
| (e1, c1, g1) -> begin
(
# 1472 "FStar.TypeChecker.Tc.fst"
let _68_2079 = (let _157_748 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _68_2076 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _157_748 e1 c1 wf_annot))
in (match (_68_2079) with
| (c1, guard_f) -> begin
(
# 1475 "FStar.TypeChecker.Tc.fst"
let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (
# 1477 "FStar.TypeChecker.Tc.fst"
let _68_2081 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _157_749 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _157_749))
end else begin
()
end
in (let _157_750 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _157_750))))
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
let _68_2088 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _68_2091 -> begin
(
# 1496 "FStar.TypeChecker.Tc.fst"
let _68_2094 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_68_2094) with
| (univ_vars, t) -> begin
(
# 1497 "FStar.TypeChecker.Tc.fst"
let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _157_754 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _157_754))
end else begin
(
# 1504 "FStar.TypeChecker.Tc.fst"
let _68_2099 = (FStar_Syntax_Util.type_u ())
in (match (_68_2099) with
| (k, _68_2098) -> begin
(
# 1505 "FStar.TypeChecker.Tc.fst"
let _68_2104 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_68_2104) with
| (t, _68_2102, g) -> begin
(
# 1506 "FStar.TypeChecker.Tc.fst"
let _68_2105 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _157_757 = (let _157_755 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _157_755))
in (let _157_756 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _157_757 _157_756)))
end else begin
()
end
in (
# 1510 "FStar.TypeChecker.Tc.fst"
let t = (norm env1 t)
in (let _157_758 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _157_758))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _68_2111 -> (match (_68_2111) with
| (x, imp) -> begin
(
# 1515 "FStar.TypeChecker.Tc.fst"
let _68_2114 = (FStar_Syntax_Util.type_u ())
in (match (_68_2114) with
| (tu, u) -> begin
(
# 1516 "FStar.TypeChecker.Tc.fst"
let _68_2119 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_68_2119) with
| (t, _68_2117, g) -> begin
(
# 1517 "FStar.TypeChecker.Tc.fst"
let x = ((
# 1517 "FStar.TypeChecker.Tc.fst"
let _68_2120 = x
in {FStar_Syntax_Syntax.ppname = _68_2120.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_2120.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (
# 1518 "FStar.TypeChecker.Tc.fst"
let _68_2123 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_762 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _157_761 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _157_762 _157_761)))
end else begin
()
end
in (let _157_763 = (maybe_push_binding env x)
in (x, _157_763, g, u))))
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
let _68_2138 = (tc_binder env b)
in (match (_68_2138) with
| (b, env', g, u) -> begin
(
# 1527 "FStar.TypeChecker.Tc.fst"
let _68_2143 = (aux env' bs)
in (match (_68_2143) with
| (bs, env', g', us) -> begin
(let _157_771 = (let _157_770 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _157_770))
in ((b)::bs, env', _157_771, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (
# 1532 "FStar.TypeChecker.Tc.fst"
let tc_args = (fun env args -> (FStar_List.fold_right (fun _68_2151 _68_2154 -> (match ((_68_2151, _68_2154)) with
| ((t, imp), (args, g)) -> begin
(
# 1536 "FStar.TypeChecker.Tc.fst"
let _68_2159 = (tc_term env t)
in (match (_68_2159) with
| (t, _68_2157, g') -> begin
(let _157_780 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _157_780))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _68_2163 -> (match (_68_2163) with
| (pats, g) -> begin
(
# 1539 "FStar.TypeChecker.Tc.fst"
let _68_2166 = (tc_args env p)
in (match (_68_2166) with
| (args, g') -> begin
(let _157_783 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _157_783))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 1544 "FStar.TypeChecker.Tc.fst"
let _68_2172 = (tc_maybe_toplevel_term env e)
in (match (_68_2172) with
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
let _68_2175 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_786 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _157_786))
end else begin
()
end
in (
# 1550 "FStar.TypeChecker.Tc.fst"
let c = (norm_c env c)
in (
# 1551 "FStar.TypeChecker.Tc.fst"
let _68_2180 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _157_787 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_157_787, false))
end else begin
(let _157_788 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_157_788, true))
end
in (match (_68_2180) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _157_789 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _157_789))
end
| _68_2184 -> begin
if allow_ghost then begin
(let _157_792 = (let _157_791 = (let _157_790 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_157_790, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_157_791))
in (Prims.raise _157_792))
end else begin
(let _157_795 = (let _157_794 = (let _157_793 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_157_793, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_157_794))
in (Prims.raise _157_795))
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
let _68_2194 = (tc_tot_or_gtot_term env t)
in (match (_68_2194) with
| (t, c, g) -> begin
(
# 1571 "FStar.TypeChecker.Tc.fst"
let _68_2195 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))

# 1574 "FStar.TypeChecker.Tc.fst"
let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (
# 1575 "FStar.TypeChecker.Tc.fst"
let _68_2203 = (tc_check_tot_or_gtot_term env t k)
in (match (_68_2203) with
| (t, c, g) -> begin
(
# 1576 "FStar.TypeChecker.Tc.fst"
let _68_2204 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))

# 1579 "FStar.TypeChecker.Tc.fst"
let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _157_815 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _157_815)))

# 1582 "FStar.TypeChecker.Tc.fst"
let check_nogen = (fun env t k -> (
# 1583 "FStar.TypeChecker.Tc.fst"
let t = (tc_check_trivial_guard env t k)
in (let _157_819 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _157_819))))

# 1586 "FStar.TypeChecker.Tc.fst"
let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (
# 1587 "FStar.TypeChecker.Tc.fst"
let _68_2219 = (tc_binders env tps)
in (match (_68_2219) with
| (tps, env, g, us) -> begin
(
# 1588 "FStar.TypeChecker.Tc.fst"
let _68_2220 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))

# 1591 "FStar.TypeChecker.Tc.fst"
let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (
# 1592 "FStar.TypeChecker.Tc.fst"
let fail = (fun _68_2226 -> (match (()) with
| () -> begin
(let _157_834 = (let _157_833 = (let _157_832 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_157_832, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_157_833))
in (Prims.raise _157_834))
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
| (a, _68_2243)::(wp, _68_2239)::(_wlp, _68_2235)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _68_2247 -> begin
(fail ())
end))
end
| _68_2249 -> begin
(fail ())
end))))

# 1603 "FStar.TypeChecker.Tc.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 1606 "FStar.TypeChecker.Tc.fst"
let _68_2256 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_68_2256) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _68_2258 -> begin
(
# 1609 "FStar.TypeChecker.Tc.fst"
let t' = (FStar_Syntax_Util.arrow binders c)
in (
# 1610 "FStar.TypeChecker.Tc.fst"
let _68_2262 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_68_2262) with
| (uvs, t') -> begin
(match ((let _157_841 = (FStar_Syntax_Subst.compress t')
in _157_841.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _68_2268 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 1615 "FStar.TypeChecker.Tc.fst"
let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (
# 1616 "FStar.TypeChecker.Tc.fst"
let fail = (fun t -> (let _157_852 = (let _157_851 = (let _157_850 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_157_850, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_157_851))
in (Prims.raise _157_852)))
in (match ((let _157_853 = (FStar_Syntax_Subst.compress signature)
in _157_853.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 1619 "FStar.TypeChecker.Tc.fst"
let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _68_2289)::(wp, _68_2285)::(_wlp, _68_2281)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _68_2293 -> begin
(fail signature)
end))
end
| _68_2295 -> begin
(fail signature)
end)))

# 1626 "FStar.TypeChecker.Tc.fst"
let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (
# 1627 "FStar.TypeChecker.Tc.fst"
let _68_2300 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_68_2300) with
| (a, wp) -> begin
(
# 1628 "FStar.TypeChecker.Tc.fst"
let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _68_2303 -> begin
(
# 1632 "FStar.TypeChecker.Tc.fst"
let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (
# 1633 "FStar.TypeChecker.Tc.fst"
let op = (fun ts -> (
# 1634 "FStar.TypeChecker.Tc.fst"
let _68_2307 = ()
in (
# 1635 "FStar.TypeChecker.Tc.fst"
let t0 = (Prims.snd ts)
in (
# 1636 "FStar.TypeChecker.Tc.fst"
let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (
# 1638 "FStar.TypeChecker.Tc.fst"
let _68_2311 = ed
in (let _157_872 = (op ed.FStar_Syntax_Syntax.ret)
in (let _157_871 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _157_870 = (op ed.FStar_Syntax_Syntax.bind_wlp)
in (let _157_869 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _157_868 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _157_867 = (op ed.FStar_Syntax_Syntax.ite_wlp)
in (let _157_866 = (op ed.FStar_Syntax_Syntax.wp_binop)
in (let _157_865 = (op ed.FStar_Syntax_Syntax.wp_as_type)
in (let _157_864 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _157_863 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _157_862 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _157_861 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _157_860 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _68_2311.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _68_2311.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _68_2311.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _68_2311.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _68_2311.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _157_872; FStar_Syntax_Syntax.bind_wp = _157_871; FStar_Syntax_Syntax.bind_wlp = _157_870; FStar_Syntax_Syntax.if_then_else = _157_869; FStar_Syntax_Syntax.ite_wp = _157_868; FStar_Syntax_Syntax.ite_wlp = _157_867; FStar_Syntax_Syntax.wp_binop = _157_866; FStar_Syntax_Syntax.wp_as_type = _157_865; FStar_Syntax_Syntax.close_wp = _157_864; FStar_Syntax_Syntax.assert_p = _157_863; FStar_Syntax_Syntax.assume_p = _157_862; FStar_Syntax_Syntax.null_wp = _157_861; FStar_Syntax_Syntax.trivial = _157_860}))))))))))))))))
end)
in (ed, a, wp))
end)))

# 1654 "FStar.TypeChecker.Tc.fst"
let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (
# 1655 "FStar.TypeChecker.Tc.fst"
let _68_2316 = ()
in (
# 1656 "FStar.TypeChecker.Tc.fst"
let _68_2320 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_68_2320) with
| (binders_un, signature_un) -> begin
(
# 1657 "FStar.TypeChecker.Tc.fst"
let _68_2325 = (tc_tparams env0 binders_un)
in (match (_68_2325) with
| (binders, env, _68_2324) -> begin
(
# 1658 "FStar.TypeChecker.Tc.fst"
let _68_2329 = (tc_trivial_guard env signature_un)
in (match (_68_2329) with
| (signature, _68_2328) -> begin
(
# 1659 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1659 "FStar.TypeChecker.Tc.fst"
let _68_2330 = ed
in {FStar_Syntax_Syntax.qualifiers = _68_2330.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _68_2330.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _68_2330.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _68_2330.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _68_2330.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _68_2330.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = _68_2330.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _68_2330.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _68_2330.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = _68_2330.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _68_2330.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _68_2330.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _68_2330.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _68_2330.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _68_2330.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _68_2330.FStar_Syntax_Syntax.trivial})
in (
# 1662 "FStar.TypeChecker.Tc.fst"
let _68_2336 = (open_effect_decl env ed)
in (match (_68_2336) with
| (ed, a, wp_a) -> begin
(
# 1663 "FStar.TypeChecker.Tc.fst"
let get_effect_signature = (fun _68_2338 -> (match (()) with
| () -> begin
(
# 1664 "FStar.TypeChecker.Tc.fst"
let _68_2342 = (tc_trivial_guard env signature_un)
in (match (_68_2342) with
| (signature, _68_2341) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (
# 1668 "FStar.TypeChecker.Tc.fst"
let env = (let _157_879 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _157_879))
in (
# 1670 "FStar.TypeChecker.Tc.fst"
let _68_2344 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _157_882 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _157_881 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _157_880 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checked effect signature: %s %s : %s\n" _157_882 _157_881 _157_880))))
end else begin
()
end
in (
# 1676 "FStar.TypeChecker.Tc.fst"
let check_and_gen' = (fun env _68_2351 k -> (match (_68_2351) with
| (_68_2349, t) -> begin
(check_and_gen env t k)
end))
in (
# 1679 "FStar.TypeChecker.Tc.fst"
let ret = (
# 1680 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _157_894 = (let _157_892 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_891 = (let _157_890 = (let _157_889 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _157_889))
in (_157_890)::[])
in (_157_892)::_157_891))
in (let _157_893 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _157_894 _157_893)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (
# 1683 "FStar.TypeChecker.Tc.fst"
let bind_wp = (
# 1684 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1685 "FStar.TypeChecker.Tc.fst"
let _68_2358 = (get_effect_signature ())
in (match (_68_2358) with
| (b, wp_b) -> begin
(
# 1686 "FStar.TypeChecker.Tc.fst"
let a_wp_b = (let _157_898 = (let _157_896 = (let _157_895 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _157_895))
in (_157_896)::[])
in (let _157_897 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _157_898 _157_897)))
in (
# 1687 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = a_wp_b
in (
# 1688 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _157_911 = (let _157_909 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_908 = (let _157_907 = (FStar_Syntax_Syntax.mk_binder b)
in (let _157_906 = (let _157_905 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _157_904 = (let _157_903 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _157_902 = (let _157_901 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (let _157_900 = (let _157_899 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_157_899)::[])
in (_157_901)::_157_900))
in (_157_903)::_157_902))
in (_157_905)::_157_904))
in (_157_907)::_157_906))
in (_157_909)::_157_908))
in (let _157_910 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _157_911 _157_910)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k))))
end)))
in (
# 1694 "FStar.TypeChecker.Tc.fst"
let bind_wlp = (
# 1695 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1696 "FStar.TypeChecker.Tc.fst"
let _68_2366 = (get_effect_signature ())
in (match (_68_2366) with
| (b, wlp_b) -> begin
(
# 1697 "FStar.TypeChecker.Tc.fst"
let a_wlp_b = (let _157_915 = (let _157_913 = (let _157_912 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _157_912))
in (_157_913)::[])
in (let _157_914 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _157_915 _157_914)))
in (
# 1698 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _157_924 = (let _157_922 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_921 = (let _157_920 = (FStar_Syntax_Syntax.mk_binder b)
in (let _157_919 = (let _157_918 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _157_917 = (let _157_916 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_157_916)::[])
in (_157_918)::_157_917))
in (_157_920)::_157_919))
in (_157_922)::_157_921))
in (let _157_923 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _157_924 _157_923)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wlp expected_k)))
end)))
in (
# 1704 "FStar.TypeChecker.Tc.fst"
let if_then_else = (
# 1705 "FStar.TypeChecker.Tc.fst"
let p = (let _157_926 = (let _157_925 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _157_925 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _157_926))
in (
# 1706 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _157_935 = (let _157_933 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_932 = (let _157_931 = (FStar_Syntax_Syntax.mk_binder p)
in (let _157_930 = (let _157_929 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _157_928 = (let _157_927 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_157_927)::[])
in (_157_929)::_157_928))
in (_157_931)::_157_930))
in (_157_933)::_157_932))
in (let _157_934 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _157_935 _157_934)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (
# 1712 "FStar.TypeChecker.Tc.fst"
let ite_wp = (
# 1713 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1714 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _157_942 = (let _157_940 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_939 = (let _157_938 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _157_937 = (let _157_936 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_157_936)::[])
in (_157_938)::_157_937))
in (_157_940)::_157_939))
in (let _157_941 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _157_942 _157_941)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k)))
in (
# 1720 "FStar.TypeChecker.Tc.fst"
let ite_wlp = (
# 1721 "FStar.TypeChecker.Tc.fst"
let wlp_a = wp_a
in (
# 1722 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _157_947 = (let _157_945 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_944 = (let _157_943 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (_157_943)::[])
in (_157_945)::_157_944))
in (let _157_946 = (FStar_Syntax_Syntax.mk_Total wlp_a)
in (FStar_Syntax_Util.arrow _157_947 _157_946)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wlp expected_k)))
in (
# 1727 "FStar.TypeChecker.Tc.fst"
let wp_binop = (
# 1728 "FStar.TypeChecker.Tc.fst"
let bin_op = (
# 1729 "FStar.TypeChecker.Tc.fst"
let _68_2381 = (FStar_Syntax_Util.type_u ())
in (match (_68_2381) with
| (t1, u1) -> begin
(
# 1730 "FStar.TypeChecker.Tc.fst"
let _68_2384 = (FStar_Syntax_Util.type_u ())
in (match (_68_2384) with
| (t2, u2) -> begin
(
# 1731 "FStar.TypeChecker.Tc.fst"
let t = (let _157_948 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_max ((u1)::(u2)::[]))) None _157_948))
in (let _157_953 = (let _157_951 = (FStar_Syntax_Syntax.null_binder t1)
in (let _157_950 = (let _157_949 = (FStar_Syntax_Syntax.null_binder t2)
in (_157_949)::[])
in (_157_951)::_157_950))
in (let _157_952 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _157_953 _157_952))))
end))
end))
in (
# 1733 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _157_962 = (let _157_960 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_959 = (let _157_958 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _157_957 = (let _157_956 = (FStar_Syntax_Syntax.null_binder bin_op)
in (let _157_955 = (let _157_954 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_157_954)::[])
in (_157_956)::_157_955))
in (_157_958)::_157_957))
in (_157_960)::_157_959))
in (let _157_961 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _157_962 _157_961)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_binop expected_k)))
in (
# 1740 "FStar.TypeChecker.Tc.fst"
let wp_as_type = (
# 1741 "FStar.TypeChecker.Tc.fst"
let _68_2392 = (FStar_Syntax_Util.type_u ())
in (match (_68_2392) with
| (t, _68_2391) -> begin
(
# 1742 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _157_967 = (let _157_965 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_964 = (let _157_963 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_157_963)::[])
in (_157_965)::_157_964))
in (let _157_966 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _157_967 _157_966)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (
# 1747 "FStar.TypeChecker.Tc.fst"
let close_wp = (
# 1748 "FStar.TypeChecker.Tc.fst"
let b = (let _157_969 = (let _157_968 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _157_968 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _157_969))
in (
# 1749 "FStar.TypeChecker.Tc.fst"
let b_wp_a = (let _157_973 = (let _157_971 = (let _157_970 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _157_970))
in (_157_971)::[])
in (let _157_972 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _157_973 _157_972)))
in (
# 1750 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _157_980 = (let _157_978 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_977 = (let _157_976 = (FStar_Syntax_Syntax.mk_binder b)
in (let _157_975 = (let _157_974 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_157_974)::[])
in (_157_976)::_157_975))
in (_157_978)::_157_977))
in (let _157_979 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _157_980 _157_979)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (
# 1754 "FStar.TypeChecker.Tc.fst"
let assert_p = (
# 1755 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _157_989 = (let _157_987 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_986 = (let _157_985 = (let _157_982 = (let _157_981 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _157_981 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _157_982))
in (let _157_984 = (let _157_983 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_157_983)::[])
in (_157_985)::_157_984))
in (_157_987)::_157_986))
in (let _157_988 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _157_989 _157_988)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (
# 1761 "FStar.TypeChecker.Tc.fst"
let assume_p = (
# 1762 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _157_998 = (let _157_996 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_995 = (let _157_994 = (let _157_991 = (let _157_990 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _157_990 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _157_991))
in (let _157_993 = (let _157_992 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_157_992)::[])
in (_157_994)::_157_993))
in (_157_996)::_157_995))
in (let _157_997 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _157_998 _157_997)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (
# 1768 "FStar.TypeChecker.Tc.fst"
let null_wp = (
# 1769 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _157_1001 = (let _157_999 = (FStar_Syntax_Syntax.mk_binder a)
in (_157_999)::[])
in (let _157_1000 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _157_1001 _157_1000)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (
# 1773 "FStar.TypeChecker.Tc.fst"
let trivial_wp = (
# 1774 "FStar.TypeChecker.Tc.fst"
let _68_2408 = (FStar_Syntax_Util.type_u ())
in (match (_68_2408) with
| (t, _68_2407) -> begin
(
# 1775 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _157_1006 = (let _157_1004 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_1003 = (let _157_1002 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_157_1002)::[])
in (_157_1004)::_157_1003))
in (let _157_1005 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _157_1006 _157_1005)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (
# 1781 "FStar.TypeChecker.Tc.fst"
let t = (let _157_1007 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _157_1007))
in (
# 1782 "FStar.TypeChecker.Tc.fst"
let _68_2414 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_68_2414) with
| (univs, t) -> begin
(
# 1783 "FStar.TypeChecker.Tc.fst"
let _68_2430 = (match ((let _157_1009 = (let _157_1008 = (FStar_Syntax_Subst.compress t)
in _157_1008.FStar_Syntax_Syntax.n)
in (binders, _157_1009))) with
| ([], _68_2417) -> begin
([], t)
end
| (_68_2420, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _68_2427 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_68_2430) with
| (binders, signature) -> begin
(
# 1787 "FStar.TypeChecker.Tc.fst"
let close = (fun n ts -> (
# 1788 "FStar.TypeChecker.Tc.fst"
let ts = (let _157_1014 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _157_1014))
in (
# 1789 "FStar.TypeChecker.Tc.fst"
let _68_2435 = ()
in ts)))
in (
# 1791 "FStar.TypeChecker.Tc.fst"
let ed = (
# 1791 "FStar.TypeChecker.Tc.fst"
let _68_2437 = ed
in (let _157_1027 = (close 0 ret)
in (let _157_1026 = (close 1 bind_wp)
in (let _157_1025 = (close 1 bind_wlp)
in (let _157_1024 = (close 0 if_then_else)
in (let _157_1023 = (close 0 ite_wp)
in (let _157_1022 = (close 0 ite_wlp)
in (let _157_1021 = (close 0 wp_binop)
in (let _157_1020 = (close 0 wp_as_type)
in (let _157_1019 = (close 1 close_wp)
in (let _157_1018 = (close 0 assert_p)
in (let _157_1017 = (close 0 assume_p)
in (let _157_1016 = (close 0 null_wp)
in (let _157_1015 = (close 0 trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _68_2437.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _68_2437.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _157_1027; FStar_Syntax_Syntax.bind_wp = _157_1026; FStar_Syntax_Syntax.bind_wlp = _157_1025; FStar_Syntax_Syntax.if_then_else = _157_1024; FStar_Syntax_Syntax.ite_wp = _157_1023; FStar_Syntax_Syntax.ite_wlp = _157_1022; FStar_Syntax_Syntax.wp_binop = _157_1021; FStar_Syntax_Syntax.wp_as_type = _157_1020; FStar_Syntax_Syntax.close_wp = _157_1019; FStar_Syntax_Syntax.assert_p = _157_1018; FStar_Syntax_Syntax.assume_p = _157_1017; FStar_Syntax_Syntax.null_wp = _157_1016; FStar_Syntax_Syntax.trivial = _157_1015}))))))))))))))
in (
# 1809 "FStar.TypeChecker.Tc.fst"
let _68_2440 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_1028 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _157_1028))
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
let _68_2446 = ()
in (
# 1821 "FStar.TypeChecker.Tc.fst"
let _68_2454 = ()
in (match (ses) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _68_2483, _68_2485, [], r)::FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _68_2474, r1)::FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _68_2463, r2)::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
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
let lex_top_t = (let _157_1036 = (let _157_1035 = (let _157_1034 = (let _157_1033 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _157_1033 FStar_Syntax_Syntax.Delta_constant None))
in (_157_1034, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_157_1035))
in (FStar_Syntax_Syntax.mk _157_1036 None r1))
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
let a = (let _157_1037 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _157_1037))
in (
# 1850 "FStar.TypeChecker.Tc.fst"
let hd = (let _157_1038 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _157_1038))
in (
# 1851 "FStar.TypeChecker.Tc.fst"
let tl = (let _157_1043 = (let _157_1042 = (let _157_1041 = (let _157_1040 = (let _157_1039 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _157_1039 FStar_Syntax_Syntax.Delta_constant None))
in (_157_1040, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_157_1041))
in (FStar_Syntax_Syntax.mk _157_1042 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _157_1043))
in (
# 1852 "FStar.TypeChecker.Tc.fst"
let res = (let _157_1047 = (let _157_1046 = (let _157_1045 = (let _157_1044 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _157_1044 FStar_Syntax_Syntax.Delta_constant None))
in (_157_1045, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_157_1046))
in (FStar_Syntax_Syntax.mk _157_1047 None r2))
in (let _157_1048 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _157_1048))))))
in (
# 1854 "FStar.TypeChecker.Tc.fst"
let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (
# 1855 "FStar.TypeChecker.Tc.fst"
let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _157_1050 = (let _157_1049 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _157_1049))
in FStar_Syntax_Syntax.Sig_bundle (_157_1050)))))))))))))))
end
| _68_2509 -> begin
(let _157_1052 = (let _157_1051 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _157_1051))
in (FStar_All.failwith _157_1052))
end))))

# 1861 "FStar.TypeChecker.Tc.fst"
let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (
# 1924 "FStar.TypeChecker.Tc.fst"
let warn_positivity = (fun l r -> (let _157_1066 = (let _157_1065 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _157_1065))
in (FStar_TypeChecker_Errors.diag r _157_1066)))
in (
# 1926 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 1929 "FStar.TypeChecker.Tc.fst"
let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(
# 1934 "FStar.TypeChecker.Tc.fst"
let _68_2531 = ()
in (
# 1935 "FStar.TypeChecker.Tc.fst"
let _68_2533 = (warn_positivity tc r)
in (
# 1936 "FStar.TypeChecker.Tc.fst"
let _68_2537 = (FStar_Syntax_Subst.open_term tps k)
in (match (_68_2537) with
| (tps, k) -> begin
(
# 1937 "FStar.TypeChecker.Tc.fst"
let _68_2541 = (tc_tparams env tps)
in (match (_68_2541) with
| (tps, env_tps, us) -> begin
(
# 1938 "FStar.TypeChecker.Tc.fst"
let _68_2544 = (FStar_Syntax_Util.arrow_formals k)
in (match (_68_2544) with
| (indices, t) -> begin
(
# 1939 "FStar.TypeChecker.Tc.fst"
let _68_2548 = (tc_tparams env_tps indices)
in (match (_68_2548) with
| (indices, env', us') -> begin
(
# 1940 "FStar.TypeChecker.Tc.fst"
let _68_2552 = (tc_trivial_guard env' t)
in (match (_68_2552) with
| (t, _68_2551) -> begin
(
# 1941 "FStar.TypeChecker.Tc.fst"
let k = (let _157_1071 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _157_1071))
in (
# 1942 "FStar.TypeChecker.Tc.fst"
let _68_2556 = (FStar_Syntax_Util.type_u ())
in (match (_68_2556) with
| (t_type, u) -> begin
(
# 1943 "FStar.TypeChecker.Tc.fst"
let _68_2557 = (let _157_1072 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _157_1072))
in (
# 1945 "FStar.TypeChecker.Tc.fst"
let t_tc = (let _157_1073 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _157_1073))
in (
# 1946 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 1947 "FStar.TypeChecker.Tc.fst"
let k = (FStar_Syntax_Subst.close tps k)
in (
# 1948 "FStar.TypeChecker.Tc.fst"
let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _157_1074 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) ([], t_tc))
in (_157_1074, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u)))))))
end)))
end))
end))
end))
end))
end))))
end
| _68_2564 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1955 "FStar.TypeChecker.Tc.fst"
let positive_if_pure = (fun _68_2566 l -> ())
in (
# 1958 "FStar.TypeChecker.Tc.fst"
let tc_data = (fun env tcs _68_6 -> (match (_68_6) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(
# 1960 "FStar.TypeChecker.Tc.fst"
let _68_2583 = ()
in (
# 1962 "FStar.TypeChecker.Tc.fst"
let _68_2618 = (
# 1963 "FStar.TypeChecker.Tc.fst"
let tps_u_opt = (FStar_Util.find_map tcs (fun _68_2587 -> (match (_68_2587) with
| (se, u_tc) -> begin
if (let _157_1087 = (let _157_1086 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _157_1086))
in (FStar_Ident.lid_equals tc_lid _157_1087)) then begin
(
# 1965 "FStar.TypeChecker.Tc.fst"
let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_68_2589, _68_2591, tps, _68_2594, _68_2596, _68_2598, _68_2600, _68_2602) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _68_2608 -> (match (_68_2608) with
| (x, _68_2607) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _68_2610 -> begin
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
in (match (_68_2618) with
| (tps, u_tc) -> begin
(
# 1978 "FStar.TypeChecker.Tc.fst"
let _68_2638 = (match ((let _157_1089 = (FStar_Syntax_Subst.compress t)
in _157_1089.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(
# 1983 "FStar.TypeChecker.Tc.fst"
let _68_2626 = (FStar_Util.first_N ntps bs)
in (match (_68_2626) with
| (_68_2624, bs') -> begin
(
# 1984 "FStar.TypeChecker.Tc.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (
# 1985 "FStar.TypeChecker.Tc.fst"
let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _68_2632 -> (match (_68_2632) with
| (x, _68_2631) -> begin
FStar_Syntax_Syntax.DB (((ntps - (1 + i)), x))
end))))
in (let _157_1092 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _157_1092))))
end))
end
| _68_2635 -> begin
([], t)
end)
in (match (_68_2638) with
| (arguments, result) -> begin
(
# 1989 "FStar.TypeChecker.Tc.fst"
let _68_2639 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_1095 = (FStar_Syntax_Print.lid_to_string c)
in (let _157_1094 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _157_1093 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _157_1095 _157_1094 _157_1093))))
end else begin
()
end
in (
# 1995 "FStar.TypeChecker.Tc.fst"
let _68_2644 = (tc_tparams env arguments)
in (match (_68_2644) with
| (arguments, env', us) -> begin
(
# 1996 "FStar.TypeChecker.Tc.fst"
let _68_2648 = (tc_trivial_guard env' result)
in (match (_68_2648) with
| (result, _68_2647) -> begin
(
# 1997 "FStar.TypeChecker.Tc.fst"
let _68_2652 = (FStar_Syntax_Util.head_and_args result)
in (match (_68_2652) with
| (head, _68_2651) -> begin
(
# 1998 "FStar.TypeChecker.Tc.fst"
let _68_2657 = (match ((let _157_1096 = (FStar_Syntax_Subst.compress head)
in _157_1096.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _68_2656 -> begin
(let _157_1100 = (let _157_1099 = (let _157_1098 = (let _157_1097 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _157_1097))
in (_157_1098, r))
in FStar_Syntax_Syntax.Error (_157_1099))
in (Prims.raise _157_1100))
end)
in (
# 2001 "FStar.TypeChecker.Tc.fst"
let g = (FStar_List.fold_left2 (fun g _68_2663 u_x -> (match (_68_2663) with
| (x, _68_2662) -> begin
(
# 2002 "FStar.TypeChecker.Tc.fst"
let _68_2665 = ()
in (let _157_1104 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _157_1104)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (
# 2008 "FStar.TypeChecker.Tc.fst"
let t = (let _157_1108 = (let _157_1106 = (FStar_All.pipe_right tps (FStar_List.map (fun _68_2671 -> (match (_68_2671) with
| (x, _68_2670) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _157_1106 arguments))
in (let _157_1107 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _157_1108 _157_1107)))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _68_2674 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 2016 "FStar.TypeChecker.Tc.fst"
let generalize_and_inst_within = (fun env g tcs datas -> (
# 2017 "FStar.TypeChecker.Tc.fst"
let _68_2680 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2018 "FStar.TypeChecker.Tc.fst"
let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _68_7 -> (match (_68_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_68_2684, _68_2686, tps, k, _68_2690, _68_2692, _68_2694, _68_2696) -> begin
(let _157_1119 = (let _157_1118 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _157_1118))
in (FStar_Syntax_Syntax.null_binder _157_1119))
end
| _68_2700 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2021 "FStar.TypeChecker.Tc.fst"
let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _68_8 -> (match (_68_8) with
| FStar_Syntax_Syntax.Sig_datacon (_68_2704, _68_2706, t, _68_2709, _68_2711, _68_2713, _68_2715, _68_2717) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _68_2721 -> begin
(FStar_All.failwith "Impossible")
end))))
in (
# 2024 "FStar.TypeChecker.Tc.fst"
let t = (let _157_1121 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _157_1121))
in (
# 2025 "FStar.TypeChecker.Tc.fst"
let _68_2724 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_1122 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _157_1122))
end else begin
()
end
in (
# 2026 "FStar.TypeChecker.Tc.fst"
let _68_2728 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_68_2728) with
| (uvs, t) -> begin
(
# 2027 "FStar.TypeChecker.Tc.fst"
let _68_2730 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_1126 = (let _157_1124 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _157_1124 (FStar_String.concat ", ")))
in (let _157_1125 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _157_1126 _157_1125)))
end else begin
()
end
in (
# 2030 "FStar.TypeChecker.Tc.fst"
let _68_2734 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_68_2734) with
| (uvs, t) -> begin
(
# 2031 "FStar.TypeChecker.Tc.fst"
let _68_2738 = (FStar_Syntax_Util.arrow_formals t)
in (match (_68_2738) with
| (args, _68_2737) -> begin
(
# 2032 "FStar.TypeChecker.Tc.fst"
let _68_2741 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_68_2741) with
| (tc_types, data_types) -> begin
(
# 2033 "FStar.TypeChecker.Tc.fst"
let tcs = (FStar_List.map2 (fun _68_2745 se -> (match (_68_2745) with
| (x, _68_2744) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _68_2749, tps, _68_2752, mutuals, datas, quals, r) -> begin
(
# 2035 "FStar.TypeChecker.Tc.fst"
let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (
# 2036 "FStar.TypeChecker.Tc.fst"
let _68_2775 = (match ((let _157_1129 = (FStar_Syntax_Subst.compress ty)
in _157_1129.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 2038 "FStar.TypeChecker.Tc.fst"
let _68_2766 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_68_2766) with
| (tps, rest) -> begin
(
# 2039 "FStar.TypeChecker.Tc.fst"
let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _68_2769 -> begin
(let _157_1130 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _157_1130 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _68_2772 -> begin
([], ty)
end)
in (match (_68_2775) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _68_2777 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (
# 2049 "FStar.TypeChecker.Tc.fst"
let datas = (match (uvs) with
| [] -> begin
datas
end
| _68_2781 -> begin
(
# 2052 "FStar.TypeChecker.Tc.fst"
let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _157_1131 -> FStar_Syntax_Syntax.U_name (_157_1131))))
in (
# 2053 "FStar.TypeChecker.Tc.fst"
let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _68_9 -> (match (_68_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _68_2786, _68_2788, _68_2790, _68_2792, _68_2794, _68_2796, _68_2798) -> begin
(tc, uvs_universes)
end
| _68_2802 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _68_2807 d -> (match (_68_2807) with
| (t, _68_2806) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _68_2811, _68_2813, tc, ntps, quals, mutuals, r) -> begin
(
# 2057 "FStar.TypeChecker.Tc.fst"
let ty = (let _157_1135 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _157_1135 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _68_2823 -> begin
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
let _68_2833 = (FStar_All.pipe_right ses (FStar_List.partition (fun _68_10 -> (match (_68_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_68_2827) -> begin
true
end
| _68_2830 -> begin
false
end))))
in (match (_68_2833) with
| (tys, datas) -> begin
(
# 2065 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2068 "FStar.TypeChecker.Tc.fst"
let _68_2850 = (FStar_List.fold_right (fun tc _68_2839 -> (match (_68_2839) with
| (env, all_tcs, g) -> begin
(
# 2069 "FStar.TypeChecker.Tc.fst"
let _68_2843 = (tc_tycon env tc)
in (match (_68_2843) with
| (env, tc, tc_u) -> begin
(
# 2070 "FStar.TypeChecker.Tc.fst"
let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (
# 2071 "FStar.TypeChecker.Tc.fst"
let _68_2845 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_1139 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _157_1139))
end else begin
()
end
in (let _157_1140 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _157_1140))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_68_2850) with
| (env, tcs, g) -> begin
(
# 2078 "FStar.TypeChecker.Tc.fst"
let _68_2860 = (FStar_List.fold_right (fun se _68_2854 -> (match (_68_2854) with
| (datas, g) -> begin
(
# 2079 "FStar.TypeChecker.Tc.fst"
let _68_2857 = (tc_data env tcs se)
in (match (_68_2857) with
| (data, g') -> begin
(let _157_1143 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _157_1143))
end))
end)) datas ([], g))
in (match (_68_2860) with
| (datas, g) -> begin
(
# 2084 "FStar.TypeChecker.Tc.fst"
let _68_2863 = (let _157_1144 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _157_1144 datas))
in (match (_68_2863) with
| (tcs, datas) -> begin
(let _157_1146 = (let _157_1145 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _157_1145))
in FStar_Syntax_Syntax.Sig_bundle (_157_1146))
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
in (let _157_1151 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _157_1151))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(
# 2105 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2106 "FStar.TypeChecker.Tc.fst"
let se = (tc_inductive env ses quals lids)
in (let _157_1152 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _157_1152))))
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
let _68_2901 = (set_options FStar_Options.Set o)
in (se, env))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(
# 2119 "FStar.TypeChecker.Tc.fst"
let _68_2905 = (let _157_1157 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _157_1157 Prims.ignore))
in (
# 2120 "FStar.TypeChecker.Tc.fst"
let _68_2910 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (
# 2123 "FStar.TypeChecker.Tc.fst"
let _68_2912 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
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
let _68_2927 = (let _157_1158 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _157_1158))
in (match (_68_2927) with
| (a, wp_a_src) -> begin
(
# 2135 "FStar.TypeChecker.Tc.fst"
let _68_2930 = (let _157_1159 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _157_1159))
in (match (_68_2930) with
| (b, wp_b_tgt) -> begin
(
# 2136 "FStar.TypeChecker.Tc.fst"
let wp_a_tgt = (let _157_1163 = (let _157_1162 = (let _157_1161 = (let _157_1160 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _157_1160))
in FStar_Syntax_Syntax.NT (_157_1161))
in (_157_1162)::[])
in (FStar_Syntax_Subst.subst _157_1163 wp_b_tgt))
in (
# 2137 "FStar.TypeChecker.Tc.fst"
let expected_k = (let _157_1168 = (let _157_1166 = (FStar_Syntax_Syntax.mk_binder a)
in (let _157_1165 = (let _157_1164 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_157_1164)::[])
in (_157_1166)::_157_1165))
in (let _157_1167 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _157_1168 _157_1167)))
in (
# 2138 "FStar.TypeChecker.Tc.fst"
let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (
# 2139 "FStar.TypeChecker.Tc.fst"
let sub = (
# 2139 "FStar.TypeChecker.Tc.fst"
let _68_2934 = sub
in {FStar_Syntax_Syntax.source = _68_2934.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _68_2934.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
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
let _68_2947 = ()
in (
# 2146 "FStar.TypeChecker.Tc.fst"
let env0 = env
in (
# 2147 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2148 "FStar.TypeChecker.Tc.fst"
let _68_2953 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_68_2953) with
| (tps, c) -> begin
(
# 2149 "FStar.TypeChecker.Tc.fst"
let _68_2957 = (tc_tparams env tps)
in (match (_68_2957) with
| (tps, env, us) -> begin
(
# 2150 "FStar.TypeChecker.Tc.fst"
let _68_2961 = (tc_comp env c)
in (match (_68_2961) with
| (c, u, g) -> begin
(
# 2151 "FStar.TypeChecker.Tc.fst"
let _68_2962 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (
# 2152 "FStar.TypeChecker.Tc.fst"
let tps = (FStar_Syntax_Subst.close_binders tps)
in (
# 2153 "FStar.TypeChecker.Tc.fst"
let c = (FStar_Syntax_Subst.close_comp tps c)
in (
# 2154 "FStar.TypeChecker.Tc.fst"
let _68_2968 = (let _157_1169 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _157_1169))
in (match (_68_2968) with
| (uvs, t) -> begin
(
# 2155 "FStar.TypeChecker.Tc.fst"
let _68_2987 = (match ((let _157_1171 = (let _157_1170 = (FStar_Syntax_Subst.compress t)
in _157_1170.FStar_Syntax_Syntax.n)
in (tps, _157_1171))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_68_2971, c)) -> begin
([], c)
end
| (_68_2977, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _68_2984 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_68_2987) with
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
let _68_2998 = ()
in (
# 2166 "FStar.TypeChecker.Tc.fst"
let k = (let _157_1172 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _157_1172))
in (
# 2167 "FStar.TypeChecker.Tc.fst"
let _68_3003 = (check_and_gen env t k)
in (match (_68_3003) with
| (uvs, t) -> begin
(
# 2168 "FStar.TypeChecker.Tc.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (
# 2169 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(
# 2173 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_range env r)
in (
# 2174 "FStar.TypeChecker.Tc.fst"
let _68_3016 = (FStar_Syntax_Util.type_u ())
in (match (_68_3016) with
| (k, _68_3015) -> begin
(
# 2175 "FStar.TypeChecker.Tc.fst"
let phi = (let _157_1173 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _157_1173 (norm env)))
in (
# 2176 "FStar.TypeChecker.Tc.fst"
let _68_3018 = (FStar_TypeChecker_Util.check_uvars r phi)
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
let _68_3031 = (tc_term env e)
in (match (_68_3031) with
| (e, c, g1) -> begin
(
# 2185 "FStar.TypeChecker.Tc.fst"
let _68_3036 = (let _157_1177 = (let _157_1174 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_157_1174))
in (let _157_1176 = (let _157_1175 = (c.FStar_Syntax_Syntax.comp ())
in (e, _157_1175))
in (check_expected_effect env _157_1177 _157_1176)))
in (match (_68_3036) with
| (e, _68_3034, g) -> begin
(
# 2186 "FStar.TypeChecker.Tc.fst"
let _68_3037 = (let _157_1178 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _157_1178))
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
(let _157_1190 = (let _157_1189 = (let _157_1188 = (let _157_1187 = (FStar_Syntax_Print.lid_to_string l)
in (let _157_1186 = (FStar_Syntax_Print.quals_to_string q)
in (let _157_1185 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _157_1187 _157_1186 _157_1185))))
in (_157_1188, r))
in FStar_Syntax_Syntax.Error (_157_1189))
in (Prims.raise _157_1190))
end
end))
in (
# 2207 "FStar.TypeChecker.Tc.fst"
let _68_3081 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _68_3058 lb -> (match (_68_3058) with
| (gen, lbs, quals_opt) -> begin
(
# 2208 "FStar.TypeChecker.Tc.fst"
let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 2209 "FStar.TypeChecker.Tc.fst"
let _68_3077 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(
# 2213 "FStar.TypeChecker.Tc.fst"
let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (
# 2214 "FStar.TypeChecker.Tc.fst"
let _68_3072 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _68_3071 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _157_1193 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _157_1193, quals_opt))))
end)
in (match (_68_3077) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_68_3081) with
| (should_generalize, lbs', quals_opt) -> begin
(
# 2223 "FStar.TypeChecker.Tc.fst"
let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _68_11 -> (match (_68_11) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _68_3090 -> begin
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
let e = (let _157_1197 = (let _157_1196 = (let _157_1195 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _157_1195))
in FStar_Syntax_Syntax.Tm_let (_157_1196))
in (FStar_Syntax_Syntax.mk _157_1197 None r))
in (
# 2236 "FStar.TypeChecker.Tc.fst"
let _68_3124 = (match ((tc_maybe_toplevel_term (
# 2236 "FStar.TypeChecker.Tc.fst"
let _68_3094 = env
in {FStar_TypeChecker_Env.solver = _68_3094.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_3094.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_3094.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_3094.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_3094.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_3094.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_3094.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_3094.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_3094.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_3094.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_3094.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _68_3094.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _68_3094.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_3094.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_3094.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_3094.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _68_3094.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_3094.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_3094.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _68_3101; FStar_Syntax_Syntax.pos = _68_3099; FStar_Syntax_Syntax.vars = _68_3097}, _68_3108, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(
# 2239 "FStar.TypeChecker.Tc.fst"
let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_68_3112, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _68_3118 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _68_3121 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_68_3124) with
| (se, lbs) -> begin
(
# 2246 "FStar.TypeChecker.Tc.fst"
let _68_3130 = if (log env) then begin
(let _157_1205 = (let _157_1204 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 2248 "FStar.TypeChecker.Tc.fst"
let should_log = (match ((let _157_1201 = (let _157_1200 = (let _157_1199 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _157_1199.FStar_Syntax_Syntax.fv_name)
in _157_1200.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _157_1201))) with
| None -> begin
true
end
| _68_3128 -> begin
false
end)
in if should_log then begin
(let _157_1203 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _157_1202 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _157_1203 _157_1202)))
end else begin
""
end))))
in (FStar_All.pipe_right _157_1204 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _157_1205))
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
let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _68_12 -> (match (_68_12) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _68_3140 -> begin
false
end)))))
in (
# 2284 "FStar.TypeChecker.Tc.fst"
let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _68_3150 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_68_3152) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _68_3163, _68_3165) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _68_3171 -> (match (_68_3171) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _68_3177, _68_3179, quals, r) -> begin
(
# 2298 "FStar.TypeChecker.Tc.fst"
let dec = (let _157_1221 = (let _157_1220 = (let _157_1219 = (let _157_1218 = (let _157_1217 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _157_1217))
in FStar_Syntax_Syntax.Tm_arrow (_157_1218))
in (FStar_Syntax_Syntax.mk _157_1219 None r))
in (l, us, _157_1220, (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_157_1221))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _68_3189, _68_3191, _68_3193, _68_3195, r) -> begin
(
# 2301 "FStar.TypeChecker.Tc.fst"
let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _68_3201 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_68_3203, _68_3205, quals, _68_3208) -> begin
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
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _68_13 -> (match (_68_13) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _68_3227 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_68_3229) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _68_3245, _68_3247, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
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
(let _157_1228 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _157_1227 = (let _157_1226 = (let _157_1225 = (let _157_1224 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _157_1224.FStar_Syntax_Syntax.fv_name)
in _157_1225.FStar_Syntax_Syntax.v)
in (_157_1226, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_157_1227)))))
in (_157_1228, hidden))
end else begin
((se)::[], hidden)
end
end))))

# 2344 "FStar.TypeChecker.Tc.fst"
let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (
# 2345 "FStar.TypeChecker.Tc.fst"
let _68_3286 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _68_3267 se -> (match (_68_3267) with
| (ses, exports, env, hidden) -> begin
(
# 2347 "FStar.TypeChecker.Tc.fst"
let _68_3269 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_1235 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _157_1235))
end else begin
()
end
in (
# 2350 "FStar.TypeChecker.Tc.fst"
let _68_3273 = (tc_decl env se)
in (match (_68_3273) with
| (se, env) -> begin
(
# 2352 "FStar.TypeChecker.Tc.fst"
let _68_3274 = if ((FStar_ST.read FStar_Options.log_types) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _157_1236 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _157_1236))
end else begin
()
end
in (
# 2355 "FStar.TypeChecker.Tc.fst"
let _68_3276 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (
# 2357 "FStar.TypeChecker.Tc.fst"
let _68_3280 = (for_export hidden se)
in (match (_68_3280) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_68_3286) with
| (ses, exports, env, _68_3285) -> begin
(let _157_1237 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _157_1237, env))
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
let _68_3291 = env
in (let _157_1242 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _68_3291.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_3291.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_3291.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_3291.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_3291.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_3291.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_3291.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_3291.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_3291.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_3291.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_3291.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_3291.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_3291.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _68_3291.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _68_3291.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_3291.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _157_1242; FStar_TypeChecker_Env.type_of = _68_3291.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_3291.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_3291.FStar_TypeChecker_Env.use_bv_sorts}))
in (
# 2366 "FStar.TypeChecker.Tc.fst"
let _68_3294 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (
# 2367 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (
# 2368 "FStar.TypeChecker.Tc.fst"
let _68_3300 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_68_3300) with
| (ses, exports, env) -> begin
((
# 2369 "FStar.TypeChecker.Tc.fst"
let _68_3301 = modul
in {FStar_Syntax_Syntax.name = _68_3301.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _68_3301.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _68_3301.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))

# 2371 "FStar.TypeChecker.Tc.fst"
let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (
# 2372 "FStar.TypeChecker.Tc.fst"
let _68_3309 = (tc_decls env decls)
in (match (_68_3309) with
| (ses, exports, env) -> begin
(
# 2373 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2373 "FStar.TypeChecker.Tc.fst"
let _68_3310 = modul
in {FStar_Syntax_Syntax.name = _68_3310.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _68_3310.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _68_3310.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))

# 2376 "FStar.TypeChecker.Tc.fst"
let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (
# 2377 "FStar.TypeChecker.Tc.fst"
let modul = (
# 2377 "FStar.TypeChecker.Tc.fst"
let _68_3316 = modul
in {FStar_Syntax_Syntax.name = _68_3316.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _68_3316.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (
# 2378 "FStar.TypeChecker.Tc.fst"
let env = (FStar_TypeChecker_Env.finish_module env modul)
in (
# 2379 "FStar.TypeChecker.Tc.fst"
let _68_3326 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(
# 2381 "FStar.TypeChecker.Tc.fst"
let _68_3320 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (
# 2382 "FStar.TypeChecker.Tc.fst"
let _68_3322 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (
# 2383 "FStar.TypeChecker.Tc.fst"
let _68_3324 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _157_1255 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _157_1255 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))

# 2388 "FStar.TypeChecker.Tc.fst"
let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (
# 2389 "FStar.TypeChecker.Tc.fst"
let _68_3333 = (tc_partial_modul env modul)
in (match (_68_3333) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

# 2392 "FStar.TypeChecker.Tc.fst"
let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (
# 2393 "FStar.TypeChecker.Tc.fst"
let _68_3336 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _157_1264 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _157_1264))
end else begin
()
end
in (
# 2395 "FStar.TypeChecker.Tc.fst"
let env = (
# 2395 "FStar.TypeChecker.Tc.fst"
let _68_3338 = env
in {FStar_TypeChecker_Env.solver = _68_3338.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_3338.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_3338.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_3338.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_3338.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_3338.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_3338.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_3338.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_3338.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_3338.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_3338.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_3338.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_3338.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _68_3338.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_3338.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_3338.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_3338.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _68_3338.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_3338.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _68_3338.FStar_TypeChecker_Env.use_bv_sorts})
in (
# 2396 "FStar.TypeChecker.Tc.fst"
let _68_3354 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _68_3346) -> begin
(let _157_1269 = (let _157_1268 = (let _157_1267 = (FStar_TypeChecker_Env.get_range env)
in ((Prims.strcat "Implicit argument: " msg), _157_1267))
in FStar_Syntax_Syntax.Error (_157_1268))
in (Prims.raise _157_1269))
end
in (match (_68_3354) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(t, c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(let _157_1274 = (let _157_1273 = (let _157_1272 = (let _157_1270 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _157_1270))
in (let _157_1271 = (FStar_TypeChecker_Env.get_range env)
in (_157_1272, _157_1271)))
in FStar_Syntax_Syntax.Error (_157_1273))
in (Prims.raise _157_1274))
end
end)))))

# 2403 "FStar.TypeChecker.Tc.fst"
let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (
# 2404 "FStar.TypeChecker.Tc.fst"
let _68_3357 = if ((let _157_1279 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _157_1279)) <> 0) then begin
(let _157_1280 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _157_1280))
end else begin
()
end
in (
# 2406 "FStar.TypeChecker.Tc.fst"
let _68_3361 = (tc_modul env m)
in (match (_68_3361) with
| (m, env) -> begin
(
# 2407 "FStar.TypeChecker.Tc.fst"
let _68_3362 = if (FStar_Options.should_dump m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _157_1281 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _157_1281))
end else begin
()
end
in (m, env))
end))))




