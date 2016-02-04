
open Prims
let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_ST.read FStar_Options.log_types) && (not ((let _198_3 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _198_3))))))

let rng : FStar_TypeChecker_Env.env  ->  FStar_Range.range = (fun env -> (FStar_TypeChecker_Env.get_range env))

let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (let _95_17 = env
in {FStar_TypeChecker_Env.solver = _95_17.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _95_17.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _95_17.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _95_17.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _95_17.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _95_17.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _95_17.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _95_17.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _95_17.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _95_17.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _95_17.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _95_17.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _95_17.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _95_17.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _95_17.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _95_17.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _95_17.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _95_17.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _95_17.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _95_17.FStar_TypeChecker_Env.use_bv_sorts}))

let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (let _95_20 = env
in {FStar_TypeChecker_Env.solver = _95_20.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _95_20.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _95_20.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _95_20.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _95_20.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _95_20.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _95_20.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _95_20.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _95_20.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _95_20.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _95_20.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _95_20.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _95_20.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _95_20.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _95_20.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _95_20.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _95_20.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _95_20.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _95_20.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _95_20.FStar_TypeChecker_Env.use_bv_sorts}))

let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (let r = if (tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
v.FStar_Syntax_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos tl.FStar_Syntax_Syntax.pos)
end
in (let _198_17 = (let _198_16 = (FStar_Syntax_Syntax.as_arg v)
in (let _198_15 = (let _198_14 = (FStar_Syntax_Syntax.as_arg tl)
in (_198_14)::[])
in (_198_16)::_198_15))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _198_17 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))

let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _95_1 -> (match (_95_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _95_30 -> begin
false
end))

let steps : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Normalize.step Prims.list = (fun env -> if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::[]
end else begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]
end)

let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Unfold)::(FStar_TypeChecker_Normalize.Beta)::[]) env t))

let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _198_30 = (steps env)
in (FStar_TypeChecker_Normalize.normalize _198_30 env t)))

let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _198_35 = (steps env)
in (FStar_TypeChecker_Normalize.normalize_comp _198_35 env c)))

let fxv_check : FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv Prims.list * (FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv  ->  Prims.bool))  ->  Prims.unit = (fun head env kt fvs -> (let rec aux = (fun try_norm t -> if (FStar_Util.set_is_empty fvs) then begin
()
end else begin
(let fvs' = (let _198_54 = if try_norm then begin
(norm env t)
end else begin
t
end
in (FStar_Syntax_Free.names _198_54))
in (let a = (FStar_Util.set_intersect fvs fvs')
in if (FStar_Util.set_is_empty a) then begin
()
end else begin
if (not (try_norm)) then begin
(aux true t)
end else begin
(let fail = (fun _95_48 -> (match (()) with
| () -> begin
(let escaping = (let _198_58 = (let _198_57 = (FStar_Util.set_elements a)
in (FStar_All.pipe_right _198_57 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _198_58 (FStar_String.concat ", ")))
in (let msg = if ((FStar_Util.set_count a) > 1) then begin
(let _198_59 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'{%s}\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" escaping _198_59))
end else begin
(let _198_60 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variable \'%s\' in the type of \'%s\' escapes because of impure applications; add explicit let-bindings" escaping _198_60))
end
in (let _198_63 = (let _198_62 = (let _198_61 = (FStar_TypeChecker_Env.get_range env)
in (msg, _198_61))
in FStar_Syntax_Syntax.Error (_198_62))
in (Prims.raise _198_63))))
end))
in (let s = (let _198_64 = (FStar_TypeChecker_Recheck.check t)
in (FStar_TypeChecker_Util.new_uvar env _198_64))
in (match ((FStar_TypeChecker_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g)
end
| _95_55 -> begin
(fail ())
end)))
end
end))
end)
in (aux false kt)))

let check_no_escape : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun env bs t -> (let fvs = (FStar_Syntax_Free.names t)
in if (FStar_Util.for_some (fun x -> (FStar_Util.set_mem x fvs)) bs) then begin
(let _95_64 = (FStar_Syntax_Util.type_u ())
in (match (_95_64) with
| (k, _95_63) -> begin
(let tnarrow = (FStar_TypeChecker_Util.new_uvar env k)
in (let _198_72 = (FStar_TypeChecker_Rel.teq env t tnarrow)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _198_72)))
end))
end else begin
()
end))

let maybe_push_binding : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder  ->  FStar_TypeChecker_Env.env = (fun env b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
env
end else begin
(let _95_68 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _198_78 = (FStar_Syntax_Print.bv_to_string (Prims.fst b))
in (let _198_77 = (FStar_Syntax_Print.term_to_string (Prims.fst b).FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _198_78 _198_77)))
end else begin
()
end
in (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))
end)

let maybe_make_subst = (fun _95_2 -> (match (_95_2) with
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Syntax_Syntax.NT ((x, e)))::[]
end
| _95_77 -> begin
[]
end))

let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.subst_t = (fun s b v -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
s
end else begin
(FStar_Syntax_Syntax.NT (((Prims.fst b), v)))::s
end)

let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (let _95_83 = lc
in {FStar_Syntax_Syntax.eff_name = _95_83.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _95_83.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _95_85 -> (match (()) with
| () -> begin
(let _198_91 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _198_91 t))
end))}))

let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _198_100 = if (not ((FStar_Syntax_Util.is_pure_or_ghost_function t))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _198_100))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (let t = lc.FStar_Syntax_Syntax.res_typ
in (let _95_117 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, guard)
end
| Some (t') -> begin
(let _95_99 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _198_102 = (FStar_Syntax_Print.term_to_string t)
in (let _198_101 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _198_102 _198_101)))
end else begin
()
end
in (let _95_103 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_95_103) with
| (e, lc) -> begin
(let t = lc.FStar_Syntax_Syntax.res_typ
in (let _95_107 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_95_107) with
| (e, g) -> begin
(let _95_108 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _198_104 = (FStar_Syntax_Print.term_to_string t)
in (let _198_103 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _198_104 _198_103)))
end else begin
()
end
in (let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (let _95_113 = (let _198_110 = (FStar_All.pipe_left (fun _198_109 -> Some (_198_109)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _198_110 env e lc g))
in (match (_95_113) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))))
end)))
end)))
end)
in (match (_95_117) with
| (e, lc, g) -> begin
(let _95_118 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_111 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _198_111))
end else begin
()
end
in (e, lc, g))
end)))))

let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (t) -> begin
(let _95_128 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_95_128) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))

let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _95_133 -> (match (_95_133) with
| (e, c) -> begin
(let expected_c_opt = (match (copt) with
| Some (_95_135) -> begin
copt
end
| None -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
(let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let md = (FStar_TypeChecker_Env.get_effect_decl env c1.FStar_Syntax_Syntax.effect_name)
in (match ((FStar_TypeChecker_Env.default_effect env md.FStar_Syntax_Syntax.mname)) with
| None -> begin
None
end
| Some (l) -> begin
(let flags = if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) then begin
(FStar_Syntax_Syntax.TOTAL)::[]
end else begin
if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_ML_lid) then begin
(FStar_Syntax_Syntax.MLEFFECT)::[]
end else begin
[]
end
end
in (let def = (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.effect_name = l; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = flags})
in Some (def)))
end)))
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _198_124 = (norm_c env c)
in (e, _198_124, FStar_TypeChecker_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(let _95_149 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_127 = (FStar_Syntax_Print.term_to_string e)
in (let _198_126 = (FStar_Syntax_Print.comp_to_string c)
in (let _198_125 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _198_127 _198_126 _198_125))))
end else begin
()
end
in (let c = (norm_c env c)
in (let _95_152 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_130 = (FStar_Syntax_Print.term_to_string e)
in (let _198_129 = (FStar_Syntax_Print.comp_to_string c)
in (let _198_128 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _198_130 _198_129 _198_128))))
end else begin
()
end
in (let _95_158 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_95_158) with
| (e, _95_156, g) -> begin
(let g = (let _198_131 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _198_131 "could not prove post-condition" g))
in (let _95_160 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_133 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _198_132 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _198_133 _198_132)))
end else begin
()
end
in (e, expected_c, g)))
end)))))
end))
end))

let no_logical_guard = (fun env _95_166 -> (match (_95_166) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
(te, kt, f)
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _198_139 = (let _198_138 = (let _198_137 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _198_136 = (FStar_TypeChecker_Env.get_range env)
in (_198_137, _198_136)))
in FStar_Syntax_Syntax.Error (_198_138))
in (Prims.raise _198_139))
end)
end))

let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _198_142 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _198_142))
end))

let with_implicits = (fun imps _95_178 -> (match (_95_178) with
| (e, l, g) -> begin
(e, l, (let _95_179 = g
in {FStar_TypeChecker_Env.guard_f = _95_179.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _95_179.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _95_179.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (FStar_List.append imps g.FStar_TypeChecker_Env.implicits)}))
end))

let add_implicit : (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun u g -> (let _95_183 = g
in {FStar_TypeChecker_Env.guard_f = _95_183.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _95_183.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _95_183.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (u)::g.FStar_TypeChecker_Env.implicits}))

let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _95_207; FStar_Syntax_Syntax.result_typ = _95_205; FStar_Syntax_Syntax.effect_args = (pre, _95_201)::(post, _95_197)::(pats, _95_193)::[]; FStar_Syntax_Syntax.flags = _95_190}) -> begin
(let rec extract_pats = (fun pats -> (match ((let _198_155 = (FStar_Syntax_Subst.compress pats)
in _198_155.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (cons, _95_220); FStar_Syntax_Syntax.tk = _95_217; FStar_Syntax_Syntax.pos = _95_215; FStar_Syntax_Syntax.vars = _95_213}, _95_233::(hd, _95_230)::(tl, _95_226)::[]) when (FStar_Ident.lid_equals cons.FStar_Syntax_Syntax.v FStar_Syntax_Const.cons_lid) -> begin
(let _95_239 = (FStar_Syntax_Util.head_and_args hd)
in (match (_95_239) with
| (head, args) -> begin
(let pat = (match (args) with
| (_::arg::[]) | (arg::[]) -> begin
(arg)::[]
end
| _95_246 -> begin
[]
end)
in (let _198_156 = (extract_pats tl)
in (FStar_List.append pat _198_156)))
end))
end
| _95_249 -> begin
[]
end))
in (let pats = (let _198_157 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env pats)
in (extract_pats _198_157))
in (let fvs = (let _198_161 = (FStar_Syntax_Syntax.new_bv_set ())
in (FStar_List.fold_left (fun out _95_255 -> (match (_95_255) with
| (a, _95_254) -> begin
(let _198_160 = (FStar_Syntax_Free.names a)
in (FStar_Util.set_union out _198_160))
end)) _198_161 pats))
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _95_260 -> (match (_95_260) with
| (b, _95_259) -> begin
(not ((FStar_Util.set_mem b fvs)))
end))))) with
| None -> begin
()
end
| Some (x, _95_264) -> begin
(let _198_164 = (let _198_163 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _198_163))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _198_164))
end))))
end
| _95_268 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end)

let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun env actuals expected_c -> (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(let r = (FStar_TypeChecker_Env.get_range env)
in (let env = (let _95_275 = env
in {FStar_TypeChecker_Env.solver = _95_275.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _95_275.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _95_275.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _95_275.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _95_275.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _95_275.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _95_275.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _95_275.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _95_275.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _95_275.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _95_275.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _95_275.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _95_275.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _95_275.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _95_275.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _95_275.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _95_275.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _95_275.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _95_275.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _95_275.FStar_TypeChecker_Env.use_bv_sorts})
in (let precedes = (let _198_171 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.precedes_lid _198_171))
in (let decreases_clause = (fun bs c -> (let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _95_287 -> (match (_95_287) with
| (b, _95_286) -> begin
(let t = (let _198_179 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _198_179))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _95_296 -> begin
(let _198_180 = (FStar_Syntax_Syntax.bv_to_name b)
in (_198_180)::[])
end))
end)))))
in (let as_lex_list = (fun dec -> (let _95_302 = (FStar_Syntax_Util.head_and_args dec)
in (match (_95_302) with
| (head, _95_301) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _95_305) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _95_309 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _95_3 -> (match (_95_3) with
| FStar_Syntax_Syntax.DECREASES (_95_313) -> begin
true
end
| _95_316 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _95_321 -> begin
(let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| x::[] -> begin
x
end
| _95_326 -> begin
(mk_lex_list xs)
end))
end)))))
in (let previous_dec = (decreases_clause actuals expected_c)
in (let guard_one_letrec = (fun _95_331 -> (match (_95_331) with
| (l, t) -> begin
(match ((let _198_186 = (FStar_Syntax_Subst.compress t)
in _198_186.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _95_338 -> (match (_95_338) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _198_190 = (let _198_189 = (let _198_188 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_198_188))
in (FStar_Syntax_Syntax.new_bv _198_189 x.FStar_Syntax_Syntax.sort))
in (_198_190, imp))
end else begin
(x, imp)
end
end))))
in (let _95_342 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_95_342) with
| (formals, c) -> begin
(let dec = (decreases_clause formals c)
in (let precedes = (let _198_194 = (let _198_193 = (FStar_Syntax_Syntax.as_arg dec)
in (let _198_192 = (let _198_191 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_198_191)::[])
in (_198_193)::_198_192))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _198_194 None r))
in (let _95_349 = (FStar_Util.prefix formals)
in (match (_95_349) with
| (bs, (last, imp)) -> begin
(let last = (let _95_350 = last
in (let _198_195 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _95_350.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _95_350.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _198_195}))
in (let refined_formals = (FStar_List.append bs (((last, imp))::[]))
in (let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (let _95_355 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_198 = (FStar_Syntax_Print.lbname_to_string l)
in (let _198_197 = (FStar_Syntax_Print.term_to_string t)
in (let _198_196 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _198_198 _198_197 _198_196))))
end else begin
()
end
in (l, t')))))
end))))
end)))
end
| _95_358 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end))

let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (let _95_361 = env
in {FStar_TypeChecker_Env.solver = _95_361.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _95_361.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _95_361.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _95_361.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _95_361.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _95_361.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _95_361.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _95_361.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _95_361.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _95_361.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _95_361.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _95_361.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _95_361.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _95_361.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _95_361.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _95_361.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _95_361.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _95_361.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _95_361.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _95_361.FStar_TypeChecker_Env.use_bv_sorts}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (let _95_366 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_264 = (let _198_262 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _198_262))
in (let _198_263 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _198_264 _198_263)))
end else begin
()
end
in (let top = e
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_95_370) -> begin
(let _198_268 = (FStar_Syntax_Subst.compress e)
in (tc_term env _198_268))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(let _95_410 = (FStar_Syntax_Util.type_u ())
in (match (_95_410) with
| (t, u) -> begin
(let _95_414 = (tc_check_tot_or_gtot_term env e t)
in (match (_95_414) with
| (e, c, g) -> begin
(let _95_421 = (let _95_418 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_95_418) with
| (env, _95_417) -> begin
(tc_pats env pats)
end))
in (match (_95_421) with
| (pats, g') -> begin
(let g' = (let _95_422 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _95_422.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _95_422.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _95_422.FStar_TypeChecker_Env.implicits})
in (let _198_270 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_pattern (pats)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _198_269 = (FStar_TypeChecker_Rel.conj_guard g g')
in (_198_270, c, _198_269))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _198_271 = (FStar_Syntax_Subst.compress e)
in _198_271.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_95_431, {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _95_438; FStar_Syntax_Syntax.lbtyp = _95_436; FStar_Syntax_Syntax.lbeff = _95_434; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(let _95_449 = (let _198_272 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Recheck.t_unit)
in (tc_term _198_272 e1))
in (match (_95_449) with
| (e1, c1, g1) -> begin
(let _95_453 = (tc_term env e2)
in (match (_95_453) with
| (e2, c2, g2) -> begin
(let c = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (None, c2))
in (let e = (let _198_277 = (let _198_276 = (let _198_275 = (let _198_274 = (let _198_273 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Recheck.t_unit, e1))
in (_198_273)::[])
in (false, _198_274))
in (_198_275, e2))
in FStar_Syntax_Syntax.Tm_let (_198_276))
in (FStar_Syntax_Syntax.mk _198_277 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _198_278 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _198_278)))))
end))
end))
end
| _95_458 -> begin
(let _95_462 = (tc_term env e)
in (match (_95_462) with
| (e, c, g) -> begin
(let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(let _95_471 = (tc_term env e)
in (match (_95_471) with
| (e, c, g) -> begin
(let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, m))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _95_476) -> begin
(let _95_481 = (FStar_Syntax_Util.type_u ())
in (match (_95_481) with
| (k, u) -> begin
(let _95_486 = (tc_check_tot_or_gtot_term env t k)
in (match (_95_486) with
| (t, _95_484, f) -> begin
(let _95_490 = (let _198_279 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _198_279 e))
in (match (_95_490) with
| (e, c, g) -> begin
(let _95_494 = (let _198_283 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _95_491 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _198_283 e c f))
in (match (_95_494) with
| (c, f) -> begin
(let _95_498 = (let _198_284 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, t, Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _198_284 c))
in (match (_95_498) with
| (e, c, f2) -> begin
(let _198_286 = (let _198_285 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _198_285))
in (e, c, _198_286))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(let env0 = env
in (let env = (let _198_288 = (let _198_287 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _198_287 Prims.fst))
in (FStar_All.pipe_right _198_288 instantiate_both))
in (let _95_505 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _198_290 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _198_289 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _198_290 _198_289)))
end else begin
()
end
in (let _95_510 = (tc_term (no_inst env) head)
in (match (_95_510) with
| (head, chead, g_head) -> begin
(let _95_514 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _198_291 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _198_291))
end else begin
(let _198_292 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _198_292))
end
in (match (_95_514) with
| (e, c, g) -> begin
(let _95_515 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _198_293 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _198_293))
end else begin
()
end
in (let c = if (((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) && (not ((FStar_Syntax_Util.is_lcomp_partial_return c)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)) then begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e c)
end else begin
c
end
in (let _95_522 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_299 = (FStar_Syntax_Print.term_to_string e)
in (let _198_298 = (let _198_294 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _198_294))
in (let _198_297 = (let _198_296 = (FStar_TypeChecker_Env.expected_typ env0)
in (FStar_All.pipe_right _198_296 (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end))))
in (FStar_Util.print3 "(%s) About to check %s against expected typ %s\n" _198_299 _198_298 _198_297))))
end else begin
()
end
in (let _95_527 = (comp_check_expected_typ env0 e c)
in (match (_95_527) with
| (e, c, g') -> begin
(let _95_528 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_302 = (FStar_Syntax_Print.term_to_string e)
in (let _198_301 = (let _198_300 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _198_300))
in (FStar_Util.print2 "(%s) checked ... got %s\n" _198_302 _198_301)))
end else begin
()
end
in (let gimp = (match ((let _198_303 = (FStar_Syntax_Subst.compress head)
in _198_303.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _95_532) -> begin
(let imp = (env0, u, e, c.FStar_Syntax_Syntax.res_typ, e.FStar_Syntax_Syntax.pos)
in (let _95_536 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _95_536.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _95_536.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _95_536.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _95_539 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (let gres = (let _198_304 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _198_304))
in (let _95_542 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _198_305 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print1 "Guard from application node is %s\n" _198_305))
end else begin
()
end
in (e, c, gres)))))
end)))))
end))
end)))))
end
| FStar_Syntax_Syntax.Tm_match (e1, eqns) -> begin
(let _95_550 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_95_550) with
| (env1, topt) -> begin
(let env1 = (instantiate_both env1)
in (let _95_555 = (tc_term env1 e1)
in (match (_95_555) with
| (e1, c1, g1) -> begin
(let _95_566 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(let _95_562 = (FStar_Syntax_Util.type_u ())
in (match (_95_562) with
| (k, _95_561) -> begin
(let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _198_306 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_198_306, res_t)))
end))
end)
in (match (_95_566) with
| (env_branches, res_t) -> begin
(let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (let _95_583 = (let _95_580 = (FStar_List.fold_right (fun _95_574 _95_577 -> (match ((_95_574, _95_577)) with
| ((_95_570, f, c, g), (caccum, gaccum)) -> begin
(let _198_309 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _198_309))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_95_580) with
| (cases, g) -> begin
(let _198_310 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_198_310, g))
end))
in (match (_95_583) with
| (c_branches, g_branches) -> begin
(let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (guard_x), c_branches))
in (let e = (let _198_314 = (let _198_313 = (let _198_312 = (FStar_List.map (fun _95_592 -> (match (_95_592) with
| (f, _95_587, _95_589, _95_591) -> begin
f
end)) t_eqns)
in (e1, _198_312))
in FStar_Syntax_Syntax.Tm_match (_198_313))
in (FStar_Syntax_Syntax.mk _198_314 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, cres.FStar_Syntax_Syntax.res_typ, Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (let _95_595 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _198_317 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _198_316 = (let _198_315 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _198_315))
in (FStar_Util.print2 "(%s) comp type = %s\n" _198_317 _198_316)))
end else begin
()
end
in (let _198_318 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _198_318))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_95_607); FStar_Syntax_Syntax.lbunivs = _95_605; FStar_Syntax_Syntax.lbtyp = _95_603; FStar_Syntax_Syntax.lbeff = _95_601; FStar_Syntax_Syntax.lbdef = _95_599}::[]), _95_613) -> begin
(let _95_616 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_319 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _198_319))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _95_620), _95_623) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_95_638); FStar_Syntax_Syntax.lbunivs = _95_636; FStar_Syntax_Syntax.lbtyp = _95_634; FStar_Syntax_Syntax.lbeff = _95_632; FStar_Syntax_Syntax.lbdef = _95_630}::_95_628), _95_644) -> begin
(let _95_647 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_320 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _198_320))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _95_651), _95_654) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (let check_instantiated_fvar = (fun env v dc e t -> (let _95_668 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_95_668) with
| (e, t, implicits) -> begin
(let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _198_334 = (let _198_333 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _198_333))
in FStar_Util.Inr (_198_334))
end
in (let is_data_ctor = (fun _95_4 -> (match (_95_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _95_678 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _198_340 = (let _198_339 = (let _198_338 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _198_337 = (FStar_TypeChecker_Env.get_range env)
in (_198_338, _198_337)))
in FStar_Syntax_Syntax.Error (_198_339))
in (Prims.raise _198_340))
end else begin
(value_check_expected_typ env e tc implicits)
end))
end)))
in (let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(FStar_All.failwith "Impossible: Violation of locally nameless convention")
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(let g = (match ((let _198_341 = (FStar_Syntax_Subst.compress t1)
in _198_341.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_95_689) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _95_692 -> begin
(let imp = (env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (let _95_694 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _95_694.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _95_694.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _95_694.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _95_700 = (FStar_Syntax_Util.type_u ())
in (match (_95_700) with
| (t, u) -> begin
(let e = (FStar_TypeChecker_Util.new_uvar env t)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))
end))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let t = if env.FStar_TypeChecker_Env.use_bv_sorts then begin
x.FStar_Syntax_Syntax.sort
end else begin
(FStar_TypeChecker_Env.lookup_bv env x)
end
in (let e = (FStar_Syntax_Syntax.bv_to_name (let _95_705 = x
in {FStar_Syntax_Syntax.ppname = _95_705.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _95_705.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (let _95_711 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_95_711) with
| (e, t, implicits) -> begin
(let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _198_343 = (let _198_342 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _198_342))
in FStar_Util.Inr (_198_343))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (v, dc); FStar_Syntax_Syntax.tk = _95_718; FStar_Syntax_Syntax.pos = _95_716; FStar_Syntax_Syntax.vars = _95_714}, us) -> begin
(let us = (FStar_List.map (tc_universe env) us)
in (let _95_730 = (FStar_TypeChecker_Env.lookup_lid env v.FStar_Syntax_Syntax.v)
in (match (_95_730) with
| (us', t) -> begin
(let _95_737 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _198_346 = (let _198_345 = (let _198_344 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _198_344))
in FStar_Syntax_Syntax.Error (_198_345))
in (Prims.raise _198_346))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _95_736 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (let e = (let _198_349 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (((let _95_739 = v
in {FStar_Syntax_Syntax.v = _95_739.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _95_739.FStar_Syntax_Syntax.p}), dc))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _198_349 us))
in (check_instantiated_fvar env v dc e t)))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (v, dc) -> begin
(let _95_748 = (FStar_TypeChecker_Env.lookup_lid env v.FStar_Syntax_Syntax.v)
in (match (_95_748) with
| (us, t) -> begin
(let e = (let _198_350 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (((let _95_749 = v
in {FStar_Syntax_Syntax.v = _95_749.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _95_749.FStar_Syntax_Syntax.p}), dc))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _198_350 us))
in (check_instantiated_fvar env v dc e t))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let t = (FStar_TypeChecker_Recheck.check e)
in (let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _95_762 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_95_762) with
| (bs, c) -> begin
(let env0 = env
in (let _95_767 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_95_767) with
| (env, _95_766) -> begin
(let _95_772 = (tc_binders env bs)
in (match (_95_772) with
| (bs, env, g, us) -> begin
(let _95_776 = (tc_comp env c)
in (match (_95_776) with
| (c, uc, f) -> begin
(let e = (let _95_777 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _95_777.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _95_777.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _95_777.FStar_Syntax_Syntax.vars})
in (let _95_780 = (check_smt_pat env e bs c)
in (let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (let g = (let _198_351 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _198_351))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let u = (tc_universe env u)
in (let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) None top.FStar_Syntax_Syntax.pos)
in (let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(let _95_796 = (let _198_353 = (let _198_352 = (FStar_Syntax_Syntax.mk_binder x)
in (_198_352)::[])
in (FStar_Syntax_Subst.open_term _198_353 phi))
in (match (_95_796) with
| (x, phi) -> begin
(let env0 = env
in (let _95_801 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_95_801) with
| (env, _95_800) -> begin
(let _95_806 = (let _198_354 = (FStar_List.hd x)
in (tc_binder env _198_354))
in (match (_95_806) with
| (x, env, f1, u) -> begin
(let _95_807 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _198_357 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _198_356 = (FStar_Syntax_Print.term_to_string phi)
in (let _198_355 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _198_357 _198_356 _198_355))))
end else begin
()
end
in (let _95_812 = (FStar_Syntax_Util.type_u ())
in (match (_95_812) with
| (t_phi, _95_811) -> begin
(let _95_817 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_95_817) with
| (phi, _95_815, f2) -> begin
(let e = (let _95_818 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _95_818.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _95_818.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _95_818.FStar_Syntax_Syntax.vars})
in (let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (let g = (let _198_358 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _198_358))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _95_826) -> begin
(let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (let _95_832 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_359 = (FStar_Syntax_Print.term_to_string (let _95_830 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _95_830.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _95_830.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _95_830.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _198_359))
end else begin
()
end
in (let _95_836 = (FStar_Syntax_Subst.open_term bs body)
in (match (_95_836) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _95_838 -> begin
(let _198_361 = (let _198_360 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _198_360))
in (FStar_All.failwith _198_361))
end)))))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _95_845 = (FStar_Syntax_Util.type_u ())
in (match (_95_845) with
| (k, u) -> begin
(let _95_850 = (tc_check_tot_or_gtot_term env t k)
in (match (_95_850) with
| (t, _95_848, g) -> begin
(let _198_364 = (FStar_Syntax_Syntax.mk_Total t)
in (_198_364, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _95_855 = (FStar_Syntax_Util.type_u ())
in (match (_95_855) with
| (k, u) -> begin
(let _95_860 = (tc_check_tot_or_gtot_term env t k)
in (match (_95_860) with
| (t, _95_858, g) -> begin
(let _198_365 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_198_365, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(let kc = (FStar_TypeChecker_Env.lookup_effect_lid env c.FStar_Syntax_Syntax.effect_name)
in (let _95_864 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_367 = (FStar_Syntax_Print.lid_to_string c.FStar_Syntax_Syntax.effect_name)
in (let _198_366 = (FStar_Syntax_Print.term_to_string kc)
in (FStar_Util.print2 "Type of effect %s is %s\n" _198_367 _198_366)))
end else begin
()
end
in (let head = (FStar_Syntax_Syntax.fvar None c.FStar_Syntax_Syntax.effect_name (FStar_Ident.range_of_lid c.FStar_Syntax_Syntax.effect_name))
in (let tc = (let _198_369 = (let _198_368 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_198_368)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _198_369 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _95_872 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_95_872) with
| (tc, _95_870, f) -> begin
(let _95_876 = (FStar_Syntax_Util.head_and_args tc)
in (match (_95_876) with
| (_95_874, args) -> begin
(let _95_879 = (let _198_371 = (FStar_List.hd args)
in (let _198_370 = (FStar_List.tl args)
in (_198_371, _198_370)))
in (match (_95_879) with
| (res, args) -> begin
(let _95_895 = (let _198_373 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _95_5 -> (match (_95_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _95_886 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_95_886) with
| (env, _95_885) -> begin
(let _95_891 = (tc_tot_or_gtot_term env e)
in (match (_95_891) with
| (e, _95_889, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _198_373 FStar_List.unzip))
in (match (_95_895) with
| (flags, guards) -> begin
(let u = (match ((FStar_TypeChecker_Recheck.check (Prims.fst res))) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type (u); FStar_Syntax_Syntax.tk = _95_901; FStar_Syntax_Syntax.pos = _95_899; FStar_Syntax_Syntax.vars = _95_897} -> begin
u
end
| _95_906 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _198_375 = (FStar_Syntax_Syntax.mk_Comp (let _95_908 = c
in {FStar_Syntax_Syntax.effect_name = _95_908.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _95_908.FStar_Syntax_Syntax.flags}))
in (let _198_374 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_198_375, u, _198_374))))
end))
end))
end))
end))))))
end))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (let rec aux = (fun u -> (let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_95_916) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _198_380 = (aux u)
in FStar_Syntax_Syntax.U_succ (_198_380))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _198_381 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_198_381))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _198_385 = (let _198_384 = (let _198_383 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _198_382 = (FStar_TypeChecker_Env.get_range env)
in (_198_383, _198_382)))
in FStar_Syntax_Syntax.Error (_198_384))
in (Prims.raise _198_385))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _198_386 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _198_386 Prims.snd))
end
| _95_931 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (let fail = (fun msg t -> (let _198_395 = (let _198_394 = (let _198_393 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_198_393, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_198_394))
in (Prims.raise _198_395)))
in (let check_binders = (fun env bs bs_expected -> (let rec aux = (fun _95_949 bs bs_expected -> (match (_95_949) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| ((hd, imp)::bs, (hd_expected, imp')::bs_expected) -> begin
(let _95_976 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit))) | ((Some (FStar_Syntax_Syntax.Implicit), None)) -> begin
(let _198_412 = (let _198_411 = (let _198_410 = (let _198_408 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _198_408))
in (let _198_409 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_198_410, _198_409)))
in FStar_Syntax_Syntax.Error (_198_411))
in (Prims.raise _198_412))
end
| _95_975 -> begin
()
end)
in (let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (let _95_993 = (match ((let _198_413 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _198_413.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _95_981 -> begin
(let _95_982 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _198_414 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _198_414))
end else begin
()
end
in (let _95_988 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_95_988) with
| (t, _95_986, g1) -> begin
(let g2 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (let g = (let _198_415 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _198_415))
in (t, g)))
end)))
end)
in (match (_95_993) with
| (t, g) -> begin
(let hd = (let _95_994 = hd
in {FStar_Syntax_Syntax.ppname = _95_994.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _95_994.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (let b = (hd, imp)
in (let b_expected = (hd_expected, imp')
in (let env = (maybe_push_binding env b)
in (let subst = (let _198_416 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _198_416))
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
in (let rec expected_function_typ = (fun env t0 -> (match (t0) with
| None -> begin
(let _95_1014 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _95_1013 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (let _95_1021 = (tc_binders env bs)
in (match (_95_1021) with
| (bs, envbody, g, _95_1020) -> begin
(None, bs, [], None, envbody, g)
end)))
end
| Some (t) -> begin
(let t = (FStar_Syntax_Subst.compress t)
in (let rec as_function_typ = (fun norm t -> (match ((let _198_425 = (FStar_Syntax_Subst.compress t)
in _198_425.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(let _95_1048 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _95_1047 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _95_1055 = (tc_binders env bs)
in (match (_95_1055) with
| (bs, envbody, g, _95_1054) -> begin
(let _95_1059 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_95_1059) with
| (envbody, _95_1058) -> begin
(Some ((t, true)), bs, [], None, envbody, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _95_1062) -> begin
(let _95_1072 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_95_1072) with
| (_95_1066, bs, bs', copt, env, g) -> begin
(Some ((t, false)), bs, bs', copt, env, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(let _95_1079 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_95_1079) with
| (bs_expected, c_expected) -> begin
(let check_actuals_against_formals = (fun env bs bs_expected -> (let rec handle_more = (fun _95_1090 c_expected -> (match (_95_1090) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _198_436 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _198_436))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(let c = (let _198_437 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _198_437))
in (let _198_438 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _198_438)))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(let c = (FStar_Syntax_Subst.subst_comp subst c_expected)
in if (FStar_Syntax_Util.is_total_comp c) then begin
(let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(let _95_1111 = (check_binders env more_bs bs_expected)
in (match (_95_1111) with
| (env, bs', more, guard', subst) -> begin
(let _198_440 = (let _198_439 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _198_439, subst))
in (handle_more _198_440 c_expected))
end))
end
| _95_1113 -> begin
(let _198_442 = (let _198_441 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _198_441))
in (fail _198_442 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _198_443 = (check_binders env bs bs_expected)
in (handle_more _198_443 c_expected))))
in (let mk_letrec_env = (fun envbody bs c -> (let letrecs = (guard_letrecs envbody bs c)
in (let envbody = (let _95_1119 = envbody
in {FStar_TypeChecker_Env.solver = _95_1119.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _95_1119.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _95_1119.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _95_1119.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _95_1119.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _95_1119.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _95_1119.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _95_1119.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _95_1119.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _95_1119.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _95_1119.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _95_1119.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _95_1119.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _95_1119.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _95_1119.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _95_1119.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _95_1119.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _95_1119.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _95_1119.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _95_1119.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _95_1124 _95_1127 -> (match ((_95_1124, _95_1127)) with
| ((env, letrec_binders), (l, t)) -> begin
(let _95_1133 = (let _198_453 = (let _198_452 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _198_452 Prims.fst))
in (tc_term _198_453 t))
in (match (_95_1133) with
| (t, _95_1130, _95_1132) -> begin
(let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _198_454 = (FStar_Syntax_Syntax.mk_binder (let _95_1137 = x
in {FStar_Syntax_Syntax.ppname = _95_1137.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _95_1137.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_198_454)::letrec_binders)
end
| _95_1140 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (let _95_1146 = (check_actuals_against_formals env bs bs_expected)
in (match (_95_1146) with
| (envbody, bs, g, c) -> begin
(let _95_1149 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_95_1149) with
| (envbody, letrecs) -> begin
(let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, g))
end))
end))))
end))
end
| _95_1152 -> begin
if (not (norm)) then begin
(let _198_455 = (unfold_whnf env t)
in (as_function_typ true _198_455))
end else begin
(let _95_1161 = (expected_function_typ env None)
in (match (_95_1161) with
| (_95_1154, bs, _95_1157, c_opt, envbody, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (let use_eq = env.FStar_TypeChecker_Env.use_eq
in (let _95_1165 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_95_1165) with
| (env, topt) -> begin
(let _95_1169 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _198_456 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _198_456 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (let _95_1177 = (expected_function_typ env topt)
in (match (_95_1177) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, g) -> begin
(let _95_1183 = (tc_term (let _95_1178 = envbody
in {FStar_TypeChecker_Env.solver = _95_1178.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _95_1178.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _95_1178.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _95_1178.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _95_1178.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _95_1178.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _95_1178.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _95_1178.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _95_1178.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _95_1178.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _95_1178.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _95_1178.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _95_1178.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _95_1178.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _95_1178.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _95_1178.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _95_1178.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _95_1178.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _95_1178.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_95_1183) with
| (body, cbody, guard_body) -> begin
(let _95_1184 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_462 = (FStar_Syntax_Print.term_to_string body)
in (let _198_461 = (let _198_457 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _198_457))
in (let _198_460 = (FStar_TypeChecker_Rel.guard_to_string env guard_body)
in (let _198_459 = (let _198_458 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _198_458))
in (FStar_Util.print4 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\nAgain cbody=%s\n" _198_462 _198_461 _198_460 _198_459)))))
end else begin
()
end
in (let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (let _95_1187 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _198_465 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _198_464 = (let _198_463 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _198_463))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _198_465 _198_464)))
end else begin
()
end
in (let _95_1194 = (let _198_467 = (let _198_466 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _198_466))
in (check_expected_effect (let _95_1189 = envbody
in {FStar_TypeChecker_Env.solver = _95_1189.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _95_1189.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _95_1189.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _95_1189.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _95_1189.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _95_1189.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _95_1189.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _95_1189.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _95_1189.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _95_1189.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _95_1189.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _95_1189.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _95_1189.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _95_1189.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _95_1189.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _95_1189.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _95_1189.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _95_1189.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _95_1189.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _95_1189.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _198_467))
in (match (_95_1194) with
| (body, cbody, guard) -> begin
(let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _198_468 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _198_468))
end else begin
(let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (let e = (FStar_Syntax_Util.abs bs body (Some ((FStar_Syntax_Util.lcomp_of_comp cbody))))
in (let _95_1217 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_95_1206) -> begin
(e, t, guard)
end
| _95_1209 -> begin
(let _95_1212 = if use_teq then begin
(let _198_469 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _198_469))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_95_1212) with
| (e, guard') -> begin
(let _198_470 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _198_470))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_95_1217) with
| (e, tfun, guard) -> begin
(let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (let _95_1221 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_95_1221) with
| (c, g) -> begin
(e, c, g)
end)))
end))))))
end)))))
end))
end)))
end)))))))
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead ghead args expected_topt -> (let n_args = (FStar_List.length args)
in (let r = (FStar_TypeChecker_Env.get_range env)
in (let thead = chead.FStar_Syntax_Syntax.res_typ
in (let _95_1231 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _198_479 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _198_478 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _198_479 _198_478)))
end else begin
()
end
in (let rec check_function_app = (fun norm tf -> (match ((let _198_484 = (FStar_Syntax_Util.unrefine tf)
in _198_484.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| (e, imp)::tl -> begin
(let _95_1265 = (tc_term env e)
in (match (_95_1265) with
| (e, c, g_e) -> begin
(let _95_1269 = (tc_args env tl)
in (match (_95_1269) with
| (args, comps, g_rest) -> begin
(let _198_489 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, (c)::comps, _198_489))
end))
end))
end))
in (let _95_1273 = (tc_args env args)
in (match (_95_1273) with
| (args, comps, g_args) -> begin
(let bs = (let _198_491 = (FStar_All.pipe_right comps (FStar_List.map (fun c -> (c.FStar_Syntax_Syntax.res_typ, None))))
in (FStar_Syntax_Util.null_binders_of_tks _198_491))
in (let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _95_1280 -> begin
FStar_Syntax_Util.ml_comp
end)
in (let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _198_506 = (FStar_Syntax_Subst.compress t)
in _198_506.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_95_1286) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _95_1291 -> begin
ml_or_tot
end)
end)
in (let cres = (let _198_511 = (let _198_510 = (let _198_509 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _198_509 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _198_510))
in (ml_or_tot _198_511 r))
in (let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (let _95_1295 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _198_514 = (FStar_Syntax_Print.term_to_string head)
in (let _198_513 = (FStar_Syntax_Print.term_to_string tf)
in (let _198_512 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _198_514 _198_513 _198_512))))
end else begin
()
end
in (let _95_1297 = (let _198_515 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _198_515))
in (let comp = (let _198_518 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_TypeChecker_Util.bind env None c (None, out))) ((chead)::comps) _198_518))
in (let _198_520 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _198_519 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_198_520, comp, _198_519)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _95_1308 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_95_1308) with
| (bs, c) -> begin
(let rec tc_args = (fun _95_1316 bs cres args -> (match (_95_1316) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((x, Some (FStar_Syntax_Syntax.Implicit))::rest, (_95_1329, None)::_95_1327) -> begin
(let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (let _95_1335 = (fxv_check head env t fvs)
in (let _95_1340 = (FStar_TypeChecker_Util.new_implicit_var env t)
in (match (_95_1340) with
| (varg, u, implicits) -> begin
(let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (let arg = (let _198_555 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _198_555))
in (let _198_561 = (let _198_560 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _198_560, fvs))
in (tc_args _198_561 rest cres args))))
end))))
end
| ((x, aqual)::rest, (e, aq)::rest') -> begin
(let _95_1368 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit), Some (FStar_Syntax_Syntax.Implicit))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _95_1367 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (let x = (let _95_1371 = x
in {FStar_Syntax_Syntax.ppname = _95_1371.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _95_1371.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (let _95_1374 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _198_562 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _198_562))
end else begin
()
end
in (let _95_1376 = (fxv_check head env targ fvs)
in (let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (let env = (let _95_1379 = env
in {FStar_TypeChecker_Env.solver = _95_1379.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _95_1379.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _95_1379.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _95_1379.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _95_1379.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _95_1379.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _95_1379.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _95_1379.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _95_1379.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _95_1379.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _95_1379.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _95_1379.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _95_1379.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _95_1379.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _95_1379.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _95_1379.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _95_1379.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _95_1379.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _95_1379.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _95_1379.FStar_TypeChecker_Env.use_bv_sorts})
in (let _95_1382 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _198_565 = (FStar_Syntax_Print.tag_of_term e)
in (let _198_564 = (FStar_Syntax_Print.term_to_string e)
in (let _198_563 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _198_565 _198_564 _198_563))))
end else begin
()
end
in (let _95_1387 = (tc_term env e)
in (match (_95_1387) with
| (e, c, g_e) -> begin
(let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(let subst = (let _198_566 = (FStar_List.hd bs)
in (maybe_extend_subst subst _198_566 e))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(let subst = (let _198_571 = (FStar_List.hd bs)
in (maybe_extend_subst subst _198_571 e))
in (let _95_1394 = (((Some (x), c))::comps, g)
in (match (_95_1394) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _198_576 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _198_576)) then begin
(let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (let arg' = (let _198_577 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _198_577))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (newx), c))::comps, g, fvs) rest cres rest')))
end else begin
(let _198_586 = (let _198_585 = (let _198_583 = (let _198_582 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _198_582))
in (_198_583)::arg_rets)
in (let _198_584 = (FStar_Util.set_add x fvs)
in (subst, (arg)::outargs, _198_585, ((Some (x), c))::comps, g, _198_584)))
in (tc_args _198_586 rest cres rest'))
end
end
end))
end))))))))))
end
| (_95_1398, []) -> begin
(let _95_1401 = (fxv_check head env cres.FStar_Syntax_Syntax.res_typ fvs)
in (let _95_1419 = (match (bs) with
| [] -> begin
(let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (let g = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _95_1409 -> (match (_95_1409) with
| (_95_1407, c) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (let cres = if refine_with_equality then begin
(let _198_588 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _198_588 cres))
end else begin
(let _95_1411 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_591 = (FStar_Syntax_Print.term_to_string head)
in (let _198_590 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _198_589 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _198_591 _198_590 _198_589))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _95_1415 -> begin
(let g = (let _198_592 = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (FStar_All.pipe_right _198_592 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _198_597 = (let _198_596 = (let _198_595 = (let _198_594 = (let _198_593 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _198_593))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _198_594))
in (FStar_Syntax_Syntax.mk_Total _198_595))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _198_596))
in (_198_597, g)))
end)
in (match (_95_1419) with
| (cres, g) -> begin
(let _95_1420 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_598 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _198_598))
end else begin
()
end
in (let comp = (FStar_List.fold_left (fun out c -> (FStar_TypeChecker_Util.bind env None (Prims.snd c) ((Prims.fst c), out))) cres comps)
in (let comp = (FStar_TypeChecker_Util.bind env None chead (None, comp))
in (let app = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev outargs) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let comp = (FStar_TypeChecker_Util.record_application_site env app comp)
in (let _95_1430 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp g)
in (match (_95_1430) with
| (comp, g) -> begin
(let _95_1431 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_604 = (FStar_TypeChecker_Normalize.term_to_string env app)
in (let _198_603 = (let _198_602 = (comp.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Print.comp_to_string _198_602))
in (FStar_Util.print2 "\t Type of app term %s is %s\n" _198_604 _198_603)))
end else begin
()
end
in (app, comp, g))
end)))))))
end)))
end
| ([], arg::_95_1435) -> begin
(let rec aux = (fun norm tres -> (let tres = (let _198_609 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _198_609 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(let _95_1447 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_610 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _198_610))
end else begin
()
end
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs (FStar_Syntax_Util.lcomp_of_comp cres') args))
end
| _95_1450 when (not (norm)) -> begin
(let _198_615 = (unfold_whnf env tres)
in (aux true _198_615))
end
| _95_1452 -> begin
(let _198_621 = (let _198_620 = (let _198_619 = (let _198_617 = (FStar_TypeChecker_Normalize.term_to_string env tf)
in (let _198_616 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _198_617 _198_616)))
in (let _198_618 = (FStar_Syntax_Syntax.argpos arg)
in (_198_619, _198_618)))
in FStar_Syntax_Syntax.Error (_198_620))
in (Prims.raise _198_621))
end)))
in (aux false cres.FStar_Syntax_Syntax.res_typ))
end)
end))
in (let _198_623 = (let _198_622 = (FStar_Syntax_Syntax.new_bv_set ())
in ([], [], [], [], FStar_TypeChecker_Rel.trivial_guard, _198_622))
in (tc_args _198_623 bs (FStar_Syntax_Util.lcomp_of_comp c) args)))
end))
end
| _95_1454 -> begin
if (not (norm)) then begin
(let _198_624 = (unfold_whnf env tf)
in (check_function_app true _198_624))
end else begin
(let _198_627 = (let _198_626 = (let _198_625 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_198_625, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_198_626))
in (Prims.raise _198_627))
end
end))
in (let _198_629 = (let _198_628 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _198_628))
in (check_function_app false _198_629))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (let r = (FStar_TypeChecker_Env.get_range env)
in (let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(let res_t = (FStar_Syntax_Util.comp_result c)
in (let _95_1490 = (FStar_List.fold_left2 (fun _95_1471 _95_1474 _95_1477 -> (match ((_95_1471, _95_1474, _95_1477)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(let _95_1478 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (let _95_1483 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_95_1483) with
| (e, c, g) -> begin
(let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (let g = (let _198_639 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _198_639 g))
in (let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _198_643 = (let _198_641 = (let _198_640 = (FStar_Syntax_Syntax.as_arg e)
in (_198_640)::[])
in (FStar_List.append seen _198_641))
in (let _198_642 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_198_643, _198_642, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_95_1490) with
| (args, guard, ghost) -> begin
(let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (let c = if ghost then begin
(let _198_644 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _198_644 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (let _95_1495 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_95_1495) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _95_1497 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (let _95_1504 = (FStar_Syntax_Subst.open_branch branch)
in (match (_95_1504) with
| (pattern, when_clause, branch_exp) -> begin
(let _95_1509 = branch
in (match (_95_1509) with
| (cpat, _95_1507, cbr) -> begin
(let tc_pat = (fun allow_implicits pat_t p0 -> (let _95_1517 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_95_1517) with
| (pat_bvs, exps, p) -> begin
(let _95_1518 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _198_656 = (FStar_Syntax_Print.pat_to_string p0)
in (let _198_655 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _198_656 _198_655)))
end else begin
()
end
in (let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (let _95_1524 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_95_1524) with
| (env1, _95_1523) -> begin
(let env1 = (let _95_1525 = env1
in {FStar_TypeChecker_Env.solver = _95_1525.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _95_1525.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _95_1525.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _95_1525.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _95_1525.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _95_1525.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _95_1525.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _95_1525.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _95_1525.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _95_1525.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _95_1525.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _95_1525.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _95_1525.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _95_1525.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _95_1525.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _95_1525.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _95_1525.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _95_1525.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _95_1525.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _95_1525.FStar_TypeChecker_Env.use_bv_sorts})
in (let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (let _95_1564 = (let _198_679 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (let _95_1530 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _198_659 = (FStar_Syntax_Print.term_to_string e)
in (let _198_658 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _198_659 _198_658)))
end else begin
()
end
in (let _95_1535 = (tc_term env1 e)
in (match (_95_1535) with
| (e, lc, g) -> begin
(let _95_1536 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _198_661 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _198_660 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _198_661 _198_660)))
end else begin
()
end
in (let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (let _95_1542 = (let _198_662 = (FStar_TypeChecker_Rel.discharge_guard env (let _95_1540 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _95_1540.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _95_1540.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _95_1540.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _198_662 FStar_TypeChecker_Rel.resolve_implicits))
in (let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (let uvars_to_string = (fun uvs -> (let _198_667 = (let _198_666 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _198_666 (FStar_List.map (fun _95_1550 -> (match (_95_1550) with
| (u, _95_1549) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _198_667 (FStar_String.concat ", "))))
in (let uvs1 = (FStar_Syntax_Free.uvars e')
in (let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (let _95_1558 = if (let _198_668 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _198_668)) then begin
(let unresolved = (let _198_669 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _198_669 FStar_Util.set_elements))
in (let _198_677 = (let _198_676 = (let _198_675 = (let _198_674 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _198_673 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _198_672 = (let _198_671 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _95_1557 -> (match (_95_1557) with
| (u, _95_1556) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _198_671 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _198_674 _198_673 _198_672))))
in (_198_675, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_198_676))
in (Prims.raise _198_677)))
end else begin
()
end
in (let _95_1560 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _198_678 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _198_678))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _198_679 FStar_List.unzip))
in (match (_95_1564) with
| (exps, norm_exps) -> begin
(let p = (FStar_TypeChecker_Util.decorate_pattern env p exps)
in (p, pat_bvs, pat_env, exps, norm_exps))
end))))
end))))
end)))
in (let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (let _95_1571 = (let _198_680 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _198_680 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_95_1571) with
| (scrutinee_env, _95_1570) -> begin
(let _95_1577 = (tc_pat true pat_t pattern)
in (match (_95_1577) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(let _95_1587 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(let _95_1584 = (let _198_681 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Recheck.t_bool)
in (tc_term _198_681 e))
in (match (_95_1584) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_95_1587) with
| (when_clause, g_when) -> begin
(let _95_1591 = (tc_term pat_env branch_exp)
in (match (_95_1591) with
| (branch_exp, c, g_branch) -> begin
(let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _198_683 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _198_682 -> Some (_198_682)) _198_683))
end)
in (let _95_1645 = (let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _95_1609 -> begin
(let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _198_687 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _198_686 -> Some (_198_686)) _198_687))
end))
end))) None))
in (let _95_1640 = (match ((eqs, when_condition)) with
| (None, None) -> begin
(c, g_when, g_branch)
end
| (Some (f), None) -> begin
(let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _198_690 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _198_689 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (let _198_688 = (FStar_TypeChecker_Rel.imp_guard g g_branch)
in (_198_690, _198_689, _198_688))))))
end
| (Some (f), Some (w)) -> begin
(let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (let g_fw = (let _198_691 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_198_691))
in (let _198_696 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _198_695 = (let _198_692 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _198_692 g_when))
in (let _198_694 = (let _198_693 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_fw)
in (FStar_TypeChecker_Rel.imp_guard _198_693 g_branch))
in (_198_696, _198_695, _198_694))))))
end
| (None, Some (w)) -> begin
(let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _198_698 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (let _198_697 = (FStar_TypeChecker_Rel.imp_guard g g_branch)
in (_198_698, g_when, _198_697)))))
end)
in (match (_95_1640) with
| (c_weak, g_when_weak, g_branch_weak) -> begin
(let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _198_701 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _198_700 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (let _198_699 = (FStar_TypeChecker_Rel.close_guard binders g_branch_weak)
in (_198_701, _198_700, _198_699)))))
end)))
in (match (_95_1645) with
| (c, g_when, g_branch) -> begin
(let branch_guard = (let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (let discriminate = (fun scrutinee_tm f -> if ((let _198_711 = (let _198_710 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _198_710))
in (FStar_List.length _198_711)) > 1) then begin
(let disc = (let _198_712 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar None _198_712 (FStar_Ident.range_of_lid f.FStar_Syntax_Syntax.v)))
in (let disc = (let _198_714 = (let _198_713 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_198_713)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _198_714 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _198_715 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_198_715)::[])))
end else begin
[]
end)
in (let fail = (fun _95_1655 -> (match (()) with
| () -> begin
(let _198_721 = (let _198_720 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _198_719 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _198_718 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _198_720 _198_719 _198_718))))
in (FStar_All.failwith _198_721))
end))
in (let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (f, _95_1660) -> begin
f
end
| FStar_Syntax_Syntax.Tm_uinst (t, _95_1665) -> begin
(head_constructor t)
end
| _95_1669 -> begin
(fail ())
end))
in (let pat_exp = (let _198_724 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _198_724 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_95_1694) -> begin
(let _198_729 = (let _198_728 = (let _198_727 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _198_726 = (let _198_725 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_198_725)::[])
in (_198_727)::_198_726))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _198_728 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_198_729)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _198_730 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _198_730))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let sub_term_guards = (let _198_736 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _95_1712 -> (match (_95_1712) with
| (ei, _95_1711) -> begin
(let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (let sub_term = (let _198_735 = (FStar_Syntax_Syntax.fvar None projector f.FStar_Syntax_Syntax.p)
in (let _198_734 = (let _198_733 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_198_733)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _198_735 _198_734 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei)))
end))))
in (FStar_All.pipe_right _198_736 FStar_List.flatten))
in (let _198_737 = (discriminate scrutinee_tm f)
in (FStar_List.append _198_737 sub_term_guards)))
end)
end
| _95_1717 -> begin
[]
end))))))
in (let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid scrutinee_tm.FStar_Syntax_Syntax.pos)
end else begin
(let t = (let _198_742 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _198_742))
in (let _95_1725 = (FStar_Syntax_Util.type_u ())
in (match (_95_1725) with
| (k, _95_1724) -> begin
(let _95_1731 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_95_1731) with
| (t, _95_1728, _95_1730) -> begin
t
end))
end)))
end)
in (let branch_guard = (let _198_743 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _198_743 FStar_Syntax_Util.mk_disj_l))
in (let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
in (let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (let _95_1739 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _198_744 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _198_744))
end else begin
()
end
in (let _198_745 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_198_745, branch_guard, c, guard)))))
end)))
end))
end))
end))
end)))))
end))
end)))
and check_top_level_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(let _95_1756 = (check_let_bound_def true env lb)
in (match (_95_1756) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(let _95_1768 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(let g1 = (let _198_748 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _198_748 FStar_TypeChecker_Rel.resolve_implicits))
in (let _95_1763 = (let _198_752 = (let _198_751 = (let _198_750 = (let _198_749 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _198_749))
in (_198_750)::[])
in (FStar_TypeChecker_Util.generalize env _198_751))
in (FStar_List.hd _198_752))
in (match (_95_1763) with
| (_95_1759, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_95_1768) with
| (g1, e1, univ_vars, c1) -> begin
(let _95_1778 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(let _95_1771 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_95_1771) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(let _95_1772 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _198_753 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _198_753 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _198_754 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_198_754, c1)))
end
end))
end else begin
(let _95_1774 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _198_755 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _198_755)))
end
in (match (_95_1778) with
| (e2, c1) -> begin
(let cres = (let _198_756 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Recheck.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _198_756))
in (let _95_1780 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Recheck.t_unit.FStar_Syntax_Syntax.n)))
in (let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _198_757 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Recheck.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_198_757, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _95_1784 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(let env = (let _95_1795 = env
in {FStar_TypeChecker_Env.solver = _95_1795.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _95_1795.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _95_1795.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _95_1795.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _95_1795.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _95_1795.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _95_1795.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _95_1795.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _95_1795.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _95_1795.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _95_1795.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _95_1795.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _95_1795.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _95_1795.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _95_1795.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _95_1795.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _95_1795.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _95_1795.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _95_1795.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _95_1795.FStar_TypeChecker_Env.use_bv_sorts})
in (let _95_1804 = (let _198_761 = (let _198_760 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _198_760 Prims.fst))
in (check_let_bound_def false _198_761 lb))
in (match (_95_1804) with
| (e1, _95_1800, c1, g1, annotated) -> begin
(let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (let x = (let _95_1806 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _95_1806.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _95_1806.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (let _95_1811 = (let _198_763 = (let _198_762 = (FStar_Syntax_Syntax.mk_binder x)
in (_198_762)::[])
in (FStar_Syntax_Subst.open_term _198_763 e2))
in (match (_95_1811) with
| (xb, e2) -> begin
(let xbinder = (FStar_List.hd xb)
in (let x = (Prims.fst xbinder)
in (let _95_1817 = (let _198_764 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _198_764 e2))
in (match (_95_1817) with
| (e2, c2, g2) -> begin
(let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (x), c2))
in (let e = (let _198_767 = (let _198_766 = (let _198_765 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _198_765))
in FStar_Syntax_Syntax.Tm_let (_198_766))
in (FStar_Syntax_Syntax.mk _198_767 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (let x_eq_e1 = (let _198_770 = (let _198_769 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _198_769 e1))
in (FStar_All.pipe_left (fun _198_768 -> FStar_TypeChecker_Common.NonTrivial (_198_768)) _198_770))
in (let g2 = (let _198_772 = (let _198_771 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _198_771 g2))
in (FStar_TypeChecker_Rel.close_guard xb _198_772))
in (let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if annotated then begin
(e, cres, guard)
end else begin
(let _95_1823 = (check_no_escape env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end)))))
end))))
end))))
end)))
end
| _95_1826 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(let _95_1838 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_95_1838) with
| (lbs, e2) -> begin
(let _95_1841 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_95_1841) with
| (env0, topt) -> begin
(let _95_1844 = (build_let_rec_env true env0 lbs)
in (match (_95_1844) with
| (lbs, rec_env) -> begin
(let _95_1847 = (check_let_recs rec_env lbs)
in (match (_95_1847) with
| (lbs, g_lbs) -> begin
(let g_lbs = (let _198_775 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _198_775 FStar_TypeChecker_Rel.resolve_implicits))
in (let all_lb_names = (let _198_778 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _198_778 (fun _198_777 -> Some (_198_777))))
in (let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(let ecs = (let _198_782 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _198_781 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _198_781)))))
in (FStar_TypeChecker_Util.generalize env _198_782))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _95_1858 -> (match (_95_1858) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (let cres = (let _198_784 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Recheck.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _198_784))
in (let _95_1861 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Recheck.t_unit.FStar_Syntax_Syntax.n)))
in (let _95_1865 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_95_1865) with
| (lbs, e2) -> begin
(let _198_786 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Recheck.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _198_785 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_198_786, cres, _198_785)))
end)))))))
end))
end))
end))
end))
end
| _95_1867 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(let _95_1879 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_95_1879) with
| (lbs, e2) -> begin
(let _95_1882 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_95_1882) with
| (env0, topt) -> begin
(let _95_1885 = (build_let_rec_env false env0 lbs)
in (match (_95_1885) with
| (lbs, rec_env) -> begin
(let _95_1888 = (check_let_recs rec_env lbs)
in (match (_95_1888) with
| (lbs, g_lbs) -> begin
(let _95_1906 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _95_1891 _95_1900 -> (match ((_95_1891, _95_1900)) with
| ((bvs, env), {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _95_1898; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _95_1895; FStar_Syntax_Syntax.lbdef = _95_1893}) -> begin
(let env = (FStar_TypeChecker_Env.push_let_binding env x ([], t))
in (let _198_792 = (let _198_791 = (let _95_1902 = (FStar_Util.left x)
in {FStar_Syntax_Syntax.ppname = _95_1902.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _95_1902.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (_198_791)::bvs)
in (_198_792, env)))
end)) ([], env)))
in (match (_95_1906) with
| (bvs, env) -> begin
(let bvs = (FStar_List.rev bvs)
in (let _95_1911 = (tc_term env e2)
in (match (_95_1911) with
| (e2, cres, g2) -> begin
(let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (let cres = (let _95_1915 = cres
in {FStar_Syntax_Syntax.eff_name = _95_1915.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _95_1915.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _95_1915.FStar_Syntax_Syntax.comp})
in (let _95_1920 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_95_1920) with
| (lbs, e2) -> begin
(let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_95_1923) -> begin
(e, cres, guard)
end
| None -> begin
(let _95_1926 = (check_no_escape env bvs tres)
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
| _95_1929 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (let env0 = env
in (let _95_1962 = (FStar_List.fold_left (fun _95_1936 lb -> (match (_95_1936) with
| (lbs, env) -> begin
(let _95_1941 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_95_1941) with
| (univ_vars, t, check_t) -> begin
(let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(let _95_1950 = (let _198_799 = (let _198_798 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _198_798))
in (tc_check_tot_or_gtot_term (let _95_1944 = env0
in {FStar_TypeChecker_Env.solver = _95_1944.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _95_1944.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _95_1944.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _95_1944.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _95_1944.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _95_1944.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _95_1944.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _95_1944.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _95_1944.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _95_1944.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _95_1944.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _95_1944.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _95_1944.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _95_1944.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _95_1944.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _95_1944.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _95_1944.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _95_1944.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _95_1944.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _95_1944.FStar_TypeChecker_Env.use_bv_sorts}) t _198_799))
in (match (_95_1950) with
| (t, _95_1948, g) -> begin
(let _95_1951 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(let _95_1954 = env
in {FStar_TypeChecker_Env.solver = _95_1954.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _95_1954.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _95_1954.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _95_1954.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _95_1954.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _95_1954.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _95_1954.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _95_1954.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _95_1954.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _95_1954.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _95_1954.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _95_1954.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _95_1954.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _95_1954.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _95_1954.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _95_1954.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _95_1954.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _95_1954.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _95_1954.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _95_1954.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (let lb = (let _95_1957 = lb
in {FStar_Syntax_Syntax.lbname = _95_1957.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _95_1957.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_95_1962) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (let _95_1975 = (let _198_804 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _95_1969 = (let _198_803 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _198_803 lb.FStar_Syntax_Syntax.lbdef))
in (match (_95_1969) with
| (e, c, g) -> begin
(let _95_1970 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _198_804 FStar_List.unzip))
in (match (_95_1975) with
| (lbs, gs) -> begin
(let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (let _95_1983 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_95_1983) with
| (env1, _95_1982) -> begin
(let e1 = lb.FStar_Syntax_Syntax.lbdef
in (let _95_1989 = (check_lbtyp top_level env lb)
in (match (_95_1989) with
| (topt, wf_annot, univ_vars, env1) -> begin
(let _95_1990 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (let _95_1997 = (tc_maybe_toplevel_term (let _95_1992 = env1
in {FStar_TypeChecker_Env.solver = _95_1992.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _95_1992.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _95_1992.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _95_1992.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _95_1992.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _95_1992.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _95_1992.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _95_1992.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _95_1992.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _95_1992.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _95_1992.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _95_1992.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _95_1992.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _95_1992.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _95_1992.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _95_1992.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _95_1992.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _95_1992.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _95_1992.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _95_1992.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_95_1997) with
| (e1, c1, g1) -> begin
(let _95_2001 = (let _198_811 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _95_1998 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _198_811 e1 c1 wf_annot))
in (match (_95_2001) with
| (c1, guard_f) -> begin
(let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (let _95_2003 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _198_812 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _198_812))
end else begin
()
end
in (let _198_813 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _198_813))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _95_2010 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _95_2013 -> begin
(let _95_2016 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_95_2016) with
| (univ_vars, t) -> begin
(let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _198_817 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _198_817))
end else begin
(let _95_2021 = (FStar_Syntax_Util.type_u ())
in (match (_95_2021) with
| (k, _95_2020) -> begin
(let _95_2026 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_95_2026) with
| (t, _95_2024, g) -> begin
(let _95_2027 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _198_820 = (let _198_818 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _198_818))
in (let _198_819 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _198_820 _198_819)))
end else begin
()
end
in (let t = (norm env1 t)
in (let _198_821 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _198_821))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _95_2033 -> (match (_95_2033) with
| (x, imp) -> begin
(let _95_2036 = (FStar_Syntax_Util.type_u ())
in (match (_95_2036) with
| (tu, u) -> begin
(let _95_2041 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_95_2041) with
| (t, _95_2039, g) -> begin
(let x = ((let _95_2042 = x
in {FStar_Syntax_Syntax.ppname = _95_2042.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _95_2042.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (let _95_2045 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _198_825 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _198_824 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _198_825 _198_824)))
end else begin
()
end
in (let _198_826 = (maybe_push_binding env x)
in (x, _198_826, g, u))))
end))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe Prims.list) = (fun env bs -> (let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_TypeChecker_Rel.trivial_guard, [])
end
| b::bs -> begin
(let _95_2060 = (tc_binder env b)
in (match (_95_2060) with
| (b, env', g, u) -> begin
(let _95_2065 = (aux env' bs)
in (match (_95_2065) with
| (bs, env', g', us) -> begin
(let _198_834 = (let _198_833 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _198_833))
in ((b)::bs, env', _198_834, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (let tc_args = (fun env args -> (FStar_List.fold_right (fun _95_2073 _95_2076 -> (match ((_95_2073, _95_2076)) with
| ((t, imp), (args, g)) -> begin
(let _95_2081 = (tc_term env t)
in (match (_95_2081) with
| (t, _95_2079, g') -> begin
(let _198_843 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _198_843))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _95_2085 -> (match (_95_2085) with
| (pats, g) -> begin
(let _95_2088 = (tc_args env p)
in (match (_95_2088) with
| (args, g') -> begin
(let _198_846 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _198_846))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (let _95_2094 = (tc_maybe_toplevel_term env e)
in (match (_95_2094) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (let c = (c.FStar_Syntax_Syntax.comp ())
in (let _95_2097 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _198_849 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _198_849))
end else begin
()
end
in (let c = (norm_c env c)
in (let _95_2102 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _198_850 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_198_850, false))
end else begin
(let _198_851 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_198_851, true))
end
in (match (_95_2102) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _198_852 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _198_852))
end
| _95_2106 -> begin
if allow_ghost then begin
(let _198_855 = (let _198_854 = (let _198_853 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_198_853, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_198_854))
in (Prims.raise _198_855))
end else begin
(let _198_858 = (let _198_857 = (let _198_856 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_198_856, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_198_857))
in (Prims.raise _198_858))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))

let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (let _95_2116 = (tc_tot_or_gtot_term env t)
in (match (_95_2116) with
| (t, c, g) -> begin
(let _95_2117 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))

let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (let _95_2125 = (tc_check_tot_or_gtot_term env t k)
in (match (_95_2125) with
| (t, c, g) -> begin
(let _95_2126 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))

let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _198_878 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _198_878)))

let check_nogen = (fun env t k -> (let t = (tc_check_trivial_guard env t k)
in (let _198_882 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _198_882))))

let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (let _95_2141 = (tc_binders env tps)
in (match (_95_2141) with
| (tps, env, g, us) -> begin
(let _95_2142 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))

let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (let fail = (fun _95_2148 -> (match (()) with
| () -> begin
(let _198_897 = (let _198_896 = (let _198_895 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_198_895, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_198_896))
in (Prims.raise _198_897))
end))
in (let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _95_2165)::(wp, _95_2161)::(_wlp, _95_2157)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _95_2169 -> begin
(fail ())
end))
end
| _95_2171 -> begin
(fail ())
end))))

let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(let _95_2178 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_95_2178) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _95_2180 -> begin
(let t' = (FStar_Syntax_Util.arrow binders c)
in (let _95_2184 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_95_2184) with
| (uvs, t') -> begin
(match ((let _198_904 = (FStar_Syntax_Subst.compress t')
in _198_904.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _95_2190 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (let fail = (fun t -> (let _198_913 = (let _198_912 = (let _198_911 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env ed.FStar_Syntax_Syntax.mname t)
in (_198_911, (FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname)))
in FStar_Syntax_Syntax.Error (_198_912))
in (Prims.raise _198_913)))
in (let _95_2219 = (match ((let _198_914 = (FStar_Syntax_Subst.compress ed.FStar_Syntax_Syntax.signature)
in _198_914.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _95_2210)::(wp, _95_2206)::(_wlp, _95_2202)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _95_2214 -> begin
(fail ed.FStar_Syntax_Syntax.signature)
end))
end
| _95_2216 -> begin
(fail ed.FStar_Syntax_Syntax.signature)
end)
in (match (_95_2219) with
| (a, wp) -> begin
(let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _95_2222 -> begin
(let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (let op = (fun ts -> (let _95_2226 = ()
in (let t0 = (Prims.snd ts)
in (let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (let _95_2230 = ed
in (let _198_929 = (op ed.FStar_Syntax_Syntax.ret)
in (let _198_928 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _198_927 = (op ed.FStar_Syntax_Syntax.bind_wlp)
in (let _198_926 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _198_925 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _198_924 = (op ed.FStar_Syntax_Syntax.ite_wlp)
in (let _198_923 = (op ed.FStar_Syntax_Syntax.wp_binop)
in (let _198_922 = (op ed.FStar_Syntax_Syntax.wp_as_type)
in (let _198_921 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _198_920 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _198_919 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _198_918 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _198_917 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _95_2230.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _95_2230.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _95_2230.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _95_2230.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _95_2230.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _198_929; FStar_Syntax_Syntax.bind_wp = _198_928; FStar_Syntax_Syntax.bind_wlp = _198_927; FStar_Syntax_Syntax.if_then_else = _198_926; FStar_Syntax_Syntax.ite_wp = _198_925; FStar_Syntax_Syntax.ite_wlp = _198_924; FStar_Syntax_Syntax.wp_binop = _198_923; FStar_Syntax_Syntax.wp_as_type = _198_922; FStar_Syntax_Syntax.close_wp = _198_921; FStar_Syntax_Syntax.assert_p = _198_920; FStar_Syntax_Syntax.assume_p = _198_919; FStar_Syntax_Syntax.null_wp = _198_918; FStar_Syntax_Syntax.trivial = _198_917}))))))))))))))))
end)
in (ed, a, wp))
end))))

let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (let _95_2235 = ()
in (let _95_2239 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_95_2239) with
| (binders, signature) -> begin
(let _95_2244 = (tc_tparams env0 binders)
in (match (_95_2244) with
| (binders, env, _95_2243) -> begin
(let _95_2248 = (tc_trivial_guard env signature)
in (match (_95_2248) with
| (signature, _95_2247) -> begin
(let ed = (let _95_2249 = ed
in {FStar_Syntax_Syntax.qualifiers = _95_2249.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _95_2249.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _95_2249.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _95_2249.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _95_2249.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _95_2249.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = _95_2249.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _95_2249.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _95_2249.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = _95_2249.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _95_2249.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _95_2249.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _95_2249.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _95_2249.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _95_2249.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _95_2249.FStar_Syntax_Syntax.trivial})
in (let _95_2255 = (open_effect_decl env ed)
in (match (_95_2255) with
| (ed, a, wp_a) -> begin
(let env = (let _198_934 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _198_934))
in (let _95_2257 = if (FStar_TypeChecker_Env.debug env0 FStar_Options.Low) then begin
(let _198_937 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _198_936 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _198_935 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checked effect signature: %s %s : %s\n" _198_937 _198_936 _198_935))))
end else begin
()
end
in (let check_and_gen' = (fun env _95_2264 k -> (match (_95_2264) with
| (_95_2262, t) -> begin
(check_and_gen env t k)
end))
in (let ret = (let expected_k = (let _198_949 = (let _198_947 = (FStar_Syntax_Syntax.mk_binder a)
in (let _198_946 = (let _198_945 = (let _198_944 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _198_944))
in (_198_945)::[])
in (_198_947)::_198_946))
in (let _198_948 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _198_949 _198_948)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (let bind_wp = (let wlp_a = wp_a
in (let b = (let _198_951 = (let _198_950 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _198_950 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _198_951))
in (let wp_b = (let _198_955 = (let _198_954 = (let _198_953 = (let _198_952 = (FStar_Syntax_Syntax.bv_to_name b)
in (a, _198_952))
in FStar_Syntax_Syntax.NT (_198_953))
in (_198_954)::[])
in (FStar_Syntax_Subst.subst _198_955 wp_a))
in (let a_wp_b = (let _198_959 = (let _198_957 = (let _198_956 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _198_956))
in (_198_957)::[])
in (let _198_958 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _198_959 _198_958)))
in (let a_wlp_b = a_wp_b
in (let expected_k = (let _198_972 = (let _198_970 = (FStar_Syntax_Syntax.mk_binder a)
in (let _198_969 = (let _198_968 = (FStar_Syntax_Syntax.mk_binder b)
in (let _198_967 = (let _198_966 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _198_965 = (let _198_964 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _198_963 = (let _198_962 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (let _198_961 = (let _198_960 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_198_960)::[])
in (_198_962)::_198_961))
in (_198_964)::_198_963))
in (_198_966)::_198_965))
in (_198_968)::_198_967))
in (_198_970)::_198_969))
in (let _198_971 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _198_972 _198_971)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))))))
in (let bind_wlp = (let wlp_a = wp_a
in (let b = (let _198_974 = (let _198_973 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _198_973 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _198_974))
in (let wlp_b = (let _198_978 = (let _198_977 = (let _198_976 = (let _198_975 = (FStar_Syntax_Syntax.bv_to_name b)
in (a, _198_975))
in FStar_Syntax_Syntax.NT (_198_976))
in (_198_977)::[])
in (FStar_Syntax_Subst.subst _198_978 wlp_a))
in (let a_wlp_b = (let _198_982 = (let _198_980 = (let _198_979 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _198_979))
in (_198_980)::[])
in (let _198_981 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _198_982 _198_981)))
in (let expected_k = (let _198_991 = (let _198_989 = (FStar_Syntax_Syntax.mk_binder a)
in (let _198_988 = (let _198_987 = (FStar_Syntax_Syntax.mk_binder b)
in (let _198_986 = (let _198_985 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _198_984 = (let _198_983 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_198_983)::[])
in (_198_985)::_198_984))
in (_198_987)::_198_986))
in (_198_989)::_198_988))
in (let _198_990 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _198_991 _198_990)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wlp expected_k))))))
in (let if_then_else = (let p = (let _198_993 = (let _198_992 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _198_992 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _198_993))
in (let expected_k = (let _198_1002 = (let _198_1000 = (FStar_Syntax_Syntax.mk_binder a)
in (let _198_999 = (let _198_998 = (FStar_Syntax_Syntax.mk_binder p)
in (let _198_997 = (let _198_996 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _198_995 = (let _198_994 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_198_994)::[])
in (_198_996)::_198_995))
in (_198_998)::_198_997))
in (_198_1000)::_198_999))
in (let _198_1001 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _198_1002 _198_1001)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (let ite_wp = (let wlp_a = wp_a
in (let expected_k = (let _198_1009 = (let _198_1007 = (FStar_Syntax_Syntax.mk_binder a)
in (let _198_1006 = (let _198_1005 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _198_1004 = (let _198_1003 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_198_1003)::[])
in (_198_1005)::_198_1004))
in (_198_1007)::_198_1006))
in (let _198_1008 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _198_1009 _198_1008)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k)))
in (let ite_wlp = (let wlp_a = wp_a
in (let expected_k = (let _198_1014 = (let _198_1012 = (FStar_Syntax_Syntax.mk_binder a)
in (let _198_1011 = (let _198_1010 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (_198_1010)::[])
in (_198_1012)::_198_1011))
in (let _198_1013 = (FStar_Syntax_Syntax.mk_Total wlp_a)
in (FStar_Syntax_Util.arrow _198_1014 _198_1013)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wlp expected_k)))
in (let wp_binop = (let bin_op = (let _95_2292 = (FStar_Syntax_Util.type_u ())
in (match (_95_2292) with
| (t1, u1) -> begin
(let _95_2295 = (FStar_Syntax_Util.type_u ())
in (match (_95_2295) with
| (t2, u2) -> begin
(let t = (let _198_1015 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_max ((u1)::(u2)::[]))) None _198_1015))
in (let _198_1020 = (let _198_1018 = (FStar_Syntax_Syntax.null_binder t1)
in (let _198_1017 = (let _198_1016 = (FStar_Syntax_Syntax.null_binder t2)
in (_198_1016)::[])
in (_198_1018)::_198_1017))
in (let _198_1019 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _198_1020 _198_1019))))
end))
end))
in (let expected_k = (let _198_1029 = (let _198_1027 = (FStar_Syntax_Syntax.mk_binder a)
in (let _198_1026 = (let _198_1025 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _198_1024 = (let _198_1023 = (FStar_Syntax_Syntax.null_binder bin_op)
in (let _198_1022 = (let _198_1021 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_198_1021)::[])
in (_198_1023)::_198_1022))
in (_198_1025)::_198_1024))
in (_198_1027)::_198_1026))
in (let _198_1028 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _198_1029 _198_1028)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_binop expected_k)))
in (let wp_as_type = (let _95_2303 = (FStar_Syntax_Util.type_u ())
in (match (_95_2303) with
| (t, _95_2302) -> begin
(let expected_k = (let _198_1034 = (let _198_1032 = (FStar_Syntax_Syntax.mk_binder a)
in (let _198_1031 = (let _198_1030 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_198_1030)::[])
in (_198_1032)::_198_1031))
in (let _198_1033 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _198_1034 _198_1033)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (let close_wp = (let b = (let _198_1036 = (let _198_1035 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _198_1035 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _198_1036))
in (let b_wp_a = (let _198_1040 = (let _198_1038 = (let _198_1037 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _198_1037))
in (_198_1038)::[])
in (let _198_1039 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _198_1040 _198_1039)))
in (let expected_k = (let _198_1047 = (let _198_1045 = (FStar_Syntax_Syntax.mk_binder a)
in (let _198_1044 = (let _198_1043 = (FStar_Syntax_Syntax.mk_binder b)
in (let _198_1042 = (let _198_1041 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_198_1041)::[])
in (_198_1043)::_198_1042))
in (_198_1045)::_198_1044))
in (let _198_1046 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _198_1047 _198_1046)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (let assert_p = (let expected_k = (let _198_1056 = (let _198_1054 = (FStar_Syntax_Syntax.mk_binder a)
in (let _198_1053 = (let _198_1052 = (let _198_1049 = (let _198_1048 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _198_1048 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _198_1049))
in (let _198_1051 = (let _198_1050 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_198_1050)::[])
in (_198_1052)::_198_1051))
in (_198_1054)::_198_1053))
in (let _198_1055 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _198_1056 _198_1055)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (let assume_p = (let expected_k = (let _198_1065 = (let _198_1063 = (FStar_Syntax_Syntax.mk_binder a)
in (let _198_1062 = (let _198_1061 = (let _198_1058 = (let _198_1057 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _198_1057 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _198_1058))
in (let _198_1060 = (let _198_1059 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_198_1059)::[])
in (_198_1061)::_198_1060))
in (_198_1063)::_198_1062))
in (let _198_1064 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _198_1065 _198_1064)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (let null_wp = (let expected_k = (let _198_1068 = (let _198_1066 = (FStar_Syntax_Syntax.mk_binder a)
in (_198_1066)::[])
in (let _198_1067 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _198_1068 _198_1067)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (let trivial_wp = (let _95_2319 = (FStar_Syntax_Util.type_u ())
in (match (_95_2319) with
| (t, _95_2318) -> begin
(let expected_k = (let _198_1073 = (let _198_1071 = (FStar_Syntax_Syntax.mk_binder a)
in (let _198_1070 = (let _198_1069 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_198_1069)::[])
in (_198_1071)::_198_1070))
in (let _198_1072 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _198_1073 _198_1072)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (let t = (let _198_1074 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _198_1074))
in (let _95_2325 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_95_2325) with
| (univs, t) -> begin
(let _95_2341 = (match ((let _198_1076 = (let _198_1075 = (FStar_Syntax_Subst.compress t)
in _198_1075.FStar_Syntax_Syntax.n)
in (binders, _198_1076))) with
| ([], _95_2328) -> begin
([], t)
end
| (_95_2331, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _95_2338 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_95_2341) with
| (binders, signature) -> begin
(let close = (fun ts -> (let _198_1079 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _198_1079)))
in (let ed = (let _95_2344 = ed
in (let _198_1092 = (close ret)
in (let _198_1091 = (close bind_wp)
in (let _198_1090 = (close bind_wlp)
in (let _198_1089 = (close if_then_else)
in (let _198_1088 = (close ite_wp)
in (let _198_1087 = (close ite_wlp)
in (let _198_1086 = (close wp_binop)
in (let _198_1085 = (close wp_as_type)
in (let _198_1084 = (close close_wp)
in (let _198_1083 = (close assert_p)
in (let _198_1082 = (close assume_p)
in (let _198_1081 = (close null_wp)
in (let _198_1080 = (close trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _95_2344.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _95_2344.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _198_1092; FStar_Syntax_Syntax.bind_wp = _198_1091; FStar_Syntax_Syntax.bind_wlp = _198_1090; FStar_Syntax_Syntax.if_then_else = _198_1089; FStar_Syntax_Syntax.ite_wp = _198_1088; FStar_Syntax_Syntax.ite_wlp = _198_1087; FStar_Syntax_Syntax.wp_binop = _198_1086; FStar_Syntax_Syntax.wp_as_type = _198_1085; FStar_Syntax_Syntax.close_wp = _198_1084; FStar_Syntax_Syntax.assert_p = _198_1083; FStar_Syntax_Syntax.assume_p = _198_1082; FStar_Syntax_Syntax.null_wp = _198_1081; FStar_Syntax_Syntax.trivial = _198_1080}))))))))))))))
in (let _95_2347 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_1093 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _198_1093))
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

let tc_lex_t = (fun env ses quals lids -> (let _95_2353 = ()
in (let _95_2361 = ()
in (match (ses) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _95_2390, _95_2392, [], r)::FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _95_2381, r1)::FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _95_2370, r2)::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (let tc = FStar_Syntax_Syntax.Sig_inductive_typ ((lex_t, (u)::[], [], t, [], (FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[], [], r))
in (let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (let lex_top_t = (let _198_1100 = (let _198_1099 = (let _198_1098 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid r1)
in (_198_1098, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_198_1099))
in (FStar_Syntax_Syntax.mk _198_1100 None r1))
in (let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (let dc_lextop = FStar_Syntax_Syntax.Sig_datacon ((lex_top, (utop)::[], lex_top_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r1))
in (let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (let lex_cons_t = (let a = (let _198_1101 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _198_1101))
in (let hd = (let _198_1102 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _198_1102))
in (let tl = (let _198_1106 = (let _198_1105 = (let _198_1104 = (let _198_1103 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid r2)
in (_198_1103, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_198_1104))
in (FStar_Syntax_Syntax.mk _198_1105 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _198_1106))
in (let res = (let _198_1109 = (let _198_1108 = (let _198_1107 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid r2)
in (_198_1107, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_198_1108))
in (FStar_Syntax_Syntax.mk _198_1109 None r2))
in (let _198_1110 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.Implicit)))::((hd, None))::((tl, None))::[]) _198_1110))))))
in (let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _198_1112 = (let _198_1111 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _198_1111))
in FStar_Syntax_Syntax.Sig_bundle (_198_1112)))))))))))))))
end
| _95_2416 -> begin
(let _198_1114 = (let _198_1113 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _198_1113))
in (FStar_All.failwith _198_1114))
end))))

let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (let warn_positivity = (fun l r -> (let _198_1128 = (let _198_1127 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _198_1127))
in (FStar_TypeChecker_Errors.warn r _198_1128)))
in (let env0 = env
in (let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(let _95_2438 = ()
in (let _95_2440 = (warn_positivity tc r)
in (let _95_2444 = (FStar_Syntax_Subst.open_term tps k)
in (match (_95_2444) with
| (tps, k) -> begin
(let _95_2448 = (tc_tparams env tps)
in (match (_95_2448) with
| (tps, env_tps, us) -> begin
(let _95_2451 = (FStar_Syntax_Util.arrow_formals k)
in (match (_95_2451) with
| (indices, t) -> begin
(let _95_2455 = (tc_tparams env_tps indices)
in (match (_95_2455) with
| (indices, env', us') -> begin
(let _95_2459 = (tc_trivial_guard env' t)
in (match (_95_2459) with
| (t, _95_2458) -> begin
(let k = (let _198_1133 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _198_1133))
in (let _95_2463 = (FStar_Syntax_Util.type_u ())
in (match (_95_2463) with
| (t_type, u) -> begin
(let _95_2464 = (let _198_1134 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _198_1134))
in (let refined_tps = (FStar_All.pipe_right tps (FStar_List.map (fun _95_2468 -> (match (_95_2468) with
| (x, imp) -> begin
(let y = (FStar_Syntax_Syntax.freshen_bv x)
in (let refined = (let _198_1138 = (let _198_1137 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _198_1136 = (FStar_Syntax_Syntax.bv_to_name y)
in (FStar_Syntax_Util.mk_eq x.FStar_Syntax_Syntax.sort x.FStar_Syntax_Syntax.sort _198_1137 _198_1136)))
in (FStar_Syntax_Util.refine y _198_1138))
in ((let _95_2471 = x
in {FStar_Syntax_Syntax.ppname = _95_2471.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _95_2471.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = refined}), imp)))
end))))
in (let t_tc = (let _198_1139 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append refined_tps indices) _198_1139))
in (let tps = (FStar_Syntax_Subst.close_binders tps)
in (let k = (FStar_Syntax_Subst.close tps k)
in (let _198_1140 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (tc)) ([], t_tc))
in (_198_1140, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u)))))))
end)))
end))
end))
end))
end))
end))))
end
| _95_2478 -> begin
(FStar_All.failwith "impossible")
end))
in (let positive_if_pure = (fun _95_2480 l -> ())
in (let tc_data = (fun env tcs _95_6 -> (match (_95_6) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(let _95_2497 = ()
in (let _95_2528 = (let _198_1155 = (FStar_Util.find_map tcs (fun _95_2501 -> (match (_95_2501) with
| (se, u_tc) -> begin
if (let _198_1153 = (let _198_1152 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _198_1152))
in (FStar_Ident.lid_equals tc_lid _198_1153)) then begin
(let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_95_2503, _95_2505, tps, _95_2508, _95_2510, _95_2512, _95_2514, _95_2516) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _95_2522 -> (match (_95_2522) with
| (x, _95_2521) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit))
end))))
end
| _95_2524 -> begin
(FStar_All.failwith "Impossible")
end)
in Some ((tps, u_tc)))
end else begin
None
end
end)))
in (FStar_All.pipe_right _198_1155 FStar_Util.must))
in (match (_95_2528) with
| (tps, u_tc) -> begin
(let _95_2548 = (match ((let _198_1156 = (FStar_Syntax_Subst.compress t)
in _198_1156.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(let _95_2536 = (FStar_Util.first_N ntps bs)
in (match (_95_2536) with
| (_95_2534, bs') -> begin
(let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _95_2542 -> (match (_95_2542) with
| (x, _95_2541) -> begin
(let _198_1160 = (let _198_1159 = (FStar_Syntax_Syntax.bv_to_name x)
in ((ntps - (1 + i)), _198_1159))
in FStar_Syntax_Syntax.DB (_198_1160))
end))))
in (let _198_1161 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _198_1161))))
end))
end
| _95_2545 -> begin
([], t)
end)
in (match (_95_2548) with
| (arguments, result) -> begin
(let _95_2549 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_1164 = (FStar_Syntax_Print.lid_to_string c)
in (let _198_1163 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _198_1162 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _198_1164 _198_1163 _198_1162))))
end else begin
()
end
in (let _95_2554 = (tc_tparams env arguments)
in (match (_95_2554) with
| (arguments, env', us) -> begin
(let _95_2558 = (tc_trivial_guard env' result)
in (match (_95_2558) with
| (result, _95_2557) -> begin
(let _95_2562 = (FStar_Syntax_Util.head_and_args result)
in (match (_95_2562) with
| (head, _95_2561) -> begin
(let _95_2570 = (match ((let _198_1165 = (FStar_Syntax_Subst.compress head)
in _198_1165.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _95_2565) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v tc_lid) -> begin
()
end
| _95_2569 -> begin
(let _198_1169 = (let _198_1168 = (let _198_1167 = (let _198_1166 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _198_1166))
in (_198_1167, r))
in FStar_Syntax_Syntax.Error (_198_1168))
in (Prims.raise _198_1169))
end)
in (let g = (FStar_List.fold_left2 (fun g _95_2576 u_x -> (match (_95_2576) with
| (x, _95_2575) -> begin
(let _95_2578 = ()
in (let _198_1173 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _198_1173)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (let t = (let _198_1174 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow (FStar_List.append tps arguments) _198_1174))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _95_2583 -> begin
(FStar_All.failwith "impossible")
end))
in (let generalize_and_recheck = (fun env g tcs datas -> (let _95_2589 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _95_7 -> (match (_95_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_95_2593, _95_2595, tps, k, _95_2599, _95_2601, _95_2603, _95_2605) -> begin
(let _198_1185 = (let _198_1184 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _198_1184))
in (FStar_Syntax_Syntax.null_binder _198_1185))
end
| _95_2609 -> begin
(FStar_All.failwith "Impossible")
end))))
in (let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _95_8 -> (match (_95_8) with
| FStar_Syntax_Syntax.Sig_datacon (_95_2613, _95_2615, t, _95_2618, _95_2620, _95_2622, _95_2624, _95_2626) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _95_2630 -> begin
(FStar_All.failwith "Impossible")
end))))
in (let t = (let _198_1187 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Recheck.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _198_1187))
in (let _95_2633 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_1188 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _198_1188))
end else begin
()
end
in (let _95_2637 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_95_2637) with
| (uvs, t) -> begin
(let _95_2639 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_1192 = (let _198_1190 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _198_1190 (FStar_String.concat ", ")))
in (let _198_1191 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _198_1192 _198_1191)))
end else begin
()
end
in (let _95_2643 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_95_2643) with
| (uvs, t) -> begin
(let _95_2647 = (FStar_Syntax_Util.arrow_formals t)
in (match (_95_2647) with
| (args, _95_2646) -> begin
(let _95_2650 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_95_2650) with
| (tc_types, data_types) -> begin
(let tcs = (FStar_List.map2 (fun _95_2654 se -> (match (_95_2654) with
| (x, _95_2653) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _95_2658, tps, _95_2661, mutuals, datas, quals, r) -> begin
(let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (let _95_2684 = (match ((let _198_1195 = (FStar_Syntax_Subst.compress ty)
in _198_1195.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(let _95_2675 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_95_2675) with
| (tps, rest) -> begin
(let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _95_2678 -> begin
(let _198_1196 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _198_1196 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _95_2681 -> begin
([], ty)
end)
in (match (_95_2684) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _95_2686 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (let env_data = (FStar_TypeChecker_Env.push_univ_vars env uvs)
in (let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _198_1197 -> FStar_Syntax_Syntax.U_name (_198_1197))))
in (let env_data = (FStar_List.fold_left (fun env tc -> (FStar_TypeChecker_Env.push_sigelt_inst env tc uvs_universes)) env_data tcs)
in (let datas = (FStar_List.map2 (fun _95_2696 -> (match (_95_2696) with
| (t, _95_2695) -> begin
(fun _95_9 -> (match (_95_9) with
| FStar_Syntax_Syntax.Sig_datacon (l, _95_2700, _95_2702, tc, ntps, quals, mutuals, r) -> begin
(let ty = (match (uvs) with
| [] -> begin
t.FStar_Syntax_Syntax.sort
end
| _95_2712 -> begin
(let _95_2713 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_1205 = (FStar_Syntax_Print.lid_to_string l)
in (let _198_1204 = (FStar_Syntax_Print.term_to_string t.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Rechecking datacon %s : %s\n" _198_1205 _198_1204)))
end else begin
()
end
in (let _95_2719 = (tc_tot_or_gtot_term env_data t.FStar_Syntax_Syntax.sort)
in (match (_95_2719) with
| (ty, _95_2717, g) -> begin
(let g = (let _95_2720 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _95_2720.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _95_2720.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _95_2720.FStar_TypeChecker_Env.implicits})
in (let _95_2723 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Subst.close_univ_vars uvs ty)))
end)))
end)
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _95_2727 -> begin
(FStar_All.failwith "Impossible")
end))
end)) data_types datas)
in (tcs, datas))))))
end))
end))
end)))
end))))))))
in (let _95_2737 = (FStar_All.pipe_right ses (FStar_List.partition (fun _95_10 -> (match (_95_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_95_2731) -> begin
true
end
| _95_2734 -> begin
false
end))))
in (match (_95_2737) with
| (tys, datas) -> begin
(let env0 = env
in (let _95_2754 = (FStar_List.fold_right (fun tc _95_2743 -> (match (_95_2743) with
| (env, all_tcs, g) -> begin
(let _95_2747 = (tc_tycon env tc)
in (match (_95_2747) with
| (env, tc, tc_u) -> begin
(let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (let _95_2749 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_1209 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _198_1209))
end else begin
()
end
in (let _198_1210 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _198_1210))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_95_2754) with
| (env, tcs, g) -> begin
(let _95_2764 = (FStar_List.fold_right (fun se _95_2758 -> (match (_95_2758) with
| (datas, g) -> begin
(let _95_2761 = (tc_data env tcs se)
in (match (_95_2761) with
| (data, g') -> begin
(let _198_1213 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _198_1213))
end))
end)) datas ([], g))
in (match (_95_2764) with
| (datas, g) -> begin
(let _95_2767 = (let _198_1214 = (FStar_List.map Prims.fst tcs)
in (generalize_and_recheck env0 g _198_1214 datas))
in (match (_95_2767) with
| (tcs, datas) -> begin
(let _198_1216 = (let _198_1215 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _198_1215))
in FStar_Syntax_Syntax.Sig_bundle (_198_1216))
end))
end))
end)))
end)))))))))

let rec tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.env) = (fun env se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(let env = (FStar_TypeChecker_Env.set_range env r)
in (let se = (tc_lex_t env ses quals lids)
in (let _198_1221 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _198_1221))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(let env = (FStar_TypeChecker_Env.set_range env r)
in (let se = (tc_inductive env ses quals lids)
in (let _198_1222 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _198_1222))))
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
(let _95_2803 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _95_2805 = (let _198_1223 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _198_1223 Prims.ignore))
in (se, env)))
end)
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(let ne = (tc_eff_decl env ne)
in (let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(let _95_2820 = (let _198_1224 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _198_1224))
in (match (_95_2820) with
| (a, wp_a_src) -> begin
(let _95_2823 = (let _198_1225 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _198_1225))
in (match (_95_2823) with
| (b, wp_b_tgt) -> begin
(let wp_a_tgt = (let _198_1229 = (let _198_1228 = (let _198_1227 = (let _198_1226 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _198_1226))
in FStar_Syntax_Syntax.NT (_198_1227))
in (_198_1228)::[])
in (FStar_Syntax_Subst.subst _198_1229 wp_b_tgt))
in (let expected_k = (let _198_1234 = (let _198_1232 = (FStar_Syntax_Syntax.mk_binder a)
in (let _198_1231 = (let _198_1230 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_198_1230)::[])
in (_198_1232)::_198_1231))
in (let _198_1233 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _198_1234 _198_1233)))
in (let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (let sub = (let _95_2827 = sub
in {FStar_Syntax_Syntax.source = _95_2827.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _95_2827.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
in (let se = FStar_Syntax_Syntax.Sig_sub_effect ((sub, r))
in (let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(let _95_2840 = ()
in (let env0 = env
in (let env = (FStar_TypeChecker_Env.set_range env r)
in (let _95_2846 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_95_2846) with
| (tps, c) -> begin
(let _95_2850 = (tc_tparams env tps)
in (match (_95_2850) with
| (tps, env, us) -> begin
(let _95_2854 = (tc_comp env c)
in (match (_95_2854) with
| (c, g, u) -> begin
(let tags = (FStar_All.pipe_right tags (FStar_List.map (fun _95_11 -> (match (_95_11) with
| FStar_Syntax_Syntax.DefaultEffect (None) -> begin
(let c' = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let _198_1237 = (FStar_All.pipe_right c'.FStar_Syntax_Syntax.effect_name (fun _198_1236 -> Some (_198_1236)))
in FStar_Syntax_Syntax.DefaultEffect (_198_1237)))
end
| t -> begin
t
end))))
in (let tps = (FStar_Syntax_Subst.close_binders tps)
in (let c = (FStar_Syntax_Subst.close_comp tps c)
in (let _95_2865 = (let _198_1238 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _198_1238))
in (match (_95_2865) with
| (uvs, t) -> begin
(let _95_2884 = (match ((let _198_1240 = (let _198_1239 = (FStar_Syntax_Subst.compress t)
in _198_1239.FStar_Syntax_Syntax.n)
in (tps, _198_1240))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_95_2868, c)) -> begin
([], c)
end
| (_95_2874, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _95_2881 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_95_2884) with
| (tps, c) -> begin
(let se = FStar_Syntax_Syntax.Sig_effect_abbrev ((lid, uvs, tps, c, tags, r))
in (let env = (FStar_TypeChecker_Env.push_sigelt env0 se)
in (se, env)))
end))
end)))))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t, quals, r) -> begin
(let env = (FStar_TypeChecker_Env.set_range env r)
in (let _95_2895 = ()
in (let k = (let _198_1241 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _198_1241))
in (let _95_2900 = (check_and_gen env t k)
in (match (_95_2900) with
| (uvs, t) -> begin
(let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(let env = (FStar_TypeChecker_Env.set_range env r)
in (let _95_2913 = (FStar_Syntax_Util.type_u ())
in (match (_95_2913) with
| (k, _95_2912) -> begin
(let phi = (let _198_1242 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _198_1242 (norm env)))
in (let _95_2915 = (FStar_TypeChecker_Util.check_uvars r phi)
in (let se = FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))
in (let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(let env = (FStar_TypeChecker_Env.set_range env r)
in (let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Recheck.t_unit)
in (let _95_2928 = (tc_term env e)
in (match (_95_2928) with
| (e, c, g1) -> begin
(let _95_2933 = (let _198_1246 = (let _198_1243 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Recheck.t_unit r)
in Some (_198_1243))
in (let _198_1245 = (let _198_1244 = (c.FStar_Syntax_Syntax.comp ())
in (e, _198_1244))
in (check_expected_effect env _198_1246 _198_1245)))
in (match (_95_2933) with
| (e, _95_2931, g) -> begin
(let _95_2934 = (let _198_1247 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _198_1247))
in (let se = FStar_Syntax_Syntax.Sig_main ((e, r))
in (let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(let env = (FStar_TypeChecker_Env.set_range env r)
in (let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
if (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q')) then begin
Some (q)
end else begin
(let _198_1257 = (let _198_1256 = (let _198_1255 = (let _198_1254 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Inconsistent qualifier annotations on %s" _198_1254))
in (_198_1255, r))
in FStar_Syntax_Syntax.Error (_198_1256))
in (Prims.raise _198_1257))
end
end))
in (let _95_2978 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _95_2955 lb -> (match (_95_2955) with
| (gen, lbs, quals_opt) -> begin
(let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (let _95_2974 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(let quals_opt = (check_quals_eq lbname quals_opt quals)
in (let _95_2969 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _95_2968 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _198_1260 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _198_1260, quals_opt))))
end)
in (match (_95_2974) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_95_2978) with
| (should_generalize, lbs', quals_opt) -> begin
(let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _95_12 -> (match (_95_12) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _95_2987 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (let lbs' = (FStar_List.rev lbs')
in (let e = (let _198_1264 = (let _198_1263 = (let _198_1262 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _198_1262))
in FStar_Syntax_Syntax.Tm_let (_198_1263))
in (FStar_Syntax_Syntax.mk _198_1264 None r))
in (let _95_3021 = (match ((tc_maybe_toplevel_term (let _95_2991 = env
in {FStar_TypeChecker_Env.solver = _95_2991.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _95_2991.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _95_2991.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _95_2991.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _95_2991.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _95_2991.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _95_2991.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _95_2991.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _95_2991.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _95_2991.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _95_2991.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _95_2991.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _95_2991.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _95_2991.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _95_2991.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _95_2991.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _95_2991.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _95_2991.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _95_2991.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _95_2998; FStar_Syntax_Syntax.pos = _95_2996; FStar_Syntax_Syntax.vars = _95_2994}, _95_3005, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_95_3009, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _95_3015 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _95_3018 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_95_3021) with
| (se, lbs) -> begin
(let _95_3027 = if (log env) then begin
(let _198_1270 = (let _198_1269 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let should_log = (match ((let _198_1266 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _198_1266))) with
| None -> begin
true
end
| _95_3025 -> begin
false
end)
in if should_log then begin
(let _198_1268 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _198_1267 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _198_1268 _198_1267)))
end else begin
""
end))))
in (FStar_All.pipe_right _198_1269 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _198_1270))
end else begin
()
end
in (let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end))))
end))

let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (let private_or_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun x -> ((x = FStar_Syntax_Syntax.Private) || (x = FStar_Syntax_Syntax.Abstract))))))
in (let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _95_3044 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_95_3046) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _95_3057, _95_3059) -> begin
if (private_or_abstract quals) then begin
(FStar_List.fold_right (fun se _95_3065 -> (match (_95_3065) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _95_3071, _95_3073, quals, r) -> begin
(let dec = (let _198_1286 = (let _198_1285 = (let _198_1284 = (let _198_1283 = (let _198_1282 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _198_1282))
in FStar_Syntax_Syntax.Tm_arrow (_198_1283))
in (FStar_Syntax_Syntax.mk _198_1284 None r))
in (l, us, _198_1285, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_198_1286))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _95_3083, _95_3085, _95_3087, _95_3089, r) -> begin
(let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _95_3095 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_95_3097, _95_3099, quals, _95_3102) -> begin
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
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _95_13 -> (match (_95_13) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _95_3121 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_95_3123) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _95_3139, _95_3141, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(let lid = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals lid))) then begin
([], hidden)
end else begin
(let dec = FStar_Syntax_Syntax.Sig_declare_typ ((lid, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::[], (FStar_Ident.range_of_lid lid)))
in ((dec)::[], (lid)::hidden))
end)
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (private_or_abstract quals) then begin
(let _198_1291 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _198_1290 = (let _198_1289 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (_198_1289, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_198_1290)))))
in (_198_1291, hidden))
end else begin
((se)::[], hidden)
end
end))))

let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (let _95_3179 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _95_3160 se -> (match (_95_3160) with
| (ses, exports, env, hidden) -> begin
(let _95_3162 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _198_1298 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _198_1298))
end else begin
()
end
in (let _95_3166 = (tc_decl env se)
in (match (_95_3166) with
| (se, env) -> begin
(let _95_3167 = if ((FStar_ST.read FStar_Options.log_types) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _198_1299 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _198_1299))
end else begin
()
end
in (let _95_3169 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (let _95_3173 = (for_export hidden se)
in (match (_95_3173) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_95_3179) with
| (ses, exports, env, _95_3178) -> begin
(let _198_1300 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _198_1300, env))
end)))

let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (let msg = (Prims.strcat "Internals for " name)
in (let env = (let _95_3184 = env
in (let _198_1305 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _95_3184.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _95_3184.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _95_3184.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _95_3184.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _95_3184.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _95_3184.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _95_3184.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _95_3184.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _95_3184.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _95_3184.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _95_3184.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _95_3184.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _95_3184.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _95_3184.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _95_3184.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _95_3184.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _198_1305; FStar_TypeChecker_Env.default_effects = _95_3184.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _95_3184.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _95_3184.FStar_TypeChecker_Env.use_bv_sorts}))
in (let _95_3187 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (let _95_3193 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_95_3193) with
| (ses, exports, env) -> begin
((let _95_3194 = modul
in {FStar_Syntax_Syntax.name = _95_3194.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _95_3194.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _95_3194.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))

let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (let _95_3202 = (tc_decls env decls)
in (match (_95_3202) with
| (ses, exports, env) -> begin
(let modul = (let _95_3203 = modul
in {FStar_Syntax_Syntax.name = _95_3203.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _95_3203.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _95_3203.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))

let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (let modul = (let _95_3209 = modul
in {FStar_Syntax_Syntax.name = _95_3209.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _95_3209.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (let env = (FStar_TypeChecker_Env.finish_module env modul)
in (let _95_3219 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(let _95_3213 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (let _95_3215 = if ((not (modul.FStar_Syntax_Syntax.is_interface)) || (let _198_1318 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_List.contains modul.FStar_Syntax_Syntax.name.FStar_Ident.str _198_1318))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
end else begin
()
end
in (let _95_3217 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _198_1319 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _198_1319 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))

let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (let _95_3226 = (tc_partial_modul env modul)
in (match (_95_3226) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

let add_modul_to_tcenv : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_TypeChecker_Env.env = (fun en m -> (let do_sigelt = (fun en elt -> (let env = (FStar_TypeChecker_Env.push_sigelt en elt)
in (let _95_3233 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env elt)
in env)))
in (let en = (FStar_TypeChecker_Env.set_current_module en m.FStar_Syntax_Syntax.name)
in (let _198_1332 = (FStar_List.fold_left do_sigelt en m.FStar_Syntax_Syntax.exports)
in (FStar_TypeChecker_Env.finish_module _198_1332 m)))))

let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (let _95_3238 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _198_1337 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _198_1337))
end else begin
()
end
in (let env = (let _95_3240 = env
in {FStar_TypeChecker_Env.solver = _95_3240.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _95_3240.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _95_3240.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _95_3240.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _95_3240.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _95_3240.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _95_3240.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _95_3240.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _95_3240.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _95_3240.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _95_3240.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _95_3240.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _95_3240.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _95_3240.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _95_3240.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _95_3240.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _95_3240.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _95_3240.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _95_3240.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _95_3240.FStar_TypeChecker_Env.use_bv_sorts})
in (let _95_3246 = (tc_tot_or_gtot_term env e)
in (match (_95_3246) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected a total term; got a ghost term", e.FStar_Syntax_Syntax.pos))))
end
end)))))

let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (let _95_3249 = if ((let _198_1342 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _198_1342)) <> 0) then begin
(let _198_1343 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _198_1343))
end else begin
()
end
in (let _95_3253 = (tc_modul env m)
in (match (_95_3253) with
| (m, env) -> begin
(let _95_3254 = if (FStar_Options.should_dump m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _198_1344 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _198_1344))
end else begin
()
end
in (m, env))
end))))




