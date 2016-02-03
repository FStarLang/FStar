
open Prims
let log = (fun env -> ((FStar_ST.read FStar_Options.log_types) && (not ((let _181_3 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _181_3))))))

let rng = (fun env -> (FStar_TypeChecker_Env.get_range env))

let instantiate_both = (fun env -> (let _90_17 = env
in {FStar_TypeChecker_Env.solver = _90_17.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _90_17.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _90_17.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _90_17.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _90_17.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _90_17.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _90_17.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _90_17.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _90_17.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _90_17.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _90_17.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _90_17.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _90_17.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _90_17.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _90_17.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _90_17.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _90_17.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _90_17.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _90_17.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _90_17.FStar_TypeChecker_Env.use_bv_sorts}))

let no_inst = (fun env -> (let _90_20 = env
in {FStar_TypeChecker_Env.solver = _90_20.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _90_20.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _90_20.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _90_20.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _90_20.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _90_20.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _90_20.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _90_20.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _90_20.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _90_20.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _90_20.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _90_20.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _90_20.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _90_20.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _90_20.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _90_20.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _90_20.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _90_20.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _90_20.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _90_20.FStar_TypeChecker_Env.use_bv_sorts}))

let mk_lex_list = (fun vs -> (FStar_List.fold_right (fun v tl -> (let r = if (tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
v.FStar_Syntax_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos tl.FStar_Syntax_Syntax.pos)
end
in (let _181_17 = (let _181_16 = (FStar_Syntax_Syntax.as_arg v)
in (let _181_15 = (let _181_14 = (FStar_Syntax_Syntax.as_arg tl)
in (_181_14)::[])
in (_181_16)::_181_15))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _181_17 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))

let is_eq = (fun _90_1 -> (match (_90_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _90_30 -> begin
false
end))

let steps = (fun env -> if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::[]
end else begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]
end)

let unfold_whnf = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Unfold)::(FStar_TypeChecker_Normalize.Beta)::[]) env t))

let norm = (fun env t -> (let _181_30 = (steps env)
in (FStar_TypeChecker_Normalize.normalize _181_30 env t)))

let norm_c = (fun env c -> (let _181_35 = (steps env)
in (FStar_TypeChecker_Normalize.normalize_comp _181_35 env c)))

let fxv_check = (fun head env kt fvs -> (let rec aux = (fun try_norm t -> if (FStar_Util.set_is_empty fvs) then begin
()
end else begin
(let fvs' = (let _181_54 = if try_norm then begin
(norm env t)
end else begin
t
end
in (FStar_Syntax_Free.names _181_54))
in (let a = (FStar_Util.set_intersect fvs fvs')
in if (FStar_Util.set_is_empty a) then begin
()
end else begin
if (not (try_norm)) then begin
(aux true t)
end else begin
(let fail = (fun _90_48 -> (match (()) with
| () -> begin
(let escaping = (let _181_58 = (let _181_57 = (FStar_Util.set_elements a)
in (FStar_All.pipe_right _181_57 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _181_58 (FStar_String.concat ", ")))
in (let msg = if ((FStar_Util.set_count a) > 1) then begin
(let _181_59 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'{%s}\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" escaping _181_59))
end else begin
(let _181_60 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variable \'%s\' in the type of \'%s\' escapes because of impure applications; add explicit let-bindings" escaping _181_60))
end
in (let _181_63 = (let _181_62 = (let _181_61 = (FStar_TypeChecker_Env.get_range env)
in (msg, _181_61))
in FStar_Syntax_Syntax.Error (_181_62))
in (Prims.raise _181_63))))
end))
in (let s = (let _181_64 = (FStar_TypeChecker_Recheck.check t)
in (FStar_TypeChecker_Util.new_uvar env _181_64))
in (match ((FStar_TypeChecker_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g)
end
| _90_55 -> begin
(fail ())
end)))
end
end))
end)
in (aux false kt)))

let check_no_escape = (fun env bs t -> (let fvs = (FStar_Syntax_Free.names t)
in if (FStar_Util.for_some (fun x -> (FStar_Util.set_mem x fvs)) bs) then begin
(let _90_64 = (FStar_Syntax_Util.type_u ())
in (match (_90_64) with
| (k, _90_63) -> begin
(let tnarrow = (FStar_TypeChecker_Util.new_uvar env k)
in (let _181_72 = (FStar_TypeChecker_Rel.teq env t tnarrow)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _181_72)))
end))
end else begin
()
end))

let maybe_push_binding = (fun env b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
env
end else begin
(let _90_68 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _181_78 = (FStar_Syntax_Print.bv_to_string (Prims.fst b))
in (let _181_77 = (FStar_Syntax_Print.term_to_string (Prims.fst b).FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _181_78 _181_77)))
end else begin
()
end
in (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))
end)

let maybe_make_subst = (fun _90_2 -> (match (_90_2) with
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Syntax_Syntax.NT ((x, e)))::[]
end
| _90_77 -> begin
[]
end))

let maybe_extend_subst = (fun s b v -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
s
end else begin
(FStar_Syntax_Syntax.NT (((Prims.fst b), v)))::s
end)

let set_lcomp_result = (fun lc t -> (let _90_83 = lc
in {FStar_Syntax_Syntax.eff_name = _90_83.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _90_83.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _90_85 -> (match (()) with
| () -> begin
(let _181_91 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _181_91 t))
end))}))

let value_check_expected_typ = (fun env e tlc guard -> (let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _181_100 = if (not ((FStar_Syntax_Util.is_pure_or_ghost_function t))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _181_100))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (let t = lc.FStar_Syntax_Syntax.res_typ
in (let _90_117 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, guard)
end
| Some (t') -> begin
(let _90_99 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _181_102 = (FStar_Syntax_Print.term_to_string t)
in (let _181_101 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _181_102 _181_101)))
end else begin
()
end
in (let _90_103 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_90_103) with
| (e, lc) -> begin
(let t = lc.FStar_Syntax_Syntax.res_typ
in (let _90_107 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_90_107) with
| (e, g) -> begin
(let _90_108 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _181_104 = (FStar_Syntax_Print.term_to_string t)
in (let _181_103 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _181_104 _181_103)))
end else begin
()
end
in (let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (let _90_113 = (let _181_110 = (FStar_All.pipe_left (fun _181_109 -> Some (_181_109)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _181_110 env e lc g))
in (match (_90_113) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))))
end)))
end)))
end)
in (match (_90_117) with
| (e, lc, g) -> begin
(let _90_118 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_111 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _181_111))
end else begin
()
end
in (e, lc, g))
end)))))

let comp_check_expected_typ = (fun env e lc -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (t) -> begin
(let _90_128 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_90_128) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))

let check_expected_effect = (fun env copt _90_133 -> (match (_90_133) with
| (e, c) -> begin
(let expected_c_opt = (match (copt) with
| Some (_90_135) -> begin
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
(let _181_124 = (norm_c env c)
in (e, _181_124, FStar_TypeChecker_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(let _90_149 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_127 = (FStar_Syntax_Print.term_to_string e)
in (let _181_126 = (FStar_Syntax_Print.comp_to_string c)
in (let _181_125 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _181_127 _181_126 _181_125))))
end else begin
()
end
in (let c = (norm_c env c)
in (let _90_152 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_130 = (FStar_Syntax_Print.term_to_string e)
in (let _181_129 = (FStar_Syntax_Print.comp_to_string c)
in (let _181_128 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _181_130 _181_129 _181_128))))
end else begin
()
end
in (let _90_158 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_90_158) with
| (e, _90_156, g) -> begin
(let g = (let _181_131 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _181_131 "could not prove post-condition" g))
in (let _90_160 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_133 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _181_132 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _181_133 _181_132)))
end else begin
()
end
in (e, expected_c, g)))
end)))))
end))
end))

let no_logical_guard = (fun env _90_166 -> (match (_90_166) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
(te, kt, f)
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _181_139 = (let _181_138 = (let _181_137 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _181_136 = (FStar_TypeChecker_Env.get_range env)
in (_181_137, _181_136)))
in FStar_Syntax_Syntax.Error (_181_138))
in (Prims.raise _181_139))
end)
end))

let print_expected_ty = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _181_142 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _181_142))
end))

let with_implicits = (fun imps _90_178 -> (match (_90_178) with
| (e, l, g) -> begin
(e, l, (let _90_179 = g
in {FStar_TypeChecker_Env.guard_f = _90_179.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _90_179.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _90_179.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (FStar_List.append imps g.FStar_TypeChecker_Env.implicits)}))
end))

let add_implicit = (fun u g -> (let _90_183 = g
in {FStar_TypeChecker_Env.guard_f = _90_183.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _90_183.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _90_183.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (u)::g.FStar_TypeChecker_Env.implicits}))

let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _90_207; FStar_Syntax_Syntax.result_typ = _90_205; FStar_Syntax_Syntax.effect_args = (pre, _90_201)::(post, _90_197)::(pats, _90_193)::[]; FStar_Syntax_Syntax.flags = _90_190}) -> begin
(let rec extract_pats = (fun pats -> (match ((let _181_155 = (FStar_Syntax_Subst.compress pats)
in _181_155.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (cons, _90_220); FStar_Syntax_Syntax.tk = _90_217; FStar_Syntax_Syntax.pos = _90_215; FStar_Syntax_Syntax.vars = _90_213}, _90_233::(hd, _90_230)::(tl, _90_226)::[]) when (FStar_Ident.lid_equals cons.FStar_Syntax_Syntax.v FStar_Syntax_Const.cons_lid) -> begin
(let _90_239 = (FStar_Syntax_Util.head_and_args hd)
in (match (_90_239) with
| (head, args) -> begin
(let pat = (match (args) with
| (_::arg::[]) | (arg::[]) -> begin
(arg)::[]
end
| _90_246 -> begin
[]
end)
in (let _181_156 = (extract_pats tl)
in (FStar_List.append pat _181_156)))
end))
end
| _90_249 -> begin
[]
end))
in (let pats = (let _181_157 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env pats)
in (extract_pats _181_157))
in (let fvs = (let _181_161 = (FStar_Syntax_Syntax.new_bv_set ())
in (FStar_List.fold_left (fun out _90_255 -> (match (_90_255) with
| (a, _90_254) -> begin
(let _181_160 = (FStar_Syntax_Free.names a)
in (FStar_Util.set_union out _181_160))
end)) _181_161 pats))
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _90_260 -> (match (_90_260) with
| (b, _90_259) -> begin
(not ((FStar_Util.set_mem b fvs)))
end))))) with
| None -> begin
()
end
| Some (x, _90_264) -> begin
(let _181_164 = (let _181_163 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _181_163))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _181_164))
end))))
end
| _90_268 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end)

let guard_letrecs = (fun env actuals expected_c -> (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(let r = (FStar_TypeChecker_Env.get_range env)
in (let env = (let _90_275 = env
in {FStar_TypeChecker_Env.solver = _90_275.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _90_275.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _90_275.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _90_275.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _90_275.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _90_275.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _90_275.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _90_275.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _90_275.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _90_275.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _90_275.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _90_275.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _90_275.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _90_275.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _90_275.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _90_275.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _90_275.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _90_275.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _90_275.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _90_275.FStar_TypeChecker_Env.use_bv_sorts})
in (let precedes = (let _181_171 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.precedes_lid _181_171))
in (let decreases_clause = (fun bs c -> (let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _90_287 -> (match (_90_287) with
| (b, _90_286) -> begin
(let t = (let _181_179 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _181_179))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _90_296 -> begin
(let _181_180 = (FStar_Syntax_Syntax.bv_to_name b)
in (_181_180)::[])
end))
end)))))
in (let as_lex_list = (fun dec -> (let _90_302 = (FStar_Syntax_Util.head_and_args dec)
in (match (_90_302) with
| (head, _90_301) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _90_305) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _90_309 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _90_3 -> (match (_90_3) with
| FStar_Syntax_Syntax.DECREASES (_90_313) -> begin
true
end
| _90_316 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _90_321 -> begin
(let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| x::[] -> begin
x
end
| _90_326 -> begin
(mk_lex_list xs)
end))
end)))))
in (let previous_dec = (decreases_clause actuals expected_c)
in (let guard_one_letrec = (fun _90_331 -> (match (_90_331) with
| (l, t) -> begin
(match ((let _181_186 = (FStar_Syntax_Subst.compress t)
in _181_186.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _90_338 -> (match (_90_338) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _181_190 = (let _181_189 = (let _181_188 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_181_188))
in (FStar_Syntax_Syntax.new_bv _181_189 x.FStar_Syntax_Syntax.sort))
in (_181_190, imp))
end else begin
(x, imp)
end
end))))
in (let _90_342 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_90_342) with
| (formals, c) -> begin
(let dec = (decreases_clause formals c)
in (let precedes = (let _181_194 = (let _181_193 = (FStar_Syntax_Syntax.as_arg dec)
in (let _181_192 = (let _181_191 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_181_191)::[])
in (_181_193)::_181_192))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _181_194 None r))
in (let _90_349 = (FStar_Util.prefix formals)
in (match (_90_349) with
| (bs, (last, imp)) -> begin
(let last = (let _90_350 = last
in (let _181_195 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _90_350.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _90_350.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _181_195}))
in (let refined_formals = (FStar_List.append bs (((last, imp))::[]))
in (let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (let _90_355 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_198 = (FStar_Syntax_Print.lbname_to_string l)
in (let _181_197 = (FStar_Syntax_Print.term_to_string t)
in (let _181_196 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _181_198 _181_197 _181_196))))
end else begin
()
end
in (l, t')))))
end))))
end)))
end
| _90_358 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end))

let rec tc_term = (fun env e -> (tc_maybe_toplevel_term (let _90_361 = env
in {FStar_TypeChecker_Env.solver = _90_361.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _90_361.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _90_361.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _90_361.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _90_361.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _90_361.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _90_361.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _90_361.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _90_361.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _90_361.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _90_361.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _90_361.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _90_361.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _90_361.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _90_361.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _90_361.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _90_361.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _90_361.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _90_361.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _90_361.FStar_TypeChecker_Env.use_bv_sorts}) e))
and tc_maybe_toplevel_term = (fun env e -> (let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (let _90_366 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_264 = (let _181_262 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _181_262))
in (let _181_263 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _181_264 _181_263)))
end else begin
()
end
in (let top = e
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_90_370) -> begin
(let _181_268 = (FStar_Syntax_Subst.compress e)
in (tc_term env _181_268))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(let _90_410 = (FStar_Syntax_Util.type_u ())
in (match (_90_410) with
| (t, u) -> begin
(let _90_414 = (tc_check_tot_or_gtot_term env e t)
in (match (_90_414) with
| (e, c, g) -> begin
(let _90_421 = (let _90_418 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_90_418) with
| (env, _90_417) -> begin
(tc_pats env pats)
end))
in (match (_90_421) with
| (pats, g') -> begin
(let g' = (let _90_422 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _90_422.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _90_422.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _90_422.FStar_TypeChecker_Env.implicits})
in (let _181_270 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_pattern (pats)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _181_269 = (FStar_TypeChecker_Rel.conj_guard g g')
in (_181_270, c, _181_269))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _181_271 = (FStar_Syntax_Subst.compress e)
in _181_271.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_90_431, {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _90_438; FStar_Syntax_Syntax.lbtyp = _90_436; FStar_Syntax_Syntax.lbeff = _90_434; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(let _90_449 = (let _181_272 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Recheck.t_unit)
in (tc_term _181_272 e1))
in (match (_90_449) with
| (e1, c1, g1) -> begin
(let _90_453 = (tc_term env e2)
in (match (_90_453) with
| (e2, c2, g2) -> begin
(let c = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (None, c2))
in (let e = (let _181_277 = (let _181_276 = (let _181_275 = (let _181_274 = (let _181_273 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Recheck.t_unit, e1))
in (_181_273)::[])
in (false, _181_274))
in (_181_275, e2))
in FStar_Syntax_Syntax.Tm_let (_181_276))
in (FStar_Syntax_Syntax.mk _181_277 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _181_278 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _181_278)))))
end))
end))
end
| _90_458 -> begin
(let _90_462 = (tc_term env e)
in (match (_90_462) with
| (e, c, g) -> begin
(let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(let _90_471 = (tc_term env e)
in (match (_90_471) with
| (e, c, g) -> begin
(let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, m))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _90_476) -> begin
(let _90_481 = (FStar_Syntax_Util.type_u ())
in (match (_90_481) with
| (k, u) -> begin
(let _90_486 = (tc_check_tot_or_gtot_term env t k)
in (match (_90_486) with
| (t, _90_484, f) -> begin
(let _90_490 = (let _181_279 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _181_279 e))
in (match (_90_490) with
| (e, c, g) -> begin
(let _90_494 = (let _181_283 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _90_491 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _181_283 e c f))
in (match (_90_494) with
| (c, f) -> begin
(let _90_498 = (let _181_284 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, t, Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _181_284 c))
in (match (_90_498) with
| (e, c, f2) -> begin
(let _181_286 = (let _181_285 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _181_285))
in (e, c, _181_286))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(let env0 = env
in (let env = (let _181_288 = (let _181_287 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _181_287 Prims.fst))
in (FStar_All.pipe_right _181_288 instantiate_both))
in (let _90_505 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _181_290 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _181_289 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _181_290 _181_289)))
end else begin
()
end
in (let _90_510 = (tc_term (no_inst env) head)
in (match (_90_510) with
| (head, chead, g_head) -> begin
(let _90_514 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _181_291 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _181_291))
end else begin
(let _181_292 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _181_292))
end
in (match (_90_514) with
| (e, c, g) -> begin
(let _90_515 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _181_293 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _181_293))
end else begin
()
end
in (let c = if (((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) && (not ((FStar_Syntax_Util.is_lcomp_partial_return c)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)) then begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e c)
end else begin
c
end
in (let _90_522 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_299 = (FStar_Syntax_Print.term_to_string e)
in (let _181_298 = (let _181_294 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _181_294))
in (let _181_297 = (let _181_296 = (FStar_TypeChecker_Env.expected_typ env0)
in (FStar_All.pipe_right _181_296 (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end))))
in (FStar_Util.print3 "(%s) About to check %s against expected typ %s\n" _181_299 _181_298 _181_297))))
end else begin
()
end
in (let _90_527 = (comp_check_expected_typ env0 e c)
in (match (_90_527) with
| (e, c, g') -> begin
(let _90_528 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_302 = (FStar_Syntax_Print.term_to_string e)
in (let _181_301 = (let _181_300 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _181_300))
in (FStar_Util.print2 "(%s) checked ... got %s\n" _181_302 _181_301)))
end else begin
()
end
in (let gimp = (match ((let _181_303 = (FStar_Syntax_Subst.compress head)
in _181_303.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _90_532) -> begin
(let imp = (env0, u, e, c.FStar_Syntax_Syntax.res_typ, e.FStar_Syntax_Syntax.pos)
in (let _90_536 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _90_536.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _90_536.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _90_536.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _90_539 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (let gres = (let _181_304 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _181_304))
in (let _90_542 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _181_305 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print1 "Guard from application node is %s\n" _181_305))
end else begin
()
end
in (e, c, gres)))))
end)))))
end))
end)))))
end
| FStar_Syntax_Syntax.Tm_match (e1, eqns) -> begin
(let _90_550 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_90_550) with
| (env1, topt) -> begin
(let env1 = (instantiate_both env1)
in (let _90_555 = (tc_term env1 e1)
in (match (_90_555) with
| (e1, c1, g1) -> begin
(let _90_566 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(let _90_562 = (FStar_Syntax_Util.type_u ())
in (match (_90_562) with
| (k, _90_561) -> begin
(let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _181_306 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_181_306, res_t)))
end))
end)
in (match (_90_566) with
| (env_branches, res_t) -> begin
(let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (let _90_583 = (let _90_580 = (FStar_List.fold_right (fun _90_574 _90_577 -> (match ((_90_574, _90_577)) with
| ((_90_570, f, c, g), (caccum, gaccum)) -> begin
(let _181_309 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _181_309))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_90_580) with
| (cases, g) -> begin
(let _181_310 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_181_310, g))
end))
in (match (_90_583) with
| (c_branches, g_branches) -> begin
(let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (guard_x), c_branches))
in (let e = (let _181_314 = (let _181_313 = (let _181_312 = (FStar_List.map (fun _90_592 -> (match (_90_592) with
| (f, _90_587, _90_589, _90_591) -> begin
f
end)) t_eqns)
in (e1, _181_312))
in FStar_Syntax_Syntax.Tm_match (_181_313))
in (FStar_Syntax_Syntax.mk _181_314 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, cres.FStar_Syntax_Syntax.res_typ, Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (let _90_595 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _181_317 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _181_316 = (let _181_315 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _181_315))
in (FStar_Util.print2 "(%s) comp type = %s\n" _181_317 _181_316)))
end else begin
()
end
in (let _181_318 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _181_318))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_90_607); FStar_Syntax_Syntax.lbunivs = _90_605; FStar_Syntax_Syntax.lbtyp = _90_603; FStar_Syntax_Syntax.lbeff = _90_601; FStar_Syntax_Syntax.lbdef = _90_599}::[]), _90_613) -> begin
(let _90_616 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_319 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _181_319))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _90_620), _90_623) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_90_638); FStar_Syntax_Syntax.lbunivs = _90_636; FStar_Syntax_Syntax.lbtyp = _90_634; FStar_Syntax_Syntax.lbeff = _90_632; FStar_Syntax_Syntax.lbdef = _90_630}::_90_628), _90_644) -> begin
(let _90_647 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_320 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _181_320))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _90_651), _90_654) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value = (fun env e -> (let check_instantiated_fvar = (fun env v dc e t -> (let _90_668 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_90_668) with
| (e, t, implicits) -> begin
(let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _181_334 = (let _181_333 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _181_333))
in FStar_Util.Inr (_181_334))
end
in (let is_data_ctor = (fun _90_4 -> (match (_90_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _90_678 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _181_340 = (let _181_339 = (let _181_338 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _181_337 = (FStar_TypeChecker_Env.get_range env)
in (_181_338, _181_337)))
in FStar_Syntax_Syntax.Error (_181_339))
in (Prims.raise _181_340))
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
(let g = (match ((let _181_341 = (FStar_Syntax_Subst.compress t1)
in _181_341.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_90_689) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _90_692 -> begin
(let imp = (env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (let _90_694 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _90_694.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _90_694.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _90_694.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _90_700 = (FStar_Syntax_Util.type_u ())
in (match (_90_700) with
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
in (let e = (FStar_Syntax_Syntax.bv_to_name (let _90_705 = x
in {FStar_Syntax_Syntax.ppname = _90_705.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _90_705.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (let _90_711 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_90_711) with
| (e, t, implicits) -> begin
(let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _181_343 = (let _181_342 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _181_342))
in FStar_Util.Inr (_181_343))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (v, dc); FStar_Syntax_Syntax.tk = _90_718; FStar_Syntax_Syntax.pos = _90_716; FStar_Syntax_Syntax.vars = _90_714}, us) -> begin
(let us = (FStar_List.map (tc_universe env) us)
in (let _90_730 = (FStar_TypeChecker_Env.lookup_lid env v.FStar_Syntax_Syntax.v)
in (match (_90_730) with
| (us', t) -> begin
(let _90_737 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _181_346 = (let _181_345 = (let _181_344 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _181_344))
in FStar_Syntax_Syntax.Error (_181_345))
in (Prims.raise _181_346))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _90_736 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (let e = (let _181_349 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (((let _90_739 = v
in {FStar_Syntax_Syntax.v = _90_739.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _90_739.FStar_Syntax_Syntax.p}), dc))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _181_349 us))
in (check_instantiated_fvar env v dc e t)))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (v, dc) -> begin
(let _90_748 = (FStar_TypeChecker_Env.lookup_lid env v.FStar_Syntax_Syntax.v)
in (match (_90_748) with
| (us, t) -> begin
(let e = (let _181_350 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (((let _90_749 = v
in {FStar_Syntax_Syntax.v = _90_749.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _90_749.FStar_Syntax_Syntax.p}), dc))) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _181_350 us))
in (check_instantiated_fvar env v dc e t))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let t = (FStar_TypeChecker_Recheck.check e)
in (let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _90_762 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_90_762) with
| (bs, c) -> begin
(let env0 = env
in (let _90_767 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_90_767) with
| (env, _90_766) -> begin
(let _90_772 = (tc_binders env bs)
in (match (_90_772) with
| (bs, env, g, us) -> begin
(let _90_776 = (tc_comp env c)
in (match (_90_776) with
| (c, uc, f) -> begin
(let e = (let _90_777 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _90_777.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _90_777.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _90_777.FStar_Syntax_Syntax.vars})
in (let _90_780 = (check_smt_pat env e bs c)
in (let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (let g = (let _181_351 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _181_351))
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
(let _90_796 = (let _181_353 = (let _181_352 = (FStar_Syntax_Syntax.mk_binder x)
in (_181_352)::[])
in (FStar_Syntax_Subst.open_term _181_353 phi))
in (match (_90_796) with
| (x, phi) -> begin
(let env0 = env
in (let _90_801 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_90_801) with
| (env, _90_800) -> begin
(let _90_806 = (let _181_354 = (FStar_List.hd x)
in (tc_binder env _181_354))
in (match (_90_806) with
| (x, env, f1, u) -> begin
(let _90_807 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _181_357 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _181_356 = (FStar_Syntax_Print.term_to_string phi)
in (let _181_355 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _181_357 _181_356 _181_355))))
end else begin
()
end
in (let _90_812 = (FStar_Syntax_Util.type_u ())
in (match (_90_812) with
| (t_phi, _90_811) -> begin
(let _90_817 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_90_817) with
| (phi, _90_815, f2) -> begin
(let e = (let _90_818 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _90_818.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _90_818.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _90_818.FStar_Syntax_Syntax.vars})
in (let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (let g = (let _181_358 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _181_358))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _90_826) -> begin
(let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (let _90_832 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_359 = (FStar_Syntax_Print.term_to_string (let _90_830 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _90_830.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _90_830.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _90_830.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _181_359))
end else begin
()
end
in (let _90_836 = (FStar_Syntax_Subst.open_term bs body)
in (match (_90_836) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _90_838 -> begin
(let _181_361 = (let _181_360 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _181_360))
in (FStar_All.failwith _181_361))
end)))))
and tc_comp = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _90_845 = (FStar_Syntax_Util.type_u ())
in (match (_90_845) with
| (k, u) -> begin
(let _90_850 = (tc_check_tot_or_gtot_term env t k)
in (match (_90_850) with
| (t, _90_848, g) -> begin
(let _181_364 = (FStar_Syntax_Syntax.mk_Total t)
in (_181_364, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _90_855 = (FStar_Syntax_Util.type_u ())
in (match (_90_855) with
| (k, u) -> begin
(let _90_860 = (tc_check_tot_or_gtot_term env t k)
in (match (_90_860) with
| (t, _90_858, g) -> begin
(let _181_365 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_181_365, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(let kc = (FStar_TypeChecker_Env.lookup_effect_lid env c.FStar_Syntax_Syntax.effect_name)
in (let _90_864 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_367 = (FStar_Syntax_Print.lid_to_string c.FStar_Syntax_Syntax.effect_name)
in (let _181_366 = (FStar_Syntax_Print.term_to_string kc)
in (FStar_Util.print2 "Type of effect %s is %s\n" _181_367 _181_366)))
end else begin
()
end
in (let head = (FStar_Syntax_Syntax.fvar None c.FStar_Syntax_Syntax.effect_name (FStar_Ident.range_of_lid c.FStar_Syntax_Syntax.effect_name))
in (let tc = (let _181_369 = (let _181_368 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_181_368)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _181_369 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _90_872 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_90_872) with
| (tc, _90_870, f) -> begin
(let _90_876 = (FStar_Syntax_Util.head_and_args tc)
in (match (_90_876) with
| (_90_874, args) -> begin
(let _90_879 = (let _181_371 = (FStar_List.hd args)
in (let _181_370 = (FStar_List.tl args)
in (_181_371, _181_370)))
in (match (_90_879) with
| (res, args) -> begin
(let _90_895 = (let _181_373 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _90_5 -> (match (_90_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _90_886 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_90_886) with
| (env, _90_885) -> begin
(let _90_891 = (tc_tot_or_gtot_term env e)
in (match (_90_891) with
| (e, _90_889, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _181_373 FStar_List.unzip))
in (match (_90_895) with
| (flags, guards) -> begin
(let u = (match ((FStar_TypeChecker_Recheck.check (Prims.fst res))) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type (u); FStar_Syntax_Syntax.tk = _90_901; FStar_Syntax_Syntax.pos = _90_899; FStar_Syntax_Syntax.vars = _90_897} -> begin
u
end
| _90_906 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _181_375 = (FStar_Syntax_Syntax.mk_Comp (let _90_908 = c
in {FStar_Syntax_Syntax.effect_name = _90_908.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _90_908.FStar_Syntax_Syntax.flags}))
in (let _181_374 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_181_375, u, _181_374))))
end))
end))
end))
end))))))
end))
and tc_universe = (fun env u -> (let rec aux = (fun u -> (let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_90_916) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _181_380 = (aux u)
in FStar_Syntax_Syntax.U_succ (_181_380))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _181_381 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_181_381))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _181_385 = (let _181_384 = (let _181_383 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _181_382 = (FStar_TypeChecker_Env.get_range env)
in (_181_383, _181_382)))
in FStar_Syntax_Syntax.Error (_181_384))
in (Prims.raise _181_385))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _181_386 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _181_386 Prims.snd))
end
| _90_931 -> begin
(aux u)
end)))
and tc_abs = (fun env top bs body -> (let fail = (fun msg t -> (let _181_395 = (let _181_394 = (let _181_393 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_181_393, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_181_394))
in (Prims.raise _181_395)))
in (let check_binders = (fun env bs bs_expected -> (let rec aux = (fun _90_949 bs bs_expected -> (match (_90_949) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| ((hd, imp)::bs, (hd_expected, imp')::bs_expected) -> begin
(let _90_976 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit))) | ((Some (FStar_Syntax_Syntax.Implicit), None)) -> begin
(let _181_412 = (let _181_411 = (let _181_410 = (let _181_408 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _181_408))
in (let _181_409 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_181_410, _181_409)))
in FStar_Syntax_Syntax.Error (_181_411))
in (Prims.raise _181_412))
end
| _90_975 -> begin
()
end)
in (let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (let _90_993 = (match ((let _181_413 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _181_413.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _90_981 -> begin
(let _90_982 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _181_414 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _181_414))
end else begin
()
end
in (let _90_988 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_90_988) with
| (t, _90_986, g1) -> begin
(let g2 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (let g = (let _181_415 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _181_415))
in (t, g)))
end)))
end)
in (match (_90_993) with
| (t, g) -> begin
(let hd = (let _90_994 = hd
in {FStar_Syntax_Syntax.ppname = _90_994.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _90_994.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (let b = (hd, imp)
in (let b_expected = (hd_expected, imp')
in (let env = (maybe_push_binding env b)
in (let subst = (let _181_416 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _181_416))
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
(let _90_1014 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _90_1013 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (let _90_1021 = (tc_binders env bs)
in (match (_90_1021) with
| (bs, envbody, g, _90_1020) -> begin
(None, bs, [], None, envbody, g)
end)))
end
| Some (t) -> begin
(let t = (FStar_Syntax_Subst.compress t)
in (let rec as_function_typ = (fun norm t -> (match ((let _181_425 = (FStar_Syntax_Subst.compress t)
in _181_425.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(let _90_1048 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _90_1047 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _90_1055 = (tc_binders env bs)
in (match (_90_1055) with
| (bs, envbody, g, _90_1054) -> begin
(let _90_1059 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_90_1059) with
| (envbody, _90_1058) -> begin
(Some ((t, true)), bs, [], None, envbody, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _90_1062) -> begin
(let _90_1072 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_90_1072) with
| (_90_1066, bs, bs', copt, env, g) -> begin
(Some ((t, false)), bs, bs', copt, env, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(let _90_1079 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_90_1079) with
| (bs_expected, c_expected) -> begin
(let check_actuals_against_formals = (fun env bs bs_expected -> (let rec handle_more = (fun _90_1090 c_expected -> (match (_90_1090) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _181_436 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in (env, bs, guard, _181_436))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(let c = (let _181_437 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _181_437))
in (let _181_438 = (FStar_Syntax_Subst.subst_comp subst c)
in (env, bs, guard, _181_438)))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(let c = (FStar_Syntax_Subst.subst_comp subst c_expected)
in if (FStar_Syntax_Util.is_total_comp c) then begin
(let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(let _90_1111 = (check_binders env more_bs bs_expected)
in (match (_90_1111) with
| (env, bs', more, guard', subst) -> begin
(let _181_440 = (let _181_439 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _181_439, subst))
in (handle_more _181_440 c_expected))
end))
end
| _90_1113 -> begin
(let _181_442 = (let _181_441 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _181_441))
in (fail _181_442 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _181_443 = (check_binders env bs bs_expected)
in (handle_more _181_443 c_expected))))
in (let mk_letrec_env = (fun envbody bs c -> (let letrecs = (guard_letrecs envbody bs c)
in (let envbody = (let _90_1119 = envbody
in {FStar_TypeChecker_Env.solver = _90_1119.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _90_1119.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _90_1119.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _90_1119.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _90_1119.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _90_1119.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _90_1119.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _90_1119.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _90_1119.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _90_1119.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _90_1119.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _90_1119.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _90_1119.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _90_1119.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _90_1119.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _90_1119.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _90_1119.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _90_1119.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _90_1119.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _90_1119.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _90_1124 _90_1127 -> (match ((_90_1124, _90_1127)) with
| ((env, letrec_binders), (l, t)) -> begin
(let _90_1133 = (let _181_453 = (let _181_452 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _181_452 Prims.fst))
in (tc_term _181_453 t))
in (match (_90_1133) with
| (t, _90_1130, _90_1132) -> begin
(let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _181_454 = (FStar_Syntax_Syntax.mk_binder (let _90_1137 = x
in {FStar_Syntax_Syntax.ppname = _90_1137.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _90_1137.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_181_454)::letrec_binders)
end
| _90_1140 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (let _90_1146 = (check_actuals_against_formals env bs bs_expected)
in (match (_90_1146) with
| (envbody, bs, g, c) -> begin
(let _90_1149 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_90_1149) with
| (envbody, letrecs) -> begin
(let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, g))
end))
end))))
end))
end
| _90_1152 -> begin
if (not (norm)) then begin
(let _181_455 = (unfold_whnf env t)
in (as_function_typ true _181_455))
end else begin
(let _90_1161 = (expected_function_typ env None)
in (match (_90_1161) with
| (_90_1154, bs, _90_1157, c_opt, envbody, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (let use_eq = env.FStar_TypeChecker_Env.use_eq
in (let _90_1165 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_90_1165) with
| (env, topt) -> begin
(let _90_1169 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _181_456 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _181_456 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (let _90_1177 = (expected_function_typ env topt)
in (match (_90_1177) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, g) -> begin
(let _90_1183 = (tc_term (let _90_1178 = envbody
in {FStar_TypeChecker_Env.solver = _90_1178.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _90_1178.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _90_1178.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _90_1178.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _90_1178.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _90_1178.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _90_1178.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _90_1178.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _90_1178.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _90_1178.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _90_1178.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _90_1178.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _90_1178.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _90_1178.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _90_1178.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _90_1178.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _90_1178.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _90_1178.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _90_1178.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_90_1183) with
| (body, cbody, guard_body) -> begin
(let _90_1184 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_462 = (FStar_Syntax_Print.term_to_string body)
in (let _181_461 = (let _181_457 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _181_457))
in (let _181_460 = (FStar_TypeChecker_Rel.guard_to_string env guard_body)
in (let _181_459 = (let _181_458 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _181_458))
in (FStar_Util.print4 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\nAgain cbody=%s\n" _181_462 _181_461 _181_460 _181_459)))))
end else begin
()
end
in (let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (let _90_1187 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _181_465 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _181_464 = (let _181_463 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _181_463))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _181_465 _181_464)))
end else begin
()
end
in (let _90_1194 = (let _181_467 = (let _181_466 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _181_466))
in (check_expected_effect (let _90_1189 = envbody
in {FStar_TypeChecker_Env.solver = _90_1189.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _90_1189.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _90_1189.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _90_1189.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _90_1189.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _90_1189.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _90_1189.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _90_1189.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _90_1189.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _90_1189.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _90_1189.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _90_1189.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _90_1189.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _90_1189.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _90_1189.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _90_1189.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _90_1189.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _90_1189.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _90_1189.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _90_1189.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _181_467))
in (match (_90_1194) with
| (body, cbody, guard) -> begin
(let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _181_468 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _181_468))
end else begin
(let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (let e = (FStar_Syntax_Util.abs bs body (Some ((FStar_Syntax_Util.lcomp_of_comp cbody))))
in (let _90_1217 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_90_1206) -> begin
(e, t, guard)
end
| _90_1209 -> begin
(let _90_1212 = if use_teq then begin
(let _181_469 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _181_469))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_90_1212) with
| (e, guard') -> begin
(let _181_470 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _181_470))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_90_1217) with
| (e, tfun, guard) -> begin
(let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (let _90_1221 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_90_1221) with
| (c, g) -> begin
(e, c, g)
end)))
end))))))
end)))))
end))
end)))
end)))))))
and check_application_args = (fun env head chead ghead args expected_topt -> (let n_args = (FStar_List.length args)
in (let r = (FStar_TypeChecker_Env.get_range env)
in (let thead = chead.FStar_Syntax_Syntax.res_typ
in (let _90_1231 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _181_479 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _181_478 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _181_479 _181_478)))
end else begin
()
end
in (let rec check_function_app = (fun norm tf -> (match ((let _181_484 = (FStar_Syntax_Util.unrefine tf)
in _181_484.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| (e, imp)::tl -> begin
(let _90_1265 = (tc_term env e)
in (match (_90_1265) with
| (e, c, g_e) -> begin
(let _90_1269 = (tc_args env tl)
in (match (_90_1269) with
| (args, comps, g_rest) -> begin
(let _181_489 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, (c)::comps, _181_489))
end))
end))
end))
in (let _90_1273 = (tc_args env args)
in (match (_90_1273) with
| (args, comps, g_args) -> begin
(let bs = (let _181_491 = (FStar_All.pipe_right comps (FStar_List.map (fun c -> (c.FStar_Syntax_Syntax.res_typ, None))))
in (FStar_Syntax_Util.null_binders_of_tks _181_491))
in (let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _90_1280 -> begin
FStar_Syntax_Util.ml_comp
end)
in (let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _181_506 = (FStar_Syntax_Subst.compress t)
in _181_506.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_90_1286) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _90_1291 -> begin
ml_or_tot
end)
end)
in (let cres = (let _181_511 = (let _181_510 = (let _181_509 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _181_509 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _181_510))
in (ml_or_tot _181_511 r))
in (let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (let _90_1295 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _181_514 = (FStar_Syntax_Print.term_to_string head)
in (let _181_513 = (FStar_Syntax_Print.term_to_string tf)
in (let _181_512 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _181_514 _181_513 _181_512))))
end else begin
()
end
in (let _90_1297 = (let _181_515 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _181_515))
in (let comp = (let _181_518 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_TypeChecker_Util.bind env None c (None, out))) ((chead)::comps) _181_518))
in (let _181_520 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _181_519 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_181_520, comp, _181_519)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _90_1308 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_90_1308) with
| (bs, c) -> begin
(let rec tc_args = (fun _90_1316 bs cres args -> (match (_90_1316) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((x, Some (FStar_Syntax_Syntax.Implicit))::rest, (_90_1329, None)::_90_1327) -> begin
(let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (let _90_1335 = (fxv_check head env t fvs)
in (let _90_1340 = (FStar_TypeChecker_Util.new_implicit_var env t)
in (match (_90_1340) with
| (varg, u, implicits) -> begin
(let subst = (FStar_Syntax_Syntax.NT ((x, varg)))::subst
in (let arg = (let _181_555 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _181_555))
in (let _181_561 = (let _181_560 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _181_560, fvs))
in (tc_args _181_561 rest cres args))))
end))))
end
| ((x, aqual)::rest, (e, aq)::rest') -> begin
(let _90_1368 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit), Some (FStar_Syntax_Syntax.Implicit))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _90_1367 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (let x = (let _90_1371 = x
in {FStar_Syntax_Syntax.ppname = _90_1371.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _90_1371.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (let _90_1374 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _181_562 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _181_562))
end else begin
()
end
in (let _90_1376 = (fxv_check head env targ fvs)
in (let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (let env = (let _90_1379 = env
in {FStar_TypeChecker_Env.solver = _90_1379.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _90_1379.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _90_1379.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _90_1379.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _90_1379.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _90_1379.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _90_1379.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _90_1379.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _90_1379.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _90_1379.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _90_1379.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _90_1379.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _90_1379.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _90_1379.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _90_1379.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _90_1379.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _90_1379.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _90_1379.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _90_1379.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _90_1379.FStar_TypeChecker_Env.use_bv_sorts})
in (let _90_1382 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _181_565 = (FStar_Syntax_Print.tag_of_term e)
in (let _181_564 = (FStar_Syntax_Print.term_to_string e)
in (let _181_563 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _181_565 _181_564 _181_563))))
end else begin
()
end
in (let _90_1387 = (tc_term env e)
in (match (_90_1387) with
| (e, c, g_e) -> begin
(let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(let subst = (let _181_566 = (FStar_List.hd bs)
in (maybe_extend_subst subst _181_566 e))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(let subst = (let _181_571 = (FStar_List.hd bs)
in (maybe_extend_subst subst _181_571 e))
in (let _90_1394 = (((Some (x), c))::comps, g)
in (match (_90_1394) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _181_576 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _181_576)) then begin
(let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (let arg' = (let _181_577 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _181_577))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (newx), c))::comps, g, fvs) rest cres rest')))
end else begin
(let _181_586 = (let _181_585 = (let _181_583 = (let _181_582 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _181_582))
in (_181_583)::arg_rets)
in (let _181_584 = (FStar_Util.set_add x fvs)
in (subst, (arg)::outargs, _181_585, ((Some (x), c))::comps, g, _181_584)))
in (tc_args _181_586 rest cres rest'))
end
end
end))
end))))))))))
end
| (_90_1398, []) -> begin
(let _90_1401 = (fxv_check head env cres.FStar_Syntax_Syntax.res_typ fvs)
in (let _90_1419 = (match (bs) with
| [] -> begin
(let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (let g = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _90_1409 -> (match (_90_1409) with
| (_90_1407, c) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (let cres = if refine_with_equality then begin
(let _181_588 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _181_588 cres))
end else begin
(let _90_1411 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_591 = (FStar_Syntax_Print.term_to_string head)
in (let _181_590 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _181_589 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _181_591 _181_590 _181_589))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _90_1415 -> begin
(let g = (let _181_592 = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (FStar_All.pipe_right _181_592 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _181_597 = (let _181_596 = (let _181_595 = (let _181_594 = (let _181_593 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _181_593))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _181_594))
in (FStar_Syntax_Syntax.mk_Total _181_595))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _181_596))
in (_181_597, g)))
end)
in (match (_90_1419) with
| (cres, g) -> begin
(let _90_1420 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_598 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _181_598))
end else begin
()
end
in (let comp = (FStar_List.fold_left (fun out c -> (FStar_TypeChecker_Util.bind env None (Prims.snd c) ((Prims.fst c), out))) cres comps)
in (let comp = (FStar_TypeChecker_Util.bind env None chead (None, comp))
in (let app = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev outargs) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let comp = (FStar_TypeChecker_Util.record_application_site env app comp)
in (let _90_1430 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp g)
in (match (_90_1430) with
| (comp, g) -> begin
(let _90_1431 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_604 = (FStar_TypeChecker_Normalize.term_to_string env app)
in (let _181_603 = (let _181_602 = (comp.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Print.comp_to_string _181_602))
in (FStar_Util.print2 "\t Type of app term %s is %s\n" _181_604 _181_603)))
end else begin
()
end
in (app, comp, g))
end)))))))
end)))
end
| ([], arg::_90_1435) -> begin
(let rec aux = (fun norm tres -> (let tres = (let _181_609 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _181_609 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(let _90_1447 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_610 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _181_610))
end else begin
()
end
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs (FStar_Syntax_Util.lcomp_of_comp cres') args))
end
| _90_1450 when (not (norm)) -> begin
(let _181_615 = (unfold_whnf env tres)
in (aux true _181_615))
end
| _90_1452 -> begin
(let _181_621 = (let _181_620 = (let _181_619 = (let _181_617 = (FStar_TypeChecker_Normalize.term_to_string env tf)
in (let _181_616 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _181_617 _181_616)))
in (let _181_618 = (FStar_Syntax_Syntax.argpos arg)
in (_181_619, _181_618)))
in FStar_Syntax_Syntax.Error (_181_620))
in (Prims.raise _181_621))
end)))
in (aux false cres.FStar_Syntax_Syntax.res_typ))
end)
end))
in (let _181_623 = (let _181_622 = (FStar_Syntax_Syntax.new_bv_set ())
in ([], [], [], [], FStar_TypeChecker_Rel.trivial_guard, _181_622))
in (tc_args _181_623 bs (FStar_Syntax_Util.lcomp_of_comp c) args)))
end))
end
| _90_1454 -> begin
if (not (norm)) then begin
(let _181_624 = (unfold_whnf env tf)
in (check_function_app true _181_624))
end else begin
(let _181_627 = (let _181_626 = (let _181_625 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_181_625, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_181_626))
in (Prims.raise _181_627))
end
end))
in (let _181_629 = (let _181_628 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _181_628))
in (check_function_app false _181_629))))))))
and check_short_circuit_args = (fun env head chead g_head args expected_topt -> (let r = (FStar_TypeChecker_Env.get_range env)
in (let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(let res_t = (FStar_Syntax_Util.comp_result c)
in (let _90_1490 = (FStar_List.fold_left2 (fun _90_1471 _90_1474 _90_1477 -> (match ((_90_1471, _90_1474, _90_1477)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(let _90_1478 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (let _90_1483 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_90_1483) with
| (e, c, g) -> begin
(let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (let g = (let _181_639 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _181_639 g))
in (let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _181_643 = (let _181_641 = (let _181_640 = (FStar_Syntax_Syntax.as_arg e)
in (_181_640)::[])
in (FStar_List.append seen _181_641))
in (let _181_642 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_181_643, _181_642, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_90_1490) with
| (args, guard, ghost) -> begin
(let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (let c = if ghost then begin
(let _181_644 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _181_644 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (let _90_1495 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_90_1495) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _90_1497 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn = (fun scrutinee env branch -> (let _90_1504 = (FStar_Syntax_Subst.open_branch branch)
in (match (_90_1504) with
| (pattern, when_clause, branch_exp) -> begin
(let _90_1509 = branch
in (match (_90_1509) with
| (cpat, _90_1507, cbr) -> begin
(let tc_pat = (fun allow_implicits pat_t p0 -> (let _90_1517 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_90_1517) with
| (pat_bvs, exps, p) -> begin
(let _90_1518 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _181_656 = (FStar_Syntax_Print.pat_to_string p0)
in (let _181_655 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _181_656 _181_655)))
end else begin
()
end
in (let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (let _90_1524 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_90_1524) with
| (env1, _90_1523) -> begin
(let env1 = (let _90_1525 = env1
in {FStar_TypeChecker_Env.solver = _90_1525.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _90_1525.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _90_1525.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _90_1525.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _90_1525.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _90_1525.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _90_1525.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _90_1525.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _90_1525.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _90_1525.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _90_1525.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _90_1525.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _90_1525.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _90_1525.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _90_1525.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _90_1525.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _90_1525.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _90_1525.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _90_1525.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _90_1525.FStar_TypeChecker_Env.use_bv_sorts})
in (let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (let _90_1564 = (let _181_679 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (let _90_1530 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _181_659 = (FStar_Syntax_Print.term_to_string e)
in (let _181_658 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _181_659 _181_658)))
end else begin
()
end
in (let _90_1535 = (tc_term env1 e)
in (match (_90_1535) with
| (e, lc, g) -> begin
(let _90_1536 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _181_661 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _181_660 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _181_661 _181_660)))
end else begin
()
end
in (let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (let _90_1542 = (let _181_662 = (FStar_TypeChecker_Rel.discharge_guard env (let _90_1540 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _90_1540.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _90_1540.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _90_1540.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _181_662 FStar_TypeChecker_Rel.resolve_implicits))
in (let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (let uvars_to_string = (fun uvs -> (let _181_667 = (let _181_666 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _181_666 (FStar_List.map (fun _90_1550 -> (match (_90_1550) with
| (u, _90_1549) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _181_667 (FStar_String.concat ", "))))
in (let uvs1 = (FStar_Syntax_Free.uvars e')
in (let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (let _90_1558 = if (let _181_668 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _181_668)) then begin
(let unresolved = (let _181_669 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _181_669 FStar_Util.set_elements))
in (let _181_677 = (let _181_676 = (let _181_675 = (let _181_674 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _181_673 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _181_672 = (let _181_671 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _90_1557 -> (match (_90_1557) with
| (u, _90_1556) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _181_671 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _181_674 _181_673 _181_672))))
in (_181_675, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_181_676))
in (Prims.raise _181_677)))
end else begin
()
end
in (let _90_1560 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _181_678 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _181_678))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _181_679 FStar_List.unzip))
in (match (_90_1564) with
| (exps, norm_exps) -> begin
(let p = (FStar_TypeChecker_Util.decorate_pattern env p exps)
in (p, pat_bvs, pat_env, exps, norm_exps))
end))))
end))))
end)))
in (let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (let _90_1571 = (let _181_680 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _181_680 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_90_1571) with
| (scrutinee_env, _90_1570) -> begin
(let _90_1577 = (tc_pat true pat_t pattern)
in (match (_90_1577) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(let _90_1587 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(let _90_1584 = (let _181_681 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Recheck.t_bool)
in (tc_term _181_681 e))
in (match (_90_1584) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_90_1587) with
| (when_clause, g_when) -> begin
(let _90_1591 = (tc_term pat_env branch_exp)
in (match (_90_1591) with
| (branch_exp, c, g_branch) -> begin
(let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _181_683 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _181_682 -> Some (_181_682)) _181_683))
end)
in (let _90_1645 = (let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _90_1609 -> begin
(let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _181_687 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _181_686 -> Some (_181_686)) _181_687))
end))
end))) None))
in (let _90_1640 = (match ((eqs, when_condition)) with
| (None, None) -> begin
(c, g_when, g_branch)
end
| (Some (f), None) -> begin
(let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _181_690 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _181_689 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (let _181_688 = (FStar_TypeChecker_Rel.imp_guard g g_branch)
in (_181_690, _181_689, _181_688))))))
end
| (Some (f), Some (w)) -> begin
(let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (let g_fw = (let _181_691 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_181_691))
in (let _181_696 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _181_695 = (let _181_692 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _181_692 g_when))
in (let _181_694 = (let _181_693 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_fw)
in (FStar_TypeChecker_Rel.imp_guard _181_693 g_branch))
in (_181_696, _181_695, _181_694))))))
end
| (None, Some (w)) -> begin
(let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _181_698 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (let _181_697 = (FStar_TypeChecker_Rel.imp_guard g g_branch)
in (_181_698, g_when, _181_697)))))
end)
in (match (_90_1640) with
| (c_weak, g_when_weak, g_branch_weak) -> begin
(let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _181_701 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _181_700 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (let _181_699 = (FStar_TypeChecker_Rel.close_guard binders g_branch_weak)
in (_181_701, _181_700, _181_699)))))
end)))
in (match (_90_1645) with
| (c, g_when, g_branch) -> begin
(let branch_guard = (let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (let discriminate = (fun scrutinee_tm f -> if ((let _181_711 = (let _181_710 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _181_710))
in (FStar_List.length _181_711)) > 1) then begin
(let disc = (let _181_712 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar None _181_712 (FStar_Ident.range_of_lid f.FStar_Syntax_Syntax.v)))
in (let disc = (let _181_714 = (let _181_713 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_181_713)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _181_714 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _181_715 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_181_715)::[])))
end else begin
[]
end)
in (let fail = (fun _90_1655 -> (match (()) with
| () -> begin
(let _181_721 = (let _181_720 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _181_719 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _181_718 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _181_720 _181_719 _181_718))))
in (FStar_All.failwith _181_721))
end))
in (let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (f, _90_1660) -> begin
f
end
| FStar_Syntax_Syntax.Tm_uinst (t, _90_1665) -> begin
(head_constructor t)
end
| _90_1669 -> begin
(fail ())
end))
in (let pat_exp = (let _181_724 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _181_724 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_90_1694) -> begin
(let _181_729 = (let _181_728 = (let _181_727 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _181_726 = (let _181_725 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_181_725)::[])
in (_181_727)::_181_726))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _181_728 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_181_729)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _181_730 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _181_730))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let sub_term_guards = (let _181_736 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _90_1712 -> (match (_90_1712) with
| (ei, _90_1711) -> begin
(let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (let sub_term = (let _181_735 = (FStar_Syntax_Syntax.fvar None projector f.FStar_Syntax_Syntax.p)
in (let _181_734 = (let _181_733 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_181_733)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _181_735 _181_734 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei)))
end))))
in (FStar_All.pipe_right _181_736 FStar_List.flatten))
in (let _181_737 = (discriminate scrutinee_tm f)
in (FStar_List.append _181_737 sub_term_guards)))
end)
end
| _90_1717 -> begin
[]
end))))))
in (let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid scrutinee_tm.FStar_Syntax_Syntax.pos)
end else begin
(let t = (let _181_742 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _181_742))
in (let _90_1725 = (FStar_Syntax_Util.type_u ())
in (match (_90_1725) with
| (k, _90_1724) -> begin
(let _90_1731 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_90_1731) with
| (t, _90_1728, _90_1730) -> begin
t
end))
end)))
end)
in (let branch_guard = (let _181_743 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _181_743 FStar_Syntax_Util.mk_disj_l))
in (let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
in (let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (let _90_1739 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _181_744 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _181_744))
end else begin
()
end
in (let _181_745 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_181_745, branch_guard, c, guard)))))
end)))
end))
end))
end))
end)))))
end))
end)))
and check_top_level_let = (fun env e -> (let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(let _90_1756 = (check_let_bound_def true env lb)
in (match (_90_1756) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(let _90_1768 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(let g1 = (let _181_748 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _181_748 FStar_TypeChecker_Rel.resolve_implicits))
in (let _90_1763 = (let _181_752 = (let _181_751 = (let _181_750 = (let _181_749 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _181_749))
in (_181_750)::[])
in (FStar_TypeChecker_Util.generalize env _181_751))
in (FStar_List.hd _181_752))
in (match (_90_1763) with
| (_90_1759, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_90_1768) with
| (g1, e1, univ_vars, c1) -> begin
(let _90_1778 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(let _90_1771 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_90_1771) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(let _90_1772 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _181_753 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _181_753 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _181_754 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_181_754, c1)))
end
end))
end else begin
(let _90_1774 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _181_755 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _181_755)))
end
in (match (_90_1778) with
| (e2, c1) -> begin
(let cres = (let _181_756 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Recheck.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _181_756))
in (let _90_1780 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Recheck.t_unit.FStar_Syntax_Syntax.n)))
in (let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _181_757 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Recheck.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_181_757, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _90_1784 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let = (fun env e -> (let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(let env = (let _90_1795 = env
in {FStar_TypeChecker_Env.solver = _90_1795.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _90_1795.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _90_1795.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _90_1795.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _90_1795.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _90_1795.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _90_1795.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _90_1795.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _90_1795.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _90_1795.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _90_1795.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _90_1795.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _90_1795.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _90_1795.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _90_1795.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _90_1795.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _90_1795.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _90_1795.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _90_1795.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _90_1795.FStar_TypeChecker_Env.use_bv_sorts})
in (let _90_1804 = (let _181_761 = (let _181_760 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _181_760 Prims.fst))
in (check_let_bound_def false _181_761 lb))
in (match (_90_1804) with
| (e1, _90_1800, c1, g1, annotated) -> begin
(let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (let x = (let _90_1806 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _90_1806.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _90_1806.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (let _90_1811 = (let _181_763 = (let _181_762 = (FStar_Syntax_Syntax.mk_binder x)
in (_181_762)::[])
in (FStar_Syntax_Subst.open_term _181_763 e2))
in (match (_90_1811) with
| (xb, e2) -> begin
(let xbinder = (FStar_List.hd xb)
in (let x = (Prims.fst xbinder)
in (let _90_1817 = (let _181_764 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _181_764 e2))
in (match (_90_1817) with
| (e2, c2, g2) -> begin
(let cres = (FStar_TypeChecker_Util.bind env (Some (e1)) c1 (Some (x), c2))
in (let e = (let _181_767 = (let _181_766 = (let _181_765 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _181_765))
in FStar_Syntax_Syntax.Tm_let (_181_766))
in (FStar_Syntax_Syntax.mk _181_767 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (let x_eq_e1 = (let _181_770 = (let _181_769 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _181_769 e1))
in (FStar_All.pipe_left (fun _181_768 -> FStar_TypeChecker_Common.NonTrivial (_181_768)) _181_770))
in (let g2 = (let _181_772 = (let _181_771 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _181_771 g2))
in (FStar_TypeChecker_Rel.close_guard xb _181_772))
in (let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if annotated then begin
(e, cres, guard)
end else begin
(let _90_1823 = (check_no_escape env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end)))))
end))))
end))))
end)))
end
| _90_1826 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec = (fun env top -> (let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(let _90_1838 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_90_1838) with
| (lbs, e2) -> begin
(let _90_1841 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_90_1841) with
| (env0, topt) -> begin
(let _90_1844 = (build_let_rec_env true env0 lbs)
in (match (_90_1844) with
| (lbs, rec_env) -> begin
(let _90_1847 = (check_let_recs rec_env lbs)
in (match (_90_1847) with
| (lbs, g_lbs) -> begin
(let g_lbs = (let _181_775 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _181_775 FStar_TypeChecker_Rel.resolve_implicits))
in (let all_lb_names = (let _181_778 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _181_778 (fun _181_777 -> Some (_181_777))))
in (let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(let ecs = (let _181_782 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _181_781 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _181_781)))))
in (FStar_TypeChecker_Util.generalize env _181_782))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _90_1858 -> (match (_90_1858) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (let cres = (let _181_784 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Recheck.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _181_784))
in (let _90_1861 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Recheck.t_unit.FStar_Syntax_Syntax.n)))
in (let _90_1865 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_90_1865) with
| (lbs, e2) -> begin
(let _181_786 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Recheck.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _181_785 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_181_786, cres, _181_785)))
end)))))))
end))
end))
end))
end))
end
| _90_1867 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec = (fun env top -> (let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(let _90_1879 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_90_1879) with
| (lbs, e2) -> begin
(let _90_1882 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_90_1882) with
| (env0, topt) -> begin
(let _90_1885 = (build_let_rec_env false env0 lbs)
in (match (_90_1885) with
| (lbs, rec_env) -> begin
(let _90_1888 = (check_let_recs rec_env lbs)
in (match (_90_1888) with
| (lbs, g_lbs) -> begin
(let _90_1906 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _90_1891 _90_1900 -> (match ((_90_1891, _90_1900)) with
| ((bvs, env), {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _90_1898; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _90_1895; FStar_Syntax_Syntax.lbdef = _90_1893}) -> begin
(let env = (FStar_TypeChecker_Env.push_let_binding env x ([], t))
in (let _181_792 = (let _181_791 = (let _90_1902 = (FStar_Util.left x)
in {FStar_Syntax_Syntax.ppname = _90_1902.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _90_1902.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (_181_791)::bvs)
in (_181_792, env)))
end)) ([], env)))
in (match (_90_1906) with
| (bvs, env) -> begin
(let bvs = (FStar_List.rev bvs)
in (let _90_1911 = (tc_term env e2)
in (match (_90_1911) with
| (e2, cres, g2) -> begin
(let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (let cres = (let _90_1915 = cres
in {FStar_Syntax_Syntax.eff_name = _90_1915.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _90_1915.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _90_1915.FStar_Syntax_Syntax.comp})
in (let _90_1920 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_90_1920) with
| (lbs, e2) -> begin
(let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_90_1923) -> begin
(e, cres, guard)
end
| None -> begin
(let _90_1926 = (check_no_escape env bvs tres)
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
| _90_1929 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env = (fun top_level env lbs -> (let env0 = env
in (let _90_1962 = (FStar_List.fold_left (fun _90_1936 lb -> (match (_90_1936) with
| (lbs, env) -> begin
(let _90_1941 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_90_1941) with
| (univ_vars, t, check_t) -> begin
(let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(let _90_1950 = (let _181_799 = (let _181_798 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _181_798))
in (tc_check_tot_or_gtot_term (let _90_1944 = env0
in {FStar_TypeChecker_Env.solver = _90_1944.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _90_1944.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _90_1944.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _90_1944.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _90_1944.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _90_1944.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _90_1944.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _90_1944.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _90_1944.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _90_1944.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _90_1944.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _90_1944.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _90_1944.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _90_1944.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _90_1944.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _90_1944.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _90_1944.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _90_1944.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _90_1944.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _90_1944.FStar_TypeChecker_Env.use_bv_sorts}) t _181_799))
in (match (_90_1950) with
| (t, _90_1948, g) -> begin
(let _90_1951 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(let _90_1954 = env
in {FStar_TypeChecker_Env.solver = _90_1954.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _90_1954.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _90_1954.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _90_1954.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _90_1954.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _90_1954.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _90_1954.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _90_1954.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _90_1954.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _90_1954.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _90_1954.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _90_1954.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _90_1954.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _90_1954.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _90_1954.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _90_1954.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _90_1954.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _90_1954.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _90_1954.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _90_1954.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (let lb = (let _90_1957 = lb
in {FStar_Syntax_Syntax.lbname = _90_1957.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _90_1957.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_90_1962) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs = (fun env lbs -> (let _90_1975 = (let _181_804 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _90_1969 = (let _181_803 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _181_803 lb.FStar_Syntax_Syntax.lbdef))
in (match (_90_1969) with
| (e, c, g) -> begin
(let _90_1970 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _181_804 FStar_List.unzip))
in (match (_90_1975) with
| (lbs, gs) -> begin
(let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def = (fun top_level env lb -> (let _90_1983 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_90_1983) with
| (env1, _90_1982) -> begin
(let e1 = lb.FStar_Syntax_Syntax.lbdef
in (let _90_1989 = (check_lbtyp top_level env lb)
in (match (_90_1989) with
| (topt, wf_annot, univ_vars, env1) -> begin
(let _90_1990 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (let _90_1997 = (tc_maybe_toplevel_term (let _90_1992 = env1
in {FStar_TypeChecker_Env.solver = _90_1992.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _90_1992.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _90_1992.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _90_1992.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _90_1992.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _90_1992.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _90_1992.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _90_1992.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _90_1992.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _90_1992.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _90_1992.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _90_1992.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _90_1992.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _90_1992.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _90_1992.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _90_1992.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _90_1992.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _90_1992.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _90_1992.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _90_1992.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_90_1997) with
| (e1, c1, g1) -> begin
(let _90_2001 = (let _181_811 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _90_1998 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _181_811 e1 c1 wf_annot))
in (match (_90_2001) with
| (c1, guard_f) -> begin
(let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (let _90_2003 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _181_812 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _181_812))
end else begin
()
end
in (let _181_813 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _181_813))))
end))
end)))
end)))
end)))
and check_lbtyp = (fun top_level env lb -> (let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _90_2010 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _90_2013 -> begin
(let _90_2016 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_90_2016) with
| (univ_vars, t) -> begin
(let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _181_817 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _181_817))
end else begin
(let _90_2021 = (FStar_Syntax_Util.type_u ())
in (match (_90_2021) with
| (k, _90_2020) -> begin
(let _90_2026 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_90_2026) with
| (t, _90_2024, g) -> begin
(let _90_2027 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _181_820 = (let _181_818 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _181_818))
in (let _181_819 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _181_820 _181_819)))
end else begin
()
end
in (let t = (norm env1 t)
in (let _181_821 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _181_821))))
end))
end))
end)
end))
end)))
and tc_binder = (fun env _90_2033 -> (match (_90_2033) with
| (x, imp) -> begin
(let _90_2036 = (FStar_Syntax_Util.type_u ())
in (match (_90_2036) with
| (tu, u) -> begin
(let _90_2041 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_90_2041) with
| (t, _90_2039, g) -> begin
(let x = ((let _90_2042 = x
in {FStar_Syntax_Syntax.ppname = _90_2042.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _90_2042.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (let _90_2045 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _181_825 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _181_824 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _181_825 _181_824)))
end else begin
()
end
in (let _181_826 = (maybe_push_binding env x)
in (x, _181_826, g, u))))
end))
end))
end))
and tc_binders = (fun env bs -> (let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_TypeChecker_Rel.trivial_guard, [])
end
| b::bs -> begin
(let _90_2060 = (tc_binder env b)
in (match (_90_2060) with
| (b, env', g, u) -> begin
(let _90_2065 = (aux env' bs)
in (match (_90_2065) with
| (bs, env', g', us) -> begin
(let _181_834 = (let _181_833 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _181_833))
in ((b)::bs, env', _181_834, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats = (fun env pats -> (let tc_args = (fun env args -> (FStar_List.fold_right (fun _90_2073 _90_2076 -> (match ((_90_2073, _90_2076)) with
| ((t, imp), (args, g)) -> begin
(let _90_2081 = (tc_term env t)
in (match (_90_2081) with
| (t, _90_2079, g') -> begin
(let _181_843 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _181_843))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _90_2085 -> (match (_90_2085) with
| (pats, g) -> begin
(let _90_2088 = (tc_args env p)
in (match (_90_2088) with
| (args, g') -> begin
(let _181_846 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _181_846))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term = (fun env e -> (let _90_2094 = (tc_maybe_toplevel_term env e)
in (match (_90_2094) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (let c = (c.FStar_Syntax_Syntax.comp ())
in (let _90_2097 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _181_849 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _181_849))
end else begin
()
end
in (let c = (norm_c env c)
in (let _90_2102 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _181_850 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_181_850, false))
end else begin
(let _181_851 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_181_851, true))
end
in (match (_90_2102) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _181_852 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _181_852))
end
| _90_2106 -> begin
if allow_ghost then begin
(let _181_855 = (let _181_854 = (let _181_853 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_181_853, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_181_854))
in (Prims.raise _181_855))
end else begin
(let _181_858 = (let _181_857 = (let _181_856 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_181_856, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_181_857))
in (Prims.raise _181_858))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term = (fun env e t -> (let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))

let tc_trivial_guard = (fun env t -> (let _90_2116 = (tc_tot_or_gtot_term env t)
in (match (_90_2116) with
| (t, c, g) -> begin
(let _90_2117 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))

let tc_check_trivial_guard = (fun env t k -> (let _90_2125 = (tc_check_tot_or_gtot_term env t k)
in (match (_90_2125) with
| (t, c, g) -> begin
(let _90_2126 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))

let check_and_gen = (fun env t k -> (let _181_878 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _181_878)))

let check_nogen = (fun env t k -> (let t = (tc_check_trivial_guard env t k)
in (let _181_882 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _181_882))))

let tc_tparams = (fun env tps -> (let _90_2141 = (tc_binders env tps)
in (match (_90_2141) with
| (tps, env, g, us) -> begin
(let _90_2142 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))

let monad_signature = (fun env m s -> (let fail = (fun _90_2148 -> (match (()) with
| () -> begin
(let _181_897 = (let _181_896 = (let _181_895 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_181_895, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_181_896))
in (Prims.raise _181_897))
end))
in (let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _90_2165)::(wp, _90_2161)::(_wlp, _90_2157)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _90_2169 -> begin
(fail ())
end))
end
| _90_2171 -> begin
(fail ())
end))))

let open_univ_vars = (fun uvs binders c -> (match (binders) with
| [] -> begin
(let _90_2178 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_90_2178) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _90_2180 -> begin
(let t' = (FStar_Syntax_Util.arrow binders c)
in (let _90_2184 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_90_2184) with
| (uvs, t') -> begin
(match ((let _181_904 = (FStar_Syntax_Subst.compress t')
in _181_904.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _90_2190 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

let open_effect_decl = (fun env ed -> (let fail = (fun t -> (let _181_913 = (let _181_912 = (let _181_911 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env ed.FStar_Syntax_Syntax.mname t)
in (_181_911, (FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname)))
in FStar_Syntax_Syntax.Error (_181_912))
in (Prims.raise _181_913)))
in (let _90_2219 = (match ((let _181_914 = (FStar_Syntax_Subst.compress ed.FStar_Syntax_Syntax.signature)
in _181_914.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _90_2210)::(wp, _90_2206)::(_wlp, _90_2202)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _90_2214 -> begin
(fail ed.FStar_Syntax_Syntax.signature)
end))
end
| _90_2216 -> begin
(fail ed.FStar_Syntax_Syntax.signature)
end)
in (match (_90_2219) with
| (a, wp) -> begin
(let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _90_2222 -> begin
(let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (let op = (fun ts -> (let _90_2226 = ()
in (let t0 = (Prims.snd ts)
in (let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (let _90_2230 = ed
in (let _181_929 = (op ed.FStar_Syntax_Syntax.ret)
in (let _181_928 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _181_927 = (op ed.FStar_Syntax_Syntax.bind_wlp)
in (let _181_926 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _181_925 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _181_924 = (op ed.FStar_Syntax_Syntax.ite_wlp)
in (let _181_923 = (op ed.FStar_Syntax_Syntax.wp_binop)
in (let _181_922 = (op ed.FStar_Syntax_Syntax.wp_as_type)
in (let _181_921 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _181_920 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _181_919 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _181_918 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _181_917 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _90_2230.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _90_2230.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _90_2230.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _90_2230.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _90_2230.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _181_929; FStar_Syntax_Syntax.bind_wp = _181_928; FStar_Syntax_Syntax.bind_wlp = _181_927; FStar_Syntax_Syntax.if_then_else = _181_926; FStar_Syntax_Syntax.ite_wp = _181_925; FStar_Syntax_Syntax.ite_wlp = _181_924; FStar_Syntax_Syntax.wp_binop = _181_923; FStar_Syntax_Syntax.wp_as_type = _181_922; FStar_Syntax_Syntax.close_wp = _181_921; FStar_Syntax_Syntax.assert_p = _181_920; FStar_Syntax_Syntax.assume_p = _181_919; FStar_Syntax_Syntax.null_wp = _181_918; FStar_Syntax_Syntax.trivial = _181_917}))))))))))))))))
end)
in (ed, a, wp))
end))))

let tc_eff_decl = (fun env0 ed -> (let _90_2235 = ()
in (let _90_2239 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_90_2239) with
| (binders, signature) -> begin
(let _90_2244 = (tc_tparams env0 binders)
in (match (_90_2244) with
| (binders, env, _90_2243) -> begin
(let _90_2248 = (tc_trivial_guard env signature)
in (match (_90_2248) with
| (signature, _90_2247) -> begin
(let ed = (let _90_2249 = ed
in {FStar_Syntax_Syntax.qualifiers = _90_2249.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _90_2249.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _90_2249.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _90_2249.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _90_2249.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _90_2249.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = _90_2249.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _90_2249.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _90_2249.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = _90_2249.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _90_2249.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _90_2249.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _90_2249.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _90_2249.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _90_2249.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _90_2249.FStar_Syntax_Syntax.trivial})
in (let _90_2255 = (open_effect_decl env ed)
in (match (_90_2255) with
| (ed, a, wp_a) -> begin
(let env = (let _181_934 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _181_934))
in (let _90_2257 = if (FStar_TypeChecker_Env.debug env0 FStar_Options.Low) then begin
(let _181_937 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _181_936 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _181_935 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checked effect signature: %s %s : %s\n" _181_937 _181_936 _181_935))))
end else begin
()
end
in (let check_and_gen' = (fun env _90_2264 k -> (match (_90_2264) with
| (_90_2262, t) -> begin
(check_and_gen env t k)
end))
in (let ret = (let expected_k = (let _181_949 = (let _181_947 = (FStar_Syntax_Syntax.mk_binder a)
in (let _181_946 = (let _181_945 = (let _181_944 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _181_944))
in (_181_945)::[])
in (_181_947)::_181_946))
in (let _181_948 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _181_949 _181_948)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (let bind_wp = (let wlp_a = wp_a
in (let b = (let _181_951 = (let _181_950 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _181_950 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _181_951))
in (let wp_b = (let _181_955 = (let _181_954 = (let _181_953 = (let _181_952 = (FStar_Syntax_Syntax.bv_to_name b)
in (a, _181_952))
in FStar_Syntax_Syntax.NT (_181_953))
in (_181_954)::[])
in (FStar_Syntax_Subst.subst _181_955 wp_a))
in (let a_wp_b = (let _181_959 = (let _181_957 = (let _181_956 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _181_956))
in (_181_957)::[])
in (let _181_958 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _181_959 _181_958)))
in (let a_wlp_b = a_wp_b
in (let expected_k = (let _181_972 = (let _181_970 = (FStar_Syntax_Syntax.mk_binder a)
in (let _181_969 = (let _181_968 = (FStar_Syntax_Syntax.mk_binder b)
in (let _181_967 = (let _181_966 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _181_965 = (let _181_964 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _181_963 = (let _181_962 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (let _181_961 = (let _181_960 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_181_960)::[])
in (_181_962)::_181_961))
in (_181_964)::_181_963))
in (_181_966)::_181_965))
in (_181_968)::_181_967))
in (_181_970)::_181_969))
in (let _181_971 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _181_972 _181_971)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))))))
in (let bind_wlp = (let wlp_a = wp_a
in (let b = (let _181_974 = (let _181_973 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _181_973 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _181_974))
in (let wlp_b = (let _181_978 = (let _181_977 = (let _181_976 = (let _181_975 = (FStar_Syntax_Syntax.bv_to_name b)
in (a, _181_975))
in FStar_Syntax_Syntax.NT (_181_976))
in (_181_977)::[])
in (FStar_Syntax_Subst.subst _181_978 wlp_a))
in (let a_wlp_b = (let _181_982 = (let _181_980 = (let _181_979 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _181_979))
in (_181_980)::[])
in (let _181_981 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _181_982 _181_981)))
in (let expected_k = (let _181_991 = (let _181_989 = (FStar_Syntax_Syntax.mk_binder a)
in (let _181_988 = (let _181_987 = (FStar_Syntax_Syntax.mk_binder b)
in (let _181_986 = (let _181_985 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _181_984 = (let _181_983 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_181_983)::[])
in (_181_985)::_181_984))
in (_181_987)::_181_986))
in (_181_989)::_181_988))
in (let _181_990 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _181_991 _181_990)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wlp expected_k))))))
in (let if_then_else = (let p = (let _181_993 = (let _181_992 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _181_992 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _181_993))
in (let expected_k = (let _181_1002 = (let _181_1000 = (FStar_Syntax_Syntax.mk_binder a)
in (let _181_999 = (let _181_998 = (FStar_Syntax_Syntax.mk_binder p)
in (let _181_997 = (let _181_996 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _181_995 = (let _181_994 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_181_994)::[])
in (_181_996)::_181_995))
in (_181_998)::_181_997))
in (_181_1000)::_181_999))
in (let _181_1001 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _181_1002 _181_1001)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (let ite_wp = (let wlp_a = wp_a
in (let expected_k = (let _181_1009 = (let _181_1007 = (FStar_Syntax_Syntax.mk_binder a)
in (let _181_1006 = (let _181_1005 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _181_1004 = (let _181_1003 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_181_1003)::[])
in (_181_1005)::_181_1004))
in (_181_1007)::_181_1006))
in (let _181_1008 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _181_1009 _181_1008)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k)))
in (let ite_wlp = (let wlp_a = wp_a
in (let expected_k = (let _181_1014 = (let _181_1012 = (FStar_Syntax_Syntax.mk_binder a)
in (let _181_1011 = (let _181_1010 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (_181_1010)::[])
in (_181_1012)::_181_1011))
in (let _181_1013 = (FStar_Syntax_Syntax.mk_Total wlp_a)
in (FStar_Syntax_Util.arrow _181_1014 _181_1013)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wlp expected_k)))
in (let wp_binop = (let bin_op = (let _90_2292 = (FStar_Syntax_Util.type_u ())
in (match (_90_2292) with
| (t1, u1) -> begin
(let _90_2295 = (FStar_Syntax_Util.type_u ())
in (match (_90_2295) with
| (t2, u2) -> begin
(let t = (let _181_1015 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_max ((u1)::(u2)::[]))) None _181_1015))
in (let _181_1020 = (let _181_1018 = (FStar_Syntax_Syntax.null_binder t1)
in (let _181_1017 = (let _181_1016 = (FStar_Syntax_Syntax.null_binder t2)
in (_181_1016)::[])
in (_181_1018)::_181_1017))
in (let _181_1019 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _181_1020 _181_1019))))
end))
end))
in (let expected_k = (let _181_1029 = (let _181_1027 = (FStar_Syntax_Syntax.mk_binder a)
in (let _181_1026 = (let _181_1025 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _181_1024 = (let _181_1023 = (FStar_Syntax_Syntax.null_binder bin_op)
in (let _181_1022 = (let _181_1021 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_181_1021)::[])
in (_181_1023)::_181_1022))
in (_181_1025)::_181_1024))
in (_181_1027)::_181_1026))
in (let _181_1028 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _181_1029 _181_1028)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_binop expected_k)))
in (let wp_as_type = (let _90_2303 = (FStar_Syntax_Util.type_u ())
in (match (_90_2303) with
| (t, _90_2302) -> begin
(let expected_k = (let _181_1034 = (let _181_1032 = (FStar_Syntax_Syntax.mk_binder a)
in (let _181_1031 = (let _181_1030 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_181_1030)::[])
in (_181_1032)::_181_1031))
in (let _181_1033 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _181_1034 _181_1033)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (let close_wp = (let b = (let _181_1036 = (let _181_1035 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _181_1035 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _181_1036))
in (let b_wp_a = (let _181_1040 = (let _181_1038 = (let _181_1037 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _181_1037))
in (_181_1038)::[])
in (let _181_1039 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _181_1040 _181_1039)))
in (let expected_k = (let _181_1047 = (let _181_1045 = (FStar_Syntax_Syntax.mk_binder a)
in (let _181_1044 = (let _181_1043 = (FStar_Syntax_Syntax.mk_binder b)
in (let _181_1042 = (let _181_1041 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_181_1041)::[])
in (_181_1043)::_181_1042))
in (_181_1045)::_181_1044))
in (let _181_1046 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _181_1047 _181_1046)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (let assert_p = (let expected_k = (let _181_1056 = (let _181_1054 = (FStar_Syntax_Syntax.mk_binder a)
in (let _181_1053 = (let _181_1052 = (let _181_1049 = (let _181_1048 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _181_1048 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _181_1049))
in (let _181_1051 = (let _181_1050 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_181_1050)::[])
in (_181_1052)::_181_1051))
in (_181_1054)::_181_1053))
in (let _181_1055 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _181_1056 _181_1055)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (let assume_p = (let expected_k = (let _181_1065 = (let _181_1063 = (FStar_Syntax_Syntax.mk_binder a)
in (let _181_1062 = (let _181_1061 = (let _181_1058 = (let _181_1057 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _181_1057 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _181_1058))
in (let _181_1060 = (let _181_1059 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_181_1059)::[])
in (_181_1061)::_181_1060))
in (_181_1063)::_181_1062))
in (let _181_1064 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _181_1065 _181_1064)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (let null_wp = (let expected_k = (let _181_1068 = (let _181_1066 = (FStar_Syntax_Syntax.mk_binder a)
in (_181_1066)::[])
in (let _181_1067 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _181_1068 _181_1067)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (let trivial_wp = (let _90_2319 = (FStar_Syntax_Util.type_u ())
in (match (_90_2319) with
| (t, _90_2318) -> begin
(let expected_k = (let _181_1073 = (let _181_1071 = (FStar_Syntax_Syntax.mk_binder a)
in (let _181_1070 = (let _181_1069 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_181_1069)::[])
in (_181_1071)::_181_1070))
in (let _181_1072 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _181_1073 _181_1072)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (let t = (let _181_1074 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _181_1074))
in (let _90_2325 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_90_2325) with
| (univs, t) -> begin
(let _90_2341 = (match ((let _181_1076 = (let _181_1075 = (FStar_Syntax_Subst.compress t)
in _181_1075.FStar_Syntax_Syntax.n)
in (binders, _181_1076))) with
| ([], _90_2328) -> begin
([], t)
end
| (_90_2331, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _90_2338 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_90_2341) with
| (binders, signature) -> begin
(let close = (fun ts -> (let _181_1079 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _181_1079)))
in (let ed = (let _90_2344 = ed
in (let _181_1092 = (close ret)
in (let _181_1091 = (close bind_wp)
in (let _181_1090 = (close bind_wlp)
in (let _181_1089 = (close if_then_else)
in (let _181_1088 = (close ite_wp)
in (let _181_1087 = (close ite_wlp)
in (let _181_1086 = (close wp_binop)
in (let _181_1085 = (close wp_as_type)
in (let _181_1084 = (close close_wp)
in (let _181_1083 = (close assert_p)
in (let _181_1082 = (close assume_p)
in (let _181_1081 = (close null_wp)
in (let _181_1080 = (close trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _90_2344.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _90_2344.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _181_1092; FStar_Syntax_Syntax.bind_wp = _181_1091; FStar_Syntax_Syntax.bind_wlp = _181_1090; FStar_Syntax_Syntax.if_then_else = _181_1089; FStar_Syntax_Syntax.ite_wp = _181_1088; FStar_Syntax_Syntax.ite_wlp = _181_1087; FStar_Syntax_Syntax.wp_binop = _181_1086; FStar_Syntax_Syntax.wp_as_type = _181_1085; FStar_Syntax_Syntax.close_wp = _181_1084; FStar_Syntax_Syntax.assert_p = _181_1083; FStar_Syntax_Syntax.assume_p = _181_1082; FStar_Syntax_Syntax.null_wp = _181_1081; FStar_Syntax_Syntax.trivial = _181_1080}))))))))))))))
in (let _90_2347 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_1093 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _181_1093))
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

let tc_lex_t = (fun env ses quals lids -> (let _90_2353 = ()
in (let _90_2361 = ()
in (match (ses) with
| FStar_Syntax_Syntax.Sig_inductive_typ (Prims.MkTuple8 (lex_t, [], [], t, _90_2390, _90_2392, [], r))::FStar_Syntax_Syntax.Sig_datacon (Prims.MkTuple8 (lex_top, [], _t_top, _lex_t_top, 0, [], _90_2381, r1))::FStar_Syntax_Syntax.Sig_datacon (Prims.MkTuple8 (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _90_2370, r2))::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (let tc = FStar_Syntax_Syntax.Sig_inductive_typ (Prims.MkTuple8 (lex_t, (u)::[], [], t, [], (FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[], [], r))
in (let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (let lex_top_t = (let _181_1100 = (let _181_1099 = (let _181_1098 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid r1)
in (_181_1098, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_181_1099))
in (FStar_Syntax_Syntax.mk _181_1100 None r1))
in (let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (let dc_lextop = FStar_Syntax_Syntax.Sig_datacon (Prims.MkTuple8 (lex_top, (utop)::[], lex_top_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r1))
in (let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (let lex_cons_t = (let a = (let _181_1101 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _181_1101))
in (let hd = (let _181_1102 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _181_1102))
in (let tl = (let _181_1106 = (let _181_1105 = (let _181_1104 = (let _181_1103 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid r2)
in (_181_1103, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_181_1104))
in (FStar_Syntax_Syntax.mk _181_1105 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _181_1106))
in (let res = (let _181_1109 = (let _181_1108 = (let _181_1107 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid r2)
in (_181_1107, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_181_1108))
in (FStar_Syntax_Syntax.mk _181_1109 None r2))
in (let _181_1110 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.Implicit)))::((hd, None))::((tl, None))::[]) _181_1110))))))
in (let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon (Prims.MkTuple8 (lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _181_1112 = (let _181_1111 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _181_1111))
in FStar_Syntax_Syntax.Sig_bundle (_181_1112)))))))))))))))
end
| _90_2416 -> begin
(let _181_1114 = (let _181_1113 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _181_1113))
in (FStar_All.failwith _181_1114))
end))))

let tc_inductive = (fun env ses quals lids -> (let warn_positivity = (fun l r -> (let _181_1128 = (let _181_1127 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _181_1127))
in (FStar_TypeChecker_Errors.warn r _181_1128)))
in (let env0 = env
in (let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (Prims.MkTuple8 (tc, uvs, tps, k, mutuals, data, quals, r)) -> begin
(let _90_2438 = ()
in (let _90_2440 = (warn_positivity tc r)
in (let _90_2444 = (FStar_Syntax_Subst.open_term tps k)
in (match (_90_2444) with
| (tps, k) -> begin
(let _90_2448 = (tc_tparams env tps)
in (match (_90_2448) with
| (tps, env_tps, us) -> begin
(let _90_2451 = (FStar_Syntax_Util.arrow_formals k)
in (match (_90_2451) with
| (indices, t) -> begin
(let _90_2455 = (tc_tparams env_tps indices)
in (match (_90_2455) with
| (indices, env', us') -> begin
(let _90_2459 = (tc_trivial_guard env' t)
in (match (_90_2459) with
| (t, _90_2458) -> begin
(let k = (let _181_1133 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _181_1133))
in (let _90_2463 = (FStar_Syntax_Util.type_u ())
in (match (_90_2463) with
| (t_type, u) -> begin
(let _90_2464 = (let _181_1134 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _181_1134))
in (let refined_tps = (FStar_All.pipe_right tps (FStar_List.map (fun _90_2468 -> (match (_90_2468) with
| (x, imp) -> begin
(let y = (FStar_Syntax_Syntax.freshen_bv x)
in (let refined = (let _181_1138 = (let _181_1137 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _181_1136 = (FStar_Syntax_Syntax.bv_to_name y)
in (FStar_Syntax_Util.mk_eq x.FStar_Syntax_Syntax.sort x.FStar_Syntax_Syntax.sort _181_1137 _181_1136)))
in (FStar_Syntax_Util.refine y _181_1138))
in ((let _90_2471 = x
in {FStar_Syntax_Syntax.ppname = _90_2471.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _90_2471.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = refined}), imp)))
end))))
in (let t_tc = (let _181_1139 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append refined_tps indices) _181_1139))
in (let tps = (FStar_Syntax_Subst.close_binders tps)
in (let k = (FStar_Syntax_Subst.close tps k)
in (let _181_1140 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (tc)) ([], t_tc))
in (_181_1140, FStar_Syntax_Syntax.Sig_inductive_typ (Prims.MkTuple8 (tc, [], tps, k, mutuals, data, quals, r)), u)))))))
end)))
end))
end))
end))
end))
end))))
end
| _90_2478 -> begin
(FStar_All.failwith "impossible")
end))
in (let positive_if_pure = (fun _90_2480 l -> ())
in (let tc_data = (fun env tcs _90_6 -> (match (_90_6) with
| FStar_Syntax_Syntax.Sig_datacon (Prims.MkTuple8 (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r)) -> begin
(let _90_2497 = ()
in (let _90_2528 = (let _181_1155 = (FStar_Util.find_map tcs (fun _90_2501 -> (match (_90_2501) with
| (se, u_tc) -> begin
if (let _181_1153 = (let _181_1152 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _181_1152))
in (FStar_Ident.lid_equals tc_lid _181_1153)) then begin
(let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (Prims.MkTuple8 (_90_2503, _90_2505, tps, _90_2508, _90_2510, _90_2512, _90_2514, _90_2516)) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _90_2522 -> (match (_90_2522) with
| (x, _90_2521) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit))
end))))
end
| _90_2524 -> begin
(FStar_All.failwith "Impossible")
end)
in Some ((tps, u_tc)))
end else begin
None
end
end)))
in (FStar_All.pipe_right _181_1155 FStar_Util.must))
in (match (_90_2528) with
| (tps, u_tc) -> begin
(let _90_2548 = (match ((let _181_1156 = (FStar_Syntax_Subst.compress t)
in _181_1156.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(let _90_2536 = (FStar_Util.first_N ntps bs)
in (match (_90_2536) with
| (_90_2534, bs') -> begin
(let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _90_2542 -> (match (_90_2542) with
| (x, _90_2541) -> begin
(let _181_1160 = (let _181_1159 = (FStar_Syntax_Syntax.bv_to_name x)
in ((ntps - (1 + i)), _181_1159))
in FStar_Syntax_Syntax.DB (_181_1160))
end))))
in (let _181_1161 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _181_1161))))
end))
end
| _90_2545 -> begin
([], t)
end)
in (match (_90_2548) with
| (arguments, result) -> begin
(let _90_2549 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_1164 = (FStar_Syntax_Print.lid_to_string c)
in (let _181_1163 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _181_1162 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _181_1164 _181_1163 _181_1162))))
end else begin
()
end
in (let _90_2554 = (tc_tparams env arguments)
in (match (_90_2554) with
| (arguments, env', us) -> begin
(let _90_2558 = (tc_trivial_guard env' result)
in (match (_90_2558) with
| (result, _90_2557) -> begin
(let _90_2562 = (FStar_Syntax_Util.head_and_args result)
in (match (_90_2562) with
| (head, _90_2561) -> begin
(let _90_2570 = (match ((let _181_1165 = (FStar_Syntax_Subst.compress head)
in _181_1165.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _90_2565) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v tc_lid) -> begin
()
end
| _90_2569 -> begin
(let _181_1169 = (let _181_1168 = (let _181_1167 = (let _181_1166 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _181_1166))
in (_181_1167, r))
in FStar_Syntax_Syntax.Error (_181_1168))
in (Prims.raise _181_1169))
end)
in (let g = (FStar_List.fold_left2 (fun g _90_2576 u_x -> (match (_90_2576) with
| (x, _90_2575) -> begin
(let _90_2578 = ()
in (let _181_1173 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _181_1173)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (let t = (let _181_1174 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow (FStar_List.append tps arguments) _181_1174))
in (FStar_Syntax_Syntax.Sig_datacon (Prims.MkTuple8 (c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _90_2583 -> begin
(FStar_All.failwith "impossible")
end))
in (let generalize_and_recheck = (fun env g tcs datas -> (let _90_2589 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _90_7 -> (match (_90_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (Prims.MkTuple8 (_90_2593, _90_2595, tps, k, _90_2599, _90_2601, _90_2603, _90_2605)) -> begin
(let _181_1185 = (let _181_1184 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _181_1184))
in (FStar_Syntax_Syntax.null_binder _181_1185))
end
| _90_2609 -> begin
(FStar_All.failwith "Impossible")
end))))
in (let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _90_8 -> (match (_90_8) with
| FStar_Syntax_Syntax.Sig_datacon (Prims.MkTuple8 (_90_2613, _90_2615, t, _90_2618, _90_2620, _90_2622, _90_2624, _90_2626)) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _90_2630 -> begin
(FStar_All.failwith "Impossible")
end))))
in (let t = (let _181_1187 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Recheck.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _181_1187))
in (let _90_2633 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_1188 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _181_1188))
end else begin
()
end
in (let _90_2637 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_90_2637) with
| (uvs, t) -> begin
(let _90_2639 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_1192 = (let _181_1190 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _181_1190 (FStar_String.concat ", ")))
in (let _181_1191 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _181_1192 _181_1191)))
end else begin
()
end
in (let _90_2643 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_90_2643) with
| (uvs, t) -> begin
(let _90_2647 = (FStar_Syntax_Util.arrow_formals t)
in (match (_90_2647) with
| (args, _90_2646) -> begin
(let _90_2650 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_90_2650) with
| (tc_types, data_types) -> begin
(let tcs = (FStar_List.map2 (fun _90_2654 se -> (match (_90_2654) with
| (x, _90_2653) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (Prims.MkTuple8 (tc, _90_2658, tps, _90_2661, mutuals, datas, quals, r)) -> begin
(let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (let _90_2684 = (match ((let _181_1195 = (FStar_Syntax_Subst.compress ty)
in _181_1195.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(let _90_2675 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_90_2675) with
| (tps, rest) -> begin
(let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _90_2678 -> begin
(let _181_1196 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _181_1196 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _90_2681 -> begin
([], ty)
end)
in (match (_90_2684) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ (Prims.MkTuple8 (tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _90_2686 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (let env_data = (FStar_TypeChecker_Env.push_univ_vars env uvs)
in (let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _181_1197 -> FStar_Syntax_Syntax.U_name (_181_1197))))
in (let env_data = (FStar_List.fold_left (fun env tc -> (FStar_TypeChecker_Env.push_sigelt_inst env tc uvs_universes)) env_data tcs)
in (let datas = (FStar_List.map2 (fun _90_2696 -> (match (_90_2696) with
| (t, _90_2695) -> begin
(fun _90_9 -> (match (_90_9) with
| FStar_Syntax_Syntax.Sig_datacon (Prims.MkTuple8 (l, _90_2700, _90_2702, tc, ntps, quals, mutuals, r)) -> begin
(let ty = (match (uvs) with
| [] -> begin
t.FStar_Syntax_Syntax.sort
end
| _90_2712 -> begin
(let _90_2713 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_1205 = (FStar_Syntax_Print.lid_to_string l)
in (let _181_1204 = (FStar_Syntax_Print.term_to_string t.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Rechecking datacon %s : %s\n" _181_1205 _181_1204)))
end else begin
()
end
in (let _90_2719 = (tc_tot_or_gtot_term env_data t.FStar_Syntax_Syntax.sort)
in (match (_90_2719) with
| (ty, _90_2717, g) -> begin
(let g = (let _90_2720 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _90_2720.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _90_2720.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _90_2720.FStar_TypeChecker_Env.implicits})
in (let _90_2723 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Subst.close_univ_vars uvs ty)))
end)))
end)
in FStar_Syntax_Syntax.Sig_datacon (Prims.MkTuple8 (l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _90_2727 -> begin
(FStar_All.failwith "Impossible")
end))
end)) data_types datas)
in (tcs, datas))))))
end))
end))
end)))
end))))))))
in (let _90_2737 = (FStar_All.pipe_right ses (FStar_List.partition (fun _90_10 -> (match (_90_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_90_2731) -> begin
true
end
| _90_2734 -> begin
false
end))))
in (match (_90_2737) with
| (tys, datas) -> begin
(let env0 = env
in (let _90_2754 = (FStar_List.fold_right (fun tc _90_2743 -> (match (_90_2743) with
| (env, all_tcs, g) -> begin
(let _90_2747 = (tc_tycon env tc)
in (match (_90_2747) with
| (env, tc, tc_u) -> begin
(let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (let _90_2749 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_1209 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _181_1209))
end else begin
()
end
in (let _181_1210 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _181_1210))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_90_2754) with
| (env, tcs, g) -> begin
(let _90_2764 = (FStar_List.fold_right (fun se _90_2758 -> (match (_90_2758) with
| (datas, g) -> begin
(let _90_2761 = (tc_data env tcs se)
in (match (_90_2761) with
| (data, g') -> begin
(let _181_1213 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _181_1213))
end))
end)) datas ([], g))
in (match (_90_2764) with
| (datas, g) -> begin
(let _90_2767 = (let _181_1214 = (FStar_List.map Prims.fst tcs)
in (generalize_and_recheck env0 g _181_1214 datas))
in (match (_90_2767) with
| (tcs, datas) -> begin
(let _181_1216 = (let _181_1215 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _181_1215))
in FStar_Syntax_Syntax.Sig_bundle (_181_1216))
end))
end))
end)))
end)))))))))

let rec tc_decl = (fun env se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(let env = (FStar_TypeChecker_Env.set_range env r)
in (let se = (tc_lex_t env ses quals lids)
in (let _181_1221 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _181_1221))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(let env = (FStar_TypeChecker_Env.set_range env r)
in (let se = (tc_inductive env ses quals lids)
in (let _181_1222 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _181_1222))))
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
(let _90_2803 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _90_2805 = (let _181_1223 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _181_1223 Prims.ignore))
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
(let _90_2820 = (let _181_1224 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _181_1224))
in (match (_90_2820) with
| (a, wp_a_src) -> begin
(let _90_2823 = (let _181_1225 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _181_1225))
in (match (_90_2823) with
| (b, wp_b_tgt) -> begin
(let wp_a_tgt = (let _181_1229 = (let _181_1228 = (let _181_1227 = (let _181_1226 = (FStar_Syntax_Syntax.bv_to_name a)
in (b, _181_1226))
in FStar_Syntax_Syntax.NT (_181_1227))
in (_181_1228)::[])
in (FStar_Syntax_Subst.subst _181_1229 wp_b_tgt))
in (let expected_k = (let _181_1234 = (let _181_1232 = (FStar_Syntax_Syntax.mk_binder a)
in (let _181_1231 = (let _181_1230 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_181_1230)::[])
in (_181_1232)::_181_1231))
in (let _181_1233 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _181_1234 _181_1233)))
in (let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (let sub = (let _90_2827 = sub
in {FStar_Syntax_Syntax.source = _90_2827.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _90_2827.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
in (let se = FStar_Syntax_Syntax.Sig_sub_effect ((sub, r))
in (let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(let _90_2840 = ()
in (let env0 = env
in (let env = (FStar_TypeChecker_Env.set_range env r)
in (let _90_2846 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_90_2846) with
| (tps, c) -> begin
(let _90_2850 = (tc_tparams env tps)
in (match (_90_2850) with
| (tps, env, us) -> begin
(let _90_2854 = (tc_comp env c)
in (match (_90_2854) with
| (c, g, u) -> begin
(let tags = (FStar_All.pipe_right tags (FStar_List.map (fun _90_11 -> (match (_90_11) with
| FStar_Syntax_Syntax.DefaultEffect (None) -> begin
(let c' = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let _181_1237 = (FStar_All.pipe_right c'.FStar_Syntax_Syntax.effect_name (fun _181_1236 -> Some (_181_1236)))
in FStar_Syntax_Syntax.DefaultEffect (_181_1237)))
end
| t -> begin
t
end))))
in (let tps = (FStar_Syntax_Subst.close_binders tps)
in (let c = (FStar_Syntax_Subst.close_comp tps c)
in (let _90_2865 = (let _181_1238 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _181_1238))
in (match (_90_2865) with
| (uvs, t) -> begin
(let _90_2884 = (match ((let _181_1240 = (let _181_1239 = (FStar_Syntax_Subst.compress t)
in _181_1239.FStar_Syntax_Syntax.n)
in (tps, _181_1240))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_90_2868, c)) -> begin
([], c)
end
| (_90_2874, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _90_2881 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_90_2884) with
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
in (let _90_2895 = ()
in (let k = (let _181_1241 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _181_1241))
in (let _90_2900 = (check_and_gen env t k)
in (match (_90_2900) with
| (uvs, t) -> begin
(let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(let env = (FStar_TypeChecker_Env.set_range env r)
in (let _90_2913 = (FStar_Syntax_Util.type_u ())
in (match (_90_2913) with
| (k, _90_2912) -> begin
(let phi = (let _181_1242 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _181_1242 (norm env)))
in (let _90_2915 = (FStar_TypeChecker_Util.check_uvars r phi)
in (let se = FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))
in (let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(let env = (FStar_TypeChecker_Env.set_range env r)
in (let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Recheck.t_unit)
in (let _90_2928 = (tc_term env e)
in (match (_90_2928) with
| (e, c, g1) -> begin
(let _90_2933 = (let _181_1246 = (let _181_1243 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Recheck.t_unit r)
in Some (_181_1243))
in (let _181_1245 = (let _181_1244 = (c.FStar_Syntax_Syntax.comp ())
in (e, _181_1244))
in (check_expected_effect env _181_1246 _181_1245)))
in (match (_90_2933) with
| (e, _90_2931, g) -> begin
(let _90_2934 = (let _181_1247 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _181_1247))
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
(let _181_1257 = (let _181_1256 = (let _181_1255 = (let _181_1254 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Inconsistent qualifier annotations on %s" _181_1254))
in (_181_1255, r))
in FStar_Syntax_Syntax.Error (_181_1256))
in (Prims.raise _181_1257))
end
end))
in (let _90_2978 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _90_2955 lb -> (match (_90_2955) with
| (gen, lbs, quals_opt) -> begin
(let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (let _90_2974 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(let quals_opt = (check_quals_eq lbname quals_opt quals)
in (let _90_2969 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _90_2968 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _181_1260 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _181_1260, quals_opt))))
end)
in (match (_90_2974) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_90_2978) with
| (should_generalize, lbs', quals_opt) -> begin
(let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _90_12 -> (match (_90_12) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _90_2987 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (let lbs' = (FStar_List.rev lbs')
in (let e = (let _181_1264 = (let _181_1263 = (let _181_1262 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _181_1262))
in FStar_Syntax_Syntax.Tm_let (_181_1263))
in (FStar_Syntax_Syntax.mk _181_1264 None r))
in (let _90_3021 = (match ((tc_maybe_toplevel_term (let _90_2991 = env
in {FStar_TypeChecker_Env.solver = _90_2991.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _90_2991.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _90_2991.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _90_2991.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _90_2991.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _90_2991.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _90_2991.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _90_2991.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _90_2991.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _90_2991.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _90_2991.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _90_2991.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _90_2991.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _90_2991.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _90_2991.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _90_2991.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _90_2991.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _90_2991.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _90_2991.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _90_2998; FStar_Syntax_Syntax.pos = _90_2996; FStar_Syntax_Syntax.vars = _90_2994}, _90_3005, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_90_3009, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _90_3015 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _90_3018 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_90_3021) with
| (se, lbs) -> begin
(let _90_3027 = if (log env) then begin
(let _181_1270 = (let _181_1269 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let should_log = (match ((let _181_1266 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _181_1266))) with
| None -> begin
true
end
| _90_3025 -> begin
false
end)
in if should_log then begin
(let _181_1268 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _181_1267 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _181_1268 _181_1267)))
end else begin
""
end))))
in (FStar_All.pipe_right _181_1269 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _181_1270))
end else begin
()
end
in (let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end))))
end))

let for_export = (fun hidden se -> (let private_or_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun x -> ((x = FStar_Syntax_Syntax.Private) || (x = FStar_Syntax_Syntax.Abstract))))))
in (let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _90_3044 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_90_3046) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _90_3057, _90_3059) -> begin
if (private_or_abstract quals) then begin
(FStar_List.fold_right (fun se _90_3065 -> (match (_90_3065) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (Prims.MkTuple8 (l, us, bs, t, _90_3071, _90_3073, quals, r)) -> begin
(let dec = (let _181_1286 = (let _181_1285 = (let _181_1284 = (let _181_1283 = (let _181_1282 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _181_1282))
in FStar_Syntax_Syntax.Tm_arrow (_181_1283))
in (FStar_Syntax_Syntax.mk _181_1284 None r))
in (l, us, _181_1285, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_181_1286))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (Prims.MkTuple8 (l, us, t, _90_3083, _90_3085, _90_3087, _90_3089, r)) -> begin
(let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _90_3095 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_90_3097, _90_3099, quals, _90_3102) -> begin
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
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _90_13 -> (match (_90_13) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _90_3121 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_90_3123) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _90_3139, _90_3141, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
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
(let _181_1291 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _181_1290 = (let _181_1289 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (_181_1289, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_181_1290)))))
in (_181_1291, hidden))
end else begin
((se)::[], hidden)
end
end))))

let tc_decls = (fun env ses -> (let _90_3179 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _90_3160 se -> (match (_90_3160) with
| (ses, exports, env, hidden) -> begin
(let _90_3162 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _181_1298 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _181_1298))
end else begin
()
end
in (let _90_3166 = (tc_decl env se)
in (match (_90_3166) with
| (se, env) -> begin
(let _90_3167 = if ((FStar_ST.read FStar_Options.log_types) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _181_1299 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _181_1299))
end else begin
()
end
in (let _90_3169 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (let _90_3173 = (for_export hidden se)
in (match (_90_3173) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_90_3179) with
| (ses, exports, env, _90_3178) -> begin
(let _181_1300 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _181_1300, env))
end)))

let tc_partial_modul = (fun env modul -> (let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (let msg = (Prims.strcat "Internals for " name)
in (let env = (let _90_3184 = env
in (let _181_1305 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _90_3184.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _90_3184.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _90_3184.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _90_3184.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _90_3184.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _90_3184.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _90_3184.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _90_3184.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _90_3184.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _90_3184.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _90_3184.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _90_3184.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _90_3184.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _90_3184.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _90_3184.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _90_3184.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _181_1305; FStar_TypeChecker_Env.default_effects = _90_3184.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _90_3184.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _90_3184.FStar_TypeChecker_Env.use_bv_sorts}))
in (let _90_3187 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (let _90_3193 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_90_3193) with
| (ses, exports, env) -> begin
((let _90_3194 = modul
in {FStar_Syntax_Syntax.name = _90_3194.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _90_3194.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _90_3194.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))

let tc_more_partial_modul = (fun env modul decls -> (let _90_3202 = (tc_decls env decls)
in (match (_90_3202) with
| (ses, exports, env) -> begin
(let modul = (let _90_3203 = modul
in {FStar_Syntax_Syntax.name = _90_3203.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _90_3203.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _90_3203.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))

let finish_partial_modul = (fun env modul exports -> (let modul = (let _90_3209 = modul
in {FStar_Syntax_Syntax.name = _90_3209.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _90_3209.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (let env = (FStar_TypeChecker_Env.finish_module env modul)
in (let _90_3219 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(let _90_3213 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (let _90_3215 = if ((not (modul.FStar_Syntax_Syntax.is_interface)) || (let _181_1318 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_List.contains modul.FStar_Syntax_Syntax.name.FStar_Ident.str _181_1318))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
end else begin
()
end
in (let _90_3217 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _181_1319 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _181_1319 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))

let tc_modul = (fun env modul -> (let _90_3226 = (tc_partial_modul env modul)
in (match (_90_3226) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

let add_modul_to_tcenv = (fun en m -> (let do_sigelt = (fun en elt -> (let env = (FStar_TypeChecker_Env.push_sigelt en elt)
in (let _90_3233 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env elt)
in env)))
in (let en = (FStar_TypeChecker_Env.set_current_module en m.FStar_Syntax_Syntax.name)
in (let _181_1332 = (FStar_List.fold_left do_sigelt en m.FStar_Syntax_Syntax.exports)
in (FStar_TypeChecker_Env.finish_module _181_1332 m)))))

let type_of = (fun env e -> (let _90_3238 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _181_1337 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _181_1337))
end else begin
()
end
in (let env = (let _90_3240 = env
in {FStar_TypeChecker_Env.solver = _90_3240.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _90_3240.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _90_3240.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _90_3240.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _90_3240.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _90_3240.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _90_3240.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _90_3240.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _90_3240.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _90_3240.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _90_3240.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _90_3240.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _90_3240.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _90_3240.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _90_3240.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _90_3240.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _90_3240.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _90_3240.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _90_3240.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _90_3240.FStar_TypeChecker_Env.use_bv_sorts})
in (let _90_3246 = (tc_tot_or_gtot_term env e)
in (match (_90_3246) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected a total term; got a ghost term", e.FStar_Syntax_Syntax.pos))))
end
end)))))

let check_module = (fun env m -> (let _90_3249 = if ((let _181_1342 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _181_1342)) <> 0) then begin
(let _181_1343 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _181_1343))
end else begin
()
end
in (let _90_3253 = (tc_modul env m)
in (match (_90_3253) with
| (m, env) -> begin
(let _90_3254 = if (FStar_Options.should_dump m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _181_1344 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _181_1344))
end else begin
()
end
in (m, env))
end))))




