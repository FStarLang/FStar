
open Prims

let set_hint_correlator : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env = (fun env se -> (match ((FStar_Options.reuse_hint_for ())) with
| Some (l) -> begin
(

let lid = (let _150_5 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_add_suffix _150_5 l))
in (

let _58_22 = env
in {FStar_TypeChecker_Env.solver = _58_22.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_22.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_22.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_22.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_22.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_22.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_22.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_22.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_22.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_22.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_22.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_22.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_22.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_22.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_22.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_22.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_22.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_22.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_22.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_22.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_22.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_22.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), (0)))}))
end
| None -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (

let lid = (match (lids) with
| [] -> begin
(let _150_8 = (FStar_TypeChecker_Env.current_module env)
in (let _150_7 = (let _150_6 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_right _150_6 FStar_Util.string_of_int))
in (FStar_Ident.lid_add_suffix _150_8 _150_7)))
end
| (l)::_58_28 -> begin
l
end)
in (

let _58_32 = env
in {FStar_TypeChecker_Env.solver = _58_32.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_32.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_32.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_32.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_32.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_32.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_32.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_32.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_32.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_32.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_32.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_32.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_32.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_32.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_32.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_32.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_32.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_32.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_32.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_32.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_32.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_32.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), (0)))})))
end))


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (not ((let _150_11 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _150_11))))))


let rng : FStar_TypeChecker_Env.env  ->  FStar_Range.range = (fun env -> (FStar_TypeChecker_Env.get_range env))


let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _58_37 = env
in {FStar_TypeChecker_Env.solver = _58_37.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_37.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_37.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_37.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_37.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_37.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_37.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_37.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_37.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _58_37.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_37.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_37.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_37.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_37.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_37.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_37.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_37.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_37.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_37.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_37.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_37.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_37.FStar_TypeChecker_Env.qname_and_index}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _58_40 = env
in {FStar_TypeChecker_Env.solver = _58_40.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_40.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_40.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_40.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_40.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_40.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_40.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_40.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_40.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _58_40.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_40.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_40.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_40.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_40.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_40.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_40.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_40.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_40.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_40.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_40.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_40.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_40.FStar_TypeChecker_Env.qname_and_index}))


let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (

let r = if (tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
v.FStar_Syntax_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos tl.FStar_Syntax_Syntax.pos)
end
in (let _150_25 = (let _150_24 = (FStar_Syntax_Syntax.as_arg v)
in (let _150_23 = (let _150_22 = (FStar_Syntax_Syntax.as_arg tl)
in (_150_22)::[])
in (_150_24)::_150_23))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _150_25 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _58_1 -> (match (_58_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _58_50 -> begin
false
end))


let steps = (fun env -> (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[])


let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Beta)::[]) env t))


let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize (steps env) env t))


let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (FStar_TypeChecker_Normalize.normalize_comp (steps env) env c))


let check_no_escape : FStar_Syntax_Syntax.term Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun head_opt env fvs kt -> (

let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
()
end
| _58_67 -> begin
(

let fvs' = (let _150_53 = if try_norm then begin
(norm env t)
end else begin
t
end
in (FStar_Syntax_Free.names _150_53))
in (match ((FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)) with
| None -> begin
()
end
| Some (x) -> begin
if (not (try_norm)) then begin
(aux true t)
end else begin
(

let fail = (fun _58_74 -> (match (()) with
| () -> begin
(

let msg = (match (head_opt) with
| None -> begin
(let _150_57 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _150_57))
end
| Some (head) -> begin
(let _150_59 = (FStar_Syntax_Print.bv_to_string x)
in (let _150_58 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _150_59 _150_58)))
end)
in (let _150_62 = (let _150_61 = (let _150_60 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (_150_60)))
in FStar_Syntax_Syntax.Error (_150_61))
in (Prims.raise _150_62)))
end))
in (

let s = (let _150_64 = (let _150_63 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _150_63))
in (FStar_TypeChecker_Util.new_uvar env _150_64))
in (match ((FStar_TypeChecker_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g)
end
| _58_83 -> begin
(fail ())
end)))
end
end))
end))
in (aux false kt)))


let push_binding = (fun env b -> (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))


let maybe_make_subst = (fun _58_2 -> (match (_58_2) with
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Syntax_Syntax.NT (((x), (e))))::[]
end
| _58_93 -> begin
[]
end))


let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.subst_t = (fun s b v -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
s
end else begin
(FStar_Syntax_Syntax.NT ((((Prims.fst b)), (v))))::s
end)


let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (

let _58_99 = lc
in {FStar_Syntax_Syntax.eff_name = _58_99.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_99.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _58_101 -> (match (()) with
| () -> begin
(let _150_79 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _150_79 t))
end))}))


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let should_return = (fun t -> (match ((let _150_90 = (FStar_Syntax_Subst.compress t)
in _150_90.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_109, c) -> begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(

let t = (FStar_All.pipe_left FStar_Syntax_Util.unrefine (FStar_Syntax_Util.comp_result c))
in (match ((let _150_91 = (FStar_Syntax_Subst.compress t)
in _150_91.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (_58_117) -> begin
false
end
| _58_120 -> begin
true
end))
end else begin
false
end
end
| _58_122 -> begin
true
end))
in (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _150_92 = if ((not ((should_return t))) || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _150_92))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _58_150 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
((e), (lc), (guard))
end
| Some (t') -> begin
(

let _58_132 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_94 = (FStar_Syntax_Print.term_to_string t)
in (let _150_93 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _150_94 _150_93)))
end else begin
()
end
in (

let _58_136 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_58_136) with
| (e, lc) -> begin
(

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _58_140 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_58_140) with
| (e, g) -> begin
(

let _58_141 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_96 = (FStar_Syntax_Print.term_to_string t)
in (let _150_95 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _150_96 _150_95)))
end else begin
()
end
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let _58_146 = (let _150_102 = (FStar_All.pipe_left (fun _150_101 -> Some (_150_101)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _150_102 env e lc g))
in (match (_58_146) with
| (lc, g) -> begin
((e), ((set_lcomp_result lc t')), (g))
end))))
end)))
end)))
end)
in (match (_58_150) with
| (e, lc, g) -> begin
(

let _58_151 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_103 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _150_103))
end else begin
()
end
in ((e), (lc), (g)))
end))))))


let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
((e), (lc), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (t) -> begin
(

let _58_161 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_58_161) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _58_166 -> (match (_58_166) with
| (e, c) -> begin
(

let expected_c_opt = (match (copt) with
| Some (_58_168) -> begin
copt
end
| None -> begin
if ((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Syntax_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) then begin
(let _150_116 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (_150_116))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
if (FStar_Syntax_Util.is_pure_comp c) then begin
(let _150_117 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (_150_117))
end else begin
if (FStar_Syntax_Util.is_pure_or_ghost_comp c) then begin
(let _150_118 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (_150_118))
end else begin
None
end
end
end
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _150_119 = (norm_c env c)
in ((e), (_150_119), (FStar_TypeChecker_Rel.trivial_guard)))
end
| Some (expected_c) -> begin
(

let _58_175 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_122 = (FStar_Syntax_Print.term_to_string e)
in (let _150_121 = (FStar_Syntax_Print.comp_to_string c)
in (let _150_120 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _150_122 _150_121 _150_120))))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _58_178 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_125 = (FStar_Syntax_Print.term_to_string e)
in (let _150_124 = (FStar_Syntax_Print.comp_to_string c)
in (let _150_123 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _150_125 _150_124 _150_123))))
end else begin
()
end
in (

let _58_184 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_58_184) with
| (e, _58_182, g) -> begin
(

let g = (let _150_126 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _150_126 "could not prove post-condition" g))
in (

let _58_186 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_128 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _150_127 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _150_128 _150_127)))
end else begin
()
end
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e (FStar_Syntax_Util.comp_effect_name c) (FStar_Syntax_Util.comp_effect_name expected_c))
in ((e), (expected_c), (g)))))
end)))))
end))
end))


let no_logical_guard = (fun env _58_193 -> (match (_58_193) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
((te), (kt), (f))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _150_134 = (let _150_133 = (let _150_132 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _150_131 = (FStar_TypeChecker_Env.get_range env)
in ((_150_132), (_150_131))))
in FStar_Syntax_Syntax.Error (_150_133))
in (Prims.raise _150_134))
end)
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _150_137 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _150_137))
end))


let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _58_217; FStar_Syntax_Syntax.result_typ = _58_215; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, _58_209))::[]; FStar_Syntax_Syntax.flags = _58_206}) -> begin
(

let pat_vars = (FStar_Syntax_Free.names pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _58_224 -> (match (_58_224) with
| (b, _58_223) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _58_228) -> begin
(let _150_144 = (let _150_143 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _150_143))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _150_144))
end))
end
| _58_232 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end)


let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun env actuals expected_c -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
env.FStar_TypeChecker_Env.letrecs
end else begin
(match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let env = (

let _58_239 = env
in {FStar_TypeChecker_Env.solver = _58_239.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_239.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_239.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_239.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_239.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_239.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_239.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_239.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_239.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_239.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_239.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_239.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _58_239.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_239.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_239.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_239.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_239.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_239.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_239.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_239.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_239.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_239.FStar_TypeChecker_Env.qname_and_index})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _58_251 -> (match (_58_251) with
| (b, _58_250) -> begin
(

let t = (let _150_158 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _150_158))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _58_260 -> begin
(let _150_159 = (FStar_Syntax_Syntax.bv_to_name b)
in (_150_159)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let _58_266 = (FStar_Syntax_Util.head_and_args dec)
in (match (_58_266) with
| (head, _58_265) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _58_270 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _58_3 -> (match (_58_3) with
| FStar_Syntax_Syntax.DECREASES (_58_274) -> begin
true
end
| _58_277 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _58_282 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| _58_287 -> begin
(mk_lex_list xs)
end))
end)))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun _58_292 -> (match (_58_292) with
| (l, t) -> begin
(match ((let _150_165 = (FStar_Syntax_Subst.compress t)
in _150_165.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _58_299 -> (match (_58_299) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _150_169 = (let _150_168 = (let _150_167 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_150_167))
in (FStar_Syntax_Syntax.new_bv _150_168 x.FStar_Syntax_Syntax.sort))
in ((_150_169), (imp)))
end else begin
((x), (imp))
end
end))))
in (

let _58_303 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_58_303) with
| (formals, c) -> begin
(

let dec = (decreases_clause formals c)
in (

let precedes = (let _150_173 = (let _150_172 = (FStar_Syntax_Syntax.as_arg dec)
in (let _150_171 = (let _150_170 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_150_170)::[])
in (_150_172)::_150_171))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _150_173 None r))
in (

let _58_310 = (FStar_Util.prefix formals)
in (match (_58_310) with
| (bs, (last, imp)) -> begin
(

let last = (

let _58_311 = last
in (let _150_174 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _58_311.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_311.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_174}))
in (

let refined_formals = (FStar_List.append bs ((((last), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (

let _58_316 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_177 = (FStar_Syntax_Print.lbname_to_string l)
in (let _150_176 = (FStar_Syntax_Print.term_to_string t)
in (let _150_175 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _150_177 _150_176 _150_175))))
end else begin
()
end
in ((l), (t'))))))
end))))
end)))
end
| _58_319 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end)
end)


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let _58_322 = env
in {FStar_TypeChecker_Env.solver = _58_322.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_322.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_322.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_322.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_322.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_322.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_322.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_322.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_322.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_322.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_322.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_322.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_322.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_322.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_322.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_322.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_322.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_322.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_322.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_322.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_322.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_322.FStar_TypeChecker_Env.qname_and_index}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (

let _58_327 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_247 = (let _150_245 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _150_245))
in (let _150_246 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _150_247 _150_246)))
end else begin
()
end
in (

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_58_331) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let _58_372 = (tc_tot_or_gtot_term env e)
in (match (_58_372) with
| (e, c, g) -> begin
(

let g = (

let _58_373 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_373.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_373.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_373.FStar_TypeChecker_Env.implicits})
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let _58_383 = (FStar_Syntax_Util.type_u ())
in (match (_58_383) with
| (t, u) -> begin
(

let _58_387 = (tc_check_tot_or_gtot_term env e t)
in (match (_58_387) with
| (e, c, g) -> begin
(

let _58_394 = (

let _58_391 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_391) with
| (env, _58_390) -> begin
(tc_pats env pats)
end))
in (match (_58_394) with
| (pats, g') -> begin
(

let g' = (

let _58_395 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_395.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_395.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_395.FStar_TypeChecker_Env.implicits})
in (let _150_252 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_pattern (pats))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _150_251 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((_150_252), (c), (_150_251)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _150_253 = (FStar_Syntax_Subst.compress e)
in _150_253.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_58_404, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _58_411; FStar_Syntax_Syntax.lbtyp = _58_409; FStar_Syntax_Syntax.lbeff = _58_407; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _58_422 = (let _150_254 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _150_254 e1))
in (match (_58_422) with
| (e1, c1, g1) -> begin
(

let _58_426 = (tc_term env e2)
in (match (_58_426) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((None), (c2)))
in (

let e = (let _150_259 = (let _150_258 = (let _150_257 = (let _150_256 = (let _150_255 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_TypeChecker_Common.t_unit), (e1)))
in (_150_255)::[])
in ((false), (_150_256)))
in ((_150_257), (e2)))
in FStar_Syntax_Syntax.Tm_let (_150_258))
in (FStar_Syntax_Syntax.mk _150_259 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _150_260 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e), (c), (_150_260))))))
end))
end))
end
| _58_431 -> begin
(

let _58_435 = (tc_term env e)
in (match (_58_435) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (_58_439)) -> begin
(tc_term env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let _58_450 = (tc_term env e)
in (match (_58_450) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (m)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _58_456) -> begin
(

let _58_462 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_462) with
| (env0, _58_461) -> begin
(

let _58_467 = (tc_comp env0 expected_c)
in (match (_58_467) with
| (expected_c, _58_465, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (

let _58_472 = (let _150_261 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term _150_261 e))
in (match (_58_472) with
| (e, c', g') -> begin
(

let _58_476 = (let _150_263 = (let _150_262 = (c'.FStar_Syntax_Syntax.comp ())
in ((e), (_150_262)))
in (check_expected_effect env0 (Some (expected_c)) _150_263))
in (match (_58_476) with
| (e, expected_c, g'') -> begin
(let _150_266 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t_res)), (Some ((FStar_Syntax_Util.comp_effect_name expected_c)))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _150_265 = (let _150_264 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _150_264))
in ((_150_266), ((FStar_Syntax_Util.lcomp_of_comp expected_c)), (_150_265))))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _58_481) -> begin
(

let _58_486 = (FStar_Syntax_Util.type_u ())
in (match (_58_486) with
| (k, u) -> begin
(

let _58_491 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_491) with
| (t, _58_489, f) -> begin
(

let _58_495 = (let _150_267 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _150_267 e))
in (match (_58_495) with
| (e, c, g) -> begin
(

let _58_499 = (let _150_271 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_496 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _150_271 e c f))
in (match (_58_499) with
| (c, f) -> begin
(

let _58_503 = (let _150_272 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t)), (Some (c.FStar_Syntax_Syntax.eff_name))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _150_272 c))
in (match (_58_503) with
| (e, c, f2) -> begin
(let _150_274 = (let _150_273 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _150_273))
in ((e), (c), (_150_274)))
end))
end))
end))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (a)::(hd)::rest)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_)); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (a)::(hd)::rest)) -> begin
(

let rest = (hd)::rest
in (

let _58_539 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_539) with
| (unary_op, _58_538) -> begin
(

let head = (let _150_275 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (Prims.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) None _150_275))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), (rest)))) None top.FStar_Syntax_Syntax.pos)
in (tc_term env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _58_547; FStar_Syntax_Syntax.pos = _58_545; FStar_Syntax_Syntax.vars = _58_543}, ((e, aqual))::[]) -> begin
(

let _58_557 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end else begin
()
end
in (

let _58_566 = (

let _58_562 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_562) with
| (env0, _58_561) -> begin
(tc_term env0 e)
end))
in (match (_58_566) with
| (e, c, g) -> begin
(

let _58_570 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_570) with
| (reify_op, _58_569) -> begin
(

let u_c = (

let _58_576 = (tc_term env c.FStar_Syntax_Syntax.res_typ)
in (match (_58_576) with
| (_58_572, c, _58_575) -> begin
(match ((let _150_276 = (FStar_Syntax_Subst.compress c.FStar_Syntax_Syntax.res_typ)
in _150_276.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| _58_580 -> begin
(FStar_All.failwith "Unexpected result type of computation")
end)
end))
in (

let repr = (FStar_TypeChecker_Util.reify_comp env c u_c)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e), (aqual)))::[])))) (Some (repr.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let c = (let _150_277 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right _150_277 FStar_Syntax_Util.lcomp_of_comp))
in (

let _58_588 = (comp_check_expected_typ env e c)
in (match (_58_588) with
| (e, c, g') -> begin
(let _150_278 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), (c), (_150_278)))
end))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.tk = _58_594; FStar_Syntax_Syntax.pos = _58_592; FStar_Syntax_Syntax.vars = _58_590}, ((e, aqual))::[]) -> begin
(

let _58_605 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end else begin
()
end
in (

let no_reflect = (fun _58_608 -> (match (()) with
| () -> begin
(let _150_283 = (let _150_282 = (let _150_281 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((_150_281), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_282))
in (Prims.raise _150_283))
end))
in (

let _58_612 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_612) with
| (reflect_op, _58_611) -> begin
(match ((FStar_TypeChecker_Env.effect_decl_opt env l)) with
| None -> begin
(no_reflect ())
end
| Some (ed) -> begin
if (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable)))) then begin
(no_reflect ())
end else begin
(

let _58_618 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_618) with
| (env_no_ex, topt) -> begin
(

let _58_646 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (let _150_289 = (let _150_288 = (let _150_287 = (let _150_286 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _150_285 = (let _150_284 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (_150_284)::[])
in (_150_286)::_150_285))
in ((repr), (_150_287)))
in FStar_Syntax_Syntax.Tm_app (_150_288))
in (FStar_Syntax_Syntax.mk _150_289 None top.FStar_Syntax_Syntax.pos))
in (

let _58_626 = (let _150_291 = (let _150_290 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _150_290 Prims.fst))
in (tc_tot_or_gtot_term _150_291 t))
in (match (_58_626) with
| (t, _58_624, g) -> begin
(match ((let _150_292 = (FStar_Syntax_Subst.compress t)
in _150_292.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_58_628, ((res, _58_635))::((wp, _58_631))::[]) -> begin
((t), (res), (wp), (g))
end
| _58_641 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))
in (match (_58_646) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let _58_660 = (

let _58_650 = (tc_tot_or_gtot_term env_no_ex e)
in (match (_58_650) with
| (e, c, g) -> begin
(

let _58_651 = if (let _150_293 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation _150_293)) then begin
(FStar_TypeChecker_Errors.add_errors env (((("Expected Tot, got a GTot computation"), (e.FStar_Syntax_Syntax.pos)))::[]))
end else begin
()
end
in (match ((FStar_TypeChecker_Rel.try_teq env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)) with
| None -> begin
(

let _58_654 = (let _150_298 = (let _150_297 = (let _150_296 = (let _150_295 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _150_294 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" _150_295 _150_294)))
in ((_150_296), (e.FStar_Syntax_Syntax.pos)))
in (_150_297)::[])
in (FStar_TypeChecker_Errors.add_errors env _150_298))
in (let _150_299 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e), (_150_299))))
end
| Some (g') -> begin
(let _150_301 = (let _150_300 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' _150_300))
in ((e), (_150_301)))
end))
end))
in (match (_58_660) with
| (e, g) -> begin
(

let c = (let _150_305 = (let _150_304 = (let _150_303 = (let _150_302 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_302)::[])
in {FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = _150_303; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp _150_304))
in (FStar_All.pipe_right _150_305 FStar_Syntax_Util.lcomp_of_comp))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e), (aqual)))::[])))) (Some (res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let _58_666 = (comp_check_expected_typ env e c)
in (match (_58_666) with
| (e, c, g') -> begin
(let _150_306 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e), (c), (_150_306)))
end))))
end))
end))
end))
end
end)
end))))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let env0 = env
in (

let env = (let _150_308 = (let _150_307 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _150_307 Prims.fst))
in (FStar_All.pipe_right _150_308 instantiate_both))
in (

let _58_673 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_310 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _150_309 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _150_310 _150_309)))
end else begin
()
end
in (

let _58_678 = (tc_term (no_inst env) head)
in (match (_58_678) with
| (head, chead, g_head) -> begin
(

let _58_682 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _150_311 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _150_311))
end else begin
(let _150_312 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _150_312))
end
in (match (_58_682) with
| (e, c, g) -> begin
(

let _58_683 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_313 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _150_313))
end else begin
()
end
in (

let c = if (((FStar_TypeChecker_Env.should_verify env) && (not ((FStar_Syntax_Util.is_lcomp_partial_return c)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)) then begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e c)
end else begin
c
end
in (

let _58_689 = (comp_check_expected_typ env0 e c)
in (match (_58_689) with
| (e, c, g') -> begin
(

let gimp = (match ((let _150_314 = (FStar_Syntax_Subst.compress head)
in _150_314.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _58_692) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e), (c.FStar_Syntax_Syntax.res_typ), (head.FStar_Syntax_Syntax.pos))
in (

let _58_696 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_696.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_696.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_696.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _58_699 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (

let gres = (let _150_315 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _150_315))
in (

let _58_702 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_317 = (FStar_Syntax_Print.term_to_string e)
in (let _150_316 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" _150_317 _150_316)))
end else begin
()
end
in ((e), (c), (gres)))))
end))))
end))
end)))))
end
| FStar_Syntax_Syntax.Tm_match (e1, eqns) -> begin
(

let _58_710 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_710) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let _58_715 = (tc_term env1 e1)
in (match (_58_715) with
| (e1, c1, g1) -> begin
(

let _58_726 = (match (topt) with
| Some (t) -> begin
((env), (t))
end
| None -> begin
(

let _58_722 = (FStar_Syntax_Util.type_u ())
in (match (_58_722) with
| (k, _58_721) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _150_318 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in ((_150_318), (res_t))))
end))
end)
in (match (_58_726) with
| (env_branches, res_t) -> begin
(

let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let _58_743 = (

let _58_740 = (FStar_List.fold_right (fun _58_734 _58_737 -> (match (((_58_734), (_58_737))) with
| ((_58_730, f, c, g), (caccum, gaccum)) -> begin
(let _150_321 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (_150_321)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_58_740) with
| (cases, g) -> begin
(let _150_322 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in ((_150_322), (g)))
end))
in (match (_58_743) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (guard_x)), (c_branches)))
in (

let e = (

let mk_match = (fun scrutinee -> (

let branches = (FStar_List.map (fun _58_754 -> (match (_58_754) with
| (f, _58_749, _58_751, _58_753) -> begin
f
end)) t_eqns)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (Some (cres.FStar_Syntax_Syntax.eff_name))))) None e.FStar_Syntax_Syntax.pos))))
in if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c1.FStar_Syntax_Syntax.eff_name) then begin
(mk_match e1)
end else begin
(

let e_match = (let _150_326 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match _150_326))
in (

let lb = (let _150_327 = (FStar_TypeChecker_Env.norm_eff_name env c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = _150_327; FStar_Syntax_Syntax.lbdef = e1})
in (let _150_332 = (let _150_331 = (let _150_330 = (let _150_329 = (let _150_328 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (_150_328)::[])
in (FStar_Syntax_Subst.close _150_329 e_match))
in ((((false), ((lb)::[]))), (_150_330)))
in FStar_Syntax_Syntax.Tm_let (_150_331))
in (FStar_Syntax_Syntax.mk _150_332 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))))
end)
in (

let _58_760 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_335 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _150_334 = (let _150_333 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _150_333))
in (FStar_Util.print2 "(%s) comp type = %s\n" _150_335 _150_334)))
end else begin
()
end
in (let _150_336 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e), (cres), (_150_336))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_772); FStar_Syntax_Syntax.lbunivs = _58_770; FStar_Syntax_Syntax.lbtyp = _58_768; FStar_Syntax_Syntax.lbeff = _58_766; FStar_Syntax_Syntax.lbdef = _58_764})::[]), _58_778) -> begin
(

let _58_781 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_337 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _150_337))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _58_785), _58_788) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_803); FStar_Syntax_Syntax.lbunivs = _58_801; FStar_Syntax_Syntax.lbtyp = _58_799; FStar_Syntax_Syntax.lbeff = _58_797; FStar_Syntax_Syntax.lbdef = _58_795})::_58_793), _58_809) -> begin
(

let _58_812 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_338 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _150_338))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _58_816), _58_819) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let _58_833 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_833) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _150_352 = (let _150_351 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_351))
in FStar_Util.Inr (_150_352))
end
in (

let is_data_ctor = (fun _58_4 -> (match (_58_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _58_843 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _150_358 = (let _150_357 = (let _150_356 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _150_355 = (FStar_TypeChecker_Env.get_range env)
in ((_150_356), (_150_355))))
in FStar_Syntax_Syntax.Error (_150_357))
in (Prims.raise _150_358))
end else begin
(value_check_expected_typ env e tc implicits)
end))
end)))
in (

let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _150_360 = (let _150_359 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" _150_359))
in (FStar_All.failwith _150_360))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (match ((let _150_361 = (FStar_Syntax_Subst.compress t1)
in _150_361.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_854) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _58_857 -> begin
(

let imp = (("uvar in term"), (env), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let _58_859 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_859.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_859.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_859.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _58_874 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(

let _58_867 = (FStar_Syntax_Util.type_u ())
in (match (_58_867) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
end))
end
| Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end)
in (match (_58_874) with
| (t, _58_872, g0) -> begin
(

let _58_879 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (_58_879) with
| (e, _58_877, g1) -> begin
(let _150_364 = (let _150_362 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right _150_362 FStar_Syntax_Util.lcomp_of_comp))
in (let _150_363 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e), (_150_364), (_150_363))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = if env.FStar_TypeChecker_Env.use_bv_sorts then begin
x.FStar_Syntax_Syntax.sort
end else begin
(FStar_TypeChecker_Env.lookup_bv env x)
end
in (

let e = (FStar_Syntax_Syntax.bv_to_name (

let _58_883 = x
in {FStar_Syntax_Syntax.ppname = _58_883.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_883.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let _58_889 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_889) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _150_366 = (let _150_365 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_365))
in FStar_Util.Inr (_150_366))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _58_896; FStar_Syntax_Syntax.pos = _58_894; FStar_Syntax_Syntax.vars = _58_892}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let _58_906 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_906) with
| (us', t) -> begin
(

let _58_913 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _150_369 = (let _150_368 = (let _150_367 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (_150_367)))
in FStar_Syntax_Syntax.Error (_150_368))
in (Prims.raise _150_369))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _58_912 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (

let fv' = (

let _58_915 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _58_917 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_917.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_917.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_915.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_915.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _150_372 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_372 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let _58_925 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_925) with
| (us, t) -> begin
(

let fv' = (

let _58_926 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _58_928 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_928.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_928.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_926.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_926.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _150_373 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_373 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t)))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let t = (tc_constant top.FStar_Syntax_Syntax.pos c)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _58_942 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_942) with
| (bs, c) -> begin
(

let env0 = env
in (

let _58_947 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_947) with
| (env, _58_946) -> begin
(

let _58_952 = (tc_binders env bs)
in (match (_58_952) with
| (bs, env, g, us) -> begin
(

let _58_956 = (tc_comp env c)
in (match (_58_956) with
| (c, uc, f) -> begin
(

let e = (

let _58_957 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _58_957.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_957.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_957.FStar_Syntax_Syntax.vars})
in (

let _58_960 = (check_smt_pat env e bs c)
in (

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _150_374 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _150_374))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u = (tc_universe env u)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) None top.FStar_Syntax_Syntax.pos)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let _58_976 = (let _150_376 = (let _150_375 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_375)::[])
in (FStar_Syntax_Subst.open_term _150_376 phi))
in (match (_58_976) with
| (x, phi) -> begin
(

let env0 = env
in (

let _58_981 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_981) with
| (env, _58_980) -> begin
(

let _58_986 = (let _150_377 = (FStar_List.hd x)
in (tc_binder env _150_377))
in (match (_58_986) with
| (x, env, f1, u) -> begin
(

let _58_987 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_380 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _150_379 = (FStar_Syntax_Print.term_to_string phi)
in (let _150_378 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _150_380 _150_379 _150_378))))
end else begin
()
end
in (

let _58_992 = (FStar_Syntax_Util.type_u ())
in (match (_58_992) with
| (t_phi, _58_991) -> begin
(

let _58_997 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_58_997) with
| (phi, _58_995, f2) -> begin
(

let e = (

let _58_998 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _58_998.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_998.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_998.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _150_381 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _150_381))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _58_1006) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (

let _58_1012 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_382 = (FStar_Syntax_Print.term_to_string (

let _58_1010 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))); FStar_Syntax_Syntax.tk = _58_1010.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _58_1010.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_1010.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _150_382))
end else begin
()
end
in (

let _58_1016 = (FStar_Syntax_Subst.open_term bs body)
in (match (_58_1016) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _58_1018 -> begin
(let _150_385 = (let _150_384 = (FStar_Syntax_Print.term_to_string top)
in (let _150_383 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" _150_384 _150_383)))
in (FStar_All.failwith _150_385))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_58_1023) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_58_1026, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_58_1031, Some (_58_1033)) -> begin
(FStar_All.failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (_58_1038) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_58_1041) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_58_1044) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_58_1048) -> begin
FStar_TypeChecker_Common.t_range
end
| _58_1051 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(

let _58_1059 = (FStar_Syntax_Util.type_u ())
in (match (_58_1059) with
| (k, u) -> begin
(

let _58_1064 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_1064) with
| (t, _58_1062, g) -> begin
(let _150_390 = (FStar_Syntax_Syntax.mk_Total t)
in ((_150_390), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(

let _58_1069 = (FStar_Syntax_Util.type_u ())
in (match (_58_1069) with
| (k, u) -> begin
(

let _58_1074 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_1074) with
| (t, _58_1072, g) -> begin
(let _150_391 = (FStar_Syntax_Syntax.mk_GTotal t)
in ((_150_391), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (

let tc = (let _150_393 = (let _150_392 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_150_392)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _150_393 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let _58_1083 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_58_1083) with
| (tc, _58_1081, f) -> begin
(

let _58_1087 = (FStar_Syntax_Util.head_and_args tc)
in (match (_58_1087) with
| (_58_1085, args) -> begin
(

let _58_1090 = (let _150_395 = (FStar_List.hd args)
in (let _150_394 = (FStar_List.tl args)
in ((_150_395), (_150_394))))
in (match (_58_1090) with
| (res, args) -> begin
(

let _58_1106 = (let _150_397 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _58_5 -> (match (_58_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _58_1097 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1097) with
| (env, _58_1096) -> begin
(

let _58_1102 = (tc_tot_or_gtot_term env e)
in (match (_58_1102) with
| (e, _58_1100, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e)), (g))
end))
end))
end
| f -> begin
((f), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right _150_397 FStar_List.unzip))
in (match (_58_1106) with
| (flags, guards) -> begin
(

let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Syntax.mk t None FStar_Range.dummyRange)
in (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| _58_1117 -> begin
(FStar_All.failwith "Impossible:Unexpected sort for computation")
end)))
end
| _58_1119 -> begin
(FStar_All.failwith "Impossible:Unexpected sort for computation")
end)
in (let _150_399 = (FStar_Syntax_Syntax.mk_Comp (

let _58_1121 = c
in {FStar_Syntax_Syntax.effect_name = _58_1121.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _58_1121.FStar_Syntax_Syntax.flags}))
in (let _150_398 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((_150_399), (u), (_150_398)))))
end))
end))
end))
end))))
end)))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_58_1129) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _150_404 = (aux u)
in FStar_Syntax_Syntax.U_succ (_150_404))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _150_405 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_150_405))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _150_409 = (let _150_408 = (let _150_407 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _150_406 = (FStar_TypeChecker_Env.get_range env)
in ((_150_407), (_150_406))))
in FStar_Syntax_Syntax.Error (_150_408))
in (Prims.raise _150_409))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _150_410 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_410 Prims.snd))
end
| _58_1144 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _150_419 = (let _150_418 = (let _150_417 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in ((_150_417), (top.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_418))
in (Prims.raise _150_419)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun _58_1162 bs bs_expected -> (match (_58_1162) with
| (env, out, g, subst) -> begin
(match (((bs), (bs_expected))) with
| ([], []) -> begin
((env), ((FStar_List.rev out)), (None), (g), (subst))
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
(

let _58_1193 = (match (((imp), (imp'))) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _150_436 = (let _150_435 = (let _150_434 = (let _150_432 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _150_432))
in (let _150_433 = (FStar_Syntax_Syntax.range_of_bv hd)
in ((_150_434), (_150_433))))
in FStar_Syntax_Syntax.Error (_150_435))
in (Prims.raise _150_436))
end
| _58_1192 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _58_1210 = (match ((let _150_437 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _150_437.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| _58_1198 -> begin
(

let _58_1199 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_438 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _150_438))
end else begin
()
end
in (

let _58_1205 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_58_1205) with
| (t, _58_1203, g1) -> begin
(

let g2 = (let _150_440 = (FStar_TypeChecker_Env.get_range env)
in (let _150_439 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _150_440 "Type annotation on parameter incompatible with the expected type" _150_439)))
in (

let g = (let _150_441 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _150_441))
in ((t), (g))))
end)))
end)
in (match (_58_1210) with
| (t, g) -> begin
(

let hd = (

let _58_1211 = hd
in {FStar_Syntax_Syntax.ppname = _58_1211.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1211.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env = (push_binding env b)
in (

let subst = (let _150_442 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _150_442))
in (aux ((env), ((b)::out), (g), (subst)) bs bs_expected))))))
end))))
end
| (rest, []) -> begin
((env), ((FStar_List.rev out)), (Some (FStar_Util.Inl (rest))), (g), (subst))
end
| ([], rest) -> begin
((env), ((FStar_List.rev out)), (Some (FStar_Util.Inr (rest))), (g), (subst))
end)
end))
in (aux ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs bs_expected)))
in (

let rec expected_function_typ = (fun env t0 body -> (match (t0) with
| None -> begin
(

let _58_1232 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _58_1231 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (

let _58_1239 = (tc_binders env bs)
in (match (_58_1239) with
| (bs, envbody, g, _58_1238) -> begin
(

let _58_1257 = (match ((let _150_449 = (FStar_Syntax_Subst.compress body)
in _150_449.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _58_1244) -> begin
(

let _58_1251 = (tc_comp envbody c)
in (match (_58_1251) with
| (c, _58_1249, g') -> begin
(let _150_450 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((Some (c)), (body), (_150_450)))
end))
end
| _58_1253 -> begin
((None), (body), (g))
end)
in (match (_58_1257) with
| (copt, body, g) -> begin
((None), (bs), ([]), (copt), (envbody), (body), (g))
end))
end)))
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm t -> (match ((let _150_455 = (FStar_Syntax_Subst.compress t)
in _150_455.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let _58_1284 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _58_1283 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _58_1291 = (tc_binders env bs)
in (match (_58_1291) with
| (bs, envbody, g, _58_1290) -> begin
(

let _58_1295 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_58_1295) with
| (envbody, _58_1294) -> begin
((Some (((t), (true)))), (bs), ([]), (None), (envbody), (body), (g))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _58_1298) -> begin
(

let _58_1309 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_58_1309) with
| (_58_1302, bs, bs', copt, env, body, g) -> begin
((Some (((t), (false)))), (bs), (bs'), (copt), (env), (body), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _58_1316 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_58_1316) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun _58_1327 c_expected -> (match (_58_1327) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _150_466 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in ((env), (bs), (guard), (_150_466)))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (let _150_467 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _150_467))
in (let _150_468 = (FStar_Syntax_Subst.subst_comp subst c)
in ((env), (bs), (guard), (_150_468))))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(

let c = (FStar_Syntax_Subst.subst_comp subst c_expected)
in if (FStar_Syntax_Util.is_total_comp c) then begin
(

let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _58_1348 = (check_binders env more_bs bs_expected)
in (match (_58_1348) with
| (env, bs', more, guard', subst) -> begin
(let _150_470 = (let _150_469 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env), ((FStar_List.append bs bs')), (more), (_150_469), (subst)))
in (handle_more _150_470 c_expected))
end))
end
| _58_1350 -> begin
(let _150_472 = (let _150_471 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _150_471))
in (fail _150_472 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _150_473 = (check_binders env bs bs_expected)
in (handle_more _150_473 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let _58_1356 = envbody
in {FStar_TypeChecker_Env.solver = _58_1356.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1356.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1356.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1356.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1356.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1356.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1356.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1356.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1356.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1356.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1356.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1356.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _58_1356.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1356.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1356.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1356.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1356.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1356.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1356.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1356.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1356.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1356.FStar_TypeChecker_Env.qname_and_index})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _58_1361 _58_1364 -> (match (((_58_1361), (_58_1364))) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _58_1370 = (let _150_483 = (let _150_482 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _150_482 Prims.fst))
in (tc_term _150_483 t))
in (match (_58_1370) with
| (t, _58_1367, _58_1369) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l (([]), (t)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _150_484 = (FStar_Syntax_Syntax.mk_binder (

let _58_1374 = x
in {FStar_Syntax_Syntax.ppname = _58_1374.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1374.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_150_484)::letrec_binders)
end
| _58_1377 -> begin
letrec_binders
end)
in ((env), (lb))))
end))
end)) ((envbody), ([])))))))
in (

let _58_1383 = (check_actuals_against_formals env bs bs_expected)
in (match (_58_1383) with
| (envbody, bs, g, c) -> begin
(

let _58_1386 = if (FStar_TypeChecker_Env.should_verify env) then begin
(mk_letrec_env envbody bs c)
end else begin
((envbody), ([]))
end
in (match (_58_1386) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in ((Some (((t), (false)))), (bs), (letrecs), (Some (c)), (envbody), (body), (g)))
end))
end))))
end))
end
| _58_1389 -> begin
if (not (norm)) then begin
(let _150_485 = (unfold_whnf env t)
in (as_function_typ true _150_485))
end else begin
(

let _58_1399 = (expected_function_typ env None body)
in (match (_58_1399) with
| (_58_1391, bs, _58_1394, c_opt, envbody, body, g) -> begin
((Some (((t), (false)))), (bs), ([]), (c_opt), (envbody), (body), (g))
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let _58_1403 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1403) with
| (env, topt) -> begin
(

let _58_1407 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_486 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _150_486 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (

let _58_1416 = (expected_function_typ env topt body)
in (match (_58_1416) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let _58_1422 = (tc_term (

let _58_1417 = envbody
in {FStar_TypeChecker_Env.solver = _58_1417.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1417.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1417.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1417.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1417.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1417.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1417.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1417.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1417.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1417.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1417.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1417.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1417.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_1417.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1417.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1417.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1417.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1417.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1417.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1417.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1417.FStar_TypeChecker_Env.qname_and_index}) body)
in (match (_58_1422) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _58_1424 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _150_489 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _150_488 = (let _150_487 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _150_487))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _150_489 _150_488)))
end else begin
()
end
in (

let _58_1431 = (let _150_491 = (let _150_490 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body), (_150_490)))
in (check_expected_effect (

let _58_1426 = envbody
in {FStar_TypeChecker_Env.solver = _58_1426.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1426.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1426.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1426.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1426.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1426.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1426.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1426.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1426.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1426.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1426.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1426.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1426.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1426.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1426.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1426.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1426.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1426.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1426.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1426.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1426.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1426.FStar_TypeChecker_Env.qname_and_index}) c_opt _150_491))
in (match (_58_1431) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(let _150_492 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _150_492))
end else begin
(

let guard = (let _150_493 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) _150_493))
in guard)
end
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _150_496 = (let _150_495 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _150_494 -> FStar_Util.Inl (_150_494)))
in Some (_150_495))
in (FStar_Syntax_Util.abs bs body _150_496))
in (

let _58_1454 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_58_1443) -> begin
((e), (t), (guard))
end
| _58_1446 -> begin
(

let _58_1449 = if use_teq then begin
(let _150_497 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in ((e), (_150_497)))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_58_1449) with
| (e, guard') -> begin
(let _150_498 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((e), (t), (_150_498)))
end))
end))
end
| None -> begin
((e), (tfun_computed), (guard))
end)
in (match (_58_1454) with
| (e, tfun, guard) -> begin
(

let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (

let _58_1458 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_58_1458) with
| (c, g) -> begin
((e), (c), (g))
end)))
end))))))
end))))
end))
end)))
end)))))))
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead ghead args expected_topt -> (

let n_args = (FStar_List.length args)
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let thead = chead.FStar_Syntax_Syntax.res_typ
in (

let _58_1468 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_507 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _150_506 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _150_507 _150_506)))
end else begin
()
end
in (

let monadic_application = (fun _58_1475 subst arg_comps_rev arg_rets guard fvs bs -> (match (_58_1475) with
| (head, chead, ghead, cres) -> begin
(

let _58_1482 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let _58_1510 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun _58_6 -> (match (_58_6) with
| (_58_1489, _58_1491, None) -> begin
false
end
| (_58_1495, _58_1497, Some (c)) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _150_523 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _150_523 cres))
end else begin
(

let _58_1502 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_526 = (FStar_Syntax_Print.term_to_string head)
in (let _150_525 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _150_524 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _150_526 _150_525 _150_524))))
end else begin
()
end
in cres)
end
in ((cres), (g))))))
end
| _58_1506 -> begin
(

let g = (let _150_527 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right _150_527 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _150_532 = (let _150_531 = (let _150_530 = (let _150_529 = (let _150_528 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _150_528))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _150_529))
in (FStar_Syntax_Syntax.mk_Total _150_530))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_531))
in ((_150_532), (g))))
end)
in (match (_58_1510) with
| (cres, guard) -> begin
(

let _58_1511 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_533 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _150_533))
end else begin
()
end
in (

let _58_1533 = (FStar_List.fold_left (fun _58_1516 _58_1522 -> (match (((_58_1516), (_58_1522))) with
| ((args, out_c, monadic), ((e, q), x, c)) -> begin
(match (c) with
| None -> begin
(((((e), (q)))::args), (out_c), (monadic))
end
| Some (c) -> begin
(

let monadic = (monadic || (not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c))))
in (

let out_c = (FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env None c ((x), (out_c)))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e c.FStar_Syntax_Syntax.eff_name out_c.FStar_Syntax_Syntax.eff_name)
in (((((e), (q)))::args), (out_c), (monadic))))))
end)
end)) (([]), (cres), (false)) arg_comps_rev)
in (match (_58_1533) with
| (args, comp, monadic) -> begin
(

let comp = (FStar_TypeChecker_Util.bind head.FStar_Syntax_Syntax.pos env None chead ((None), (comp)))
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app = if monadic then begin
(FStar_TypeChecker_Util.maybe_monadic env app comp.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.res_typ)
end else begin
app
end
in (

let _58_1539 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (_58_1539) with
| (comp, g) -> begin
((app), (comp), (g))
end)))))
end)))
end)))
end))
in (

let rec tc_args = (fun head_info _58_1547 bs args -> (match (_58_1547) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args))) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (_58_1553))))::rest, ((_58_1561, None))::_58_1559) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _58_1567 = (check_no_escape (Some (head)) env fvs t)
in (

let _58_1573 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_58_1573) with
| (varg, _58_1571, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst
in (

let arg = (let _150_545 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (_150_545)))
in (let _150_547 = (let _150_546 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst), ((((arg), (None), (None)))::outargs), ((arg)::arg_rets), (_150_546), (fvs)))
in (tc_args head_info _150_547 rest args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
(

let _58_1605 = (match (((aqual), (aq))) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _58_1604 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifier"), (e.FStar_Syntax_Syntax.pos)))))
end)
in (

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let _58_1608 = x
in {FStar_Syntax_Syntax.ppname = _58_1608.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1608.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (

let _58_1611 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_548 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _150_548))
end else begin
()
end
in (

let _58_1613 = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let _58_1616 = env
in {FStar_TypeChecker_Env.solver = _58_1616.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1616.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1616.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1616.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1616.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1616.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1616.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1616.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1616.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1616.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1616.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1616.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1616.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1616.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1616.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _58_1616.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1616.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1616.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1616.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1616.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1616.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1616.FStar_TypeChecker_Env.qname_and_index})
in (

let _58_1619 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_551 = (FStar_Syntax_Print.tag_of_term e)
in (let _150_550 = (FStar_Syntax_Print.term_to_string e)
in (let _150_549 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _150_551 _150_550 _150_549))))
end else begin
()
end
in (

let _58_1624 = (tc_term env e)
in (match (_58_1624) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = ((e), (aq))
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(

let subst = (let _150_552 = (FStar_List.hd bs)
in (maybe_extend_subst subst _150_552 e))
in (tc_args head_info ((subst), ((((arg), (None), (None)))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(

let subst = (let _150_553 = (FStar_List.hd bs)
in (maybe_extend_subst subst _150_553 e))
in (tc_args head_info ((subst), ((((arg), (Some (x)), (Some (c))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (let _150_554 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _150_554)) then begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _150_555 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_555))
in (tc_args head_info ((subst), ((((arg), (Some (newx)), (Some (c))))::outargs), ((arg')::arg_rets), (g), (fvs)) rest rest')))
end else begin
(let _150_559 = (let _150_558 = (let _150_557 = (let _150_556 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _150_556))
in (_150_557)::arg_rets)
in ((subst), ((((arg), (Some (x)), (Some (c))))::outargs), (_150_558), (g), ((x)::fvs)))
in (tc_args head_info _150_559 rest rest'))
end
end
end))
end))))))))))
end
| (_58_1632, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::_58_1637) -> begin
(

let _58_1644 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (_58_1644) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _150_564 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _150_564 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let _58_1655 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (_58_1655) with
| (bs, cres') -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp cres')))
in (

let _58_1657 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_565 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _150_565))
end else begin
()
end
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args)))
end))
end
| _58_1660 when (not (norm)) -> begin
(let _150_566 = (unfold_whnf env tres)
in (aux true _150_566))
end
| _58_1662 -> begin
(let _150_572 = (let _150_571 = (let _150_570 = (let _150_568 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (let _150_567 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _150_568 _150_567)))
in (let _150_569 = (FStar_Syntax_Syntax.argpos arg)
in ((_150_570), (_150_569))))
in FStar_Syntax_Syntax.Error (_150_571))
in (Prims.raise _150_572))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (match ((let _150_577 = (FStar_Syntax_Util.unrefine tf)
in _150_577.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl -> begin
(

let _58_1695 = (tc_term env e)
in (match (_58_1695) with
| (e, c, g_e) -> begin
(

let _58_1699 = (tc_args env tl)
in (match (_58_1699) with
| (args, comps, g_rest) -> begin
(let _150_582 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e), (imp)))::args), ((((e.FStar_Syntax_Syntax.pos), (c)))::comps), (_150_582)))
end))
end))
end))
in (

let _58_1703 = (tc_args env args)
in (match (_58_1703) with
| (args, comps, g_args) -> begin
(

let bs = (let _150_584 = (FStar_All.pipe_right comps (FStar_List.map (fun _58_1707 -> (match (_58_1707) with
| (_58_1705, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks _150_584))
in (

let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _58_1713 -> begin
FStar_Syntax_Util.ml_comp
end)
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _150_599 = (FStar_Syntax_Subst.compress t)
in _150_599.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_58_1719) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _58_1724 -> begin
ml_or_tot
end)
end)
in (

let cres = (let _150_604 = (let _150_603 = (let _150_602 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_602 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _150_603))
in (ml_or_tot _150_604 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (

let _58_1728 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_607 = (FStar_Syntax_Print.term_to_string head)
in (let _150_606 = (FStar_Syntax_Print.term_to_string tf)
in (let _150_605 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _150_607 _150_606 _150_605))))
end else begin
()
end
in (

let _58_1730 = (let _150_608 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _150_608))
in (

let comp = (let _150_611 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _58_1734 out -> (match (_58_1734) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c ((None), (out)))
end)) ((((head.FStar_Syntax_Syntax.pos), (chead)))::comps) _150_611))
in (let _150_613 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _150_612 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((_150_613), (comp), (_150_612))))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _58_1743 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_1743) with
| (bs, c) -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp c)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args))
end))
end
| _58_1746 -> begin
if (not (norm)) then begin
(let _150_614 = (unfold_whnf env tf)
in (check_function_app true _150_614))
end else begin
(let _150_617 = (let _150_616 = (let _150_615 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in ((_150_615), (head.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_616))
in (Prims.raise _150_617))
end
end))
in (let _150_619 = (let _150_618 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _150_618))
in (check_function_app false _150_619))))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let _58_1782 = (FStar_List.fold_left2 (fun _58_1763 _58_1766 _58_1769 -> (match (((_58_1763), (_58_1766), (_58_1769))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(

let _58_1770 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifiers"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _58_1775 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_58_1775) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (let _150_629 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _150_629 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _150_633 = (let _150_631 = (let _150_630 = (FStar_Syntax_Syntax.as_arg e)
in (_150_630)::[])
in (FStar_List.append seen _150_631))
in (let _150_632 = (FStar_TypeChecker_Rel.conj_guard guard g)
in ((_150_633), (_150_632), (ghost)))))))
end)))
end)) (([]), (g_head), (false)) args bs)
in (match (_58_1782) with
| (args, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = if ghost then begin
(let _150_634 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _150_634 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (

let _58_1787 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_58_1787) with
| (c, g) -> begin
((e), (c), (g))
end))))
end)))
end
| _58_1789 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let _58_1796 = (FStar_Syntax_Subst.open_branch branch)
in (match (_58_1796) with
| (pattern, when_clause, branch_exp) -> begin
(

let _58_1801 = branch
in (match (_58_1801) with
| (cpat, _58_1799, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _58_1809 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_58_1809) with
| (pat_bvs, exps, p) -> begin
(

let _58_1810 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_646 = (FStar_Syntax_Print.pat_to_string p0)
in (let _150_645 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _150_646 _150_645)))
end else begin
()
end
in (

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let _58_1816 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_58_1816) with
| (env1, _58_1815) -> begin
(

let env1 = (

let _58_1817 = env1
in {FStar_TypeChecker_Env.solver = _58_1817.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1817.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1817.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1817.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1817.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1817.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1817.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1817.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _58_1817.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1817.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1817.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1817.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1817.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1817.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1817.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1817.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1817.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1817.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1817.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1817.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1817.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1817.FStar_TypeChecker_Env.qname_and_index})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _58_1856 = (let _150_669 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _58_1822 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_649 = (FStar_Syntax_Print.term_to_string e)
in (let _150_648 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _150_649 _150_648)))
end else begin
()
end
in (

let _58_1827 = (tc_term env1 e)
in (match (_58_1827) with
| (e, lc, g) -> begin
(

let _58_1828 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_651 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _150_650 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _150_651 _150_650)))
end else begin
()
end
in (

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let _58_1834 = (let _150_652 = (FStar_TypeChecker_Rel.discharge_guard env (

let _58_1832 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_1832.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_1832.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_1832.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _150_652 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _150_657 = (let _150_656 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _150_656 (FStar_List.map (fun _58_1842 -> (match (_58_1842) with
| (u, _58_1841) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _150_657 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _58_1850 = if (let _150_658 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _150_658)) then begin
(

let unresolved = (let _150_659 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _150_659 FStar_Util.set_elements))
in (let _150_667 = (let _150_666 = (let _150_665 = (let _150_664 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _150_663 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _150_662 = (let _150_661 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _58_1849 -> (match (_58_1849) with
| (u, _58_1848) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _150_661 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _150_664 _150_663 _150_662))))
in ((_150_665), (p.FStar_Syntax_Syntax.p)))
in FStar_Syntax_Syntax.Error (_150_666))
in (Prims.raise _150_667)))
end else begin
()
end
in (

let _58_1852 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_668 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _150_668))
end else begin
()
end
in ((e), (e'))))))))))))
end))))))
in (FStar_All.pipe_right _150_669 FStar_List.unzip))
in (match (_58_1856) with
| (exps, norm_exps) -> begin
(

let p = (FStar_TypeChecker_Util.decorate_pattern env p exps)
in ((p), (pat_bvs), (pat_env), (exps), (norm_exps)))
end))))
end))))
end)))
in (

let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (

let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (

let _58_1863 = (let _150_670 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _150_670 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_58_1863) with
| (scrutinee_env, _58_1862) -> begin
(

let _58_1869 = (tc_pat true pat_t pattern)
in (match (_58_1869) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let _58_1879 = (match (when_clause) with
| None -> begin
((None), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (e) -> begin
if (FStar_TypeChecker_Env.should_verify env) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("When clauses are not yet supported in --verify mode; they will be some day"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
(

let _58_1876 = (let _150_671 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _150_671 e))
in (match (_58_1876) with
| (e, c, g) -> begin
((Some (e)), (g))
end))
end
end)
in (match (_58_1879) with
| (when_clause, g_when) -> begin
(

let _58_1883 = (tc_term pat_env branch_exp)
in (match (_58_1883) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _150_673 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _150_672 -> Some (_150_672)) _150_673))
end)
in (

let _58_1941 = (

let eqs = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
None
end else begin
(FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _58_1901 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _150_677 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _150_676 -> Some (_150_676)) _150_677))
end))
end))) None))
end
in (

let _58_1909 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_58_1909) with
| (c, g_branch) -> begin
(

let _58_1936 = (match (((eqs), (when_condition))) with
| _58_1911 when (not ((FStar_TypeChecker_Env.should_verify env))) -> begin
((c), (g_when))
end
| (None, None) -> begin
((c), (g_when))
end
| (Some (f), None) -> begin
(

let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _150_680 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _150_679 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((_150_680), (_150_679))))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (let _150_681 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_150_681))
in (let _150_684 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _150_683 = (let _150_682 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _150_682 g_when))
in ((_150_684), (_150_683))))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _150_685 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in ((_150_685), (g_when)))))
end)
in (match (_58_1936) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _150_687 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _150_686 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in ((_150_687), (_150_686), (g_branch)))))
end))
end)))
in (match (_58_1941) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
FStar_Syntax_Util.t_true
end else begin
(

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> if ((let _150_697 = (let _150_696 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _150_696))
in (FStar_List.length _150_697)) > 1) then begin
(

let disc = (let _150_698 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _150_698 FStar_Syntax_Syntax.Delta_equational None))
in (

let disc = (let _150_700 = (let _150_699 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_150_699)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _150_700 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _150_701 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_150_701)::[])))
end else begin
[]
end)
in (

let fail = (fun _58_1951 -> (match (()) with
| () -> begin
(let _150_707 = (let _150_706 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _150_705 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _150_704 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _150_706 _150_705 _150_704))))
in (FStar_All.failwith _150_707))
end))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _58_1958) -> begin
(head_constructor t)
end
| _58_1962 -> begin
(fail ())
end))
in (

let pat_exp = (let _150_710 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _150_710 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_58_1987) -> begin
(let _150_715 = (let _150_714 = (let _150_713 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _150_712 = (let _150_711 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_150_711)::[])
in (_150_713)::_150_712))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _150_714 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_150_715)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _150_716 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _150_716))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(

let sub_term_guards = (let _150_723 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _58_2005 -> (match (_58_2005) with
| (ei, _58_2004) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _58_2009 -> begin
(

let sub_term = (let _150_722 = (let _150_719 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _150_719 FStar_Syntax_Syntax.Delta_equational None))
in (let _150_721 = (let _150_720 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_150_720)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _150_722 _150_721 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _150_723 FStar_List.flatten))
in (let _150_724 = (discriminate scrutinee_tm f)
in (FStar_List.append _150_724 sub_term_guards)))
end)
end
| _58_2013 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(

let t = (let _150_729 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _150_729))
in (

let _58_2021 = (FStar_Syntax_Util.type_u ())
in (match (_58_2021) with
| (k, _58_2020) -> begin
(

let _58_2027 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_58_2027) with
| (t, _58_2024, _58_2026) -> begin
t
end))
end)))
end)
in (

let branch_guard = (let _150_730 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _150_730 FStar_Syntax_Util.mk_disj_l))
in (

let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
end
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (

let _58_2035 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_731 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _150_731))
end else begin
()
end
in (let _150_732 = (FStar_Syntax_Subst.close_branch ((pattern), (when_clause), (branch_exp)))
in ((_150_732), (branch_guard), (c), (guard))))))
end)))
end))
end))
end))
end)))))
end))
end)))
and check_top_level_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let _58_2052 = (check_let_bound_def true env lb)
in (match (_58_2052) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let _58_2064 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
((g1), (e1), (univ_vars), (c1))
end else begin
(

let g1 = (let _150_735 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _150_735 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _58_2059 = (let _150_739 = (let _150_738 = (let _150_737 = (let _150_736 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (_150_736)))
in (_150_737)::[])
in (FStar_TypeChecker_Util.generalize env _150_738))
in (FStar_List.hd _150_739))
in (match (_58_2059) with
| (_58_2055, univs, e1, c1) -> begin
((g1), (e1), (univs), ((FStar_Syntax_Util.lcomp_of_comp c1)))
end)))
end
in (match (_58_2064) with
| (g1, e1, univ_vars, c1) -> begin
(

let _58_2074 = if (FStar_TypeChecker_Env.should_verify env) then begin
(

let _58_2067 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_58_2067) with
| (ok, c1) -> begin
if ok then begin
((e2), (c1))
end else begin
(

let _58_2068 = if (FStar_Options.warn_top_level_effects ()) then begin
(let _150_740 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _150_740 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _150_741 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) None e2.FStar_Syntax_Syntax.pos)
in ((_150_741), (c1))))
end
end))
end else begin
(

let _58_2070 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _150_742 = (c1.FStar_Syntax_Syntax.comp ())
in ((e2), (_150_742))))
end
in (match (_58_2074) with
| (e2, c1) -> begin
(

let cres = (let _150_743 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_743))
in (

let _58_2076 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _150_744 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((_150_744), (cres), (FStar_TypeChecker_Rel.trivial_guard))))))
end))
end))
end))
end
| _58_2080 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let _58_2091 = env
in {FStar_TypeChecker_Env.solver = _58_2091.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2091.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2091.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2091.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2091.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2091.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2091.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2091.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2091.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2091.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2091.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2091.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2091.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_2091.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2091.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2091.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2091.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2091.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2091.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2091.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2091.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2091.FStar_TypeChecker_Env.qname_and_index})
in (

let _58_2100 = (let _150_748 = (let _150_747 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _150_747 Prims.fst))
in (check_let_bound_def false _150_748 lb))
in (match (_58_2100) with
| (e1, _58_2096, c1, g1, annotated) -> begin
(

let x = (

let _58_2101 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_2101.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2101.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let _58_2107 = (let _150_750 = (let _150_749 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_749)::[])
in (FStar_Syntax_Subst.open_term _150_750 e2))
in (match (_58_2107) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _58_2113 = (let _150_751 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _150_751 e2))
in (match (_58_2113) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (x)), (c2)))
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e2 = (FStar_TypeChecker_Util.maybe_lift env e2 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e = (let _150_754 = (let _150_753 = (let _150_752 = (FStar_Syntax_Subst.close xb e2)
in ((((false), ((lb)::[]))), (_150_752)))
in FStar_Syntax_Syntax.Tm_let (_150_753))
in (FStar_Syntax_Syntax.mk _150_754 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (let _150_757 = (let _150_756 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _150_756 e1))
in (FStar_All.pipe_left (fun _150_755 -> FStar_TypeChecker_Common.NonTrivial (_150_755)) _150_757))
in (

let g2 = (let _150_759 = (let _150_758 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _150_758 g2))
in (FStar_TypeChecker_Rel.close_guard xb _150_759))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if (let _150_760 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome _150_760)) then begin
((e), (cres), (guard))
end else begin
(

let _58_2122 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in ((e), (cres), (guard)))
end))))))))
end))))
end))))
end)))
end
| _58_2125 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _58_2137 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_58_2137) with
| (lbs, e2) -> begin
(

let _58_2140 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2140) with
| (env0, topt) -> begin
(

let _58_2143 = (build_let_rec_env true env0 lbs)
in (match (_58_2143) with
| (lbs, rec_env) -> begin
(

let _58_2146 = (check_let_recs rec_env lbs)
in (match (_58_2146) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (let _150_763 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _150_763 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _150_766 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _150_766 (fun _150_765 -> Some (_150_765))))
in (

let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(

let ecs = (let _150_770 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _150_769 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (_150_769))))))
in (FStar_TypeChecker_Util.generalize env _150_770))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _58_2157 -> (match (_58_2157) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _150_772 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_772))
in (

let _58_2160 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _58_2164 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_2164) with
| (lbs, e2) -> begin
(let _150_774 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _150_773 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in ((_150_774), (cres), (_150_773))))
end)))))))
end))
end))
end))
end))
end
| _58_2166 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _58_2178 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_58_2178) with
| (lbs, e2) -> begin
(

let _58_2181 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2181) with
| (env0, topt) -> begin
(

let _58_2184 = (build_let_rec_env false env0 lbs)
in (match (_58_2184) with
| (lbs, rec_env) -> begin
(

let _58_2187 = (check_let_recs rec_env lbs)
in (match (_58_2187) with
| (lbs, g_lbs) -> begin
(

let _58_2199 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let _58_2190 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_2190.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2190.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let _58_2193 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _58_2193.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _58_2193.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _58_2193.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _58_2193.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (lb.FStar_Syntax_Syntax.lbtyp)))
in ((env), (lb)))))) env))
in (match (_58_2199) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let _58_2205 = (tc_term env e2)
in (match (_58_2205) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _58_2209 = cres
in {FStar_Syntax_Syntax.eff_name = _58_2209.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _58_2209.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_2209.FStar_Syntax_Syntax.comp})
in (

let _58_2214 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_2214) with
| (lbs, e2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_58_2217) -> begin
((e), (cres), (guard))
end
| None -> begin
(

let _58_2220 = (check_no_escape None env bvs tres)
in ((e), (cres), (guard)))
end))
end))))))
end)))
end))
end))
end))
end))
end))
end
| _58_2223 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let _58_2256 = (FStar_List.fold_left (fun _58_2230 lb -> (match (_58_2230) with
| (lbs, env) -> begin
(

let _58_2235 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_58_2235) with
| (univ_vars, t, check_t) -> begin
(

let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (

let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (

let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(

let _58_2244 = (let _150_786 = (let _150_785 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _150_785))
in (tc_check_tot_or_gtot_term (

let _58_2238 = env0
in {FStar_TypeChecker_Env.solver = _58_2238.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2238.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2238.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2238.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2238.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2238.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2238.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2238.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2238.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2238.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2238.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2238.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2238.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2238.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _58_2238.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2238.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2238.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2238.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2238.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2238.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2238.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2238.FStar_TypeChecker_Env.qname_and_index}) t _150_786))
in (match (_58_2244) with
| (t, _58_2242, g) -> begin
(

let _58_2245 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (

let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_TypeChecker_Env.should_verify env)) then begin
(

let _58_2248 = env
in {FStar_TypeChecker_Env.solver = _58_2248.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2248.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2248.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2248.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2248.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2248.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2248.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2248.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2248.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2248.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2248.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2248.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t)))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2248.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_2248.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2248.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2248.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2248.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2248.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2248.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2248.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2248.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2248.FStar_TypeChecker_Env.qname_and_index})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (t)))
end
in (

let lb = (

let _58_2251 = lb
in {FStar_Syntax_Syntax.lbname = _58_2251.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _58_2251.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb)::lbs), (env)))))))
end))
end)) (([]), (env)) lbs)
in (match (_58_2256) with
| (lbs, env) -> begin
(((FStar_List.rev lbs)), (env))
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _58_2269 = (let _150_791 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _58_2263 = (let _150_790 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _150_790 lb.FStar_Syntax_Syntax.lbdef))
in (match (_58_2263) with
| (e, c, g) -> begin
(

let _58_2264 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in ((lb), (g))))
end)))))
in (FStar_All.pipe_right _150_791 FStar_List.unzip))
in (match (_58_2269) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _58_2277 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2277) with
| (env1, _58_2276) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _58_2283 = (check_lbtyp top_level env lb)
in (match (_58_2283) with
| (topt, wf_annot, univ_vars, env1) -> begin
(

let _58_2284 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _58_2291 = (tc_maybe_toplevel_term (

let _58_2286 = env1
in {FStar_TypeChecker_Env.solver = _58_2286.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2286.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2286.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2286.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2286.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2286.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2286.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2286.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2286.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2286.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2286.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2286.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2286.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _58_2286.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2286.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2286.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2286.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2286.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2286.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2286.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2286.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2286.FStar_TypeChecker_Env.qname_and_index}) e1)
in (match (_58_2291) with
| (e1, c1, g1) -> begin
(

let _58_2295 = (let _150_798 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_2292 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _150_798 e1 c1 wf_annot))
in (match (_58_2295) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _58_2297 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_799 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _150_799))
end else begin
()
end
in (let _150_800 = (FStar_Option.isSome topt)
in ((e1), (univ_vars), (c1), (g1), (_150_800)))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _58_2304 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in ((None), (FStar_TypeChecker_Rel.trivial_guard), ([]), (env)))
end
| _58_2307 -> begin
(

let _58_2310 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_58_2310) with
| (univ_vars, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _150_804 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars), (_150_804)))
end else begin
(

let _58_2315 = (FStar_Syntax_Util.type_u ())
in (match (_58_2315) with
| (k, _58_2314) -> begin
(

let _58_2320 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_58_2320) with
| (t, _58_2318, g) -> begin
(

let _58_2321 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_807 = (let _150_805 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _150_805))
in (let _150_806 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _150_807 _150_806)))
end else begin
()
end
in (

let t = (norm env1 t)
in (let _150_808 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (g), (univ_vars), (_150_808)))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _58_2327 -> (match (_58_2327) with
| (x, imp) -> begin
(

let _58_2330 = (FStar_Syntax_Util.type_u ())
in (match (_58_2330) with
| (tu, u) -> begin
(

let _58_2335 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_58_2335) with
| (t, _58_2333, g) -> begin
(

let x = (((

let _58_2336 = x
in {FStar_Syntax_Syntax.ppname = _58_2336.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2336.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in (

let _58_2339 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_812 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _150_811 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _150_812 _150_811)))
end else begin
()
end
in (let _150_813 = (push_binding env x)
in ((x), (_150_813), (g), (u)))))
end))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe Prims.list) = (fun env bs -> (

let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
(([]), (env), (FStar_TypeChecker_Rel.trivial_guard), ([]))
end
| (b)::bs -> begin
(

let _58_2354 = (tc_binder env b)
in (match (_58_2354) with
| (b, env', g, u) -> begin
(

let _58_2359 = (aux env' bs)
in (match (_58_2359) with
| (bs, env', g', us) -> begin
(let _150_821 = (let _150_820 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _150_820))
in (((b)::bs), (env'), (_150_821), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun _58_2367 _58_2370 -> (match (((_58_2367), (_58_2370))) with
| ((t, imp), (args, g)) -> begin
(

let _58_2375 = (tc_term env t)
in (match (_58_2375) with
| (t, _58_2373, g') -> begin
(let _150_830 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t), (imp)))::args), (_150_830)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p _58_2379 -> (match (_58_2379) with
| (pats, g) -> begin
(

let _58_2382 = (tc_args env p)
in (match (_58_2382) with
| (args, g') -> begin
(let _150_833 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats), (_150_833)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _58_2388 = (tc_maybe_toplevel_term env e)
in (match (_58_2388) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
((e), (c), (g))
end else begin
(

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let c = (norm_c env c)
in (

let _58_2394 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _150_836 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in ((_150_836), (false)))
end else begin
(let _150_837 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in ((_150_837), (true)))
end
in (match (_58_2394) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _150_838 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (_150_838)))
end
| _58_2398 -> begin
if allow_ghost then begin
(let _150_841 = (let _150_840 = (let _150_839 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in ((_150_839), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_840))
in (Prims.raise _150_841))
end else begin
(let _150_844 = (let _150_843 = (let _150_842 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in ((_150_842), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_843))
in (Prims.raise _150_844))
end
end)
end)))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let _58_2408 = (tc_tot_or_gtot_term env t)
in (match (_58_2408) with
| (t, c, g) -> begin
(

let _58_2409 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in ((t), (c)))
end)))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let _58_2417 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_2417) with
| (t, c, g) -> begin
(

let _58_2418 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _150_862 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _150_862)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _150_866 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (([]), (_150_866)))))


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let _58_2433 = (tc_binders env tps)
in (match (_58_2433) with
| (tps, env, g, us) -> begin
(

let _58_2434 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in ((tps), (env), (us)))
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (

let fail = (fun _58_2440 -> (match (()) with
| () -> begin
(let _150_881 = (let _150_880 = (let _150_879 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in ((_150_879), ((FStar_Ident.range_of_lid m))))
in FStar_Syntax_Syntax.Error (_150_880))
in (Prims.raise _150_881))
end))
in (

let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _58_2453))::((wp, _58_2449))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _58_2457 -> begin
(fail ())
end))
end
| _58_2459 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let _58_2466 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_58_2466) with
| (uvs, c) -> begin
((uvs), ([]), (c))
end))
end
| _58_2468 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let _58_2472 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_58_2472) with
| (uvs, t') -> begin
(match ((let _150_888 = (FStar_Syntax_Subst.compress t')
in _150_888.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
((uvs), (binders), (c))
end
| _58_2478 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))


let rec tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (

let _58_2481 = ()
in (

let _58_2486 = (FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_58_2486) with
| (effect_params_un, signature_un, opening) -> begin
(

let _58_2491 = (tc_tparams env0 effect_params_un)
in (match (_58_2491) with
| (effect_params, env, _58_2490) -> begin
(

let _58_2495 = (tc_trivial_guard env signature_un)
in (match (_58_2495) with
| (signature, _58_2494) -> begin
(

let ed = (

let _58_2496 = ed
in {FStar_Syntax_Syntax.qualifiers = _58_2496.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2496.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _58_2496.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _58_2496.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _58_2496.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _58_2496.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _58_2496.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _58_2496.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _58_2496.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _58_2496.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _58_2496.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _58_2496.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _58_2496.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _58_2496.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _58_2496.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _58_2496.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _58_2496.FStar_Syntax_Syntax.actions})
in (

let ed = (match (effect_params) with
| [] -> begin
ed
end
| _58_2501 -> begin
(

let op = (fun ts -> (

let _58_2504 = ()
in (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in (([]), (t1)))))
in (

let _58_2507 = ed
in (let _150_931 = (op ed.FStar_Syntax_Syntax.ret_wp)
in (let _150_930 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _150_929 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _150_928 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _150_927 = (op ed.FStar_Syntax_Syntax.stronger)
in (let _150_926 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _150_925 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _150_924 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _150_923 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _150_922 = (op ed.FStar_Syntax_Syntax.trivial)
in (let _150_921 = (let _150_912 = (op (([]), (ed.FStar_Syntax_Syntax.repr)))
in (Prims.snd _150_912))
in (let _150_920 = (op ed.FStar_Syntax_Syntax.return_repr)
in (let _150_919 = (op ed.FStar_Syntax_Syntax.bind_repr)
in (let _150_918 = (FStar_List.map (fun a -> (

let _58_2510 = a
in (let _150_917 = (let _150_914 = (op (([]), (a.FStar_Syntax_Syntax.action_defn)))
in (Prims.snd _150_914))
in (let _150_916 = (let _150_915 = (op (([]), (a.FStar_Syntax_Syntax.action_typ)))
in (Prims.snd _150_915))
in {FStar_Syntax_Syntax.action_name = _58_2510.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = _58_2510.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _150_917; FStar_Syntax_Syntax.action_typ = _150_916})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = _58_2507.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2507.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _58_2507.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _58_2507.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _58_2507.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _150_931; FStar_Syntax_Syntax.bind_wp = _150_930; FStar_Syntax_Syntax.if_then_else = _150_929; FStar_Syntax_Syntax.ite_wp = _150_928; FStar_Syntax_Syntax.stronger = _150_927; FStar_Syntax_Syntax.close_wp = _150_926; FStar_Syntax_Syntax.assert_p = _150_925; FStar_Syntax_Syntax.assume_p = _150_924; FStar_Syntax_Syntax.null_wp = _150_923; FStar_Syntax_Syntax.trivial = _150_922; FStar_Syntax_Syntax.repr = _150_921; FStar_Syntax_Syntax.return_repr = _150_920; FStar_Syntax_Syntax.bind_repr = _150_919; FStar_Syntax_Syntax.actions = _150_918}))))))))))))))))
end)
in (

let wp_with_fresh_result_type = (fun env mname signature -> (

let fail = (fun t -> (let _150_942 = (let _150_941 = (let _150_940 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in ((_150_940), ((FStar_Ident.range_of_lid mname))))
in FStar_Syntax_Syntax.Error (_150_941))
in (Prims.raise _150_942)))
in (match ((let _150_943 = (FStar_Syntax_Subst.compress signature)
in _150_943.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _58_2530))::((wp, _58_2526))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _58_2534 -> begin
(fail signature)
end))
end
| _58_2536 -> begin
(fail signature)
end)))
in (

let _58_2539 = (wp_with_fresh_result_type env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_58_2539) with
| (a, wp_a) -> begin
(

let fresh_effect_signature = (fun _58_2541 -> (match (()) with
| () -> begin
(

let _58_2545 = (tc_trivial_guard env signature_un)
in (match (_58_2545) with
| (signature, _58_2544) -> begin
(wp_with_fresh_result_type env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (

let env = (let _150_946 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _150_946))
in (

let _58_2547 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _150_952 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _150_951 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _150_950 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _150_949 = (let _150_947 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Print.term_to_string _150_947))
in (let _150_948 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort)
in (FStar_Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n" _150_952 _150_951 _150_950 _150_949 _150_948))))))
end else begin
()
end
in (

let check_and_gen' = (fun env _58_2554 k -> (match (_58_2554) with
| (_58_2552, t) -> begin
(check_and_gen env t k)
end))
in (

let return_wp = (

let expected_k = (let _150_964 = (let _150_962 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_961 = (let _150_960 = (let _150_959 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _150_959))
in (_150_960)::[])
in (_150_962)::_150_961))
in (let _150_963 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _150_964 _150_963)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let _58_2560 = (fresh_effect_signature ())
in (match (_58_2560) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _150_968 = (let _150_966 = (let _150_965 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _150_965))
in (_150_966)::[])
in (let _150_967 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _150_968 _150_967)))
in (

let expected_k = (let _150_979 = (let _150_977 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _150_976 = (let _150_975 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_974 = (let _150_973 = (FStar_Syntax_Syntax.mk_binder b)
in (let _150_972 = (let _150_971 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _150_970 = (let _150_969 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (_150_969)::[])
in (_150_971)::_150_970))
in (_150_973)::_150_972))
in (_150_975)::_150_974))
in (_150_977)::_150_976))
in (let _150_978 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _150_979 _150_978)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (let _150_981 = (let _150_980 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_980 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _150_981))
in (

let expected_k = (let _150_990 = (let _150_988 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_987 = (let _150_986 = (FStar_Syntax_Syntax.mk_binder p)
in (let _150_985 = (let _150_984 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _150_983 = (let _150_982 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_982)::[])
in (_150_984)::_150_983))
in (_150_986)::_150_985))
in (_150_988)::_150_987))
in (let _150_989 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_990 _150_989)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (let _150_995 = (let _150_993 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_992 = (let _150_991 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_991)::[])
in (_150_993)::_150_992))
in (let _150_994 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_995 _150_994)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let _58_2572 = (FStar_Syntax_Util.type_u ())
in (match (_58_2572) with
| (t, _58_2571) -> begin
(

let expected_k = (let _150_1002 = (let _150_1000 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_999 = (let _150_998 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _150_997 = (let _150_996 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_996)::[])
in (_150_998)::_150_997))
in (_150_1000)::_150_999))
in (let _150_1001 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _150_1002 _150_1001)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (let _150_1004 = (let _150_1003 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_1003 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _150_1004))
in (

let b_wp_a = (let _150_1008 = (let _150_1006 = (let _150_1005 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _150_1005))
in (_150_1006)::[])
in (let _150_1007 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_1008 _150_1007)))
in (

let expected_k = (let _150_1015 = (let _150_1013 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1012 = (let _150_1011 = (FStar_Syntax_Syntax.mk_binder b)
in (let _150_1010 = (let _150_1009 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_150_1009)::[])
in (_150_1011)::_150_1010))
in (_150_1013)::_150_1012))
in (let _150_1014 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_1015 _150_1014)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (let _150_1024 = (let _150_1022 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1021 = (let _150_1020 = (let _150_1017 = (let _150_1016 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_1016 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _150_1017))
in (let _150_1019 = (let _150_1018 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_1018)::[])
in (_150_1020)::_150_1019))
in (_150_1022)::_150_1021))
in (let _150_1023 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_1024 _150_1023)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _150_1033 = (let _150_1031 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1030 = (let _150_1029 = (let _150_1026 = (let _150_1025 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_1025 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _150_1026))
in (let _150_1028 = (let _150_1027 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_1027)::[])
in (_150_1029)::_150_1028))
in (_150_1031)::_150_1030))
in (let _150_1032 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_1033 _150_1032)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _150_1036 = (let _150_1034 = (FStar_Syntax_Syntax.mk_binder a)
in (_150_1034)::[])
in (let _150_1035 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_1036 _150_1035)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let _58_2588 = (FStar_Syntax_Util.type_u ())
in (match (_58_2588) with
| (t, _58_2587) -> begin
(

let expected_k = (let _150_1041 = (let _150_1039 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1038 = (let _150_1037 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_1037)::[])
in (_150_1039)::_150_1038))
in (let _150_1040 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _150_1041 _150_1040)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let _58_2729 = if ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) || (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable))) then begin
(

let repr = (

let _58_2594 = (FStar_Syntax_Util.type_u ())
in (match (_58_2594) with
| (t, _58_2593) -> begin
(

let expected_k = (let _150_1046 = (let _150_1044 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1043 = (let _150_1042 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_1042)::[])
in (_150_1044)::_150_1043))
in (let _150_1045 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _150_1046 _150_1045)))
in (tc_check_trivial_guard env ed.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (

let repr = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env repr)
in (let _150_1056 = (let _150_1055 = (let _150_1054 = (let _150_1053 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_1052 = (let _150_1051 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_1051)::[])
in (_150_1053)::_150_1052))
in ((repr), (_150_1054)))
in FStar_Syntax_Syntax.Tm_app (_150_1055))
in (FStar_Syntax_Syntax.mk _150_1056 None FStar_Range.dummyRange))))
in (

let mk_repr = (fun a wp -> (let _150_1061 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_repr' _150_1061 wp)))
in (

let destruct_repr = (fun t -> (match ((let _150_1064 = (FStar_Syntax_Subst.compress t)
in _150_1064.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_58_2607, ((t, _58_2614))::((wp, _58_2610))::[]) -> begin
((t), (wp))
end
| _58_2620 -> begin
(FStar_All.failwith "Unexpected repr type")
end))
in (

let bind_repr = (

let r = (let _150_1065 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_0 FStar_Syntax_Syntax.Delta_constant None)
in (FStar_All.pipe_right _150_1065 FStar_Syntax_Syntax.fv_to_tm))
in (

let _58_2624 = (fresh_effect_signature ())
in (match (_58_2624) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _150_1069 = (let _150_1067 = (let _150_1066 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _150_1066))
in (_150_1067)::[])
in (let _150_1068 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _150_1069 _150_1068)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" None a_wp_b)
in (

let x_a = (let _150_1070 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _150_1070))
in (

let wp_g_x = (let _150_1074 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (let _150_1073 = (let _150_1072 = (let _150_1071 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_1071))
in (_150_1072)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _150_1074 _150_1073 None FStar_Range.dummyRange)))
in (

let res = (

let wp = (let _150_1086 = (let _150_1075 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right _150_1075 Prims.snd))
in (let _150_1085 = (let _150_1084 = (let _150_1083 = (let _150_1082 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_1081 = (let _150_1080 = (FStar_Syntax_Syntax.bv_to_name b)
in (let _150_1079 = (let _150_1078 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (let _150_1077 = (let _150_1076 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (_150_1076)::[])
in (_150_1078)::_150_1077))
in (_150_1080)::_150_1079))
in (_150_1082)::_150_1081))
in (r)::_150_1083)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _150_1084))
in (FStar_Syntax_Syntax.mk_Tm_app _150_1086 _150_1085 None FStar_Range.dummyRange)))
in (mk_repr b wp))
in (

let expected_k = (let _150_1106 = (let _150_1104 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1103 = (let _150_1102 = (FStar_Syntax_Syntax.mk_binder b)
in (let _150_1101 = (let _150_1100 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (let _150_1099 = (let _150_1098 = (let _150_1088 = (let _150_1087 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a _150_1087))
in (FStar_Syntax_Syntax.null_binder _150_1088))
in (let _150_1097 = (let _150_1096 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (let _150_1095 = (let _150_1094 = (let _150_1093 = (let _150_1092 = (let _150_1089 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_150_1089)::[])
in (let _150_1091 = (let _150_1090 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _150_1090))
in (FStar_Syntax_Util.arrow _150_1092 _150_1091)))
in (FStar_Syntax_Syntax.null_binder _150_1093))
in (_150_1094)::[])
in (_150_1096)::_150_1095))
in (_150_1098)::_150_1097))
in (_150_1100)::_150_1099))
in (_150_1102)::_150_1101))
in (_150_1104)::_150_1103))
in (let _150_1105 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _150_1106 _150_1105)))
in (

let _58_2638 = (tc_tot_or_gtot_term env expected_k)
in (match (_58_2638) with
| (expected_k, _58_2635, _58_2637) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (

let env = (

let _58_2640 = env
in {FStar_TypeChecker_Env.solver = _58_2640.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2640.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2640.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2640.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2640.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2640.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2640.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2640.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2640.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2640.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2640.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2640.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2640.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2640.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_2640.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2640.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2640.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2640.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _58_2640.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2640.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2640.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2640.FStar_TypeChecker_Env.qname_and_index})
in (

let br = (check_and_gen' env ed.FStar_Syntax_Syntax.bind_repr expected_k)
in br)))
end)))))))))
end)))
in (

let return_repr = (

let x_a = (let _150_1107 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _150_1107))
in (

let res = (

let wp = (let _150_1114 = (let _150_1108 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right _150_1108 Prims.snd))
in (let _150_1113 = (let _150_1112 = (let _150_1111 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_1110 = (let _150_1109 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (_150_1109)::[])
in (_150_1111)::_150_1110))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _150_1112))
in (FStar_Syntax_Syntax.mk_Tm_app _150_1114 _150_1113 None FStar_Range.dummyRange)))
in (mk_repr a wp))
in (

let expected_k = (let _150_1119 = (let _150_1117 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1116 = (let _150_1115 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_150_1115)::[])
in (_150_1117)::_150_1116))
in (let _150_1118 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _150_1119 _150_1118)))
in (

let _58_2654 = (tc_tot_or_gtot_term env expected_k)
in (match (_58_2654) with
| (expected_k, _58_2651, _58_2653) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let _58_2658 = (check_and_gen' env ed.FStar_Syntax_Syntax.return_repr expected_k)
in (match (_58_2658) with
| (univs, repr) -> begin
(match (univs) with
| [] -> begin
(([]), (repr))
end
| _58_2661 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected universe-polymorphic return for effect"), (repr.FStar_Syntax_Syntax.pos)))))
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let _58_2669 = (tc_tot_or_gtot_term env act.FStar_Syntax_Syntax.action_typ)
in (match (_58_2669) with
| (act_typ, _58_2667, g_t) -> begin
(

let env' = (FStar_TypeChecker_Env.set_expected_typ env act_typ)
in (

let _58_2671 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _150_1123 = (FStar_Syntax_Print.term_to_string act.FStar_Syntax_Syntax.action_defn)
in (let _150_1122 = (FStar_Syntax_Print.term_to_string act_typ)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" (FStar_Ident.text_of_lid act.FStar_Syntax_Syntax.action_name) _150_1123 _150_1122)))
end else begin
()
end
in (

let _58_2677 = (tc_tot_or_gtot_term env' act.FStar_Syntax_Syntax.action_defn)
in (match (_58_2677) with
| (act_defn, _58_2675, g_a) -> begin
(

let act_defn = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env act_defn)
in (

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let _58_2700 = (

let act_typ = (FStar_Syntax_Subst.compress act_typ)
in (match (act_typ.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _58_2688 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_2688) with
| (bs, _58_2687) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (let _150_1124 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs _150_1124))
in (

let _58_2695 = (tc_tot_or_gtot_term env k)
in (match (_58_2695) with
| (k, _58_2693, g) -> begin
((k), (g))
end))))
end))
end
| _58_2697 -> begin
(let _150_1129 = (let _150_1128 = (let _150_1127 = (let _150_1126 = (FStar_Syntax_Print.term_to_string act_typ)
in (let _150_1125 = (FStar_Syntax_Print.tag_of_term act_typ)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" _150_1126 _150_1125)))
in ((_150_1127), (act_defn.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_1128))
in (Prims.raise _150_1129))
end))
in (match (_58_2700) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env act_typ expected_k)
in (

let _58_2702 = (let _150_1132 = (let _150_1131 = (let _150_1130 = (FStar_TypeChecker_Rel.conj_guard g_t g)
in (FStar_TypeChecker_Rel.conj_guard g_k _150_1130))
in (FStar_TypeChecker_Rel.conj_guard g_a _150_1131))
in (FStar_TypeChecker_Rel.force_trivial_guard env _150_1132))
in (

let act_typ = (match ((let _150_1133 = (FStar_Syntax_Subst.compress expected_k)
in _150_1133.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _58_2710 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_2710) with
| (bs, c) -> begin
(

let _58_2713 = (destruct_repr (FStar_Syntax_Util.comp_result c))
in (match (_58_2713) with
| (a, wp) -> begin
(

let c = (let _150_1135 = (let _150_1134 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_1134)::[])
in {FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a; FStar_Syntax_Syntax.effect_args = _150_1135; FStar_Syntax_Syntax.flags = []})
in (let _150_1136 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Util.arrow bs _150_1136)))
end))
end))
end
| _58_2716 -> begin
(FStar_All.failwith "")
end)
in (

let _58_2720 = (FStar_TypeChecker_Util.generalize_universes env act_defn)
in (match (_58_2720) with
| (univs, act_defn) -> begin
(

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let _58_2722 = act
in {FStar_Syntax_Syntax.action_name = _58_2722.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = act_defn; FStar_Syntax_Syntax.action_typ = act_typ}))
end)))))
end))))
end))))
end)))
in (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.map check_action)))
in ((repr), (bind_repr), (return_repr), (actions)))))))))
end else begin
((ed.FStar_Syntax_Syntax.repr), (ed.FStar_Syntax_Syntax.bind_repr), (ed.FStar_Syntax_Syntax.return_repr), (ed.FStar_Syntax_Syntax.actions))
end
in (match (_58_2729) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t = (let _150_1137 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _150_1137))
in (

let _58_2733 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_58_2733) with
| (univs, t) -> begin
(

let signature = (match ((let _150_1139 = (let _150_1138 = (FStar_Syntax_Subst.compress t)
in _150_1138.FStar_Syntax_Syntax.n)
in ((effect_params), (_150_1139)))) with
| ([], _58_2736) -> begin
t
end
| (_58_2739, FStar_Syntax_Syntax.Tm_arrow (_58_2741, c)) -> begin
(FStar_Syntax_Util.comp_result c)
end
| _58_2747 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let close = (fun n ts -> (

let ts = (let _150_1144 = (FStar_Syntax_Subst.close_tscheme effect_params ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _150_1144))
in (

let _58_2753 = if (((n > 0) && (not ((FStar_Syntax_Util.is_unknown (Prims.snd ts))))) && ((FStar_List.length (Prims.fst ts)) <> n)) then begin
(let _150_1147 = (let _150_1146 = (FStar_Util.string_of_int n)
in (let _150_1145 = (FStar_Syntax_Print.tscheme_to_string ts)
in (FStar_Util.format2 "The effect combinator is not universe-polymorphic enough (n=%s) (%s)" _150_1146 _150_1145)))
in (FStar_All.failwith _150_1147))
end else begin
()
end
in ts)))
in (

let close_action = (fun act -> (

let _58_2759 = (close (- (1)) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (_58_2759) with
| (univs, defn) -> begin
(

let _58_2762 = (close (- (1)) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (_58_2762) with
| (univs', typ) -> begin
(

let _58_2763 = ()
in (

let _58_2765 = act
in {FStar_Syntax_Syntax.action_name = _58_2765.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ}))
end))
end)))
in (

let _58_2767 = ()
in (

let ed = (

let _58_2769 = ed
in (let _150_1164 = (close 0 return_wp)
in (let _150_1163 = (close 1 bind_wp)
in (let _150_1162 = (close 0 if_then_else)
in (let _150_1161 = (close 0 ite_wp)
in (let _150_1160 = (close 0 stronger)
in (let _150_1159 = (close 1 close_wp)
in (let _150_1158 = (close 0 assert_p)
in (let _150_1157 = (close 0 assume_p)
in (let _150_1156 = (close 0 null_wp)
in (let _150_1155 = (close 0 trivial_wp)
in (let _150_1154 = (let _150_1150 = (close 0 (([]), (repr)))
in (Prims.snd _150_1150))
in (let _150_1153 = (close 0 return_repr)
in (let _150_1152 = (close 1 bind_repr)
in (let _150_1151 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.qualifiers = _58_2769.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2769.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _150_1164; FStar_Syntax_Syntax.bind_wp = _150_1163; FStar_Syntax_Syntax.if_then_else = _150_1162; FStar_Syntax_Syntax.ite_wp = _150_1161; FStar_Syntax_Syntax.stronger = _150_1160; FStar_Syntax_Syntax.close_wp = _150_1159; FStar_Syntax_Syntax.assert_p = _150_1158; FStar_Syntax_Syntax.assume_p = _150_1157; FStar_Syntax_Syntax.null_wp = _150_1156; FStar_Syntax_Syntax.trivial = _150_1155; FStar_Syntax_Syntax.repr = _150_1154; FStar_Syntax_Syntax.return_repr = _150_1153; FStar_Syntax_Syntax.bind_repr = _150_1152; FStar_Syntax_Syntax.actions = _150_1151})))))))))))))))
in (

let _58_2772 = if ((FStar_TypeChecker_Env.debug env FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ED")))) then begin
(let _150_1165 = (FStar_Syntax_Print.eff_decl_to_string false ed)
in (FStar_Util.print_string _150_1165))
end else begin
()
end
in ed))))))
end)))
end))))))))))))))))
end)))))
end))
end))
end))))
and cps_and_elaborate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl) = (fun env ed -> (

let _58_2778 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_58_2778) with
| (effect_binders_un, signature_un) -> begin
(

let _58_2783 = (tc_tparams env effect_binders_un)
in (match (_58_2783) with
| (effect_binders, env, _58_2782) -> begin
(

let _58_2787 = (tc_trivial_guard env signature_un)
in (match (_58_2787) with
| (signature, _58_2786) -> begin
(

let effect_binders = (FStar_List.map (fun _58_2790 -> (match (_58_2790) with
| (bv, qual) -> begin
(let _150_1170 = (

let _58_2791 = bv
in (let _150_1169 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _58_2791.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2791.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_1169}))
in ((_150_1170), (qual)))
end)) effect_binders)
in (

let _58_2806 = (match ((let _150_1171 = (FStar_Syntax_Subst.compress signature_un)
in _150_1171.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (((a, _58_2796))::[], effect_marker) -> begin
((a), (effect_marker))
end
| _58_2803 -> begin
(FStar_All.failwith "bad shape for effect-for-free signature")
end)
in (match (_58_2806) with
| (a, effect_marker) -> begin
(

let open_and_check = (fun t -> (

let subst = (FStar_Syntax_Subst.opening_of_binders effect_binders)
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (

let _58_2815 = (tc_term env t)
in (match (_58_2815) with
| (t, comp, _58_2814) -> begin
((t), (comp))
end)))))
in (

let recheck_debug = (fun s env t -> (

let _58_2820 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _150_1180 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Term has been %s-transformed to:\n%s\n----------\n" s _150_1180))
end else begin
()
end
in (

let _58_2827 = (tc_term env t)
in (match (_58_2827) with
| (t', _58_2824, _58_2826) -> begin
(

let _58_2828 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _150_1181 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print1 "Re-checked; got:\n%s\n----------\n" _150_1181))
end else begin
()
end
in t)
end))))
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None signature.FStar_Syntax_Syntax.pos))
in (

let _58_2834 = (open_and_check ed.FStar_Syntax_Syntax.repr)
in (match (_58_2834) with
| (repr, _comp) -> begin
(

let _58_2835 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _150_1184 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" _150_1184))
end else begin
()
end
in (

let dmff_env = (FStar_TypeChecker_DMFF.empty env (tc_constant FStar_Range.dummyRange))
in (

let wp_type = (FStar_TypeChecker_DMFF.star_type dmff_env repr)
in (

let wp_type = (recheck_debug "*" env wp_type)
in (

let wp_a = (let _150_1191 = (let _150_1190 = (let _150_1189 = (let _150_1188 = (let _150_1187 = (let _150_1186 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_1185 = (FStar_Syntax_Syntax.as_implicit false)
in ((_150_1186), (_150_1185))))
in (_150_1187)::[])
in ((wp_type), (_150_1188)))
in FStar_Syntax_Syntax.Tm_app (_150_1189))
in (mk _150_1190))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _150_1191))
in (

let effect_signature = (

let binders = (let _150_1196 = (let _150_1192 = (FStar_Syntax_Syntax.as_implicit false)
in ((a), (_150_1192)))
in (let _150_1195 = (let _150_1194 = (let _150_1193 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" None wp_a)
in (FStar_All.pipe_right _150_1193 FStar_Syntax_Syntax.mk_binder))
in (_150_1194)::[])
in (_150_1196)::_150_1195))
in (

let binders = (FStar_Syntax_Subst.close_binders binders)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (effect_marker)))))))
in (

let effect_signature = (recheck_debug "turned into the effect signature" env effect_signature)
in (

let sigelts = (FStar_ST.alloc [])
in (

let mk_lid = (fun name -> (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" name))) FStar_Range.dummyRange))
in (

let elaborate_and_star = (fun dmff_env item -> (

let _58_2853 = item
in (match (_58_2853) with
| (u_item, item) -> begin
(

let _58_2856 = (open_and_check item)
in (match (_58_2856) with
| (item, item_comp) -> begin
(

let _58_2857 = if (not ((FStar_Syntax_Util.is_total_lcomp item_comp))) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Computation for [item] is not total!")))
end else begin
()
end
in (

let _58_2862 = (FStar_TypeChecker_DMFF.star_expr dmff_env item)
in (match (_58_2862) with
| (item_t, item_wp, item_elab) -> begin
(

let item_wp = (recheck_debug "*" env item_wp)
in (

let item_elab = (recheck_debug "_" env item_elab)
in ((dmff_env), (item_t), (item_wp), (item_elab))))
end)))
end))
end)))
in (

let _58_2870 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.bind_repr)
in (match (_58_2870) with
| (dmff_env, _58_2867, bind_wp, bind_elab) -> begin
(

let _58_2876 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.return_repr)
in (match (_58_2876) with
| (dmff_env, _58_2873, return_wp, return_elab) -> begin
(

let return_wp = (match ((let _150_1203 = (FStar_Syntax_Subst.compress return_wp)
in _150_1203.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(let _150_1204 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) _150_1204 (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_GTot_lid)))))
end
| _58_2887 -> begin
(FStar_All.failwith "unexpected shape for return")
end)
in (

let bind_wp = (match ((let _150_1205 = (FStar_Syntax_Subst.compress bind_wp)
in _150_1205.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (let _150_1209 = (let _150_1208 = (let _150_1207 = (let _150_1206 = (mk (FStar_Syntax_Syntax.Tm_fvar (r)))
in (FStar_Syntax_Syntax.null_binder _150_1206))
in (_150_1207)::[])
in (FStar_List.append _150_1208 binders))
in (FStar_Syntax_Util.abs _150_1209 body what)))
end
| _58_2896 -> begin
(FStar_All.failwith "unexpected shape for bind")
end)
in (

let apply_close = (fun t -> if ((FStar_List.length effect_binders) = 0) then begin
t
end else begin
(let _150_1216 = (let _150_1215 = (let _150_1214 = (let _150_1213 = (let _150_1212 = (FStar_Syntax_Util.args_of_binders effect_binders)
in (Prims.snd _150_1212))
in ((t), (_150_1213)))
in FStar_Syntax_Syntax.Tm_app (_150_1214))
in (mk _150_1215))
in (FStar_Syntax_Subst.close effect_binders _150_1216))
end)
in (

let register = (fun name item -> (

let _58_2905 = (let _150_1222 = (mk_lid name)
in (let _150_1221 = (FStar_Syntax_Util.abs effect_binders item None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env _150_1222 _150_1221)))
in (match (_58_2905) with
| (sigelt, fv) -> begin
(

let _58_2906 = (let _150_1224 = (let _150_1223 = (FStar_ST.read sigelts)
in (sigelt)::_150_1223)
in (FStar_ST.op_Colon_Equals sigelts _150_1224))
in fv)
end)))
in (

let return_wp = (register "return_wp" return_wp)
in (

let return_elab = (register "return_elab" return_elab)
in (

let bind_wp = (register "bind_wp" bind_wp)
in (

let _58_2911 = (let _150_1226 = (let _150_1225 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::_150_1225)
in (FStar_ST.op_Colon_Equals sigelts _150_1226))
in (

let bind_elab = (register "bind_elab" bind_elab)
in (

let _58_2914 = (let _150_1228 = (let _150_1227 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::_150_1227)
in (FStar_ST.op_Colon_Equals sigelts _150_1228))
in (

let _58_2933 = (FStar_List.fold_left (fun _58_2918 action -> (match (_58_2918) with
| (dmff_env, actions) -> begin
(

let _58_2924 = (elaborate_and_star dmff_env ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (_58_2924) with
| (dmff_env, action_t, action_wp, action_elab) -> begin
(

let name = action.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText
in (

let action_typ_with_wp = (FStar_TypeChecker_DMFF.trans_F dmff_env action_t action_wp)
in (

let action_elab = (register (Prims.strcat name "_elab") action_elab)
in (

let action_typ_with_wp = (register (Prims.strcat name "_complete_type") action_typ_with_wp)
in (let _150_1234 = (let _150_1233 = (

let _58_2929 = action
in (let _150_1232 = (apply_close action_elab)
in (let _150_1231 = (apply_close action_typ_with_wp)
in {FStar_Syntax_Syntax.action_name = _58_2929.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = _58_2929.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _150_1232; FStar_Syntax_Syntax.action_typ = _150_1231})))
in (_150_1233)::actions)
in ((dmff_env), (_150_1234)))))))
end))
end)) ((dmff_env), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (_58_2933) with
| (dmff_env, actions) -> begin
(

let actions = (FStar_List.rev actions)
in (

let repr = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" None wp_a)
in (

let binders = (let _150_1237 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1236 = (let _150_1235 = (FStar_Syntax_Syntax.mk_binder wp)
in (_150_1235)::[])
in (_150_1237)::_150_1236))
in (let _150_1246 = (let _150_1245 = (let _150_1243 = (let _150_1242 = (let _150_1241 = (let _150_1240 = (let _150_1239 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_1238 = (FStar_Syntax_Syntax.as_implicit false)
in ((_150_1239), (_150_1238))))
in (_150_1240)::[])
in ((repr), (_150_1241)))
in FStar_Syntax_Syntax.Tm_app (_150_1242))
in (mk _150_1243))
in (let _150_1244 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env _150_1245 _150_1244)))
in (FStar_Syntax_Util.abs binders _150_1246 None))))
in (

let repr = (recheck_debug "FC" env repr)
in (

let repr = (register "repr" repr)
in (

let _58_2965 = (match ((let _150_1247 = (FStar_Syntax_Subst.compress wp_type)
in _150_1247.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (effect_param, arrow, _58_2943) -> begin
(

let _58_2948 = (FStar_Syntax_Subst.open_term effect_param arrow)
in (match (_58_2948) with
| (effect_param, arrow) -> begin
(match ((let _150_1248 = (FStar_Syntax_Subst.compress arrow)
in _150_1248.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let _58_2955 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (_58_2955) with
| (wp_binders, c) -> begin
(

let _58_2958 = (FStar_Util.prefix wp_binders)
in (match (_58_2958) with
| (pre_args, post) -> begin
(let _150_1250 = (FStar_Syntax_Util.arrow pre_args c)
in (let _150_1249 = (FStar_Syntax_Util.abs effect_param (Prims.fst post).FStar_Syntax_Syntax.sort None)
in ((_150_1250), (_150_1249))))
end))
end))
end
| _58_2960 -> begin
(let _150_1252 = (let _150_1251 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" _150_1251))
in (FStar_All.failwith _150_1252))
end)
end))
end
| _58_2962 -> begin
(let _150_1254 = (let _150_1253 = (FStar_Syntax_Print.term_to_string wp_type)
in (FStar_Util.format1 "Impossible: pre/post abs %s" _150_1253))
in (FStar_All.failwith _150_1254))
end)
in (match (_58_2965) with
| (pre, post) -> begin
(

let _58_2966 = (let _150_1255 = (register "pre" pre)
in (Prims.ignore _150_1255))
in (

let _58_2968 = (let _150_1256 = (register "post" post)
in (Prims.ignore _150_1256))
in (

let _58_2970 = (let _150_1257 = (register "wp" wp_type)
in (Prims.ignore _150_1257))
in (

let ed = (

let _58_2972 = ed
in (let _150_1268 = (FStar_Syntax_Subst.close_binders effect_binders)
in (let _150_1267 = (FStar_Syntax_Subst.close effect_binders effect_signature)
in (let _150_1266 = (let _150_1258 = (apply_close return_wp)
in (([]), (_150_1258)))
in (let _150_1265 = (let _150_1259 = (apply_close bind_wp)
in (([]), (_150_1259)))
in (let _150_1264 = (apply_close repr)
in (let _150_1263 = (let _150_1260 = (apply_close return_elab)
in (([]), (_150_1260)))
in (let _150_1262 = (let _150_1261 = (apply_close bind_elab)
in (([]), (_150_1261)))
in {FStar_Syntax_Syntax.qualifiers = _58_2972.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2972.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _58_2972.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _150_1268; FStar_Syntax_Syntax.signature = _150_1267; FStar_Syntax_Syntax.ret_wp = _150_1266; FStar_Syntax_Syntax.bind_wp = _150_1265; FStar_Syntax_Syntax.if_then_else = _58_2972.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _58_2972.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _58_2972.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _58_2972.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _58_2972.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _58_2972.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _58_2972.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _58_2972.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _150_1264; FStar_Syntax_Syntax.return_repr = _150_1263; FStar_Syntax_Syntax.bind_repr = _150_1262; FStar_Syntax_Syntax.actions = actions}))))))))
in (

let _58_2977 = (FStar_TypeChecker_DMFF.gen_wps_for_free env effect_binders a wp_a ed)
in (match (_58_2977) with
| (sigelts', ed) -> begin
(

let _58_2978 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _150_1269 = (FStar_Syntax_Print.eff_decl_to_string true ed)
in (FStar_Util.print_string _150_1269))
end else begin
()
end
in (let _150_1272 = (let _150_1271 = (let _150_1270 = (FStar_ST.read sigelts)
in (FStar_List.rev _150_1270))
in (FStar_List.append _150_1271 sigelts'))
in ((_150_1272), (ed))))
end))))))
end))))))
end))))))))))))
end))
end))))))))))))
end)))))
end)))
end))
end))
end)))
and tc_lex_t : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (

let _58_2984 = ()
in (

let _58_2992 = ()
in (match (ses) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _58_3021, _58_3023, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _58_3012, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _58_3001, r2))::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(

let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (

let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (

let tc = FStar_Syntax_Syntax.Sig_inductive_typ (((lex_t), ((u)::[]), ([]), (t), ([]), ((FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[]), ([]), (r)))
in (

let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (

let lex_top_t = (let _150_1280 = (let _150_1279 = (let _150_1278 = (let _150_1277 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _150_1277 FStar_Syntax_Syntax.Delta_constant None))
in ((_150_1278), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_150_1279))
in (FStar_Syntax_Syntax.mk _150_1280 None r1))
in (

let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (

let dc_lextop = FStar_Syntax_Syntax.Sig_datacon (((lex_top), ((utop)::[]), (lex_top_t), (FStar_Syntax_Const.lex_t_lid), (0), ([]), ([]), (r1)))
in (

let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (

let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (

let lex_cons_t = (

let a = (let _150_1281 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _150_1281))
in (

let hd = (let _150_1282 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _150_1282))
in (

let tl = (let _150_1287 = (let _150_1286 = (let _150_1285 = (let _150_1284 = (let _150_1283 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _150_1283 FStar_Syntax_Syntax.Delta_constant None))
in ((_150_1284), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_150_1285))
in (FStar_Syntax_Syntax.mk _150_1286 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _150_1287))
in (

let res = (let _150_1291 = (let _150_1290 = (let _150_1289 = (let _150_1288 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _150_1288 FStar_Syntax_Syntax.Delta_constant None))
in ((_150_1289), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_150_1290))
in (FStar_Syntax_Syntax.mk _150_1291 None r2))
in (let _150_1292 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (Some (FStar_Syntax_Syntax.imp_tag))))::(((hd), (None)))::(((tl), (None)))::[]) _150_1292))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t), (FStar_Syntax_Const.lex_t_lid), (0), ([]), ([]), (r2)))
in (let _150_1294 = (let _150_1293 = (FStar_TypeChecker_Env.get_range env)
in (((tc)::(dc_lextop)::(dc_lexcons)::[]), ([]), (lids), (_150_1293)))
in FStar_Syntax_Syntax.Sig_bundle (_150_1294)))))))))))))))
end
| _58_3047 -> begin
(let _150_1296 = (let _150_1295 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle (((ses), ([]), (lids), (FStar_Range.dummyRange)))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _150_1295))
in (FStar_All.failwith _150_1296))
end))))
and tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _58_3057 = (FStar_Syntax_Util.type_u ())
in (match (_58_3057) with
| (k, _58_3056) -> begin
(

let phi = (let _150_1302 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _150_1302 (norm env)))
in (

let _58_3059 = (FStar_TypeChecker_Util.check_uvars r phi)
in FStar_Syntax_Syntax.Sig_assume (((lid), (phi), (quals), (r)))))
end))))
and tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _150_1312 = (let _150_1311 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _150_1311))
in (FStar_TypeChecker_Errors.diag r _150_1312)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let _58_3082 = ()
in (

let _58_3084 = (warn_positivity tc r)
in (

let _58_3088 = (FStar_Syntax_Subst.open_term tps k)
in (match (_58_3088) with
| (tps, k) -> begin
(

let _58_3093 = (tc_binders env tps)
in (match (_58_3093) with
| (tps, env_tps, guard_params, us) -> begin
(

let _58_3096 = (FStar_Syntax_Util.arrow_formals k)
in (match (_58_3096) with
| (indices, t) -> begin
(

let _58_3101 = (tc_binders env_tps indices)
in (match (_58_3101) with
| (indices, env', guard_indices, us') -> begin
(

let _58_3109 = (

let _58_3106 = (tc_tot_or_gtot_term env' t)
in (match (_58_3106) with
| (t, _58_3104, g) -> begin
(let _150_1319 = (let _150_1318 = (let _150_1317 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params _150_1317))
in (FStar_TypeChecker_Rel.discharge_guard env' _150_1318))
in ((t), (_150_1319)))
end))
in (match (_58_3109) with
| (t, guard) -> begin
(

let k = (let _150_1320 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _150_1320))
in (

let _58_3113 = (FStar_Syntax_Util.type_u ())
in (match (_58_3113) with
| (t_type, u) -> begin
(

let _58_3114 = (let _150_1321 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _150_1321))
in (

let t_tc = (let _150_1322 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _150_1322))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _150_1323 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((_150_1323), (FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps), (k), (mutuals), (data), (quals), (r)))), (u), (guard))))))))
end)))
end))
end))
end))
end))
end))))
end
| _58_3121 -> begin
(FStar_All.failwith "impossible")
end))
in (

let positive_if_pure = (fun _58_3123 l -> ())
in (

let tc_data = (fun env tcs _58_7 -> (match (_58_7) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let _58_3140 = ()
in (

let _58_3175 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _58_3144 -> (match (_58_3144) with
| (se, u_tc) -> begin
if (let _150_1336 = (let _150_1335 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _150_1335))
in (FStar_Ident.lid_equals tc_lid _150_1336)) then begin
(

let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_3146, _58_3148, tps, _58_3151, _58_3153, _58_3155, _58_3157, _58_3159) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _58_3165 -> (match (_58_3165) with
| (x, _58_3164) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
end
| _58_3167 -> begin
(FStar_All.failwith "Impossible")
end)
in Some (((tps), (u_tc))))
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
(([]), (FStar_Syntax_Syntax.U_zero))
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected data constructor"), (r)))))
end
end))
in (match (_58_3175) with
| (tps, u_tc) -> begin
(

let _58_3195 = (match ((let _150_1338 = (FStar_Syntax_Subst.compress t)
in _150_1338.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _58_3183 = (FStar_Util.first_N ntps bs)
in (match (_58_3183) with
| (_58_3181, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res)))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _58_3189 -> (match (_58_3189) with
| (x, _58_3188) -> begin
FStar_Syntax_Syntax.DB ((((ntps - (1 + i))), (x)))
end))))
in (let _150_1341 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _150_1341))))
end))
end
| _58_3192 -> begin
(([]), (t))
end)
in (match (_58_3195) with
| (arguments, result) -> begin
(

let _58_3196 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1344 = (FStar_Syntax_Print.lid_to_string c)
in (let _150_1343 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _150_1342 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _150_1344 _150_1343 _150_1342))))
end else begin
()
end
in (

let _58_3201 = (tc_tparams env arguments)
in (match (_58_3201) with
| (arguments, env', us) -> begin
(

let _58_3205 = (tc_trivial_guard env' result)
in (match (_58_3205) with
| (result, _58_3204) -> begin
(

let _58_3209 = (FStar_Syntax_Util.head_and_args result)
in (match (_58_3209) with
| (head, _58_3208) -> begin
(

let _58_3214 = (match ((let _150_1345 = (FStar_Syntax_Subst.compress head)
in _150_1345.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _58_3213 -> begin
(let _150_1350 = (let _150_1349 = (let _150_1348 = (let _150_1347 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _150_1346 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _150_1347 _150_1346)))
in ((_150_1348), (r)))
in FStar_Syntax_Syntax.Error (_150_1349))
in (Prims.raise _150_1350))
end)
in (

let g = (FStar_List.fold_left2 (fun g _58_3220 u_x -> (match (_58_3220) with
| (x, _58_3219) -> begin
(

let _58_3222 = ()
in (let _150_1354 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _150_1354)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _150_1358 = (let _150_1356 = (FStar_All.pipe_right tps (FStar_List.map (fun _58_3228 -> (match (_58_3228) with
| (x, _58_3227) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append _150_1356 arguments))
in (let _150_1357 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _150_1358 _150_1357)))
in ((FStar_Syntax_Syntax.Sig_datacon (((c), ([]), (t), (tc_lid), (ntps), (quals), ([]), (r)))), (g)))))
end))
end))
end)))
end))
end)))
end
| _58_3231 -> begin
(FStar_All.failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let _58_3237 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _58_8 -> (match (_58_8) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_3241, _58_3243, tps, k, _58_3247, _58_3249, _58_3251, _58_3253) -> begin
(let _150_1369 = (let _150_1368 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _150_1368))
in (FStar_Syntax_Syntax.null_binder _150_1369))
end
| _58_3257 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _58_9 -> (match (_58_9) with
| FStar_Syntax_Syntax.Sig_datacon (_58_3261, _58_3263, t, _58_3266, _58_3268, _58_3270, _58_3272, _58_3274) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _58_3278 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let t = (let _150_1371 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _150_1371))
in (

let _58_3281 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1372 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _150_1372))
end else begin
()
end
in (

let _58_3285 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_58_3285) with
| (uvs, t) -> begin
(

let _58_3287 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1376 = (let _150_1374 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _150_1374 (FStar_String.concat ", ")))
in (let _150_1375 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _150_1376 _150_1375)))
end else begin
()
end
in (

let _58_3291 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_58_3291) with
| (uvs, t) -> begin
(

let _58_3295 = (FStar_Syntax_Util.arrow_formals t)
in (match (_58_3295) with
| (args, _58_3294) -> begin
(

let _58_3298 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_58_3298) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _58_3302 se -> (match (_58_3302) with
| (x, _58_3301) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _58_3306, tps, _58_3309, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let _58_3332 = (match ((let _150_1379 = (FStar_Syntax_Subst.compress ty)
in _150_1379.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _58_3323 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_58_3323) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _58_3326 -> begin
(let _150_1380 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) _150_1380 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps), (t)))
end))
end
| _58_3329 -> begin
(([]), (ty))
end)
in (match (_58_3332) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs), (tps), (t), (mutuals), (datas), (quals), (r)))
end)))
end
| _58_3334 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| _58_3338 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _150_1381 -> FStar_Syntax_Syntax.U_name (_150_1381))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _58_10 -> (match (_58_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _58_3343, _58_3345, _58_3347, _58_3349, _58_3351, _58_3353, _58_3355) -> begin
((tc), (uvs_universes))
end
| _58_3359 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _58_3364 d -> (match (_58_3364) with
| (t, _58_3363) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _58_3368, _58_3370, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _150_1385 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _150_1385 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon (((l), (uvs), (ty), (tc), (ntps), (quals), (mutuals), (r))))
end
| _58_3380 -> begin
(FStar_All.failwith "Impossible")
end)
end)) data_types datas)))
end)
in ((tcs), (datas))))
end))
end))
end)))
end))))))))
in (

let _58_3390 = (FStar_All.pipe_right ses (FStar_List.partition (fun _58_11 -> (match (_58_11) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_3384) -> begin
true
end
| _58_3387 -> begin
false
end))))
in (match (_58_3390) with
| (tys, datas) -> begin
(

let _58_3397 = if (FStar_All.pipe_right datas (FStar_Util.for_some (fun _58_12 -> (match (_58_12) with
| FStar_Syntax_Syntax.Sig_datacon (_58_3393) -> begin
false
end
| _58_3396 -> begin
true
end)))) then begin
(let _150_1390 = (let _150_1389 = (let _150_1388 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (_150_1388)))
in FStar_Syntax_Syntax.Error (_150_1389))
in (Prims.raise _150_1390))
end else begin
()
end
in (

let env0 = env
in (

let _58_3416 = (FStar_List.fold_right (fun tc _58_3404 -> (match (_58_3404) with
| (env, all_tcs, g) -> begin
(

let _58_3409 = (tc_tycon env tc)
in (match (_58_3409) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (

let _58_3411 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1393 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _150_1393))
end else begin
()
end
in (let _150_1395 = (let _150_1394 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g _150_1394))
in ((env), ((((tc), (tc_u)))::all_tcs), (_150_1395)))))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_58_3416) with
| (env, tcs, g) -> begin
(

let _58_3426 = (FStar_List.fold_right (fun se _58_3420 -> (match (_58_3420) with
| (datas, g) -> begin
(

let _58_3423 = (tc_data env tcs se)
in (match (_58_3423) with
| (data, g') -> begin
(let _150_1398 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((data)::datas), (_150_1398)))
end))
end)) datas (([]), (g)))
in (match (_58_3426) with
| (datas, g) -> begin
(

let _58_3429 = (let _150_1399 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _150_1399 datas))
in (match (_58_3429) with
| (tcs, datas) -> begin
(

let sig_bndle = (let _150_1401 = (let _150_1400 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_150_1400)))
in FStar_Syntax_Syntax.Sig_bundle (_150_1401))
in (

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (_58_3434, _58_3436, t, _58_3439, _58_3441, _58_3443, _58_3445, _58_3447) -> begin
t
end
| _58_3451 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let dr = FStar_Range.dummyRange
in (

let optimized_haseq_scheme = (fun _58_3454 -> (

let haseq_ty = (fun usubst us acc ty -> (

let _58_3481 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _58_3463, bs, t, _58_3467, d_lids, _58_3470, _58_3472) -> begin
((lid), (bs), (t), (d_lids))
end
| _58_3476 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_58_3481) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _150_1414 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _150_1414 t))
in (

let _58_3486 = (FStar_Syntax_Subst.open_term bs t)
in (match (_58_3486) with
| (bs, t) -> begin
(

let ibs = (match ((let _150_1415 = (FStar_Syntax_Subst.compress t)
in _150_1415.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _58_3489) -> begin
ibs
end
| _58_3493 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _150_1418 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _150_1417 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_1418 _150_1417)))
in (

let ind = (let _150_1421 = (FStar_List.map (fun _58_3500 -> (match (_58_3500) with
| (bv, aq) -> begin
(let _150_1420 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_150_1420), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _150_1421 None dr))
in (

let ind = (let _150_1424 = (FStar_List.map (fun _58_3504 -> (match (_58_3504) with
| (bv, aq) -> begin
(let _150_1423 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_150_1423), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _150_1424 None dr))
in (

let haseq_ind = (let _150_1426 = (let _150_1425 = (FStar_Syntax_Syntax.as_arg ind)
in (_150_1425)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _150_1426 None dr))
in (

let bs' = (FStar_List.filter (fun b -> (

let _58_3515 = acc
in (match (_58_3515) with
| (_58_3509, en, _58_3512, _58_3514) -> begin
(

let opt = (let _150_1429 = (let _150_1428 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _150_1428))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort _150_1429 false))
in (match (opt) with
| None -> begin
false
end
| Some (_58_3519) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (let _150_1435 = (let _150_1434 = (let _150_1433 = (let _150_1432 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg _150_1432))
in (_150_1433)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _150_1434 None dr))
in (FStar_Syntax_Util.mk_conj t _150_1435))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let _58_3526 = fml
in (let _150_1441 = (let _150_1440 = (let _150_1439 = (let _150_1438 = (let _150_1437 = (let _150_1436 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_150_1436)::[])
in (_150_1437)::[])
in FStar_Syntax_Syntax.Meta_pattern (_150_1438))
in ((fml), (_150_1439)))
in FStar_Syntax_Syntax.Tm_meta (_150_1440))
in {FStar_Syntax_Syntax.n = _150_1441; FStar_Syntax_Syntax.tk = _58_3526.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _58_3526.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_3526.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _150_1447 = (let _150_1446 = (let _150_1445 = (let _150_1444 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _150_1444 None))
in (FStar_Syntax_Syntax.as_arg _150_1445))
in (_150_1446)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _150_1447 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _150_1453 = (let _150_1452 = (let _150_1451 = (let _150_1450 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _150_1450 None))
in (FStar_Syntax_Syntax.as_arg _150_1451))
in (_150_1452)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _150_1453 None dr))) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let _58_3540 = acc
in (match (_58_3540) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_58_3545, _58_3547, _58_3549, t_lid, _58_3552, _58_3554, _58_3556, _58_3558) -> begin
(t_lid = lid)
end
| _58_3562 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let haseq_data = (fun acc data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (match ((let _150_1459 = (FStar_Syntax_Subst.compress dt)
in _150_1459.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _58_3571) -> begin
(

let dbs = (let _150_1460 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _150_1460))
in (

let dbs = (let _150_1461 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _150_1461 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = (let _150_1465 = (let _150_1464 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_150_1464)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _150_1465 None dr))
in (

let sort_range = (Prims.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b = (let _150_1467 = (let _150_1466 = (FStar_Syntax_Print.term_to_string ind)
in (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add the \'noeq\' qualifier" _150_1466))
in (FStar_TypeChecker_Util.label _150_1467 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b))))) FStar_Syntax_Util.t_true dbs)
in (

let _58_3585 = acc
in (match (_58_3585) with
| (env, cond') -> begin
(let _150_1469 = (FStar_TypeChecker_Env.push_binders env dbs)
in (let _150_1468 = (FStar_Syntax_Util.mk_conj cond' cond)
in ((_150_1469), (_150_1468))))
end))))))
end
| _58_3587 -> begin
acc
end))))
in (

let _58_3590 = (FStar_List.fold_left haseq_data ((env), (FStar_Syntax_Util.t_true)) t_datas)
in (match (_58_3590) with
| (env, cond) -> begin
(

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (let _150_1471 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _150_1470 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env), (_150_1471), (_150_1470)))))
end))))))
end)))))))))))))))
end))))
end)))
in (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_3594, us, _58_3597, _58_3599, _58_3601, _58_3603, _58_3605, _58_3607) -> begin
us
end
| _58_3611 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let _58_3615 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_58_3615) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _58_3617 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _58_3619 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let _58_3626 = (FStar_List.fold_left (haseq_ty usubst us) (([]), (env), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (_58_3626) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let _58_3631 = (tc_trivial_guard env phi)
in (match (_58_3631) with
| (phi, _58_3630) -> begin
(

let _58_3632 = if (FStar_TypeChecker_Env.should_verify env) then begin
(let _150_1472 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _150_1472))
end else begin
()
end
in (

let ses = (FStar_List.fold_left (fun l _58_3637 -> (match (_58_3637) with
| (lid, fml) -> begin
(

let se = (tc_assume env lid fml [] dr)
in (FStar_List.append l ((se)::[])))
end)) [] axioms)
in (

let _58_3640 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in ses)))
end)))
end))))))
end)))))
in (

let unoptimized_haseq_scheme = (fun _58_3643 -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _58_3648, _58_3650, _58_3652, _58_3654, _58_3656, _58_3658, _58_3660) -> begin
lid
end
| _58_3664 -> begin
(FStar_All.failwith "Impossible!")
end)) tcs)
in (

let haseq_ty = (fun usubst us acc ty -> (

let _58_3691 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _58_3673, bs, t, _58_3677, d_lids, _58_3680, _58_3682) -> begin
((lid), (bs), (t), (d_lids))
end
| _58_3686 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_58_3691) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _150_1486 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _150_1486 t))
in (

let _58_3696 = (FStar_Syntax_Subst.open_term bs t)
in (match (_58_3696) with
| (bs, t) -> begin
(

let ibs = (match ((let _150_1487 = (FStar_Syntax_Subst.compress t)
in _150_1487.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _58_3699) -> begin
ibs
end
| _58_3703 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _150_1490 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _150_1489 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_1490 _150_1489)))
in (

let ind = (let _150_1493 = (FStar_List.map (fun _58_3710 -> (match (_58_3710) with
| (bv, aq) -> begin
(let _150_1492 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_150_1492), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _150_1493 None dr))
in (

let ind = (let _150_1496 = (FStar_List.map (fun _58_3714 -> (match (_58_3714) with
| (bv, aq) -> begin
(let _150_1495 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_150_1495), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _150_1496 None dr))
in (

let haseq_ind = (let _150_1498 = (let _150_1497 = (FStar_Syntax_Syntax.as_arg ind)
in (_150_1497)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _150_1498 None dr))
in (

let rec is_mutual = (fun t -> (match ((let _150_1502 = (FStar_Syntax_Subst.compress t)
in _150_1502.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', _58_3725) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
if (is_mutual t') then begin
true
end else begin
(let _150_1504 = (FStar_List.map Prims.fst args)
in (exists_mutual _150_1504))
end
end
| FStar_Syntax_Syntax.Tm_meta (t', _58_3738) -> begin
(is_mutual t')
end
| _58_3742 -> begin
false
end))
and exists_mutual = (fun _58_13 -> (match (_58_13) with
| [] -> begin
false
end
| (hd)::tl -> begin
((is_mutual hd) || (exists_mutual tl))
end))
in (

let haseq_data = (fun acc data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (match ((let _150_1510 = (FStar_Syntax_Subst.compress dt)
in _150_1510.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _58_3755) -> begin
(

let dbs = (let _150_1511 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _150_1511))
in (

let dbs = (let _150_1512 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _150_1512 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = (let _150_1516 = (let _150_1515 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_150_1515)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _150_1516 None dr))
in (

let haseq_sort = if (is_mutual sort) then begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end else begin
haseq_sort
end
in (FStar_Syntax_Util.mk_conj t haseq_sort))))) FStar_Syntax_Util.t_true dbs)
in (

let cond = (FStar_List.fold_right (fun b t -> (let _150_1522 = (let _150_1521 = (let _150_1520 = (let _150_1519 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _150_1519 None))
in (FStar_Syntax_Syntax.as_arg _150_1520))
in (_150_1521)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _150_1522 None dr))) dbs cond)
in (FStar_Syntax_Util.mk_conj acc cond))))))
end
| _58_3771 -> begin
acc
end))))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_58_3774, _58_3776, _58_3778, t_lid, _58_3781, _58_3783, _58_3785, _58_3787) -> begin
(t_lid = lid)
end
| _58_3791 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let data_cond = (FStar_List.fold_left haseq_data FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml = (

let _58_3795 = fml
in (let _150_1529 = (let _150_1528 = (let _150_1527 = (let _150_1526 = (let _150_1525 = (let _150_1524 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_150_1524)::[])
in (_150_1525)::[])
in FStar_Syntax_Syntax.Meta_pattern (_150_1526))
in ((fml), (_150_1527)))
in FStar_Syntax_Syntax.Tm_meta (_150_1528))
in {FStar_Syntax_Syntax.n = _150_1529; FStar_Syntax_Syntax.tk = _58_3795.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _58_3795.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_3795.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _150_1535 = (let _150_1534 = (let _150_1533 = (let _150_1532 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _150_1532 None))
in (FStar_Syntax_Syntax.as_arg _150_1533))
in (_150_1534)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _150_1535 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _150_1541 = (let _150_1540 = (let _150_1539 = (let _150_1538 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _150_1538 None))
in (FStar_Syntax_Syntax.as_arg _150_1539))
in (_150_1540)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _150_1541 None dr))) bs fml)
in (FStar_Syntax_Util.mk_conj acc fml)))))))))))))))
end))))
end)))
in (

let _58_3825 = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, _58_3808, _58_3810, _58_3812, _58_3814, _58_3816, _58_3818) -> begin
((lid), (us))
end
| _58_3822 -> begin
(FStar_All.failwith "Impossible!")
end))
in (match (_58_3825) with
| (lid, us) -> begin
(

let _58_3828 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_58_3828) with
| (usubst, us) -> begin
(

let fml = (FStar_List.fold_left (haseq_ty usubst us) FStar_Syntax_Util.t_true tcs)
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _58_3831 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _58_3833 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let se = (let _150_1542 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (tc_assume env _150_1542 fml [] dr))
in (se)::[]))))))
end))
end)))))
in (

let is_noeq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Noeq)) quals)
in if (((FStar_Ident.lid_equals env.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid) || is_noeq) || ((FStar_List.length tcs) = 0)) then begin
(sig_bndle)::[]
end else begin
(

let is_unopteq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Unopteq)) quals)
in (

let ses = if is_unopteq then begin
(unoptimized_haseq_scheme ())
end else begin
(optimized_haseq_scheme ())
end
in (let _150_1547 = (let _150_1546 = (let _150_1545 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_150_1545)))
in FStar_Syntax_Syntax.Sig_bundle (_150_1546))
in (_150_1547)::ses)))
end))))))
end))
end))
end))))
end)))))))))
and tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env se -> (

let env = (set_hint_correlator env se)
in (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let se = (tc_lex_t env ses quals lids)
in (let _150_1550 = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (_150_1550)))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let ses = (tc_inductive env ses quals lids)
in (

let env = (FStar_List.fold_left (fun env' se -> (FStar_TypeChecker_Env.push_sigelt env' se)) env ses)
in ((ses), (env)))))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(

let set_options = (fun t s -> (match ((FStar_Options.set_options t s)) with
| FStar_Getopt.Success -> begin
()
end
| FStar_Getopt.Help -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Failed to process pragma: use \'fstar --help\' to see which options are available"), (r)))))
end
| FStar_Getopt.Error (s) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Failed to process pragma: " s)), (r)))))
end))
in (match (p) with
| FStar_Syntax_Syntax.SetOptions (o) -> begin
(

let _58_3883 = (set_options FStar_Options.Set o)
in (((se)::[]), (env)))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(

let _58_3887 = (let _150_1557 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _150_1557 Prims.ignore))
in (

let _58_3892 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _58_3894 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (((se)::[]), (env)))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_58_3897) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(

let ne = (tc_eff_decl env ne)
in (

let se = FStar_Syntax_Syntax.Sig_new_effect (((ne), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (

let _58_3913 = (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun _58_3908 a -> (match (_58_3908) with
| (env, ses) -> begin
(

let se_let = (FStar_Syntax_Util.action_as_lb a)
in (let _150_1560 = (FStar_TypeChecker_Env.push_sigelt env se_let)
in ((_150_1560), ((se_let)::ses))))
end)) ((env), ((se)::[]))))
in (match (_58_3913) with
| (env, ses) -> begin
(((se)::[]), (env))
end)))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(

let ed_src = (FStar_TypeChecker_Env.get_effect_decl env sub.FStar_Syntax_Syntax.source)
in (

let ed_tgt = (FStar_TypeChecker_Env.get_effect_decl env sub.FStar_Syntax_Syntax.target)
in (

let _58_3922 = (let _150_1561 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _150_1561))
in (match (_58_3922) with
| (a, wp_a_src) -> begin
(

let _58_3925 = (let _150_1562 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _150_1562))
in (match (_58_3925) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _150_1566 = (let _150_1565 = (let _150_1564 = (let _150_1563 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (_150_1563)))
in FStar_Syntax_Syntax.NT (_150_1564))
in (_150_1565)::[])
in (FStar_Syntax_Subst.subst _150_1566 wp_b_tgt))
in (

let expected_k = (let _150_1571 = (let _150_1569 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1568 = (let _150_1567 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_150_1567)::[])
in (_150_1569)::_150_1568))
in (let _150_1570 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _150_1571 _150_1570)))
in (

let lift_wp = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift_wp) expected_k)
in (

let repr_type = (fun eff_name a wp -> (

let no_reify = (fun l -> (let _150_1583 = (let _150_1582 = (let _150_1581 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _150_1580 = (FStar_TypeChecker_Env.get_range env)
in ((_150_1581), (_150_1580))))
in FStar_Syntax_Syntax.Error (_150_1582))
in (Prims.raise _150_1583)))
in (match ((FStar_TypeChecker_Env.effect_decl_opt env eff_name)) with
| None -> begin
(no_reify eff_name)
end
| Some (ed) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((FStar_Syntax_Syntax.U_unknown)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in if (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)))) then begin
(no_reify eff_name)
end else begin
(let _150_1590 = (let _150_1588 = (let _150_1587 = (let _150_1586 = (FStar_Syntax_Syntax.as_arg a)
in (let _150_1585 = (let _150_1584 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_1584)::[])
in (_150_1586)::_150_1585))
in ((repr), (_150_1587)))
in FStar_Syntax_Syntax.Tm_app (_150_1588))
in (let _150_1589 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _150_1590 None _150_1589)))
end)
end)))
in (

let lift = (match (sub.FStar_Syntax_Syntax.lift) with
| None -> begin
None
end
| Some (_58_3941, lift) -> begin
(

let _58_3947 = (let _150_1591 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _150_1591))
in (match (_58_3947) with
| (a, wp_a_src) -> begin
(

let wp_a = (FStar_Syntax_Syntax.new_bv None wp_a_src)
in (

let a_typ = (FStar_Syntax_Syntax.bv_to_name a)
in (

let wp_a_typ = (FStar_Syntax_Syntax.bv_to_name wp_a)
in (

let repr_f = (repr_type sub.FStar_Syntax_Syntax.source a_typ wp_a_typ)
in (

let repr_result = (

let lift_wp_a = (let _150_1598 = (let _150_1596 = (let _150_1595 = (let _150_1594 = (FStar_Syntax_Syntax.as_arg a_typ)
in (let _150_1593 = (let _150_1592 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (_150_1592)::[])
in (_150_1594)::_150_1593))
in (((Prims.snd sub.FStar_Syntax_Syntax.lift_wp)), (_150_1595)))
in FStar_Syntax_Syntax.Tm_app (_150_1596))
in (let _150_1597 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _150_1598 None _150_1597)))
in (repr_type sub.FStar_Syntax_Syntax.target a_typ lift_wp_a))
in (

let expected_k = (let _150_1605 = (let _150_1603 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1602 = (let _150_1601 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (let _150_1600 = (let _150_1599 = (FStar_Syntax_Syntax.null_binder repr_f)
in (_150_1599)::[])
in (_150_1601)::_150_1600))
in (_150_1603)::_150_1602))
in (let _150_1604 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow _150_1605 _150_1604)))
in (

let _58_3960 = (tc_tot_or_gtot_term env expected_k)
in (match (_58_3960) with
| (expected_k, _58_3957, _58_3959) -> begin
(

let lift = (check_and_gen env lift expected_k)
in Some (lift))
end))))))))
end))
end)
in (

let sub = (

let _58_3963 = sub
in {FStar_Syntax_Syntax.source = _58_3963.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _58_3963.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift})
in (

let se = FStar_Syntax_Syntax.Sig_sub_effect (((sub), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env))))))))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(

let _58_3976 = ()
in (

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _58_3982 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_58_3982) with
| (tps, c) -> begin
(

let _58_3986 = (tc_tparams env tps)
in (match (_58_3986) with
| (tps, env, us) -> begin
(

let _58_3990 = (tc_comp env c)
in (match (_58_3990) with
| (c, u, g) -> begin
(

let _58_3991 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let _58_3997 = (let _150_1606 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _150_1606))
in (match (_58_3997) with
| (uvs, t) -> begin
(

let _58_4016 = (match ((let _150_1608 = (let _150_1607 = (FStar_Syntax_Subst.compress t)
in _150_1607.FStar_Syntax_Syntax.n)
in ((tps), (_150_1608)))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_58_4000, c)) -> begin
(([]), (c))
end
| (_58_4006, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
((tps), (c))
end
| _58_4013 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_58_4016) with
| (tps, c) -> begin
(

let se = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (uvs), (tps), (c), (tags), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 se)
in (((se)::[]), (env))))
end))
end)))))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t, quals, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _58_4027 = ()
in (

let _58_4031 = (let _150_1610 = (let _150_1609 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _150_1609))
in (check_and_gen env t _150_1610))
in (match (_58_4031) with
| (uvs, t) -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (uvs), (t), (quals), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env))))
end))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(

let se = (tc_assume env lid phi quals r)
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env))))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (

let _58_4051 = (tc_term env e)
in (match (_58_4051) with
| (e, c, g1) -> begin
(

let _58_4056 = (let _150_1614 = (let _150_1611 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_150_1611))
in (let _150_1613 = (let _150_1612 = (c.FStar_Syntax_Syntax.comp ())
in ((e), (_150_1612)))
in (check_expected_effect env _150_1614 _150_1613)))
in (match (_58_4056) with
| (e, _58_4054, g) -> begin
(

let _58_4057 = (let _150_1615 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _150_1615))
in (

let se = FStar_Syntax_Syntax.Sig_main (((e), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env)))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
if (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q')) then begin
Some (q)
end else begin
(let _150_1627 = (let _150_1626 = (let _150_1625 = (let _150_1624 = (FStar_Syntax_Print.lid_to_string l)
in (let _150_1623 = (FStar_Syntax_Print.quals_to_string q)
in (let _150_1622 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _150_1624 _150_1623 _150_1622))))
in ((_150_1625), (r)))
in FStar_Syntax_Syntax.Error (_150_1626))
in (Prims.raise _150_1627))
end
end))
in (

let _58_4101 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _58_4078 lb -> (match (_58_4078) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _58_4097 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
((gen), (lb), (quals_opt))
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (

let _58_4092 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _58_4091 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _150_1630 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Syntax_Const.effect_ALL_lid), (tval), (lb.FStar_Syntax_Syntax.lbdef)))
in ((false), (_150_1630), (quals_opt)))))
end)
in (match (_58_4097) with
| (gen, lb, quals_opt) -> begin
((gen), ((lb)::lbs), (quals_opt))
end)))
end)) ((true), ([]), (if (quals = []) then begin
None
end else begin
Some (quals)
end))))
in (match (_58_4101) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _58_14 -> (match (_58_14) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _58_4110 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (

let lbs' = (FStar_List.rev lbs')
in (

let e = (let _150_1634 = (let _150_1633 = (let _150_1632 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((((Prims.fst lbs)), (lbs'))), (_150_1632)))
in FStar_Syntax_Syntax.Tm_let (_150_1633))
in (FStar_Syntax_Syntax.mk _150_1634 None r))
in (

let _58_4144 = (match ((tc_maybe_toplevel_term (

let _58_4114 = env
in {FStar_TypeChecker_Env.solver = _58_4114.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_4114.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_4114.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_4114.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_4114.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_4114.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_4114.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_4114.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_4114.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_4114.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_4114.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _58_4114.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _58_4114.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_4114.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_4114.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_4114.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_4114.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_4114.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_4114.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_4114.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_4114.FStar_TypeChecker_Env.qname_and_index}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _58_4121; FStar_Syntax_Syntax.pos = _58_4119; FStar_Syntax_Syntax.vars = _58_4117}, _58_4128, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_58_4132, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _58_4138 -> begin
quals
end)
in ((FStar_Syntax_Syntax.Sig_let (((lbs), (r), (lids), (quals)))), (lbs)))
end
| _58_4141 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_58_4144) with
| (se, lbs) -> begin
(

let _58_4150 = if (log env) then begin
(let _150_1642 = (let _150_1641 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _150_1638 = (let _150_1637 = (let _150_1636 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _150_1636.FStar_Syntax_Syntax.fv_name)
in _150_1637.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _150_1638))) with
| None -> begin
true
end
| _58_4148 -> begin
false
end)
in if should_log then begin
(let _150_1640 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _150_1639 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _150_1640 _150_1639)))
end else begin
""
end))))
in (FStar_All.pipe_right _150_1641 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _150_1642))
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env))))
end)))))
end))))
end)))


let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _58_15 -> (match (_58_15) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _58_4160 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _58_4170 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_58_4172) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _58_4183, _58_4185) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _58_4191 -> (match (_58_4191) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _58_4197, _58_4199, quals, r) -> begin
(

let dec = (let _150_1658 = (let _150_1657 = (let _150_1656 = (let _150_1655 = (let _150_1654 = (FStar_Syntax_Syntax.mk_Total t)
in ((bs), (_150_1654)))
in FStar_Syntax_Syntax.Tm_arrow (_150_1655))
in (FStar_Syntax_Syntax.mk _150_1656 None r))
in ((l), (us), (_150_1657), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_150_1658))
in (((dec)::out), (hidden)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _58_4209, _58_4211, _58_4213, _58_4215, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r)))
in (((dec)::out), ((l)::hidden)))
end
| _58_4221 -> begin
((out), (hidden))
end)
end)) ses (([]), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end
| FStar_Syntax_Syntax.Sig_assume (_58_4223, _58_4225, quals, _58_4228) -> begin
if (is_abstract quals) then begin
(([]), (hidden))
end else begin
(((se)::[]), (hidden))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, us, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) then begin
(((FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r))))::[]), ((l)::hidden))
end else begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _58_16 -> (match (_58_16) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _58_4247 -> begin
false
end)))) then begin
(((se)::[]), (hidden))
end else begin
(([]), (hidden))
end
end
end
| FStar_Syntax_Syntax.Sig_main (_58_4249) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _58_4268, _58_4270, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))) then begin
(([]), (hidden))
end else begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::[]), ((FStar_Ident.range_of_lid lid))))
in (((dec)::[]), ((lid)::hidden)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (is_abstract quals) then begin
(let _150_1665 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _150_1664 = (let _150_1663 = (let _150_1662 = (let _150_1661 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _150_1661.FStar_Syntax_Syntax.fv_name)
in _150_1662.FStar_Syntax_Syntax.v)
in ((_150_1663), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_150_1664)))))
in ((_150_1665), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let process_one_decl = (fun _58_4291 se -> (match (_58_4291) with
| (ses, exports, env, hidden) -> begin
(

let _58_4293 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1674 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _150_1674))
end else begin
()
end
in (

let _58_4297 = (tc_decl env se)
in (match (_58_4297) with
| (ses', env) -> begin
(

let _58_4300 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _150_1679 = (FStar_List.fold_left (fun s se -> (let _150_1678 = (let _150_1677 = (FStar_Syntax_Print.sigelt_to_string se)
in (Prims.strcat _150_1677 "\n"))
in (Prims.strcat s _150_1678))) "" ses')
in (FStar_Util.print1 "Checked: %s\n" _150_1679))
end else begin
()
end
in (

let _58_4303 = (FStar_List.iter (fun se -> (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)) ses')
in (

let _58_4312 = (FStar_List.fold_left (fun _58_4307 se -> (match (_58_4307) with
| (le, lh) -> begin
(

let tup = (for_export hidden se)
in (((FStar_List.rev_append (Prims.fst tup) le)), ((FStar_List.rev_append (Prims.snd tup) lh))))
end)) (([]), ([])) ses')
in (match (_58_4312) with
| (exported, hidden) -> begin
(((FStar_List.rev_append ses' ses)), (((FStar_List.rev_append exported []))::exports), (env), (hidden))
end))))
end)))
end))
in (

let _58_4338 = (FStar_List.fold_left (fun acc se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(

let _58_4326 = acc
in (match (_58_4326) with
| (_58_4320, _58_4322, env, _58_4325) -> begin
(

let _58_4329 = (cps_and_elaborate env ne)
in (match (_58_4329) with
| (ses, ne) -> begin
(

let ses = (FStar_List.append ses ((FStar_Syntax_Syntax.Sig_new_effect (((ne), (r))))::[]))
in (FStar_List.fold_left process_one_decl acc ses))
end))
end))
end
| _58_4332 -> begin
(process_one_decl acc se)
end)) (([]), ([]), (env), ([])) ses)
in (match (_58_4338) with
| (ses, exports, env, _58_4337) -> begin
(let _150_1685 = (FStar_All.pipe_right (FStar_List.rev_append exports []) FStar_List.flatten)
in (((FStar_List.rev_append ses [])), (_150_1685), (env)))
end))))


let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let msg = (Prims.strcat "Internals for " name)
in (

let env = (

let _58_4343 = env
in (let _150_1690 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _58_4343.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_4343.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_4343.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_4343.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_4343.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_4343.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_4343.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_4343.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_4343.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_4343.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_4343.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_4343.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_4343.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_4343.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_4343.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_4343.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _150_1690; FStar_TypeChecker_Env.lax = _58_4343.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_4343.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_4343.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_4343.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_4343.FStar_TypeChecker_Env.qname_and_index}))
in (

let _58_4346 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
in (

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let _58_4352 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_58_4352) with
| (ses, exports, env) -> begin
(((

let _58_4353 = modul
in {FStar_Syntax_Syntax.name = _58_4353.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _58_4353.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _58_4353.FStar_Syntax_Syntax.is_interface})), (exports), (env))
end))))))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let _58_4361 = (tc_decls env decls)
in (match (_58_4361) with
| (ses, exports, env) -> begin
(

let modul = (

let _58_4362 = modul
in {FStar_Syntax_Syntax.name = _58_4362.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _58_4362.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _58_4362.FStar_Syntax_Syntax.is_interface})
in ((modul), (exports), (env)))
end)))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul = (

let _58_4368 = modul
in {FStar_Syntax_Syntax.name = _58_4368.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _58_4368.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in (

let _58_4372 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let _58_4374 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (

let _58_4376 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (

let _58_4378 = (let _150_1703 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _150_1703 Prims.ignore))
in ((modul), (env)))))))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let _58_4385 = (tc_partial_modul env modul)
in (match (_58_4385) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _58_4388 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _150_1712 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _150_1712))
end else begin
()
end
in (

let env = (

let _58_4390 = env
in {FStar_TypeChecker_Env.solver = _58_4390.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_4390.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_4390.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_4390.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_4390.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_4390.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_4390.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_4390.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_4390.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_4390.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_4390.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_4390.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_4390.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_4390.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_4390.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_4390.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_4390.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_4390.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_4390.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_4390.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_4390.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_4390.FStar_TypeChecker_Env.qname_and_index})
in (

let _58_4406 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _58_4398) -> begin
(let _150_1717 = (let _150_1716 = (let _150_1715 = (FStar_TypeChecker_Env.get_range env)
in (((Prims.strcat "Implicit argument: " msg)), (_150_1715)))
in FStar_Syntax_Syntax.Error (_150_1716))
in (Prims.raise _150_1717))
end
in (match (_58_4406) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end else begin
(let _150_1722 = (let _150_1721 = (let _150_1720 = (let _150_1718 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _150_1718))
in (let _150_1719 = (FStar_TypeChecker_Env.get_range env)
in ((_150_1720), (_150_1719))))
in FStar_Syntax_Syntax.Error (_150_1721))
in (Prims.raise _150_1722))
end
end)))))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
FStar_Syntax_Syntax.U_zero
end else begin
(

let _58_4409 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_1727 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print1 "universe_of %s\n" _150_1727))
end else begin
()
end
in (

let _58_4414 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_4414) with
| (env, _58_4413) -> begin
(

let env = (

let _58_4415 = env
in {FStar_TypeChecker_Env.solver = _58_4415.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_4415.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_4415.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_4415.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_4415.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_4415.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_4415.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_4415.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_4415.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_4415.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_4415.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_4415.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_4415.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_4415.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_4415.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_4415.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_4415.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _58_4415.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_4415.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _58_4415.FStar_TypeChecker_Env.qname_and_index})
in (

let fail = (fun e t -> (let _150_1737 = (let _150_1736 = (let _150_1735 = (let _150_1733 = (FStar_Syntax_Print.term_to_string e)
in (let _150_1732 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" _150_1733 _150_1732)))
in (let _150_1734 = (FStar_TypeChecker_Env.get_range env)
in ((_150_1735), (_150_1734))))
in FStar_Syntax_Syntax.Error (_150_1736))
in (Prims.raise _150_1737)))
in (

let ok = (fun u -> (

let _58_4423 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_1741 = (FStar_Syntax_Print.tag_of_term e)
in (let _150_1740 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.print2 "<end> universe_of %s is %s\n" _150_1741 _150_1740)))
end else begin
()
end
in u))
in (

let universe_of_type = (fun e t -> (match ((let _150_1746 = (FStar_Syntax_Util.unrefine t)
in _150_1746.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(ok u)
end
| _58_4431 -> begin
(fail e t)
end))
in (

let _58_4434 = (FStar_Syntax_Util.head_and_args e)
in (match (_58_4434) with
| (head, args) -> begin
(match ((let _150_1747 = (FStar_Syntax_Subst.compress head)
in _150_1747.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_58_4436, t) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _150_1748 = (FStar_Syntax_Subst.compress t)
in _150_1748.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_4442, t) -> begin
(universe_of_type e (FStar_Syntax_Util.comp_result t))
end
| _58_4447 -> begin
(universe_of_type e t)
end))
end
| _58_4449 -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoInline)::[]) env e)
in (

let _58_4462 = (tc_term env e)
in (match (_58_4462) with
| (_58_4452, {FStar_Syntax_Syntax.eff_name = _58_4459; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_4456; FStar_Syntax_Syntax.comp = _58_4454}, g) -> begin
(

let _58_4463 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (let _150_1750 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (FStar_All.pipe_left (universe_of_type e) _150_1750)))
end)))
end)
end))))))
end)))
end)


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

let _58_4467 = if (FStar_Options.debug_any ()) then begin
(let _150_1755 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _150_1755))
end else begin
()
end
in (

let _58_4471 = (tc_modul env m)
in (match (_58_4471) with
| (m, env) -> begin
(

let _58_4472 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _150_1756 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _150_1756))
end else begin
()
end
in ((m), (env)))
end))))




