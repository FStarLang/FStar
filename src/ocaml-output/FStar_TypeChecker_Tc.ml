
open Prims

let set_hint_correlator : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env = (fun env se -> (match ((FStar_Options.reuse_hint_for ())) with
| Some (l) -> begin
(

let lid = (let _151_5 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_add_suffix _151_5 l))
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
(let _151_8 = (FStar_TypeChecker_Env.current_module env)
in (let _151_7 = (let _151_6 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_right _151_6 FStar_Util.string_of_int))
in (FStar_Ident.lid_add_suffix _151_8 _151_7)))
end
| (l)::_58_28 -> begin
l
end)
in (

let _58_32 = env
in {FStar_TypeChecker_Env.solver = _58_32.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_32.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_32.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_32.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_32.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_32.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_32.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_32.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_32.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_32.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_32.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_32.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_32.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_32.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_32.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_32.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_32.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_32.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_32.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_32.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_32.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_32.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), (0)))})))
end))


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (not ((let _151_11 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _151_11))))))


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
in (let _151_25 = (let _151_24 = (FStar_Syntax_Syntax.as_arg v)
in (let _151_23 = (let _151_22 = (FStar_Syntax_Syntax.as_arg tl)
in (_151_22)::[])
in (_151_24)::_151_23))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _151_25 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))


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

let fvs' = (let _151_53 = if try_norm then begin
(norm env t)
end else begin
t
end
in (FStar_Syntax_Free.names _151_53))
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
(let _151_57 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _151_57))
end
| Some (head) -> begin
(let _151_59 = (FStar_Syntax_Print.bv_to_string x)
in (let _151_58 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _151_59 _151_58)))
end)
in (let _151_62 = (let _151_61 = (let _151_60 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (_151_60)))
in FStar_Syntax_Syntax.Error (_151_61))
in (Prims.raise _151_62)))
end))
in (

let s = (let _151_64 = (let _151_63 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _151_63))
in (FStar_TypeChecker_Util.new_uvar env _151_64))
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
(let _151_79 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _151_79 t))
end))}))


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let should_return = (fun t -> (match ((let _151_90 = (FStar_Syntax_Subst.compress t)
in _151_90.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_109, c) -> begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(

let t = (FStar_All.pipe_left FStar_Syntax_Util.unrefine (FStar_Syntax_Util.comp_result c))
in (match ((let _151_91 = (FStar_Syntax_Subst.compress t)
in _151_91.FStar_Syntax_Syntax.n)) with
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
(let _151_92 = if ((not ((should_return t))) || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _151_92))
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
(let _151_94 = (FStar_Syntax_Print.term_to_string t)
in (let _151_93 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _151_94 _151_93)))
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
(let _151_96 = (FStar_Syntax_Print.term_to_string t)
in (let _151_95 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _151_96 _151_95)))
end else begin
()
end
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let _58_146 = (let _151_102 = (FStar_All.pipe_left (fun _151_101 -> Some (_151_101)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _151_102 env e lc g))
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
(let _151_103 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _151_103))
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
(let _151_116 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (_151_116))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
if (FStar_Syntax_Util.is_pure_comp c) then begin
(let _151_117 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (_151_117))
end else begin
if (FStar_Syntax_Util.is_pure_or_ghost_comp c) then begin
(let _151_118 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (_151_118))
end else begin
None
end
end
end
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _151_119 = (norm_c env c)
in ((e), (_151_119), (FStar_TypeChecker_Rel.trivial_guard)))
end
| Some (expected_c) -> begin
(

let _58_175 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_122 = (FStar_Syntax_Print.term_to_string e)
in (let _151_121 = (FStar_Syntax_Print.comp_to_string c)
in (let _151_120 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _151_122 _151_121 _151_120))))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _58_178 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_125 = (FStar_Syntax_Print.term_to_string e)
in (let _151_124 = (FStar_Syntax_Print.comp_to_string c)
in (let _151_123 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _151_125 _151_124 _151_123))))
end else begin
()
end
in (

let _58_184 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_58_184) with
| (e, _58_182, g) -> begin
(

let g = (let _151_126 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _151_126 "could not prove post-condition" g))
in (

let _58_186 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_128 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _151_127 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _151_128 _151_127)))
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
(let _151_134 = (let _151_133 = (let _151_132 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _151_131 = (FStar_TypeChecker_Env.get_range env)
in ((_151_132), (_151_131))))
in FStar_Syntax_Syntax.Error (_151_133))
in (Prims.raise _151_134))
end)
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _151_137 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _151_137))
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
(let _151_144 = (let _151_143 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _151_143))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _151_144))
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

let t = (let _151_158 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _151_158))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _58_260 -> begin
(let _151_159 = (FStar_Syntax_Syntax.bv_to_name b)
in (_151_159)::[])
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
(match ((let _151_165 = (FStar_Syntax_Subst.compress t)
in _151_165.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _58_299 -> (match (_58_299) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _151_169 = (let _151_168 = (let _151_167 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_151_167))
in (FStar_Syntax_Syntax.new_bv _151_168 x.FStar_Syntax_Syntax.sort))
in ((_151_169), (imp)))
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

let precedes = (let _151_173 = (let _151_172 = (FStar_Syntax_Syntax.as_arg dec)
in (let _151_171 = (let _151_170 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_151_170)::[])
in (_151_172)::_151_171))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _151_173 None r))
in (

let _58_310 = (FStar_Util.prefix formals)
in (match (_58_310) with
| (bs, (last, imp)) -> begin
(

let last = (

let _58_311 = last
in (let _151_174 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _58_311.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_311.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _151_174}))
in (

let refined_formals = (FStar_List.append bs ((((last), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (

let _58_316 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_177 = (FStar_Syntax_Print.lbname_to_string l)
in (let _151_176 = (FStar_Syntax_Print.term_to_string t)
in (let _151_175 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _151_177 _151_176 _151_175))))
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
(let _151_247 = (let _151_245 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _151_245))
in (let _151_246 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _151_247 _151_246)))
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
in (let _151_252 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_pattern (pats))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _151_251 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((_151_252), (c), (_151_251)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _151_253 = (FStar_Syntax_Subst.compress e)
in _151_253.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_58_404, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _58_411; FStar_Syntax_Syntax.lbtyp = _58_409; FStar_Syntax_Syntax.lbeff = _58_407; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _58_422 = (let _151_254 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _151_254 e1))
in (match (_58_422) with
| (e1, c1, g1) -> begin
(

let _58_426 = (tc_term env e2)
in (match (_58_426) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((None), (c2)))
in (

let e = (let _151_259 = (let _151_258 = (let _151_257 = (let _151_256 = (let _151_255 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_TypeChecker_Common.t_unit), (e1)))
in (_151_255)::[])
in ((false), (_151_256)))
in ((_151_257), (e2)))
in FStar_Syntax_Syntax.Tm_let (_151_258))
in (FStar_Syntax_Syntax.mk _151_259 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _151_260 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e), (c), (_151_260))))))
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

let _58_472 = (let _151_261 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term _151_261 e))
in (match (_58_472) with
| (e, c', g') -> begin
(

let _58_476 = (let _151_263 = (let _151_262 = (c'.FStar_Syntax_Syntax.comp ())
in ((e), (_151_262)))
in (check_expected_effect env0 (Some (expected_c)) _151_263))
in (match (_58_476) with
| (e, expected_c, g'') -> begin
(let _151_266 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t_res)), (Some ((FStar_Syntax_Util.comp_effect_name expected_c)))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _151_265 = (let _151_264 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _151_264))
in ((_151_266), ((FStar_Syntax_Util.lcomp_of_comp expected_c)), (_151_265))))
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

let _58_495 = (let _151_267 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _151_267 e))
in (match (_58_495) with
| (e, c, g) -> begin
(

let _58_499 = (let _151_271 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_496 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _151_271 e c f))
in (match (_58_499) with
| (c, f) -> begin
(

let _58_503 = (let _151_272 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t)), (Some (c.FStar_Syntax_Syntax.eff_name))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _151_272 c))
in (match (_58_503) with
| (e, c, f2) -> begin
(let _151_274 = (let _151_273 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _151_273))
in ((e), (c), (_151_274)))
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

let head = (let _151_275 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (Prims.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) None _151_275))
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
(match ((let _151_276 = (FStar_Syntax_Subst.compress c.FStar_Syntax_Syntax.res_typ)
in _151_276.FStar_Syntax_Syntax.n)) with
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

let c = (let _151_277 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right _151_277 FStar_Syntax_Util.lcomp_of_comp))
in (

let _58_588 = (comp_check_expected_typ env e c)
in (match (_58_588) with
| (e, c, g') -> begin
(let _151_278 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), (c), (_151_278)))
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
(let _151_283 = (let _151_282 = (let _151_281 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((_151_281), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_151_282))
in (Prims.raise _151_283))
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

let t = (let _151_289 = (let _151_288 = (let _151_287 = (let _151_286 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _151_285 = (let _151_284 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (_151_284)::[])
in (_151_286)::_151_285))
in ((repr), (_151_287)))
in FStar_Syntax_Syntax.Tm_app (_151_288))
in (FStar_Syntax_Syntax.mk _151_289 None top.FStar_Syntax_Syntax.pos))
in (

let _58_626 = (let _151_291 = (let _151_290 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _151_290 Prims.fst))
in (tc_tot_or_gtot_term _151_291 t))
in (match (_58_626) with
| (t, _58_624, g) -> begin
(match ((let _151_292 = (FStar_Syntax_Subst.compress t)
in _151_292.FStar_Syntax_Syntax.n)) with
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

let _58_651 = if (let _151_293 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation _151_293)) then begin
(FStar_TypeChecker_Errors.add_errors env (((("Expected Tot, got a GTot computation"), (e.FStar_Syntax_Syntax.pos)))::[]))
end else begin
()
end
in (match ((FStar_TypeChecker_Rel.try_teq env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)) with
| None -> begin
(

let _58_654 = (let _151_298 = (let _151_297 = (let _151_296 = (let _151_295 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _151_294 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" _151_295 _151_294)))
in ((_151_296), (e.FStar_Syntax_Syntax.pos)))
in (_151_297)::[])
in (FStar_TypeChecker_Errors.add_errors env _151_298))
in (let _151_299 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e), (_151_299))))
end
| Some (g') -> begin
(let _151_301 = (let _151_300 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' _151_300))
in ((e), (_151_301)))
end))
end))
in (match (_58_660) with
| (e, g) -> begin
(

let c = (let _151_305 = (let _151_304 = (let _151_303 = (let _151_302 = (FStar_Syntax_Syntax.as_arg wp)
in (_151_302)::[])
in {FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = _151_303; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp _151_304))
in (FStar_All.pipe_right _151_305 FStar_Syntax_Util.lcomp_of_comp))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e), (aqual)))::[])))) (Some (res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let _58_666 = (comp_check_expected_typ env e c)
in (match (_58_666) with
| (e, c, g') -> begin
(let _151_306 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e), (c), (_151_306)))
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

let env = (let _151_308 = (let _151_307 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _151_307 Prims.fst))
in (FStar_All.pipe_right _151_308 instantiate_both))
in (

let _58_673 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_310 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _151_309 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _151_310 _151_309)))
end else begin
()
end
in (

let _58_678 = (tc_term (no_inst env) head)
in (match (_58_678) with
| (head, chead, g_head) -> begin
(

let _58_682 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _151_311 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _151_311))
end else begin
(let _151_312 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _151_312))
end
in (match (_58_682) with
| (e, c, g) -> begin
(

let _58_683 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _151_313 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _151_313))
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

let gimp = (match ((let _151_314 = (FStar_Syntax_Subst.compress head)
in _151_314.FStar_Syntax_Syntax.n)) with
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

let gres = (let _151_315 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _151_315))
in (

let _58_702 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _151_317 = (FStar_Syntax_Print.term_to_string e)
in (let _151_316 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" _151_317 _151_316)))
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
in (let _151_318 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in ((_151_318), (res_t))))
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
(let _151_321 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (_151_321)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_58_740) with
| (cases, g) -> begin
(let _151_322 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in ((_151_322), (g)))
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

let e_match = (let _151_326 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match _151_326))
in (

let lb = (let _151_327 = (FStar_TypeChecker_Env.norm_eff_name env c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = _151_327; FStar_Syntax_Syntax.lbdef = e1})
in (let _151_332 = (let _151_331 = (let _151_330 = (let _151_329 = (let _151_328 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (_151_328)::[])
in (FStar_Syntax_Subst.close _151_329 e_match))
in ((((false), ((lb)::[]))), (_151_330)))
in FStar_Syntax_Syntax.Tm_let (_151_331))
in (FStar_Syntax_Syntax.mk _151_332 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))))
end)
in (

let _58_760 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _151_335 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _151_334 = (let _151_333 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _151_333))
in (FStar_Util.print2 "(%s) comp type = %s\n" _151_335 _151_334)))
end else begin
()
end
in (let _151_336 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e), (cres), (_151_336))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_772); FStar_Syntax_Syntax.lbunivs = _58_770; FStar_Syntax_Syntax.lbtyp = _58_768; FStar_Syntax_Syntax.lbeff = _58_766; FStar_Syntax_Syntax.lbdef = _58_764})::[]), _58_778) -> begin
(

let _58_781 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_337 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _151_337))
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
(let _151_338 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _151_338))
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
(let _151_352 = (let _151_351 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_351))
in FStar_Util.Inr (_151_352))
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
(let _151_358 = (let _151_357 = (let _151_356 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _151_355 = (FStar_TypeChecker_Env.get_range env)
in ((_151_356), (_151_355))))
in FStar_Syntax_Syntax.Error (_151_357))
in (Prims.raise _151_358))
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
(let _151_360 = (let _151_359 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" _151_359))
in (FStar_All.failwith _151_360))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (match ((let _151_361 = (FStar_Syntax_Subst.compress t1)
in _151_361.FStar_Syntax_Syntax.n)) with
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
(let _151_364 = (let _151_362 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right _151_362 FStar_Syntax_Util.lcomp_of_comp))
in (let _151_363 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e), (_151_364), (_151_363))))
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
(let _151_366 = (let _151_365 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_365))
in FStar_Util.Inr (_151_366))
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
(let _151_369 = (let _151_368 = (let _151_367 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (_151_367)))
in FStar_Syntax_Syntax.Error (_151_368))
in (Prims.raise _151_369))
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

let e = (let _151_372 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _151_372 us))
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

let e = (let _151_373 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _151_373 us))
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

let g = (let _151_374 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _151_374))
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

let _58_976 = (let _151_376 = (let _151_375 = (FStar_Syntax_Syntax.mk_binder x)
in (_151_375)::[])
in (FStar_Syntax_Subst.open_term _151_376 phi))
in (match (_58_976) with
| (x, phi) -> begin
(

let env0 = env
in (

let _58_981 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_981) with
| (env, _58_980) -> begin
(

let _58_986 = (let _151_377 = (FStar_List.hd x)
in (tc_binder env _151_377))
in (match (_58_986) with
| (x, env, f1, u) -> begin
(

let _58_987 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_380 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _151_379 = (FStar_Syntax_Print.term_to_string phi)
in (let _151_378 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _151_380 _151_379 _151_378))))
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

let g = (let _151_381 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _151_381))
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
(let _151_382 = (FStar_Syntax_Print.term_to_string (

let _58_1010 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))); FStar_Syntax_Syntax.tk = _58_1010.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _58_1010.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_1010.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _151_382))
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
(let _151_385 = (let _151_384 = (FStar_Syntax_Print.term_to_string top)
in (let _151_383 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" _151_384 _151_383)))
in (FStar_All.failwith _151_385))
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
(let _151_390 = (FStar_Syntax_Syntax.mk_Total t)
in ((_151_390), (u), (g)))
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
(let _151_391 = (FStar_Syntax_Syntax.mk_GTotal t)
in ((_151_391), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (

let tc = (let _151_393 = (let _151_392 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_151_392)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _151_393 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let _58_1083 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_58_1083) with
| (tc, _58_1081, f) -> begin
(

let _58_1087 = (FStar_Syntax_Util.head_and_args tc)
in (match (_58_1087) with
| (_58_1085, args) -> begin
(

let _58_1090 = (let _151_395 = (FStar_List.hd args)
in (let _151_394 = (FStar_List.tl args)
in ((_151_395), (_151_394))))
in (match (_58_1090) with
| (res, args) -> begin
(

let _58_1106 = (let _151_397 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _58_5 -> (match (_58_5) with
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
in (FStar_All.pipe_right _151_397 FStar_List.unzip))
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
in (let _151_399 = (FStar_Syntax_Syntax.mk_Comp (

let _58_1121 = c
in {FStar_Syntax_Syntax.effect_name = _58_1121.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _58_1121.FStar_Syntax_Syntax.flags}))
in (let _151_398 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((_151_399), (u), (_151_398)))))
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
(let _151_404 = (aux u)
in FStar_Syntax_Syntax.U_succ (_151_404))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _151_405 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_151_405))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _151_409 = (let _151_408 = (let _151_407 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _151_406 = (FStar_TypeChecker_Env.get_range env)
in ((_151_407), (_151_406))))
in FStar_Syntax_Syntax.Error (_151_408))
in (Prims.raise _151_409))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _151_410 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_410 Prims.snd))
end
| _58_1144 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _151_419 = (let _151_418 = (let _151_417 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in ((_151_417), (top.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_151_418))
in (Prims.raise _151_419)))
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
(let _151_436 = (let _151_435 = (let _151_434 = (let _151_432 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _151_432))
in (let _151_433 = (FStar_Syntax_Syntax.range_of_bv hd)
in ((_151_434), (_151_433))))
in FStar_Syntax_Syntax.Error (_151_435))
in (Prims.raise _151_436))
end
| _58_1192 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _58_1210 = (match ((let _151_437 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _151_437.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| _58_1198 -> begin
(

let _58_1199 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_438 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _151_438))
end else begin
()
end
in (

let _58_1205 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_58_1205) with
| (t, _58_1203, g1) -> begin
(

let g2 = (let _151_440 = (FStar_TypeChecker_Env.get_range env)
in (let _151_439 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _151_440 "Type annotation on parameter incompatible with the expected type" _151_439)))
in (

let g = (let _151_441 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _151_441))
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

let subst = (let _151_442 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _151_442))
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

let _58_1257 = (match ((let _151_449 = (FStar_Syntax_Subst.compress body)
in _151_449.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _58_1244) -> begin
(

let _58_1251 = (tc_comp envbody c)
in (match (_58_1251) with
| (c, _58_1249, g') -> begin
(let _151_450 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((Some (c)), (body), (_151_450)))
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

let rec as_function_typ = (fun norm t -> (match ((let _151_455 = (FStar_Syntax_Subst.compress t)
in _151_455.FStar_Syntax_Syntax.n)) with
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
(let _151_466 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in ((env), (bs), (guard), (_151_466)))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (let _151_467 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _151_467))
in (let _151_468 = (FStar_Syntax_Subst.subst_comp subst c)
in ((env), (bs), (guard), (_151_468))))
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
(let _151_470 = (let _151_469 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env), ((FStar_List.append bs bs')), (more), (_151_469), (subst)))
in (handle_more _151_470 c_expected))
end))
end
| _58_1350 -> begin
(let _151_472 = (let _151_471 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _151_471))
in (fail _151_472 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _151_473 = (check_binders env bs bs_expected)
in (handle_more _151_473 c_expected))))
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

let _58_1370 = (let _151_483 = (let _151_482 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _151_482 Prims.fst))
in (tc_term _151_483 t))
in (match (_58_1370) with
| (t, _58_1367, _58_1369) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l (([]), (t)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _151_484 = (FStar_Syntax_Syntax.mk_binder (

let _58_1374 = x
in {FStar_Syntax_Syntax.ppname = _58_1374.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1374.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_151_484)::letrec_binders)
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
(let _151_485 = (unfold_whnf env t)
in (as_function_typ true _151_485))
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
(let _151_486 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _151_486 (if env.FStar_TypeChecker_Env.top_level then begin
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
(let _151_489 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _151_488 = (let _151_487 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _151_487))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _151_489 _151_488)))
end else begin
()
end
in (

let _58_1431 = (let _151_491 = (let _151_490 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body), (_151_490)))
in (check_expected_effect (

let _58_1426 = envbody
in {FStar_TypeChecker_Env.solver = _58_1426.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1426.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1426.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1426.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1426.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1426.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1426.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1426.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1426.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1426.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1426.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1426.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1426.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1426.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1426.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1426.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1426.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1426.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1426.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1426.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1426.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1426.FStar_TypeChecker_Env.qname_and_index}) c_opt _151_491))
in (match (_58_1431) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(let _151_492 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _151_492))
end else begin
(

let guard = (let _151_493 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) _151_493))
in guard)
end
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _151_496 = (let _151_495 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _151_494 -> FStar_Util.Inl (_151_494)))
in Some (_151_495))
in (FStar_Syntax_Util.abs bs body _151_496))
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
(let _151_497 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in ((e), (_151_497)))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_58_1449) with
| (e, guard') -> begin
(let _151_498 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((e), (t), (_151_498)))
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
(let _151_507 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _151_506 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _151_507 _151_506)))
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
(let _151_523 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _151_523 cres))
end else begin
(

let _58_1502 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_526 = (FStar_Syntax_Print.term_to_string head)
in (let _151_525 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _151_524 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _151_526 _151_525 _151_524))))
end else begin
()
end
in cres)
end
in ((cres), (g))))))
end
| _58_1506 -> begin
(

let g = (let _151_527 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right _151_527 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _151_532 = (let _151_531 = (let _151_530 = (let _151_529 = (let _151_528 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _151_528))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _151_529))
in (FStar_Syntax_Syntax.mk_Total _151_530))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_531))
in ((_151_532), (g))))
end)
in (match (_58_1510) with
| (cres, guard) -> begin
(

let _58_1511 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_533 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _151_533))
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

let arg = (let _151_545 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (_151_545)))
in (let _151_547 = (let _151_546 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst), ((((arg), (None), (None)))::outargs), ((arg)::arg_rets), (_151_546), (fvs)))
in (tc_args head_info _151_547 rest args))))
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
(let _151_548 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _151_548))
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
(let _151_551 = (FStar_Syntax_Print.tag_of_term e)
in (let _151_550 = (FStar_Syntax_Print.term_to_string e)
in (let _151_549 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _151_551 _151_550 _151_549))))
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

let subst = (let _151_552 = (FStar_List.hd bs)
in (maybe_extend_subst subst _151_552 e))
in (tc_args head_info ((subst), ((((arg), (None), (None)))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(

let subst = (let _151_553 = (FStar_List.hd bs)
in (maybe_extend_subst subst _151_553 e))
in (tc_args head_info ((subst), ((((arg), (Some (x)), (Some (c))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (let _151_554 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _151_554)) then begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _151_555 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _151_555))
in (tc_args head_info ((subst), ((((arg), (Some (newx)), (Some (c))))::outargs), ((arg')::arg_rets), (g), (fvs)) rest rest')))
end else begin
(let _151_559 = (let _151_558 = (let _151_557 = (let _151_556 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _151_556))
in (_151_557)::arg_rets)
in ((subst), ((((arg), (Some (x)), (Some (c))))::outargs), (_151_558), (g), ((x)::fvs)))
in (tc_args head_info _151_559 rest rest'))
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

let tres = (let _151_564 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _151_564 FStar_Syntax_Util.unrefine))
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
(let _151_565 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _151_565))
end else begin
()
end
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args)))
end))
end
| _58_1660 when (not (norm)) -> begin
(let _151_566 = (unfold_whnf env tres)
in (aux true _151_566))
end
| _58_1662 -> begin
(let _151_572 = (let _151_571 = (let _151_570 = (let _151_568 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (let _151_567 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _151_568 _151_567)))
in (let _151_569 = (FStar_Syntax_Syntax.argpos arg)
in ((_151_570), (_151_569))))
in FStar_Syntax_Syntax.Error (_151_571))
in (Prims.raise _151_572))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (match ((let _151_577 = (FStar_Syntax_Util.unrefine tf)
in _151_577.FStar_Syntax_Syntax.n)) with
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
(let _151_582 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e), (imp)))::args), ((((e.FStar_Syntax_Syntax.pos), (c)))::comps), (_151_582)))
end))
end))
end))
in (

let _58_1703 = (tc_args env args)
in (match (_58_1703) with
| (args, comps, g_args) -> begin
(

let bs = (let _151_584 = (FStar_All.pipe_right comps (FStar_List.map (fun _58_1707 -> (match (_58_1707) with
| (_58_1705, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks _151_584))
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
(match ((let _151_599 = (FStar_Syntax_Subst.compress t)
in _151_599.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_58_1719) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _58_1724 -> begin
ml_or_tot
end)
end)
in (

let cres = (let _151_604 = (let _151_603 = (let _151_602 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_602 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _151_603))
in (ml_or_tot _151_604 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (

let _58_1728 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _151_607 = (FStar_Syntax_Print.term_to_string head)
in (let _151_606 = (FStar_Syntax_Print.term_to_string tf)
in (let _151_605 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _151_607 _151_606 _151_605))))
end else begin
()
end
in (

let _58_1730 = (let _151_608 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _151_608))
in (

let comp = (let _151_611 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _58_1734 out -> (match (_58_1734) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c ((None), (out)))
end)) ((((head.FStar_Syntax_Syntax.pos), (chead)))::comps) _151_611))
in (let _151_613 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _151_612 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((_151_613), (comp), (_151_612))))))))))))
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
(let _151_614 = (unfold_whnf env tf)
in (check_function_app true _151_614))
end else begin
(let _151_617 = (let _151_616 = (let _151_615 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in ((_151_615), (head.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_151_616))
in (Prims.raise _151_617))
end
end))
in (let _151_619 = (let _151_618 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _151_618))
in (check_function_app false _151_619))))))))))
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

let g = (let _151_629 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _151_629 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _151_633 = (let _151_631 = (let _151_630 = (FStar_Syntax_Syntax.as_arg e)
in (_151_630)::[])
in (FStar_List.append seen _151_631))
in (let _151_632 = (FStar_TypeChecker_Rel.conj_guard guard g)
in ((_151_633), (_151_632), (ghost)))))))
end)))
end)) (([]), (g_head), (false)) args bs)
in (match (_58_1782) with
| (args, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = if ghost then begin
(let _151_634 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _151_634 FStar_Syntax_Util.lcomp_of_comp))
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
(let _151_646 = (FStar_Syntax_Print.pat_to_string p0)
in (let _151_645 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _151_646 _151_645)))
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

let _58_1856 = (let _151_669 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _58_1822 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_649 = (FStar_Syntax_Print.term_to_string e)
in (let _151_648 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _151_649 _151_648)))
end else begin
()
end
in (

let _58_1827 = (tc_term env1 e)
in (match (_58_1827) with
| (e, lc, g) -> begin
(

let _58_1828 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_651 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _151_650 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _151_651 _151_650)))
end else begin
()
end
in (

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let _58_1834 = (let _151_652 = (FStar_TypeChecker_Rel.discharge_guard env (

let _58_1832 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_1832.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_1832.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_1832.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _151_652 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _151_657 = (let _151_656 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _151_656 (FStar_List.map (fun _58_1842 -> (match (_58_1842) with
| (u, _58_1841) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _151_657 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _58_1850 = if (let _151_658 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _151_658)) then begin
(

let unresolved = (let _151_659 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _151_659 FStar_Util.set_elements))
in (let _151_667 = (let _151_666 = (let _151_665 = (let _151_664 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _151_663 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _151_662 = (let _151_661 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _58_1849 -> (match (_58_1849) with
| (u, _58_1848) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _151_661 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _151_664 _151_663 _151_662))))
in ((_151_665), (p.FStar_Syntax_Syntax.p)))
in FStar_Syntax_Syntax.Error (_151_666))
in (Prims.raise _151_667)))
end else begin
()
end
in (

let _58_1852 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _151_668 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _151_668))
end else begin
()
end
in ((e), (e'))))))))))))
end))))))
in (FStar_All.pipe_right _151_669 FStar_List.unzip))
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

let _58_1863 = (let _151_670 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _151_670 FStar_TypeChecker_Env.clear_expected_typ))
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

let _58_1876 = (let _151_671 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _151_671 e))
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
(let _151_673 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _151_672 -> Some (_151_672)) _151_673))
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
(let _151_677 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _151_676 -> Some (_151_676)) _151_677))
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
in (let _151_680 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _151_679 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((_151_680), (_151_679))))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (let _151_681 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_151_681))
in (let _151_684 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _151_683 = (let _151_682 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _151_682 g_when))
in ((_151_684), (_151_683))))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _151_685 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in ((_151_685), (g_when)))))
end)
in (match (_58_1936) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _151_687 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _151_686 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in ((_151_687), (_151_686), (g_branch)))))
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

let discriminate = (fun scrutinee_tm f -> if ((let _151_697 = (let _151_696 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _151_696))
in (FStar_List.length _151_697)) > 1) then begin
(

let disc = (let _151_698 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _151_698 FStar_Syntax_Syntax.Delta_equational None))
in (

let disc = (let _151_700 = (let _151_699 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_151_699)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _151_700 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _151_701 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_151_701)::[])))
end else begin
[]
end)
in (

let fail = (fun _58_1951 -> (match (()) with
| () -> begin
(let _151_707 = (let _151_706 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _151_705 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _151_704 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _151_706 _151_705 _151_704))))
in (FStar_All.failwith _151_707))
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

let pat_exp = (let _151_710 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _151_710 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_58_1987) -> begin
(let _151_715 = (let _151_714 = (let _151_713 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _151_712 = (let _151_711 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_151_711)::[])
in (_151_713)::_151_712))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _151_714 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_151_715)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _151_716 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _151_716))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(

let sub_term_guards = (let _151_723 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _58_2005 -> (match (_58_2005) with
| (ei, _58_2004) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _58_2009 -> begin
(

let sub_term = (let _151_722 = (let _151_719 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _151_719 FStar_Syntax_Syntax.Delta_equational None))
in (let _151_721 = (let _151_720 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_151_720)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _151_722 _151_721 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _151_723 FStar_List.flatten))
in (let _151_724 = (discriminate scrutinee_tm f)
in (FStar_List.append _151_724 sub_term_guards)))
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

let t = (let _151_729 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _151_729))
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

let branch_guard = (let _151_730 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _151_730 FStar_Syntax_Util.mk_disj_l))
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
(let _151_731 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _151_731))
end else begin
()
end
in (let _151_732 = (FStar_Syntax_Subst.close_branch ((pattern), (when_clause), (branch_exp)))
in ((_151_732), (branch_guard), (c), (guard))))))
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

let g1 = (let _151_735 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _151_735 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _58_2059 = (let _151_739 = (let _151_738 = (let _151_737 = (let _151_736 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (_151_736)))
in (_151_737)::[])
in (FStar_TypeChecker_Util.generalize env _151_738))
in (FStar_List.hd _151_739))
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
(let _151_740 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _151_740 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _151_741 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) None e2.FStar_Syntax_Syntax.pos)
in ((_151_741), (c1))))
end
end))
end else begin
(

let _58_2070 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _151_742 = (c1.FStar_Syntax_Syntax.comp ())
in ((e2), (_151_742))))
end
in (match (_58_2074) with
| (e2, c1) -> begin
(

let cres = (let _151_743 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_743))
in (

let _58_2076 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _151_744 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((_151_744), (cres), (FStar_TypeChecker_Rel.trivial_guard))))))
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

let _58_2100 = (let _151_748 = (let _151_747 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _151_747 Prims.fst))
in (check_let_bound_def false _151_748 lb))
in (match (_58_2100) with
| (e1, _58_2096, c1, g1, annotated) -> begin
(

let x = (

let _58_2101 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_2101.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2101.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let _58_2107 = (let _151_750 = (let _151_749 = (FStar_Syntax_Syntax.mk_binder x)
in (_151_749)::[])
in (FStar_Syntax_Subst.open_term _151_750 e2))
in (match (_58_2107) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _58_2113 = (let _151_751 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _151_751 e2))
in (match (_58_2113) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (x)), (c2)))
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e2 = (FStar_TypeChecker_Util.maybe_lift env e2 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e = (let _151_754 = (let _151_753 = (let _151_752 = (FStar_Syntax_Subst.close xb e2)
in ((((false), ((lb)::[]))), (_151_752)))
in FStar_Syntax_Syntax.Tm_let (_151_753))
in (FStar_Syntax_Syntax.mk _151_754 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (let _151_757 = (let _151_756 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _151_756 e1))
in (FStar_All.pipe_left (fun _151_755 -> FStar_TypeChecker_Common.NonTrivial (_151_755)) _151_757))
in (

let g2 = (let _151_759 = (let _151_758 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _151_758 g2))
in (FStar_TypeChecker_Rel.close_guard xb _151_759))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if (let _151_760 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome _151_760)) then begin
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

let g_lbs = (let _151_763 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _151_763 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _151_766 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _151_766 (fun _151_765 -> Some (_151_765))))
in (

let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(

let ecs = (let _151_770 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _151_769 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (_151_769))))))
in (FStar_TypeChecker_Util.generalize env _151_770))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _58_2157 -> (match (_58_2157) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _151_772 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_772))
in (

let _58_2160 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _58_2164 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_2164) with
| (lbs, e2) -> begin
(let _151_774 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _151_773 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in ((_151_774), (cres), (_151_773))))
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

let _58_2244 = (let _151_786 = (let _151_785 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _151_785))
in (tc_check_tot_or_gtot_term (

let _58_2238 = env0
in {FStar_TypeChecker_Env.solver = _58_2238.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2238.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2238.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2238.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2238.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2238.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2238.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2238.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2238.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2238.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2238.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2238.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2238.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2238.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _58_2238.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2238.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2238.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2238.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2238.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2238.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2238.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2238.FStar_TypeChecker_Env.qname_and_index}) t _151_786))
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

let _58_2269 = (let _151_791 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _58_2263 = (let _151_790 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _151_790 lb.FStar_Syntax_Syntax.lbdef))
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
in (FStar_All.pipe_right _151_791 FStar_List.unzip))
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

let _58_2295 = (let _151_798 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_2292 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _151_798 e1 c1 wf_annot))
in (match (_58_2295) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _58_2297 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _151_799 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _151_799))
end else begin
()
end
in (let _151_800 = (FStar_Option.isSome topt)
in ((e1), (univ_vars), (c1), (g1), (_151_800)))))
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
(let _151_804 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars), (_151_804)))
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
(let _151_807 = (let _151_805 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _151_805))
in (let _151_806 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _151_807 _151_806)))
end else begin
()
end
in (

let t = (norm env1 t)
in (let _151_808 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (g), (univ_vars), (_151_808)))))
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
(let _151_812 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _151_811 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _151_812 _151_811)))
end else begin
()
end
in (let _151_813 = (push_binding env x)
in ((x), (_151_813), (g), (u)))))
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
(let _151_821 = (let _151_820 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _151_820))
in (((b)::bs), (env'), (_151_821), ((u)::us)))
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
(let _151_830 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t), (imp)))::args), (_151_830)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p _58_2379 -> (match (_58_2379) with
| (pats, g) -> begin
(

let _58_2382 = (tc_args env p)
in (match (_58_2382) with
| (args, g') -> begin
(let _151_833 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats), (_151_833)))
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
(let _151_836 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in ((_151_836), (false)))
end else begin
(let _151_837 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in ((_151_837), (true)))
end
in (match (_58_2394) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _151_838 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (_151_838)))
end
| _58_2398 -> begin
if allow_ghost then begin
(let _151_841 = (let _151_840 = (let _151_839 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in ((_151_839), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_151_840))
in (Prims.raise _151_841))
end else begin
(let _151_844 = (let _151_843 = (let _151_842 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in ((_151_842), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_151_843))
in (Prims.raise _151_844))
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


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _151_862 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _151_862)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _151_866 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (([]), (_151_866)))))


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
(let _151_881 = (let _151_880 = (let _151_879 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in ((_151_879), ((FStar_Ident.range_of_lid m))))
in FStar_Syntax_Syntax.Error (_151_880))
in (Prims.raise _151_881))
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
(match ((let _151_888 = (FStar_Syntax_Subst.compress t')
in _151_888.FStar_Syntax_Syntax.n)) with
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
in (let _151_931 = (op ed.FStar_Syntax_Syntax.ret_wp)
in (let _151_930 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _151_929 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _151_928 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _151_927 = (op ed.FStar_Syntax_Syntax.stronger)
in (let _151_926 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _151_925 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _151_924 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _151_923 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _151_922 = (op ed.FStar_Syntax_Syntax.trivial)
in (let _151_921 = (let _151_912 = (op (([]), (ed.FStar_Syntax_Syntax.repr)))
in (Prims.snd _151_912))
in (let _151_920 = (op ed.FStar_Syntax_Syntax.return_repr)
in (let _151_919 = (op ed.FStar_Syntax_Syntax.bind_repr)
in (let _151_918 = (FStar_List.map (fun a -> (

let _58_2510 = a
in (let _151_917 = (let _151_914 = (op (([]), (a.FStar_Syntax_Syntax.action_defn)))
in (Prims.snd _151_914))
in (let _151_916 = (let _151_915 = (op (([]), (a.FStar_Syntax_Syntax.action_typ)))
in (Prims.snd _151_915))
in {FStar_Syntax_Syntax.action_name = _58_2510.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = _58_2510.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _151_917; FStar_Syntax_Syntax.action_typ = _151_916})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = _58_2507.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2507.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _58_2507.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _58_2507.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _58_2507.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _151_931; FStar_Syntax_Syntax.bind_wp = _151_930; FStar_Syntax_Syntax.if_then_else = _151_929; FStar_Syntax_Syntax.ite_wp = _151_928; FStar_Syntax_Syntax.stronger = _151_927; FStar_Syntax_Syntax.close_wp = _151_926; FStar_Syntax_Syntax.assert_p = _151_925; FStar_Syntax_Syntax.assume_p = _151_924; FStar_Syntax_Syntax.null_wp = _151_923; FStar_Syntax_Syntax.trivial = _151_922; FStar_Syntax_Syntax.repr = _151_921; FStar_Syntax_Syntax.return_repr = _151_920; FStar_Syntax_Syntax.bind_repr = _151_919; FStar_Syntax_Syntax.actions = _151_918}))))))))))))))))
end)
in (

let wp_with_fresh_result_type = (fun env mname signature -> (

let fail = (fun t -> (let _151_942 = (let _151_941 = (let _151_940 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in ((_151_940), ((FStar_Ident.range_of_lid mname))))
in FStar_Syntax_Syntax.Error (_151_941))
in (Prims.raise _151_942)))
in (match ((let _151_943 = (FStar_Syntax_Subst.compress signature)
in _151_943.FStar_Syntax_Syntax.n)) with
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

let env = (let _151_946 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _151_946))
in (

let _58_2547 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _151_952 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _151_951 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _151_950 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _151_949 = (let _151_947 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Print.term_to_string _151_947))
in (let _151_948 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort)
in (FStar_Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n" _151_952 _151_951 _151_950 _151_949 _151_948))))))
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

let expected_k = (let _151_964 = (let _151_962 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_961 = (let _151_960 = (let _151_959 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _151_959))
in (_151_960)::[])
in (_151_962)::_151_961))
in (let _151_963 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _151_964 _151_963)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let _58_2560 = (fresh_effect_signature ())
in (match (_58_2560) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _151_968 = (let _151_966 = (let _151_965 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _151_965))
in (_151_966)::[])
in (let _151_967 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _151_968 _151_967)))
in (

let expected_k = (let _151_979 = (let _151_977 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _151_976 = (let _151_975 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_974 = (let _151_973 = (FStar_Syntax_Syntax.mk_binder b)
in (let _151_972 = (let _151_971 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _151_970 = (let _151_969 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (_151_969)::[])
in (_151_971)::_151_970))
in (_151_973)::_151_972))
in (_151_975)::_151_974))
in (_151_977)::_151_976))
in (let _151_978 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _151_979 _151_978)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (let _151_981 = (let _151_980 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_980 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _151_981))
in (

let expected_k = (let _151_990 = (let _151_988 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_987 = (let _151_986 = (FStar_Syntax_Syntax.mk_binder p)
in (let _151_985 = (let _151_984 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _151_983 = (let _151_982 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_982)::[])
in (_151_984)::_151_983))
in (_151_986)::_151_985))
in (_151_988)::_151_987))
in (let _151_989 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_990 _151_989)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (let _151_995 = (let _151_993 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_992 = (let _151_991 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_991)::[])
in (_151_993)::_151_992))
in (let _151_994 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_995 _151_994)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let _58_2572 = (FStar_Syntax_Util.type_u ())
in (match (_58_2572) with
| (t, _58_2571) -> begin
(

let expected_k = (let _151_1002 = (let _151_1000 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_999 = (let _151_998 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _151_997 = (let _151_996 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_996)::[])
in (_151_998)::_151_997))
in (_151_1000)::_151_999))
in (let _151_1001 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _151_1002 _151_1001)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (let _151_1004 = (let _151_1003 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_1003 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _151_1004))
in (

let b_wp_a = (let _151_1008 = (let _151_1006 = (let _151_1005 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _151_1005))
in (_151_1006)::[])
in (let _151_1007 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_1008 _151_1007)))
in (

let expected_k = (let _151_1015 = (let _151_1013 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1012 = (let _151_1011 = (FStar_Syntax_Syntax.mk_binder b)
in (let _151_1010 = (let _151_1009 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_151_1009)::[])
in (_151_1011)::_151_1010))
in (_151_1013)::_151_1012))
in (let _151_1014 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_1015 _151_1014)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (let _151_1024 = (let _151_1022 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1021 = (let _151_1020 = (let _151_1017 = (let _151_1016 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_1016 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _151_1017))
in (let _151_1019 = (let _151_1018 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_1018)::[])
in (_151_1020)::_151_1019))
in (_151_1022)::_151_1021))
in (let _151_1023 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_1024 _151_1023)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _151_1033 = (let _151_1031 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1030 = (let _151_1029 = (let _151_1026 = (let _151_1025 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _151_1025 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _151_1026))
in (let _151_1028 = (let _151_1027 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_1027)::[])
in (_151_1029)::_151_1028))
in (_151_1031)::_151_1030))
in (let _151_1032 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_1033 _151_1032)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _151_1036 = (let _151_1034 = (FStar_Syntax_Syntax.mk_binder a)
in (_151_1034)::[])
in (let _151_1035 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_1036 _151_1035)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let _58_2588 = (FStar_Syntax_Util.type_u ())
in (match (_58_2588) with
| (t, _58_2587) -> begin
(

let expected_k = (let _151_1041 = (let _151_1039 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1038 = (let _151_1037 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_1037)::[])
in (_151_1039)::_151_1038))
in (let _151_1040 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _151_1041 _151_1040)))
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

let expected_k = (let _151_1046 = (let _151_1044 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1043 = (let _151_1042 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_1042)::[])
in (_151_1044)::_151_1043))
in (let _151_1045 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _151_1046 _151_1045)))
in (tc_check_trivial_guard env ed.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (

let repr = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env repr)
in (let _151_1056 = (let _151_1055 = (let _151_1054 = (let _151_1053 = (FStar_Syntax_Syntax.as_arg t)
in (let _151_1052 = (let _151_1051 = (FStar_Syntax_Syntax.as_arg wp)
in (_151_1051)::[])
in (_151_1053)::_151_1052))
in ((repr), (_151_1054)))
in FStar_Syntax_Syntax.Tm_app (_151_1055))
in (FStar_Syntax_Syntax.mk _151_1056 None FStar_Range.dummyRange))))
in (

let mk_repr = (fun a wp -> (let _151_1061 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_repr' _151_1061 wp)))
in (

let destruct_repr = (fun t -> (match ((let _151_1064 = (FStar_Syntax_Subst.compress t)
in _151_1064.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_58_2607, ((t, _58_2614))::((wp, _58_2610))::[]) -> begin
((t), (wp))
end
| _58_2620 -> begin
(FStar_All.failwith "Unexpected repr type")
end))
in (

let bind_repr = (

let r = (let _151_1065 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_0 FStar_Syntax_Syntax.Delta_constant None)
in (FStar_All.pipe_right _151_1065 FStar_Syntax_Syntax.fv_to_tm))
in (

let _58_2624 = (fresh_effect_signature ())
in (match (_58_2624) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _151_1069 = (let _151_1067 = (let _151_1066 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _151_1066))
in (_151_1067)::[])
in (let _151_1068 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _151_1069 _151_1068)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" None a_wp_b)
in (

let x_a = (let _151_1070 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _151_1070))
in (

let wp_g_x = (let _151_1074 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (let _151_1073 = (let _151_1072 = (let _151_1071 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _151_1071))
in (_151_1072)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _151_1074 _151_1073 None FStar_Range.dummyRange)))
in (

let res = (

let wp = (let _151_1086 = (let _151_1075 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right _151_1075 Prims.snd))
in (let _151_1085 = (let _151_1084 = (let _151_1083 = (let _151_1082 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _151_1081 = (let _151_1080 = (FStar_Syntax_Syntax.bv_to_name b)
in (let _151_1079 = (let _151_1078 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (let _151_1077 = (let _151_1076 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (_151_1076)::[])
in (_151_1078)::_151_1077))
in (_151_1080)::_151_1079))
in (_151_1082)::_151_1081))
in (r)::_151_1083)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _151_1084))
in (FStar_Syntax_Syntax.mk_Tm_app _151_1086 _151_1085 None FStar_Range.dummyRange)))
in (mk_repr b wp))
in (

let expected_k = (let _151_1106 = (let _151_1104 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1103 = (let _151_1102 = (FStar_Syntax_Syntax.mk_binder b)
in (let _151_1101 = (let _151_1100 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (let _151_1099 = (let _151_1098 = (let _151_1088 = (let _151_1087 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a _151_1087))
in (FStar_Syntax_Syntax.null_binder _151_1088))
in (let _151_1097 = (let _151_1096 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (let _151_1095 = (let _151_1094 = (let _151_1093 = (let _151_1092 = (let _151_1089 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_151_1089)::[])
in (let _151_1091 = (let _151_1090 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _151_1090))
in (FStar_Syntax_Util.arrow _151_1092 _151_1091)))
in (FStar_Syntax_Syntax.null_binder _151_1093))
in (_151_1094)::[])
in (_151_1096)::_151_1095))
in (_151_1098)::_151_1097))
in (_151_1100)::_151_1099))
in (_151_1102)::_151_1101))
in (_151_1104)::_151_1103))
in (let _151_1105 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _151_1106 _151_1105)))
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

let x_a = (let _151_1107 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _151_1107))
in (

let res = (

let wp = (let _151_1114 = (let _151_1108 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right _151_1108 Prims.snd))
in (let _151_1113 = (let _151_1112 = (let _151_1111 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _151_1110 = (let _151_1109 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (_151_1109)::[])
in (_151_1111)::_151_1110))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _151_1112))
in (FStar_Syntax_Syntax.mk_Tm_app _151_1114 _151_1113 None FStar_Range.dummyRange)))
in (mk_repr a wp))
in (

let expected_k = (let _151_1119 = (let _151_1117 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1116 = (let _151_1115 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_151_1115)::[])
in (_151_1117)::_151_1116))
in (let _151_1118 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _151_1119 _151_1118)))
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
(let _151_1123 = (FStar_Syntax_Print.term_to_string act.FStar_Syntax_Syntax.action_defn)
in (let _151_1122 = (FStar_Syntax_Print.term_to_string act_typ)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" (FStar_Ident.text_of_lid act.FStar_Syntax_Syntax.action_name) _151_1123 _151_1122)))
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

let k = (let _151_1124 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs _151_1124))
in (

let _58_2695 = (tc_tot_or_gtot_term env k)
in (match (_58_2695) with
| (k, _58_2693, g) -> begin
((k), (g))
end))))
end))
end
| _58_2697 -> begin
(let _151_1129 = (let _151_1128 = (let _151_1127 = (let _151_1126 = (FStar_Syntax_Print.term_to_string act_typ)
in (let _151_1125 = (FStar_Syntax_Print.tag_of_term act_typ)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" _151_1126 _151_1125)))
in ((_151_1127), (act_defn.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_151_1128))
in (Prims.raise _151_1129))
end))
in (match (_58_2700) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env act_typ expected_k)
in (

let _58_2702 = (let _151_1132 = (let _151_1131 = (let _151_1130 = (FStar_TypeChecker_Rel.conj_guard g_t g)
in (FStar_TypeChecker_Rel.conj_guard g_k _151_1130))
in (FStar_TypeChecker_Rel.conj_guard g_a _151_1131))
in (FStar_TypeChecker_Rel.force_trivial_guard env _151_1132))
in (

let act_typ = (match ((let _151_1133 = (FStar_Syntax_Subst.compress expected_k)
in _151_1133.FStar_Syntax_Syntax.n)) with
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

let c = (let _151_1135 = (let _151_1134 = (FStar_Syntax_Syntax.as_arg wp)
in (_151_1134)::[])
in {FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a; FStar_Syntax_Syntax.effect_args = _151_1135; FStar_Syntax_Syntax.flags = []})
in (let _151_1136 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Util.arrow bs _151_1136)))
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

let t = (let _151_1137 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _151_1137))
in (

let _58_2733 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_58_2733) with
| (univs, t) -> begin
(

let signature = (match ((let _151_1139 = (let _151_1138 = (FStar_Syntax_Subst.compress t)
in _151_1138.FStar_Syntax_Syntax.n)
in ((effect_params), (_151_1139)))) with
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

let ts = (let _151_1144 = (FStar_Syntax_Subst.close_tscheme effect_params ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _151_1144))
in (

let _58_2753 = if (((n > 0) && (not ((FStar_Syntax_Util.is_unknown (Prims.snd ts))))) && ((FStar_List.length (Prims.fst ts)) <> n)) then begin
(let _151_1147 = (let _151_1146 = (FStar_Util.string_of_int n)
in (let _151_1145 = (FStar_Syntax_Print.tscheme_to_string ts)
in (FStar_Util.format2 "The effect combinator is not universe-polymorphic enough (n=%s) (%s)" _151_1146 _151_1145)))
in (FStar_All.failwith _151_1147))
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
in (let _151_1164 = (close 0 return_wp)
in (let _151_1163 = (close 1 bind_wp)
in (let _151_1162 = (close 0 if_then_else)
in (let _151_1161 = (close 0 ite_wp)
in (let _151_1160 = (close 0 stronger)
in (let _151_1159 = (close 1 close_wp)
in (let _151_1158 = (close 0 assert_p)
in (let _151_1157 = (close 0 assume_p)
in (let _151_1156 = (close 0 null_wp)
in (let _151_1155 = (close 0 trivial_wp)
in (let _151_1154 = (let _151_1150 = (close 0 (([]), (repr)))
in (Prims.snd _151_1150))
in (let _151_1153 = (close 0 return_repr)
in (let _151_1152 = (close 1 bind_repr)
in (let _151_1151 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.qualifiers = _58_2769.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2769.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _151_1164; FStar_Syntax_Syntax.bind_wp = _151_1163; FStar_Syntax_Syntax.if_then_else = _151_1162; FStar_Syntax_Syntax.ite_wp = _151_1161; FStar_Syntax_Syntax.stronger = _151_1160; FStar_Syntax_Syntax.close_wp = _151_1159; FStar_Syntax_Syntax.assert_p = _151_1158; FStar_Syntax_Syntax.assume_p = _151_1157; FStar_Syntax_Syntax.null_wp = _151_1156; FStar_Syntax_Syntax.trivial = _151_1155; FStar_Syntax_Syntax.repr = _151_1154; FStar_Syntax_Syntax.return_repr = _151_1153; FStar_Syntax_Syntax.bind_repr = _151_1152; FStar_Syntax_Syntax.actions = _151_1151})))))))))))))))
in (

let _58_2772 = if ((FStar_TypeChecker_Env.debug env FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ED")))) then begin
(let _151_1165 = (FStar_Syntax_Print.eff_decl_to_string false ed)
in (FStar_Util.print_string _151_1165))
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
(let _151_1170 = (

let _58_2791 = bv
in (let _151_1169 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _58_2791.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2791.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _151_1169}))
in ((_151_1170), (qual)))
end)) effect_binders)
in (

let _58_2806 = (match ((let _151_1171 = (FStar_Syntax_Subst.compress signature_un)
in _151_1171.FStar_Syntax_Syntax.n)) with
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
(let _151_1180 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Term has been %s-transformed to:\n%s\n----------\n" s _151_1180))
end else begin
()
end
in (

let _58_2827 = (tc_term env t)
in (match (_58_2827) with
| (t', _58_2824, _58_2826) -> begin
(

let _58_2828 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _151_1181 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print1 "Re-checked; got:\n%s\n----------\n" _151_1181))
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
(let _151_1184 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" _151_1184))
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

let wp_a = (let _151_1191 = (let _151_1190 = (let _151_1189 = (let _151_1188 = (let _151_1187 = (let _151_1186 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _151_1185 = (FStar_Syntax_Syntax.as_implicit false)
in ((_151_1186), (_151_1185))))
in (_151_1187)::[])
in ((wp_type), (_151_1188)))
in FStar_Syntax_Syntax.Tm_app (_151_1189))
in (mk _151_1190))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _151_1191))
in (

let effect_signature = (

let binders = (let _151_1196 = (let _151_1192 = (FStar_Syntax_Syntax.as_implicit false)
in ((a), (_151_1192)))
in (let _151_1195 = (let _151_1194 = (let _151_1193 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" None wp_a)
in (FStar_All.pipe_right _151_1193 FStar_Syntax_Syntax.mk_binder))
in (_151_1194)::[])
in (_151_1196)::_151_1195))
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

let return_wp = (match ((let _151_1203 = (FStar_Syntax_Subst.compress return_wp)
in _151_1203.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(let _151_1204 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) _151_1204 (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_GTot_lid)))))
end
| _58_2887 -> begin
(FStar_All.failwith "unexpected shape for return")
end)
in (

let bind_wp = (match ((let _151_1205 = (FStar_Syntax_Subst.compress bind_wp)
in _151_1205.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (let _151_1209 = (let _151_1208 = (let _151_1207 = (let _151_1206 = (mk (FStar_Syntax_Syntax.Tm_fvar (r)))
in (FStar_Syntax_Syntax.null_binder _151_1206))
in (_151_1207)::[])
in (FStar_List.append _151_1208 binders))
in (FStar_Syntax_Util.abs _151_1209 body what)))
end
| _58_2896 -> begin
(FStar_All.failwith "unexpected shape for bind")
end)
in (

let apply_close = (fun t -> if ((FStar_List.length effect_binders) = 0) then begin
t
end else begin
(let _151_1216 = (let _151_1215 = (let _151_1214 = (let _151_1213 = (let _151_1212 = (FStar_Syntax_Util.args_of_binders effect_binders)
in (Prims.snd _151_1212))
in ((t), (_151_1213)))
in FStar_Syntax_Syntax.Tm_app (_151_1214))
in (mk _151_1215))
in (FStar_Syntax_Subst.close effect_binders _151_1216))
end)
in (

let register = (fun name item -> (

let _58_2905 = (let _151_1222 = (mk_lid name)
in (let _151_1221 = (FStar_Syntax_Util.abs effect_binders item None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env _151_1222 _151_1221)))
in (match (_58_2905) with
| (sigelt, fv) -> begin
(

let _58_2906 = (let _151_1224 = (let _151_1223 = (FStar_ST.read sigelts)
in (sigelt)::_151_1223)
in (FStar_ST.op_Colon_Equals sigelts _151_1224))
in fv)
end)))
in (

let return_wp = (register "return_wp" return_wp)
in (

let return_elab = (register "return_elab" return_elab)
in (

let bind_wp = (register "bind_wp" bind_wp)
in (

let _58_2911 = (let _151_1226 = (let _151_1225 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::_151_1225)
in (FStar_ST.op_Colon_Equals sigelts _151_1226))
in (

let bind_elab = (register "bind_elab" bind_elab)
in (

let _58_2914 = (let _151_1228 = (let _151_1227 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::_151_1227)
in (FStar_ST.op_Colon_Equals sigelts _151_1228))
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
in (let _151_1234 = (let _151_1233 = (

let _58_2929 = action
in (let _151_1232 = (apply_close action_elab)
in (let _151_1231 = (apply_close action_typ_with_wp)
in {FStar_Syntax_Syntax.action_name = _58_2929.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = _58_2929.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _151_1232; FStar_Syntax_Syntax.action_typ = _151_1231})))
in (_151_1233)::actions)
in ((dmff_env), (_151_1234)))))))
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

let binders = (let _151_1237 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1236 = (let _151_1235 = (FStar_Syntax_Syntax.mk_binder wp)
in (_151_1235)::[])
in (_151_1237)::_151_1236))
in (let _151_1246 = (let _151_1245 = (let _151_1243 = (let _151_1242 = (let _151_1241 = (let _151_1240 = (let _151_1239 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _151_1238 = (FStar_Syntax_Syntax.as_implicit false)
in ((_151_1239), (_151_1238))))
in (_151_1240)::[])
in ((repr), (_151_1241)))
in FStar_Syntax_Syntax.Tm_app (_151_1242))
in (mk _151_1243))
in (let _151_1244 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env _151_1245 _151_1244)))
in (FStar_Syntax_Util.abs binders _151_1246 None))))
in (

let repr = (recheck_debug "FC" env repr)
in (

let repr = (register "repr" repr)
in (

let _58_2965 = (match ((let _151_1247 = (FStar_Syntax_Subst.compress wp_type)
in _151_1247.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (effect_param, arrow, _58_2943) -> begin
(

let _58_2948 = (FStar_Syntax_Subst.open_term effect_param arrow)
in (match (_58_2948) with
| (effect_param, arrow) -> begin
(match ((let _151_1248 = (FStar_Syntax_Subst.compress arrow)
in _151_1248.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let _58_2955 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (_58_2955) with
| (wp_binders, c) -> begin
(

let _58_2958 = (FStar_Util.prefix wp_binders)
in (match (_58_2958) with
| (pre_args, post) -> begin
(let _151_1250 = (FStar_Syntax_Util.arrow pre_args c)
in (let _151_1249 = (FStar_Syntax_Util.abs effect_param (Prims.fst post).FStar_Syntax_Syntax.sort None)
in ((_151_1250), (_151_1249))))
end))
end))
end
| _58_2960 -> begin
(let _151_1252 = (let _151_1251 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" _151_1251))
in (FStar_All.failwith _151_1252))
end)
end))
end
| _58_2962 -> begin
(let _151_1254 = (let _151_1253 = (FStar_Syntax_Print.term_to_string wp_type)
in (FStar_Util.format1 "Impossible: pre/post abs %s" _151_1253))
in (FStar_All.failwith _151_1254))
end)
in (match (_58_2965) with
| (pre, post) -> begin
(

let _58_2966 = (let _151_1255 = (register "pre" pre)
in (Prims.ignore _151_1255))
in (

let _58_2968 = (let _151_1256 = (register "post" post)
in (Prims.ignore _151_1256))
in (

let _58_2970 = (let _151_1257 = (register "wp" wp_type)
in (Prims.ignore _151_1257))
in (

let ed = (

let _58_2972 = ed
in (let _151_1268 = (FStar_Syntax_Subst.close_binders effect_binders)
in (let _151_1267 = (FStar_Syntax_Subst.close effect_binders effect_signature)
in (let _151_1266 = (let _151_1258 = (apply_close return_wp)
in (([]), (_151_1258)))
in (let _151_1265 = (let _151_1259 = (apply_close bind_wp)
in (([]), (_151_1259)))
in (let _151_1264 = (apply_close repr)
in (let _151_1263 = (let _151_1260 = (apply_close return_elab)
in (([]), (_151_1260)))
in (let _151_1262 = (let _151_1261 = (apply_close bind_elab)
in (([]), (_151_1261)))
in {FStar_Syntax_Syntax.qualifiers = _58_2972.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2972.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _58_2972.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _151_1268; FStar_Syntax_Syntax.signature = _151_1267; FStar_Syntax_Syntax.ret_wp = _151_1266; FStar_Syntax_Syntax.bind_wp = _151_1265; FStar_Syntax_Syntax.if_then_else = _58_2972.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _58_2972.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _58_2972.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _58_2972.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _58_2972.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _58_2972.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _58_2972.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _58_2972.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _151_1264; FStar_Syntax_Syntax.return_repr = _151_1263; FStar_Syntax_Syntax.bind_repr = _151_1262; FStar_Syntax_Syntax.actions = actions}))))))))
in (

let _58_2977 = (FStar_TypeChecker_DMFF.gen_wps_for_free env effect_binders a wp_a ed)
in (match (_58_2977) with
| (sigelts', ed) -> begin
(

let _58_2978 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _151_1269 = (FStar_Syntax_Print.eff_decl_to_string true ed)
in (FStar_Util.print_string _151_1269))
end else begin
()
end
in (let _151_1272 = (let _151_1271 = (let _151_1270 = (FStar_ST.read sigelts)
in (FStar_List.rev _151_1270))
in (FStar_List.append _151_1271 sigelts'))
in ((_151_1272), (ed))))
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

let lex_top_t = (let _151_1280 = (let _151_1279 = (let _151_1278 = (let _151_1277 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _151_1277 FStar_Syntax_Syntax.Delta_constant None))
in ((_151_1278), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_151_1279))
in (FStar_Syntax_Syntax.mk _151_1280 None r1))
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

let a = (let _151_1281 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _151_1281))
in (

let hd = (let _151_1282 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _151_1282))
in (

let tl = (let _151_1287 = (let _151_1286 = (let _151_1285 = (let _151_1284 = (let _151_1283 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _151_1283 FStar_Syntax_Syntax.Delta_constant None))
in ((_151_1284), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_151_1285))
in (FStar_Syntax_Syntax.mk _151_1286 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _151_1287))
in (

let res = (let _151_1291 = (let _151_1290 = (let _151_1289 = (let _151_1288 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _151_1288 FStar_Syntax_Syntax.Delta_constant None))
in ((_151_1289), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_151_1290))
in (FStar_Syntax_Syntax.mk _151_1291 None r2))
in (let _151_1292 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (Some (FStar_Syntax_Syntax.imp_tag))))::(((hd), (None)))::(((tl), (None)))::[]) _151_1292))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t), (FStar_Syntax_Const.lex_t_lid), (0), ([]), ([]), (r2)))
in (let _151_1294 = (let _151_1293 = (FStar_TypeChecker_Env.get_range env)
in (((tc)::(dc_lextop)::(dc_lexcons)::[]), ([]), (lids), (_151_1293)))
in FStar_Syntax_Syntax.Sig_bundle (_151_1294)))))))))))))))
end
| _58_3047 -> begin
(let _151_1296 = (let _151_1295 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle (((ses), ([]), (lids), (FStar_Range.dummyRange)))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _151_1295))
in (FStar_All.failwith _151_1296))
end))))
and tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _58_3057 = (FStar_Syntax_Util.type_u ())
in (match (_58_3057) with
| (k, _58_3056) -> begin
(

let phi = (let _151_1302 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _151_1302 (norm env)))
in (

let _58_3059 = (FStar_TypeChecker_Util.check_uvars r phi)
in FStar_Syntax_Syntax.Sig_assume (((lid), (phi), (quals), (r)))))
end))))
and tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _151_1312 = (let _151_1311 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _151_1311))
in (FStar_TypeChecker_Errors.diag r _151_1312)))
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
(let _151_1319 = (let _151_1318 = (let _151_1317 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params _151_1317))
in (FStar_TypeChecker_Rel.discharge_guard env' _151_1318))
in ((t), (_151_1319)))
end))
in (match (_58_3109) with
| (t, guard) -> begin
(

let k = (let _151_1320 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _151_1320))
in (

let _58_3113 = (FStar_Syntax_Util.type_u ())
in (match (_58_3113) with
| (t_type, u) -> begin
(

let _58_3114 = (let _151_1321 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _151_1321))
in (

let t_tc = (let _151_1322 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _151_1322))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _151_1323 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((_151_1323), (FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps), (k), (mutuals), (data), (quals), (r)))), (u), (guard))))))))
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
if (let _151_1336 = (let _151_1335 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _151_1335))
in (FStar_Ident.lid_equals tc_lid _151_1336)) then begin
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

let _58_3195 = (match ((let _151_1338 = (FStar_Syntax_Subst.compress t)
in _151_1338.FStar_Syntax_Syntax.n)) with
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
in (let _151_1341 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _151_1341))))
end))
end
| _58_3192 -> begin
(([]), (t))
end)
in (match (_58_3195) with
| (arguments, result) -> begin
(

let _58_3196 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1344 = (FStar_Syntax_Print.lid_to_string c)
in (let _151_1343 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _151_1342 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _151_1344 _151_1343 _151_1342))))
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

let _58_3214 = (match ((let _151_1345 = (FStar_Syntax_Subst.compress head)
in _151_1345.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _58_3213 -> begin
(let _151_1350 = (let _151_1349 = (let _151_1348 = (let _151_1347 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _151_1346 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _151_1347 _151_1346)))
in ((_151_1348), (r)))
in FStar_Syntax_Syntax.Error (_151_1349))
in (Prims.raise _151_1350))
end)
in (

let g = (FStar_List.fold_left2 (fun g _58_3220 u_x -> (match (_58_3220) with
| (x, _58_3219) -> begin
(

let _58_3222 = ()
in (let _151_1354 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _151_1354)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _151_1358 = (let _151_1356 = (FStar_All.pipe_right tps (FStar_List.map (fun _58_3228 -> (match (_58_3228) with
| (x, _58_3227) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append _151_1356 arguments))
in (let _151_1357 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _151_1358 _151_1357)))
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
(let _151_1369 = (let _151_1368 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _151_1368))
in (FStar_Syntax_Syntax.null_binder _151_1369))
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

let t = (let _151_1371 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _151_1371))
in (

let _58_3281 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1372 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _151_1372))
end else begin
()
end
in (

let _58_3285 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_58_3285) with
| (uvs, t) -> begin
(

let _58_3287 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1376 = (let _151_1374 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _151_1374 (FStar_String.concat ", ")))
in (let _151_1375 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _151_1376 _151_1375)))
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

let _58_3332 = (match ((let _151_1379 = (FStar_Syntax_Subst.compress ty)
in _151_1379.FStar_Syntax_Syntax.n)) with
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
(let _151_1380 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) _151_1380 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
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

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _151_1381 -> FStar_Syntax_Syntax.U_name (_151_1381))))
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

let ty = (let _151_1385 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _151_1385 (FStar_Syntax_Subst.close_univ_vars uvs)))
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
(let _151_1390 = (let _151_1389 = (let _151_1388 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (_151_1388)))
in FStar_Syntax_Syntax.Error (_151_1389))
in (Prims.raise _151_1390))
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
(let _151_1393 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _151_1393))
end else begin
()
end
in (let _151_1395 = (let _151_1394 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g _151_1394))
in ((env), ((((tc), (tc_u)))::all_tcs), (_151_1395)))))
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
(let _151_1398 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((data)::datas), (_151_1398)))
end))
end)) datas (([]), (g)))
in (match (_58_3426) with
| (datas, g) -> begin
(

let _58_3429 = (let _151_1399 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _151_1399 datas))
in (match (_58_3429) with
| (tcs, datas) -> begin
(

let sig_bndle = (let _151_1401 = (let _151_1400 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_151_1400)))
in FStar_Syntax_Syntax.Sig_bundle (_151_1401))
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

let t = (let _151_1414 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _151_1414 t))
in (

let _58_3486 = (FStar_Syntax_Subst.open_term bs t)
in (match (_58_3486) with
| (bs, t) -> begin
(

let ibs = (match ((let _151_1415 = (FStar_Syntax_Subst.compress t)
in _151_1415.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _58_3489) -> begin
ibs
end
| _58_3493 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _151_1418 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _151_1417 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _151_1418 _151_1417)))
in (

let ind = (let _151_1421 = (FStar_List.map (fun _58_3500 -> (match (_58_3500) with
| (bv, aq) -> begin
(let _151_1420 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_151_1420), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _151_1421 None dr))
in (

let ind = (let _151_1424 = (FStar_List.map (fun _58_3504 -> (match (_58_3504) with
| (bv, aq) -> begin
(let _151_1423 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_151_1423), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _151_1424 None dr))
in (

let haseq_ind = (let _151_1426 = (let _151_1425 = (FStar_Syntax_Syntax.as_arg ind)
in (_151_1425)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _151_1426 None dr))
in (

let bs' = (FStar_List.filter (fun b -> (

let _58_3515 = acc
in (match (_58_3515) with
| (_58_3509, en, _58_3512, _58_3514) -> begin
(

let opt = (let _151_1429 = (let _151_1428 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _151_1428))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort _151_1429 false))
in (match (opt) with
| None -> begin
false
end
| Some (_58_3519) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (let _151_1435 = (let _151_1434 = (let _151_1433 = (let _151_1432 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg _151_1432))
in (_151_1433)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _151_1434 None dr))
in (FStar_Syntax_Util.mk_conj t _151_1435))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let _58_3526 = fml
in (let _151_1441 = (let _151_1440 = (let _151_1439 = (let _151_1438 = (let _151_1437 = (let _151_1436 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_151_1436)::[])
in (_151_1437)::[])
in FStar_Syntax_Syntax.Meta_pattern (_151_1438))
in ((fml), (_151_1439)))
in FStar_Syntax_Syntax.Tm_meta (_151_1440))
in {FStar_Syntax_Syntax.n = _151_1441; FStar_Syntax_Syntax.tk = _58_3526.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _58_3526.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_3526.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _151_1447 = (let _151_1446 = (let _151_1445 = (let _151_1444 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _151_1444 None))
in (FStar_Syntax_Syntax.as_arg _151_1445))
in (_151_1446)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _151_1447 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _151_1453 = (let _151_1452 = (let _151_1451 = (let _151_1450 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _151_1450 None))
in (FStar_Syntax_Syntax.as_arg _151_1451))
in (_151_1452)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _151_1453 None dr))) bs fml)
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
in (match ((let _151_1459 = (FStar_Syntax_Subst.compress dt)
in _151_1459.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _58_3571) -> begin
(

let dbs = (let _151_1460 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _151_1460))
in (

let dbs = (let _151_1461 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _151_1461 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = (let _151_1465 = (let _151_1464 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_151_1464)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _151_1465 None dr))
in (

let sort_range = (Prims.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b = (let _151_1467 = (let _151_1466 = (FStar_Syntax_Print.term_to_string ind)
in (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add the \'noeq\' qualifier" _151_1466))
in (FStar_TypeChecker_Util.label _151_1467 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b))))) FStar_Syntax_Util.t_true dbs)
in (

let _58_3585 = acc
in (match (_58_3585) with
| (env, cond') -> begin
(let _151_1469 = (FStar_TypeChecker_Env.push_binders env dbs)
in (let _151_1468 = (FStar_Syntax_Util.mk_conj cond' cond)
in ((_151_1469), (_151_1468))))
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
in (let _151_1471 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _151_1470 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env), (_151_1471), (_151_1470)))))
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
(let _151_1472 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _151_1472))
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

let t = (let _151_1486 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _151_1486 t))
in (

let _58_3696 = (FStar_Syntax_Subst.open_term bs t)
in (match (_58_3696) with
| (bs, t) -> begin
(

let ibs = (match ((let _151_1487 = (FStar_Syntax_Subst.compress t)
in _151_1487.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _58_3699) -> begin
ibs
end
| _58_3703 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _151_1490 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _151_1489 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _151_1490 _151_1489)))
in (

let ind = (let _151_1493 = (FStar_List.map (fun _58_3710 -> (match (_58_3710) with
| (bv, aq) -> begin
(let _151_1492 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_151_1492), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _151_1493 None dr))
in (

let ind = (let _151_1496 = (FStar_List.map (fun _58_3714 -> (match (_58_3714) with
| (bv, aq) -> begin
(let _151_1495 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_151_1495), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _151_1496 None dr))
in (

let haseq_ind = (let _151_1498 = (let _151_1497 = (FStar_Syntax_Syntax.as_arg ind)
in (_151_1497)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _151_1498 None dr))
in (

let rec is_mutual = (fun t -> (match ((let _151_1502 = (FStar_Syntax_Subst.compress t)
in _151_1502.FStar_Syntax_Syntax.n)) with
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
(let _151_1504 = (FStar_List.map Prims.fst args)
in (exists_mutual _151_1504))
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
in (match ((let _151_1510 = (FStar_Syntax_Subst.compress dt)
in _151_1510.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _58_3755) -> begin
(

let dbs = (let _151_1511 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _151_1511))
in (

let dbs = (let _151_1512 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _151_1512 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = (let _151_1516 = (let _151_1515 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_151_1515)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _151_1516 None dr))
in (

let haseq_sort = if (is_mutual sort) then begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end else begin
haseq_sort
end
in (FStar_Syntax_Util.mk_conj t haseq_sort))))) FStar_Syntax_Util.t_true dbs)
in (

let cond = (FStar_List.fold_right (fun b t -> (let _151_1522 = (let _151_1521 = (let _151_1520 = (let _151_1519 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _151_1519 None))
in (FStar_Syntax_Syntax.as_arg _151_1520))
in (_151_1521)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _151_1522 None dr))) dbs cond)
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
in (let _151_1529 = (let _151_1528 = (let _151_1527 = (let _151_1526 = (let _151_1525 = (let _151_1524 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_151_1524)::[])
in (_151_1525)::[])
in FStar_Syntax_Syntax.Meta_pattern (_151_1526))
in ((fml), (_151_1527)))
in FStar_Syntax_Syntax.Tm_meta (_151_1528))
in {FStar_Syntax_Syntax.n = _151_1529; FStar_Syntax_Syntax.tk = _58_3795.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _58_3795.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_3795.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _151_1535 = (let _151_1534 = (let _151_1533 = (let _151_1532 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _151_1532 None))
in (FStar_Syntax_Syntax.as_arg _151_1533))
in (_151_1534)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _151_1535 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _151_1541 = (let _151_1540 = (let _151_1539 = (let _151_1538 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _151_1538 None))
in (FStar_Syntax_Syntax.as_arg _151_1539))
in (_151_1540)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _151_1541 None dr))) bs fml)
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

let se = (let _151_1542 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (tc_assume env _151_1542 fml [] dr))
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
in (let _151_1547 = (let _151_1546 = (let _151_1545 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_151_1545)))
in FStar_Syntax_Syntax.Sig_bundle (_151_1546))
in (_151_1547)::ses)))
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
in (let _151_1550 = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (_151_1550)))))
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

let _58_3887 = (let _151_1557 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _151_1557 Prims.ignore))
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
in (let _151_1560 = (FStar_TypeChecker_Env.push_sigelt env se_let)
in ((_151_1560), ((se_let)::ses))))
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

let _58_3922 = (let _151_1561 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _151_1561))
in (match (_58_3922) with
| (a, wp_a_src) -> begin
(

let _58_3925 = (let _151_1562 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _151_1562))
in (match (_58_3925) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _151_1566 = (let _151_1565 = (let _151_1564 = (let _151_1563 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (_151_1563)))
in FStar_Syntax_Syntax.NT (_151_1564))
in (_151_1565)::[])
in (FStar_Syntax_Subst.subst _151_1566 wp_b_tgt))
in (

let expected_k = (let _151_1571 = (let _151_1569 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1568 = (let _151_1567 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_151_1567)::[])
in (_151_1569)::_151_1568))
in (let _151_1570 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _151_1571 _151_1570)))
in (

let lift_wp = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift_wp) expected_k)
in (

let repr_type = (fun eff_name a wp -> (

let no_reify = (fun l -> (let _151_1583 = (let _151_1582 = (let _151_1581 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _151_1580 = (FStar_TypeChecker_Env.get_range env)
in ((_151_1581), (_151_1580))))
in FStar_Syntax_Syntax.Error (_151_1582))
in (Prims.raise _151_1583)))
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
(let _151_1590 = (let _151_1588 = (let _151_1587 = (let _151_1586 = (FStar_Syntax_Syntax.as_arg a)
in (let _151_1585 = (let _151_1584 = (FStar_Syntax_Syntax.as_arg wp)
in (_151_1584)::[])
in (_151_1586)::_151_1585))
in ((repr), (_151_1587)))
in FStar_Syntax_Syntax.Tm_app (_151_1588))
in (let _151_1589 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _151_1590 None _151_1589)))
end)
end)))
in (

let lift = (match (sub.FStar_Syntax_Syntax.lift) with
| None -> begin
None
end
| Some (_58_3941, lift) -> begin
(

let _58_3947 = (let _151_1591 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _151_1591))
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

let lift_wp_a = (let _151_1598 = (let _151_1596 = (let _151_1595 = (let _151_1594 = (FStar_Syntax_Syntax.as_arg a_typ)
in (let _151_1593 = (let _151_1592 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (_151_1592)::[])
in (_151_1594)::_151_1593))
in (((Prims.snd sub.FStar_Syntax_Syntax.lift_wp)), (_151_1595)))
in FStar_Syntax_Syntax.Tm_app (_151_1596))
in (let _151_1597 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _151_1598 None _151_1597)))
in (repr_type sub.FStar_Syntax_Syntax.target a_typ lift_wp_a))
in (

let expected_k = (let _151_1605 = (let _151_1603 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_1602 = (let _151_1601 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (let _151_1600 = (let _151_1599 = (FStar_Syntax_Syntax.null_binder repr_f)
in (_151_1599)::[])
in (_151_1601)::_151_1600))
in (_151_1603)::_151_1602))
in (let _151_1604 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow _151_1605 _151_1604)))
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

let _58_3997 = (let _151_1606 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _151_1606))
in (match (_58_3997) with
| (uvs, t) -> begin
(

let _58_4016 = (match ((let _151_1608 = (let _151_1607 = (FStar_Syntax_Subst.compress t)
in _151_1607.FStar_Syntax_Syntax.n)
in ((tps), (_151_1608)))) with
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

let _58_4031 = (let _151_1610 = (let _151_1609 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _151_1609))
in (check_and_gen env t _151_1610))
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

let _58_4056 = (let _151_1614 = (let _151_1611 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_151_1611))
in (let _151_1613 = (let _151_1612 = (c.FStar_Syntax_Syntax.comp ())
in ((e), (_151_1612)))
in (check_expected_effect env _151_1614 _151_1613)))
in (match (_58_4056) with
| (e, _58_4054, g) -> begin
(

let _58_4057 = (let _151_1615 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _151_1615))
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
(let _151_1627 = (let _151_1626 = (let _151_1625 = (let _151_1624 = (FStar_Syntax_Print.lid_to_string l)
in (let _151_1623 = (FStar_Syntax_Print.quals_to_string q)
in (let _151_1622 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _151_1624 _151_1623 _151_1622))))
in ((_151_1625), (r)))
in FStar_Syntax_Syntax.Error (_151_1626))
in (Prims.raise _151_1627))
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
in (let _151_1630 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Syntax_Const.effect_ALL_lid), (tval), (lb.FStar_Syntax_Syntax.lbdef)))
in ((false), (_151_1630), (quals_opt)))))
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

let e = (let _151_1634 = (let _151_1633 = (let _151_1632 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((((Prims.fst lbs)), (lbs'))), (_151_1632)))
in FStar_Syntax_Syntax.Tm_let (_151_1633))
in (FStar_Syntax_Syntax.mk _151_1634 None r))
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
(let _151_1642 = (let _151_1641 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _151_1638 = (let _151_1637 = (let _151_1636 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _151_1636.FStar_Syntax_Syntax.fv_name)
in _151_1637.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _151_1638))) with
| None -> begin
true
end
| _58_4148 -> begin
false
end)
in if should_log then begin
(let _151_1640 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _151_1639 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _151_1640 _151_1639)))
end else begin
""
end))))
in (FStar_All.pipe_right _151_1641 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _151_1642))
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

let dec = (let _151_1658 = (let _151_1657 = (let _151_1656 = (let _151_1655 = (let _151_1654 = (FStar_Syntax_Syntax.mk_Total t)
in ((bs), (_151_1654)))
in FStar_Syntax_Syntax.Tm_arrow (_151_1655))
in (FStar_Syntax_Syntax.mk _151_1656 None r))
in ((l), (us), (_151_1657), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_151_1658))
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
(let _151_1665 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _151_1664 = (let _151_1663 = (let _151_1662 = (let _151_1661 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _151_1661.FStar_Syntax_Syntax.fv_name)
in _151_1662.FStar_Syntax_Syntax.v)
in ((_151_1663), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_151_1664)))))
in ((_151_1665), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let process_one_decl = (fun _58_4291 se -> (match (_58_4291) with
| (ses, exports, env, hidden) -> begin
(

let _58_4293 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _151_1674 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _151_1674))
end else begin
()
end
in (

let _58_4297 = (tc_decl env se)
in (match (_58_4297) with
| (ses', env) -> begin
(

let _58_4300 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _151_1679 = (FStar_List.fold_left (fun s se -> (let _151_1678 = (let _151_1677 = (FStar_Syntax_Print.sigelt_to_string se)
in (Prims.strcat _151_1677 "\n"))
in (Prims.strcat s _151_1678))) "" ses')
in (FStar_Util.print1 "Checked: %s\n" _151_1679))
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
(let _151_1685 = (FStar_All.pipe_right (FStar_List.rev_append exports []) FStar_List.flatten)
in (((FStar_List.rev_append ses [])), (_151_1685), (env)))
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
in (let _151_1690 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _58_4343.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_4343.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_4343.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_4343.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_4343.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_4343.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_4343.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_4343.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_4343.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_4343.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_4343.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_4343.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_4343.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_4343.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_4343.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_4343.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _151_1690; FStar_TypeChecker_Env.lax = _58_4343.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_4343.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_4343.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_4343.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_4343.FStar_TypeChecker_Env.qname_and_index}))
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

let _58_4378 = (let _151_1703 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _151_1703 Prims.ignore))
in ((modul), (env)))))))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let _58_4385 = (tc_partial_modul env modul)
in (match (_58_4385) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _58_4388 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _151_1712 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _151_1712))
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
(let _151_1717 = (let _151_1716 = (let _151_1715 = (FStar_TypeChecker_Env.get_range env)
in (((Prims.strcat "Implicit argument: " msg)), (_151_1715)))
in FStar_Syntax_Syntax.Error (_151_1716))
in (Prims.raise _151_1717))
end
in (match (_58_4406) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end else begin
(let _151_1722 = (let _151_1721 = (let _151_1720 = (let _151_1718 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _151_1718))
in (let _151_1719 = (FStar_TypeChecker_Env.get_range env)
in ((_151_1720), (_151_1719))))
in FStar_Syntax_Syntax.Error (_151_1721))
in (Prims.raise _151_1722))
end
end)))))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
FStar_Syntax_Syntax.U_zero
end else begin
(

let _58_4409 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _151_1727 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print1 "universe_of %s\n" _151_1727))
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

let fail = (fun e t -> (let _151_1737 = (let _151_1736 = (let _151_1735 = (let _151_1733 = (FStar_Syntax_Print.term_to_string e)
in (let _151_1732 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" _151_1733 _151_1732)))
in (let _151_1734 = (FStar_TypeChecker_Env.get_range env)
in ((_151_1735), (_151_1734))))
in FStar_Syntax_Syntax.Error (_151_1736))
in (Prims.raise _151_1737)))
in (

let ok = (fun u -> (

let _58_4423 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _151_1741 = (FStar_Syntax_Print.tag_of_term e)
in (let _151_1740 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.print2 "<end> universe_of %s is %s\n" _151_1741 _151_1740)))
end else begin
()
end
in u))
in (

let universe_of_type = (fun e t -> (match ((let _151_1746 = (FStar_Syntax_Util.unrefine t)
in _151_1746.FStar_Syntax_Syntax.n)) with
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
(match ((let _151_1747 = (FStar_Syntax_Subst.compress head)
in _151_1747.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_58_4436, t) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _151_1748 = (FStar_Syntax_Subst.compress t)
in _151_1748.FStar_Syntax_Syntax.n)) with
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
in (let _151_1750 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (FStar_All.pipe_left (universe_of_type e) _151_1750)))
end)))
end)
end))))))
end)))
end)


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

let _58_4467 = if (FStar_Options.debug_any ()) then begin
(let _151_1755 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _151_1755))
end else begin
()
end
in (

let _58_4471 = (tc_modul env m)
in (match (_58_4471) with
| (m, env) -> begin
(

let _58_4472 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _151_1756 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _151_1756))
end else begin
()
end
in ((m), (env)))
end))))




