
open Prims

let set_hint_correlator : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env = (fun env se -> (match ((FStar_Options.reuse_hint_for ())) with
| Some (l) -> begin
(

let lid = (let _153_5 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_add_suffix _153_5 l))
in (

let _59_22 = env
in {FStar_TypeChecker_Env.solver = _59_22.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_22.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_22.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_22.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_22.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_22.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_22.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_22.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_22.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_22.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_22.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_22.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_22.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_22.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_22.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_22.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_22.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_22.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_22.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _59_22.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_22.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_22.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))}))
end
| None -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (

let lid = (match (lids) with
| [] -> begin
(let _153_8 = (FStar_TypeChecker_Env.current_module env)
in (let _153_7 = (let _153_6 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_right _153_6 FStar_Util.string_of_int))
in (FStar_Ident.lid_add_suffix _153_8 _153_7)))
end
| (l)::_59_28 -> begin
l
end)
in (

let _59_32 = env
in {FStar_TypeChecker_Env.solver = _59_32.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_32.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_32.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_32.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_32.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_32.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_32.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_32.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_32.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_32.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_32.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_32.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_32.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_32.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_32.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_32.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_32.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_32.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_32.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _59_32.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_32.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_32.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))})))
end))


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (not ((let _153_11 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _153_11))))))


let rng : FStar_TypeChecker_Env.env  ->  FStar_Range.range = (fun env -> (FStar_TypeChecker_Env.get_range env))


let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _59_37 = env
in {FStar_TypeChecker_Env.solver = _59_37.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_37.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_37.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_37.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_37.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_37.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_37.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_37.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_37.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _59_37.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_37.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_37.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_37.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_37.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_37.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_37.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_37.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_37.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _59_37.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_37.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_37.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_37.FStar_TypeChecker_Env.qname_and_index}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _59_40 = env
in {FStar_TypeChecker_Env.solver = _59_40.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_40.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_40.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_40.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_40.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_40.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_40.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_40.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_40.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _59_40.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_40.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_40.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_40.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_40.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_40.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_40.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_40.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_40.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _59_40.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_40.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_40.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_40.FStar_TypeChecker_Env.qname_and_index}))


let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (

let r = if (tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
v.FStar_Syntax_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos tl.FStar_Syntax_Syntax.pos)
end
in (let _153_25 = (let _153_24 = (FStar_Syntax_Syntax.as_arg v)
in (let _153_23 = (let _153_22 = (FStar_Syntax_Syntax.as_arg tl)
in (_153_22)::[])
in (_153_24)::_153_23))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _153_25 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _59_1 -> (match (_59_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _59_50 -> begin
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
| _59_67 -> begin
(

let fvs' = (let _153_53 = if try_norm then begin
(norm env t)
end else begin
t
end
in (FStar_Syntax_Free.names _153_53))
in (match ((FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)) with
| None -> begin
()
end
| Some (x) -> begin
if (not (try_norm)) then begin
(aux true t)
end else begin
(

let fail = (fun _59_74 -> (match (()) with
| () -> begin
(

let msg = (match (head_opt) with
| None -> begin
(let _153_57 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _153_57))
end
| Some (head) -> begin
(let _153_59 = (FStar_Syntax_Print.bv_to_string x)
in (let _153_58 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _153_59 _153_58)))
end)
in (let _153_62 = (let _153_61 = (let _153_60 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (_153_60)))
in FStar_Syntax_Syntax.Error (_153_61))
in (Prims.raise _153_62)))
end))
in (

let s = (let _153_64 = (let _153_63 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _153_63))
in (FStar_TypeChecker_Util.new_uvar env _153_64))
in (match ((FStar_TypeChecker_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g)
end
| _59_83 -> begin
(fail ())
end)))
end
end))
end))
in (aux false kt)))


let push_binding = (fun env b -> (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))


let maybe_make_subst = (fun _59_2 -> (match (_59_2) with
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Syntax_Syntax.NT (((x), (e))))::[]
end
| _59_93 -> begin
[]
end))


let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.subst_t = (fun s b v -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
s
end else begin
(FStar_Syntax_Syntax.NT ((((Prims.fst b)), (v))))::s
end)


let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (

let _59_99 = lc
in {FStar_Syntax_Syntax.eff_name = _59_99.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _59_99.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _59_101 -> (match (()) with
| () -> begin
(let _153_79 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _153_79 t))
end))}))


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let should_return = (fun t -> (match ((let _153_90 = (FStar_Syntax_Subst.compress t)
in _153_90.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_59_109, c) -> begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(

let t = (FStar_All.pipe_left FStar_Syntax_Util.unrefine (FStar_Syntax_Util.comp_result c))
in (match ((let _153_91 = (FStar_Syntax_Subst.compress t)
in _153_91.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (_59_117) -> begin
false
end
| _59_120 -> begin
true
end))
end else begin
false
end
end
| _59_122 -> begin
true
end))
in (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _153_92 = if ((not ((should_return t))) || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _153_92))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _59_150 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
((e), (lc), (guard))
end
| Some (t') -> begin
(

let _59_132 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_94 = (FStar_Syntax_Print.term_to_string t)
in (let _153_93 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _153_94 _153_93)))
end else begin
()
end
in (

let _59_136 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_59_136) with
| (e, lc) -> begin
(

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _59_140 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_59_140) with
| (e, g) -> begin
(

let _59_141 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_96 = (FStar_Syntax_Print.term_to_string t)
in (let _153_95 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _153_96 _153_95)))
end else begin
()
end
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let _59_146 = (let _153_102 = (FStar_All.pipe_left (fun _153_101 -> Some (_153_101)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _153_102 env e lc g))
in (match (_59_146) with
| (lc, g) -> begin
((e), ((set_lcomp_result lc t')), (g))
end))))
end)))
end)))
end)
in (match (_59_150) with
| (e, lc, g) -> begin
(

let _59_151 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_103 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _153_103))
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

let _59_161 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_59_161) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _59_166 -> (match (_59_166) with
| (e, c) -> begin
(

let expected_c_opt = (match (copt) with
| Some (_59_168) -> begin
copt
end
| None -> begin
if ((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Syntax_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) then begin
(let _153_116 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (_153_116))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
if (FStar_Syntax_Util.is_pure_comp c) then begin
(let _153_117 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (_153_117))
end else begin
if (FStar_Syntax_Util.is_pure_or_ghost_comp c) then begin
(let _153_118 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (_153_118))
end else begin
None
end
end
end
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _153_119 = (norm_c env c)
in ((e), (_153_119), (FStar_TypeChecker_Rel.trivial_guard)))
end
| Some (expected_c) -> begin
(

let _59_175 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_122 = (FStar_Syntax_Print.term_to_string e)
in (let _153_121 = (FStar_Syntax_Print.comp_to_string c)
in (let _153_120 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _153_122 _153_121 _153_120))))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _59_178 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_125 = (FStar_Syntax_Print.term_to_string e)
in (let _153_124 = (FStar_Syntax_Print.comp_to_string c)
in (let _153_123 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _153_125 _153_124 _153_123))))
end else begin
()
end
in (

let _59_184 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_59_184) with
| (e, _59_182, g) -> begin
(

let g = (let _153_126 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _153_126 "could not prove post-condition" g))
in (

let _59_186 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_128 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _153_127 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _153_128 _153_127)))
end else begin
()
end
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e (FStar_Syntax_Util.comp_effect_name c) (FStar_Syntax_Util.comp_effect_name expected_c))
in ((e), (expected_c), (g)))))
end)))))
end))
end))


let no_logical_guard = (fun env _59_193 -> (match (_59_193) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
((te), (kt), (f))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _153_134 = (let _153_133 = (let _153_132 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _153_131 = (FStar_TypeChecker_Env.get_range env)
in ((_153_132), (_153_131))))
in FStar_Syntax_Syntax.Error (_153_133))
in (Prims.raise _153_134))
end)
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _153_137 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _153_137))
end))


let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _59_217; FStar_Syntax_Syntax.result_typ = _59_215; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, _59_209))::[]; FStar_Syntax_Syntax.flags = _59_206}) -> begin
(

let pat_vars = (let _153_142 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env pats)
in (FStar_Syntax_Free.names _153_142))
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _59_224 -> (match (_59_224) with
| (b, _59_223) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _59_228) -> begin
(let _153_145 = (let _153_144 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" _153_144))
in (FStar_TypeChecker_Errors.warn pats.FStar_Syntax_Syntax.pos _153_145))
end))
end
| _59_232 -> begin
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

let _59_239 = env
in {FStar_TypeChecker_Env.solver = _59_239.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_239.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_239.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_239.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_239.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_239.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_239.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_239.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_239.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_239.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_239.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_239.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _59_239.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_239.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_239.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_239.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_239.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_239.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _59_239.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_239.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_239.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_239.FStar_TypeChecker_Env.qname_and_index})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _59_251 -> (match (_59_251) with
| (b, _59_250) -> begin
(

let t = (let _153_159 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _153_159))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _59_260 -> begin
(let _153_160 = (FStar_Syntax_Syntax.bv_to_name b)
in (_153_160)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let _59_266 = (FStar_Syntax_Util.head_and_args dec)
in (match (_59_266) with
| (head, _59_265) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _59_270 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _59_3 -> (match (_59_3) with
| FStar_Syntax_Syntax.DECREASES (_59_274) -> begin
true
end
| _59_277 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _59_282 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| _59_287 -> begin
(mk_lex_list xs)
end))
end)))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun _59_292 -> (match (_59_292) with
| (l, t) -> begin
(match ((let _153_166 = (FStar_Syntax_Subst.compress t)
in _153_166.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _59_299 -> (match (_59_299) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _153_170 = (let _153_169 = (let _153_168 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_153_168))
in (FStar_Syntax_Syntax.new_bv _153_169 x.FStar_Syntax_Syntax.sort))
in ((_153_170), (imp)))
end else begin
((x), (imp))
end
end))))
in (

let _59_303 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_59_303) with
| (formals, c) -> begin
(

let dec = (decreases_clause formals c)
in (

let precedes = (let _153_174 = (let _153_173 = (FStar_Syntax_Syntax.as_arg dec)
in (let _153_172 = (let _153_171 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_153_171)::[])
in (_153_173)::_153_172))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _153_174 None r))
in (

let _59_310 = (FStar_Util.prefix formals)
in (match (_59_310) with
| (bs, (last, imp)) -> begin
(

let last = (

let _59_311 = last
in (let _153_175 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _59_311.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_311.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _153_175}))
in (

let refined_formals = (FStar_List.append bs ((((last), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (

let _59_316 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_178 = (FStar_Syntax_Print.lbname_to_string l)
in (let _153_177 = (FStar_Syntax_Print.term_to_string t)
in (let _153_176 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _153_178 _153_177 _153_176))))
end else begin
()
end
in ((l), (t'))))))
end))))
end)))
end
| _59_319 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end)
end)


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let _59_322 = env
in {FStar_TypeChecker_Env.solver = _59_322.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_322.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_322.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_322.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_322.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_322.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_322.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_322.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_322.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_322.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_322.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_322.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_322.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _59_322.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_322.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_322.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_322.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_322.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _59_322.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_322.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_322.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_322.FStar_TypeChecker_Env.qname_and_index}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (

let _59_327 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_248 = (let _153_246 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _153_246))
in (let _153_247 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _153_248 _153_247)))
end else begin
()
end
in (

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_59_331) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let _59_372 = (tc_tot_or_gtot_term env e)
in (match (_59_372) with
| (e, c, g) -> begin
(

let g = (

let _59_373 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _59_373.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _59_373.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _59_373.FStar_TypeChecker_Env.implicits})
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let _59_383 = (FStar_Syntax_Util.type_u ())
in (match (_59_383) with
| (t, u) -> begin
(

let _59_387 = (tc_check_tot_or_gtot_term env e t)
in (match (_59_387) with
| (e, c, g) -> begin
(

let _59_394 = (

let _59_391 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_391) with
| (env, _59_390) -> begin
(tc_pats env pats)
end))
in (match (_59_394) with
| (pats, g') -> begin
(

let g' = (

let _59_395 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _59_395.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _59_395.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _59_395.FStar_TypeChecker_Env.implicits})
in (let _153_253 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_pattern (pats))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _153_252 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((_153_253), (c), (_153_252)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _153_254 = (FStar_Syntax_Subst.compress e)
in _153_254.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_59_404, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _59_411; FStar_Syntax_Syntax.lbtyp = _59_409; FStar_Syntax_Syntax.lbeff = _59_407; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _59_422 = (let _153_255 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _153_255 e1))
in (match (_59_422) with
| (e1, c1, g1) -> begin
(

let _59_426 = (tc_term env e2)
in (match (_59_426) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((None), (c2)))
in (

let e = (let _153_260 = (let _153_259 = (let _153_258 = (let _153_257 = (let _153_256 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_TypeChecker_Common.t_unit), (e1)))
in (_153_256)::[])
in ((false), (_153_257)))
in ((_153_258), (e2)))
in FStar_Syntax_Syntax.Tm_let (_153_259))
in (FStar_Syntax_Syntax.mk _153_260 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _153_261 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e), (c), (_153_261))))))
end))
end))
end
| _59_431 -> begin
(

let _59_435 = (tc_term env e)
in (match (_59_435) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (_59_439)) -> begin
(tc_term env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let _59_450 = (tc_term env e)
in (match (_59_450) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (m)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _59_456) -> begin
(

let _59_462 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_462) with
| (env0, _59_461) -> begin
(

let _59_467 = (tc_comp env0 expected_c)
in (match (_59_467) with
| (expected_c, _59_465, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (

let _59_472 = (let _153_262 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term _153_262 e))
in (match (_59_472) with
| (e, c', g') -> begin
(

let _59_476 = (let _153_264 = (let _153_263 = (c'.FStar_Syntax_Syntax.comp ())
in ((e), (_153_263)))
in (check_expected_effect env0 (Some (expected_c)) _153_264))
in (match (_59_476) with
| (e, expected_c, g'') -> begin
(let _153_267 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t_res)), (Some ((FStar_Syntax_Util.comp_effect_name expected_c)))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _153_266 = (let _153_265 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _153_265))
in ((_153_267), ((FStar_Syntax_Util.lcomp_of_comp expected_c)), (_153_266))))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _59_481) -> begin
(

let _59_486 = (FStar_Syntax_Util.type_u ())
in (match (_59_486) with
| (k, u) -> begin
(

let _59_491 = (tc_check_tot_or_gtot_term env t k)
in (match (_59_491) with
| (t, _59_489, f) -> begin
(

let _59_495 = (let _153_268 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _153_268 e))
in (match (_59_495) with
| (e, c, g) -> begin
(

let _59_499 = (let _153_272 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _59_496 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _153_272 e c f))
in (match (_59_499) with
| (c, f) -> begin
(

let _59_503 = (let _153_273 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t)), (Some (c.FStar_Syntax_Syntax.eff_name))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _153_273 c))
in (match (_59_503) with
| (e, c, f2) -> begin
(let _153_275 = (let _153_274 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _153_274))
in ((e), (c), (_153_275)))
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

let _59_539 = (FStar_Syntax_Util.head_and_args top)
in (match (_59_539) with
| (unary_op, _59_538) -> begin
(

let head = (let _153_276 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (Prims.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) None _153_276))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), (rest)))) None top.FStar_Syntax_Syntax.pos)
in (tc_term env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _59_547; FStar_Syntax_Syntax.pos = _59_545; FStar_Syntax_Syntax.vars = _59_543}, ((e, aqual))::[]) -> begin
(

let _59_557 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end else begin
()
end
in (

let _59_566 = (

let _59_562 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_562) with
| (env0, _59_561) -> begin
(tc_term env0 e)
end))
in (match (_59_566) with
| (e, c, g) -> begin
(

let _59_570 = (FStar_Syntax_Util.head_and_args top)
in (match (_59_570) with
| (reify_op, _59_569) -> begin
(

let u_c = (

let _59_576 = (tc_term env c.FStar_Syntax_Syntax.res_typ)
in (match (_59_576) with
| (_59_572, c, _59_575) -> begin
(match ((let _153_277 = (FStar_Syntax_Subst.compress c.FStar_Syntax_Syntax.res_typ)
in _153_277.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| _59_580 -> begin
(FStar_All.failwith "Unexpected result type of computation")
end)
end))
in (

let repr = (FStar_TypeChecker_Util.reify_comp env c u_c)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e), (aqual)))::[])))) (Some (repr.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let c = (let _153_278 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right _153_278 FStar_Syntax_Util.lcomp_of_comp))
in (

let _59_588 = (comp_check_expected_typ env e c)
in (match (_59_588) with
| (e, c, g') -> begin
(let _153_279 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), (c), (_153_279)))
end))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.tk = _59_594; FStar_Syntax_Syntax.pos = _59_592; FStar_Syntax_Syntax.vars = _59_590}, ((e, aqual))::[]) -> begin
(

let _59_605 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end else begin
()
end
in (

let no_reflect = (fun _59_608 -> (match (()) with
| () -> begin
(let _153_284 = (let _153_283 = (let _153_282 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((_153_282), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_153_283))
in (Prims.raise _153_284))
end))
in (

let _59_612 = (FStar_Syntax_Util.head_and_args top)
in (match (_59_612) with
| (reflect_op, _59_611) -> begin
(match ((FStar_TypeChecker_Env.effect_decl_opt env l)) with
| None -> begin
(no_reflect ())
end
| Some (ed) -> begin
if (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable)))) then begin
(no_reflect ())
end else begin
(

let _59_618 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_618) with
| (env_no_ex, topt) -> begin
(

let _59_646 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (let _153_290 = (let _153_289 = (let _153_288 = (let _153_287 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _153_286 = (let _153_285 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (_153_285)::[])
in (_153_287)::_153_286))
in ((repr), (_153_288)))
in FStar_Syntax_Syntax.Tm_app (_153_289))
in (FStar_Syntax_Syntax.mk _153_290 None top.FStar_Syntax_Syntax.pos))
in (

let _59_626 = (let _153_292 = (let _153_291 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _153_291 Prims.fst))
in (tc_tot_or_gtot_term _153_292 t))
in (match (_59_626) with
| (t, _59_624, g) -> begin
(match ((let _153_293 = (FStar_Syntax_Subst.compress t)
in _153_293.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_59_628, ((res, _59_635))::((wp, _59_631))::[]) -> begin
((t), (res), (wp), (g))
end
| _59_641 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))
in (match (_59_646) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let _59_660 = (

let _59_650 = (tc_tot_or_gtot_term env_no_ex e)
in (match (_59_650) with
| (e, c, g) -> begin
(

let _59_651 = if (let _153_294 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation _153_294)) then begin
(FStar_TypeChecker_Errors.add_errors env (((("Expected Tot, got a GTot computation"), (e.FStar_Syntax_Syntax.pos)))::[]))
end else begin
()
end
in (match ((FStar_TypeChecker_Rel.try_teq env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)) with
| None -> begin
(

let _59_654 = (let _153_299 = (let _153_298 = (let _153_297 = (let _153_296 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _153_295 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" _153_296 _153_295)))
in ((_153_297), (e.FStar_Syntax_Syntax.pos)))
in (_153_298)::[])
in (FStar_TypeChecker_Errors.add_errors env _153_299))
in (let _153_300 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e), (_153_300))))
end
| Some (g') -> begin
(let _153_302 = (let _153_301 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' _153_301))
in ((e), (_153_302)))
end))
end))
in (match (_59_660) with
| (e, g) -> begin
(

let c = (let _153_306 = (let _153_305 = (let _153_304 = (let _153_303 = (FStar_Syntax_Syntax.as_arg wp)
in (_153_303)::[])
in {FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = _153_304; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp _153_305))
in (FStar_All.pipe_right _153_306 FStar_Syntax_Util.lcomp_of_comp))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e), (aqual)))::[])))) (Some (res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let _59_666 = (comp_check_expected_typ env e c)
in (match (_59_666) with
| (e, c, g') -> begin
(let _153_307 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e), (c), (_153_307)))
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

let env = (let _153_309 = (let _153_308 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _153_308 Prims.fst))
in (FStar_All.pipe_right _153_309 instantiate_both))
in (

let _59_673 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_311 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _153_310 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _153_311 _153_310)))
end else begin
()
end
in (

let _59_678 = (tc_term (no_inst env) head)
in (match (_59_678) with
| (head, chead, g_head) -> begin
(

let _59_682 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _153_312 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _153_312))
end else begin
(let _153_313 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _153_313))
end
in (match (_59_682) with
| (e, c, g) -> begin
(

let _59_683 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _153_314 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _153_314))
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

let _59_689 = (comp_check_expected_typ env0 e c)
in (match (_59_689) with
| (e, c, g') -> begin
(

let gimp = (match ((let _153_315 = (FStar_Syntax_Subst.compress head)
in _153_315.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _59_692) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e), (c.FStar_Syntax_Syntax.res_typ), (head.FStar_Syntax_Syntax.pos))
in (

let _59_696 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _59_696.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _59_696.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _59_696.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _59_699 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (

let gres = (let _153_316 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _153_316))
in (

let _59_702 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _153_318 = (FStar_Syntax_Print.term_to_string e)
in (let _153_317 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" _153_318 _153_317)))
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

let _59_710 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_710) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let _59_715 = (tc_term env1 e1)
in (match (_59_715) with
| (e1, c1, g1) -> begin
(

let _59_726 = (match (topt) with
| Some (t) -> begin
((env), (t))
end
| None -> begin
(

let _59_722 = (FStar_Syntax_Util.type_u ())
in (match (_59_722) with
| (k, _59_721) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _153_319 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in ((_153_319), (res_t))))
end))
end)
in (match (_59_726) with
| (env_branches, res_t) -> begin
(

let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let _59_743 = (

let _59_740 = (FStar_List.fold_right (fun _59_734 _59_737 -> (match (((_59_734), (_59_737))) with
| ((_59_730, f, c, g), (caccum, gaccum)) -> begin
(let _153_322 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (_153_322)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_59_740) with
| (cases, g) -> begin
(let _153_323 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in ((_153_323), (g)))
end))
in (match (_59_743) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (guard_x)), (c_branches)))
in (

let e = (

let mk_match = (fun scrutinee -> (

let branches = (FStar_List.map (fun _59_754 -> (match (_59_754) with
| (f, _59_749, _59_751, _59_753) -> begin
f
end)) t_eqns)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (Some (cres.FStar_Syntax_Syntax.eff_name))))) None e.FStar_Syntax_Syntax.pos))))
in if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c1.FStar_Syntax_Syntax.eff_name) then begin
(mk_match e1)
end else begin
(

let e_match = (let _153_327 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match _153_327))
in (

let lb = (let _153_328 = (FStar_TypeChecker_Env.norm_eff_name env c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = _153_328; FStar_Syntax_Syntax.lbdef = e1})
in (let _153_333 = (let _153_332 = (let _153_331 = (let _153_330 = (let _153_329 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (_153_329)::[])
in (FStar_Syntax_Subst.close _153_330 e_match))
in ((((false), ((lb)::[]))), (_153_331)))
in FStar_Syntax_Syntax.Tm_let (_153_332))
in (FStar_Syntax_Syntax.mk _153_333 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))))
end)
in (

let _59_760 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _153_336 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _153_335 = (let _153_334 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _153_334))
in (FStar_Util.print2 "(%s) comp type = %s\n" _153_336 _153_335)))
end else begin
()
end
in (let _153_337 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e), (cres), (_153_337))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_59_772); FStar_Syntax_Syntax.lbunivs = _59_770; FStar_Syntax_Syntax.lbtyp = _59_768; FStar_Syntax_Syntax.lbeff = _59_766; FStar_Syntax_Syntax.lbdef = _59_764})::[]), _59_778) -> begin
(

let _59_781 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_338 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _153_338))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _59_785), _59_788) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_59_803); FStar_Syntax_Syntax.lbunivs = _59_801; FStar_Syntax_Syntax.lbtyp = _59_799; FStar_Syntax_Syntax.lbeff = _59_797; FStar_Syntax_Syntax.lbdef = _59_795})::_59_793), _59_809) -> begin
(

let _59_812 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_339 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _153_339))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _59_816), _59_819) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let _59_833 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_59_833) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _153_353 = (let _153_352 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _153_352))
in FStar_Util.Inr (_153_353))
end
in (

let is_data_ctor = (fun _59_4 -> (match (_59_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _59_843 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _153_359 = (let _153_358 = (let _153_357 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _153_356 = (FStar_TypeChecker_Env.get_range env)
in ((_153_357), (_153_356))))
in FStar_Syntax_Syntax.Error (_153_358))
in (Prims.raise _153_359))
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
(let _153_361 = (let _153_360 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" _153_360))
in (FStar_All.failwith _153_361))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (match ((let _153_362 = (FStar_Syntax_Subst.compress t1)
in _153_362.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_59_854) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _59_857 -> begin
(

let imp = (("uvar in term"), (env), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let _59_859 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _59_859.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _59_859.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _59_859.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _59_874 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(

let _59_867 = (FStar_Syntax_Util.type_u ())
in (match (_59_867) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
end))
end
| Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end)
in (match (_59_874) with
| (t, _59_872, g0) -> begin
(

let _59_879 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (_59_879) with
| (e, _59_877, g1) -> begin
(let _153_365 = (let _153_363 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right _153_363 FStar_Syntax_Util.lcomp_of_comp))
in (let _153_364 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e), (_153_365), (_153_364))))
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

let _59_883 = x
in {FStar_Syntax_Syntax.ppname = _59_883.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_883.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let _59_889 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_59_889) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _153_367 = (let _153_366 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _153_366))
in FStar_Util.Inr (_153_367))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _59_896; FStar_Syntax_Syntax.pos = _59_894; FStar_Syntax_Syntax.vars = _59_892}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let _59_906 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_59_906) with
| (us', t) -> begin
(

let _59_913 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _153_370 = (let _153_369 = (let _153_368 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (_153_368)))
in FStar_Syntax_Syntax.Error (_153_369))
in (Prims.raise _153_370))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _59_912 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (

let fv' = (

let _59_915 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _59_917 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _59_917.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _59_917.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _59_915.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _59_915.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _153_373 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _153_373 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let _59_925 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_59_925) with
| (us, t) -> begin
(

let fv' = (

let _59_926 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _59_928 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _59_928.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _59_928.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _59_926.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _59_926.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _153_374 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _153_374 us))
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

let _59_942 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_59_942) with
| (bs, c) -> begin
(

let env0 = env
in (

let _59_947 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_947) with
| (env, _59_946) -> begin
(

let _59_952 = (tc_binders env bs)
in (match (_59_952) with
| (bs, env, g, us) -> begin
(

let _59_956 = (tc_comp env c)
in (match (_59_956) with
| (c, uc, f) -> begin
(

let e = (

let _59_957 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _59_957.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _59_957.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _59_957.FStar_Syntax_Syntax.vars})
in (

let _59_960 = (check_smt_pat env e bs c)
in (

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _153_375 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _153_375))
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

let _59_976 = (let _153_377 = (let _153_376 = (FStar_Syntax_Syntax.mk_binder x)
in (_153_376)::[])
in (FStar_Syntax_Subst.open_term _153_377 phi))
in (match (_59_976) with
| (x, phi) -> begin
(

let env0 = env
in (

let _59_981 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_981) with
| (env, _59_980) -> begin
(

let _59_986 = (let _153_378 = (FStar_List.hd x)
in (tc_binder env _153_378))
in (match (_59_986) with
| (x, env, f1, u) -> begin
(

let _59_987 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_381 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _153_380 = (FStar_Syntax_Print.term_to_string phi)
in (let _153_379 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _153_381 _153_380 _153_379))))
end else begin
()
end
in (

let _59_992 = (FStar_Syntax_Util.type_u ())
in (match (_59_992) with
| (t_phi, _59_991) -> begin
(

let _59_997 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_59_997) with
| (phi, _59_995, f2) -> begin
(

let e = (

let _59_998 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _59_998.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _59_998.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _59_998.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _153_382 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _153_382))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _59_1006) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (

let _59_1012 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_383 = (FStar_Syntax_Print.term_to_string (

let _59_1010 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))); FStar_Syntax_Syntax.tk = _59_1010.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _59_1010.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _59_1010.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _153_383))
end else begin
()
end
in (

let _59_1016 = (FStar_Syntax_Subst.open_term bs body)
in (match (_59_1016) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _59_1018 -> begin
(let _153_386 = (let _153_385 = (FStar_Syntax_Print.term_to_string top)
in (let _153_384 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" _153_385 _153_384)))
in (FStar_All.failwith _153_386))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_59_1023) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_59_1026, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_59_1031, Some (_59_1033)) -> begin
(FStar_All.failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (_59_1038) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_59_1041) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_59_1044) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_59_1048) -> begin
FStar_TypeChecker_Common.t_range
end
| _59_1051 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(

let _59_1059 = (FStar_Syntax_Util.type_u ())
in (match (_59_1059) with
| (k, u) -> begin
(

let _59_1064 = (tc_check_tot_or_gtot_term env t k)
in (match (_59_1064) with
| (t, _59_1062, g) -> begin
(let _153_391 = (FStar_Syntax_Syntax.mk_Total t)
in ((_153_391), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(

let _59_1069 = (FStar_Syntax_Util.type_u ())
in (match (_59_1069) with
| (k, u) -> begin
(

let _59_1074 = (tc_check_tot_or_gtot_term env t k)
in (match (_59_1074) with
| (t, _59_1072, g) -> begin
(let _153_392 = (FStar_Syntax_Syntax.mk_GTotal t)
in ((_153_392), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (

let tc = (let _153_394 = (let _153_393 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_153_393)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _153_394 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let _59_1083 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_59_1083) with
| (tc, _59_1081, f) -> begin
(

let _59_1087 = (FStar_Syntax_Util.head_and_args tc)
in (match (_59_1087) with
| (_59_1085, args) -> begin
(

let _59_1090 = (let _153_396 = (FStar_List.hd args)
in (let _153_395 = (FStar_List.tl args)
in ((_153_396), (_153_395))))
in (match (_59_1090) with
| (res, args) -> begin
(

let _59_1106 = (let _153_398 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _59_5 -> (match (_59_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _59_1097 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_1097) with
| (env, _59_1096) -> begin
(

let _59_1102 = (tc_tot_or_gtot_term env e)
in (match (_59_1102) with
| (e, _59_1100, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e)), (g))
end))
end))
end
| f -> begin
((f), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right _153_398 FStar_List.unzip))
in (match (_59_1106) with
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
| _59_1117 -> begin
(FStar_All.failwith "Impossible:Unexpected sort for computation")
end)))
end
| _59_1119 -> begin
(FStar_All.failwith "Impossible:Unexpected sort for computation")
end)
in (

let c = (FStar_Syntax_Syntax.mk_Comp (

let _59_1121 = c
in {FStar_Syntax_Syntax.effect_name = _59_1121.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _59_1121.FStar_Syntax_Syntax.flags}))
in (

let u_c = (match ((FStar_TypeChecker_Util.effect_repr env c u)) with
| None -> begin
u
end
| Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end)
in (let _153_399 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((c), (u_c), (_153_399))))))
end))
end))
end))
end))))
end)))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_59_1134) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _153_404 = (aux u)
in FStar_Syntax_Syntax.U_succ (_153_404))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _153_405 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_153_405))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _153_409 = (let _153_408 = (let _153_407 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _153_406 = (FStar_TypeChecker_Env.get_range env)
in ((_153_407), (_153_406))))
in FStar_Syntax_Syntax.Error (_153_408))
in (Prims.raise _153_409))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _153_410 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_410 Prims.snd))
end
| _59_1149 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _153_419 = (let _153_418 = (let _153_417 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in ((_153_417), (top.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_153_418))
in (Prims.raise _153_419)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun _59_1167 bs bs_expected -> (match (_59_1167) with
| (env, out, g, subst) -> begin
(match (((bs), (bs_expected))) with
| ([], []) -> begin
((env), ((FStar_List.rev out)), (None), (g), (subst))
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
(

let _59_1198 = (match (((imp), (imp'))) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _153_436 = (let _153_435 = (let _153_434 = (let _153_432 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _153_432))
in (let _153_433 = (FStar_Syntax_Syntax.range_of_bv hd)
in ((_153_434), (_153_433))))
in FStar_Syntax_Syntax.Error (_153_435))
in (Prims.raise _153_436))
end
| _59_1197 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _59_1215 = (match ((let _153_437 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _153_437.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| _59_1203 -> begin
(

let _59_1204 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_438 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _153_438))
end else begin
()
end
in (

let _59_1210 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_59_1210) with
| (t, _59_1208, g1) -> begin
(

let g2 = (let _153_440 = (FStar_TypeChecker_Env.get_range env)
in (let _153_439 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _153_440 "Type annotation on parameter incompatible with the expected type" _153_439)))
in (

let g = (let _153_441 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _153_441))
in ((t), (g))))
end)))
end)
in (match (_59_1215) with
| (t, g) -> begin
(

let hd = (

let _59_1216 = hd
in {FStar_Syntax_Syntax.ppname = _59_1216.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_1216.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env = (push_binding env b)
in (

let subst = (let _153_442 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _153_442))
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

let _59_1237 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _59_1236 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (

let _59_1244 = (tc_binders env bs)
in (match (_59_1244) with
| (bs, envbody, g, _59_1243) -> begin
(

let _59_1262 = (match ((let _153_449 = (FStar_Syntax_Subst.compress body)
in _153_449.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _59_1249) -> begin
(

let _59_1256 = (tc_comp envbody c)
in (match (_59_1256) with
| (c, _59_1254, g') -> begin
(let _153_450 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((Some (c)), (body), (_153_450)))
end))
end
| _59_1258 -> begin
((None), (body), (g))
end)
in (match (_59_1262) with
| (copt, body, g) -> begin
((None), (bs), ([]), (copt), (envbody), (body), (g))
end))
end)))
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm t -> (match ((let _153_455 = (FStar_Syntax_Subst.compress t)
in _153_455.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let _59_1289 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _59_1288 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _59_1296 = (tc_binders env bs)
in (match (_59_1296) with
| (bs, envbody, g, _59_1295) -> begin
(

let _59_1300 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_59_1300) with
| (envbody, _59_1299) -> begin
((Some (((t), (true)))), (bs), ([]), (None), (envbody), (body), (g))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _59_1303) -> begin
(

let _59_1314 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_59_1314) with
| (_59_1307, bs, bs', copt, env, body, g) -> begin
((Some (((t), (false)))), (bs), (bs'), (copt), (env), (body), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _59_1321 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_59_1321) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun _59_1332 c_expected -> (match (_59_1332) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _153_466 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in ((env), (bs), (guard), (_153_466)))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (let _153_467 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _153_467))
in (let _153_468 = (FStar_Syntax_Subst.subst_comp subst c)
in ((env), (bs), (guard), (_153_468))))
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

let _59_1353 = (check_binders env more_bs bs_expected)
in (match (_59_1353) with
| (env, bs', more, guard', subst) -> begin
(let _153_470 = (let _153_469 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env), ((FStar_List.append bs bs')), (more), (_153_469), (subst)))
in (handle_more _153_470 c_expected))
end))
end
| _59_1355 -> begin
(let _153_472 = (let _153_471 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _153_471))
in (fail _153_472 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _153_473 = (check_binders env bs bs_expected)
in (handle_more _153_473 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let _59_1361 = envbody
in {FStar_TypeChecker_Env.solver = _59_1361.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_1361.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_1361.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_1361.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_1361.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_1361.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_1361.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_1361.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_1361.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_1361.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_1361.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_1361.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _59_1361.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_1361.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_1361.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_1361.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_1361.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_1361.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _59_1361.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_1361.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_1361.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_1361.FStar_TypeChecker_Env.qname_and_index})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _59_1366 _59_1369 -> (match (((_59_1366), (_59_1369))) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _59_1375 = (let _153_483 = (let _153_482 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _153_482 Prims.fst))
in (tc_term _153_483 t))
in (match (_59_1375) with
| (t, _59_1372, _59_1374) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l (([]), (t)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _153_484 = (FStar_Syntax_Syntax.mk_binder (

let _59_1379 = x
in {FStar_Syntax_Syntax.ppname = _59_1379.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_1379.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_153_484)::letrec_binders)
end
| _59_1382 -> begin
letrec_binders
end)
in ((env), (lb))))
end))
end)) ((envbody), ([])))))))
in (

let _59_1388 = (check_actuals_against_formals env bs bs_expected)
in (match (_59_1388) with
| (envbody, bs, g, c) -> begin
(

let _59_1391 = if (FStar_TypeChecker_Env.should_verify env) then begin
(mk_letrec_env envbody bs c)
end else begin
((envbody), ([]))
end
in (match (_59_1391) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in ((Some (((t), (false)))), (bs), (letrecs), (Some (c)), (envbody), (body), (g)))
end))
end))))
end))
end
| _59_1394 -> begin
if (not (norm)) then begin
(let _153_485 = (unfold_whnf env t)
in (as_function_typ true _153_485))
end else begin
(

let _59_1404 = (expected_function_typ env None body)
in (match (_59_1404) with
| (_59_1396, bs, _59_1399, c_opt, envbody, body, g) -> begin
((Some (((t), (false)))), (bs), ([]), (c_opt), (envbody), (body), (g))
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let _59_1408 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_1408) with
| (env, topt) -> begin
(

let _59_1412 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_486 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _153_486 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (

let _59_1421 = (expected_function_typ env topt body)
in (match (_59_1421) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let _59_1427 = (tc_term (

let _59_1422 = envbody
in {FStar_TypeChecker_Env.solver = _59_1422.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_1422.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_1422.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_1422.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_1422.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_1422.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_1422.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_1422.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_1422.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_1422.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_1422.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_1422.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_1422.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _59_1422.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _59_1422.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_1422.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_1422.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _59_1422.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_1422.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_1422.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_1422.FStar_TypeChecker_Env.qname_and_index}) body)
in (match (_59_1427) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _59_1429 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _153_489 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _153_488 = (let _153_487 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _153_487))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _153_489 _153_488)))
end else begin
()
end
in (

let _59_1436 = (let _153_491 = (let _153_490 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body), (_153_490)))
in (check_expected_effect (

let _59_1431 = envbody
in {FStar_TypeChecker_Env.solver = _59_1431.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_1431.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_1431.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_1431.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_1431.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_1431.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_1431.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_1431.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_1431.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_1431.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_1431.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_1431.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_1431.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_1431.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_1431.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _59_1431.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_1431.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_1431.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _59_1431.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_1431.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_1431.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_1431.FStar_TypeChecker_Env.qname_and_index}) c_opt _153_491))
in (match (_59_1436) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(let _153_492 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _153_492))
end else begin
(

let guard = (let _153_493 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) _153_493))
in guard)
end
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _153_496 = (let _153_495 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _153_494 -> FStar_Util.Inl (_153_494)))
in Some (_153_495))
in (FStar_Syntax_Util.abs bs body _153_496))
in (

let _59_1459 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_59_1448) -> begin
((e), (t), (guard))
end
| _59_1451 -> begin
(

let _59_1454 = if use_teq then begin
(let _153_497 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in ((e), (_153_497)))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_59_1454) with
| (e, guard') -> begin
(let _153_498 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((e), (t), (_153_498)))
end))
end))
end
| None -> begin
((e), (tfun_computed), (guard))
end)
in (match (_59_1459) with
| (e, tfun, guard) -> begin
(

let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (

let _59_1463 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_59_1463) with
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

let _59_1473 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_507 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _153_506 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _153_507 _153_506)))
end else begin
()
end
in (

let monadic_application = (fun _59_1480 subst arg_comps_rev arg_rets guard fvs bs -> (match (_59_1480) with
| (head, chead, ghead, cres) -> begin
(

let _59_1487 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let _59_1515 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun _59_6 -> (match (_59_6) with
| (_59_1494, _59_1496, None) -> begin
false
end
| (_59_1500, _59_1502, Some (c)) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _153_523 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _153_523 cres))
end else begin
(

let _59_1507 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_526 = (FStar_Syntax_Print.term_to_string head)
in (let _153_525 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _153_524 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _153_526 _153_525 _153_524))))
end else begin
()
end
in cres)
end
in ((cres), (g))))))
end
| _59_1511 -> begin
(

let g = (let _153_527 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right _153_527 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _153_532 = (let _153_531 = (let _153_530 = (let _153_529 = (let _153_528 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _153_528))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _153_529))
in (FStar_Syntax_Syntax.mk_Total _153_530))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _153_531))
in ((_153_532), (g))))
end)
in (match (_59_1515) with
| (cres, guard) -> begin
(

let _59_1516 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_533 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _153_533))
end else begin
()
end
in (

let _59_1538 = (FStar_List.fold_left (fun _59_1521 _59_1527 -> (match (((_59_1521), (_59_1527))) with
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
in (match (_59_1538) with
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

let _59_1544 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (_59_1544) with
| (comp, g) -> begin
((app), (comp), (g))
end)))))
end)))
end)))
end))
in (

let rec tc_args = (fun head_info _59_1552 bs args -> (match (_59_1552) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args))) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (_59_1558))))::rest, ((_59_1566, None))::_59_1564) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _59_1572 = (check_no_escape (Some (head)) env fvs t)
in (

let _59_1578 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_59_1578) with
| (varg, _59_1576, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst
in (

let arg = (let _153_545 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (_153_545)))
in (let _153_547 = (let _153_546 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst), ((((arg), (None), (None)))::outargs), ((arg)::arg_rets), (_153_546), (fvs)))
in (tc_args head_info _153_547 rest args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
(

let _59_1610 = (match (((aqual), (aq))) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _59_1609 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifier"), (e.FStar_Syntax_Syntax.pos)))))
end)
in (

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let _59_1613 = x
in {FStar_Syntax_Syntax.ppname = _59_1613.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_1613.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (

let _59_1616 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _153_548 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _153_548))
end else begin
()
end
in (

let _59_1618 = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let _59_1621 = env
in {FStar_TypeChecker_Env.solver = _59_1621.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_1621.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_1621.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_1621.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_1621.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_1621.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_1621.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_1621.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_1621.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_1621.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_1621.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_1621.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_1621.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_1621.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_1621.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _59_1621.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_1621.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_1621.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _59_1621.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_1621.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_1621.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_1621.FStar_TypeChecker_Env.qname_and_index})
in (

let _59_1624 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_551 = (FStar_Syntax_Print.tag_of_term e)
in (let _153_550 = (FStar_Syntax_Print.term_to_string e)
in (let _153_549 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _153_551 _153_550 _153_549))))
end else begin
()
end
in (

let _59_1629 = (tc_term env e)
in (match (_59_1629) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = ((e), (aq))
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(

let subst = (let _153_552 = (FStar_List.hd bs)
in (maybe_extend_subst subst _153_552 e))
in (tc_args head_info ((subst), ((((arg), (None), (None)))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(

let subst = (let _153_553 = (FStar_List.hd bs)
in (maybe_extend_subst subst _153_553 e))
in (tc_args head_info ((subst), ((((arg), (Some (x)), (Some (c))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (let _153_554 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _153_554)) then begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _153_555 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _153_555))
in (tc_args head_info ((subst), ((((arg), (Some (newx)), (Some (c))))::outargs), ((arg')::arg_rets), (g), (fvs)) rest rest')))
end else begin
(let _153_559 = (let _153_558 = (let _153_557 = (let _153_556 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _153_556))
in (_153_557)::arg_rets)
in ((subst), ((((arg), (Some (x)), (Some (c))))::outargs), (_153_558), (g), ((x)::fvs)))
in (tc_args head_info _153_559 rest rest'))
end
end
end))
end))))))))))
end
| (_59_1637, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::_59_1642) -> begin
(

let _59_1649 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (_59_1649) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _153_564 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _153_564 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let _59_1660 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (_59_1660) with
| (bs, cres') -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp cres')))
in (

let _59_1662 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_565 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _153_565))
end else begin
()
end
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args)))
end))
end
| _59_1665 when (not (norm)) -> begin
(let _153_566 = (unfold_whnf env tres)
in (aux true _153_566))
end
| _59_1667 -> begin
(let _153_572 = (let _153_571 = (let _153_570 = (let _153_568 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (let _153_567 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _153_568 _153_567)))
in (let _153_569 = (FStar_Syntax_Syntax.argpos arg)
in ((_153_570), (_153_569))))
in FStar_Syntax_Syntax.Error (_153_571))
in (Prims.raise _153_572))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (match ((let _153_577 = (FStar_Syntax_Util.unrefine tf)
in _153_577.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl -> begin
(

let _59_1700 = (tc_term env e)
in (match (_59_1700) with
| (e, c, g_e) -> begin
(

let _59_1704 = (tc_args env tl)
in (match (_59_1704) with
| (args, comps, g_rest) -> begin
(let _153_582 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e), (imp)))::args), ((((e.FStar_Syntax_Syntax.pos), (c)))::comps), (_153_582)))
end))
end))
end))
in (

let _59_1708 = (tc_args env args)
in (match (_59_1708) with
| (args, comps, g_args) -> begin
(

let bs = (let _153_584 = (FStar_All.pipe_right comps (FStar_List.map (fun _59_1712 -> (match (_59_1712) with
| (_59_1710, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks _153_584))
in (

let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _59_1718 -> begin
FStar_Syntax_Util.ml_comp
end)
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _153_599 = (FStar_Syntax_Subst.compress t)
in _153_599.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_59_1724) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _59_1729 -> begin
ml_or_tot
end)
end)
in (

let cres = (let _153_604 = (let _153_603 = (let _153_602 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_602 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _153_603))
in (ml_or_tot _153_604 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (

let _59_1733 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _153_607 = (FStar_Syntax_Print.term_to_string head)
in (let _153_606 = (FStar_Syntax_Print.term_to_string tf)
in (let _153_605 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _153_607 _153_606 _153_605))))
end else begin
()
end
in (

let _59_1735 = (let _153_608 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _153_608))
in (

let comp = (let _153_611 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _59_1739 out -> (match (_59_1739) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c ((None), (out)))
end)) ((((head.FStar_Syntax_Syntax.pos), (chead)))::comps) _153_611))
in (let _153_613 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _153_612 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((_153_613), (comp), (_153_612))))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _59_1748 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_59_1748) with
| (bs, c) -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp c)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args))
end))
end
| _59_1751 -> begin
if (not (norm)) then begin
(let _153_614 = (unfold_whnf env tf)
in (check_function_app true _153_614))
end else begin
(let _153_617 = (let _153_616 = (let _153_615 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in ((_153_615), (head.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_153_616))
in (Prims.raise _153_617))
end
end))
in (let _153_619 = (let _153_618 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _153_618))
in (check_function_app false _153_619))))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let _59_1787 = (FStar_List.fold_left2 (fun _59_1768 _59_1771 _59_1774 -> (match (((_59_1768), (_59_1771), (_59_1774))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(

let _59_1775 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifiers"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _59_1780 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_59_1780) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (let _153_629 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _153_629 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _153_633 = (let _153_631 = (let _153_630 = (FStar_Syntax_Syntax.as_arg e)
in (_153_630)::[])
in (FStar_List.append seen _153_631))
in (let _153_632 = (FStar_TypeChecker_Rel.conj_guard guard g)
in ((_153_633), (_153_632), (ghost)))))))
end)))
end)) (([]), (g_head), (false)) args bs)
in (match (_59_1787) with
| (args, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = if ghost then begin
(let _153_634 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _153_634 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (

let _59_1792 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_59_1792) with
| (c, g) -> begin
((e), (c), (g))
end))))
end)))
end
| _59_1794 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let _59_1801 = (FStar_Syntax_Subst.open_branch branch)
in (match (_59_1801) with
| (pattern, when_clause, branch_exp) -> begin
(

let _59_1806 = branch
in (match (_59_1806) with
| (cpat, _59_1804, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _59_1814 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_59_1814) with
| (pat_bvs, exps, p) -> begin
(

let _59_1815 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_646 = (FStar_Syntax_Print.pat_to_string p0)
in (let _153_645 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _153_646 _153_645)))
end else begin
()
end
in (

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let _59_1821 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_59_1821) with
| (env1, _59_1820) -> begin
(

let env1 = (

let _59_1822 = env1
in {FStar_TypeChecker_Env.solver = _59_1822.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_1822.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_1822.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_1822.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_1822.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_1822.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_1822.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_1822.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _59_1822.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_1822.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_1822.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_1822.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_1822.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_1822.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_1822.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_1822.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_1822.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_1822.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _59_1822.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_1822.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_1822.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_1822.FStar_TypeChecker_Env.qname_and_index})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _59_1861 = (let _153_669 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _59_1827 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_649 = (FStar_Syntax_Print.term_to_string e)
in (let _153_648 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _153_649 _153_648)))
end else begin
()
end
in (

let _59_1832 = (tc_term env1 e)
in (match (_59_1832) with
| (e, lc, g) -> begin
(

let _59_1833 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_651 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _153_650 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _153_651 _153_650)))
end else begin
()
end
in (

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let _59_1839 = (let _153_652 = (FStar_TypeChecker_Rel.discharge_guard env (

let _59_1837 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _59_1837.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _59_1837.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _59_1837.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _153_652 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _153_657 = (let _153_656 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _153_656 (FStar_List.map (fun _59_1847 -> (match (_59_1847) with
| (u, _59_1846) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _153_657 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _59_1855 = if (let _153_658 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _153_658)) then begin
(

let unresolved = (let _153_659 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _153_659 FStar_Util.set_elements))
in (let _153_667 = (let _153_666 = (let _153_665 = (let _153_664 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _153_663 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _153_662 = (let _153_661 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _59_1854 -> (match (_59_1854) with
| (u, _59_1853) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _153_661 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _153_664 _153_663 _153_662))))
in ((_153_665), (p.FStar_Syntax_Syntax.p)))
in FStar_Syntax_Syntax.Error (_153_666))
in (Prims.raise _153_667)))
end else begin
()
end
in (

let _59_1857 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_668 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _153_668))
end else begin
()
end
in ((e), (e'))))))))))))
end))))))
in (FStar_All.pipe_right _153_669 FStar_List.unzip))
in (match (_59_1861) with
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

let _59_1868 = (let _153_670 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _153_670 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_59_1868) with
| (scrutinee_env, _59_1867) -> begin
(

let _59_1874 = (tc_pat true pat_t pattern)
in (match (_59_1874) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let _59_1884 = (match (when_clause) with
| None -> begin
((None), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (e) -> begin
if (FStar_TypeChecker_Env.should_verify env) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("When clauses are not yet supported in --verify mode; they will be some day"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
(

let _59_1881 = (let _153_671 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _153_671 e))
in (match (_59_1881) with
| (e, c, g) -> begin
((Some (e)), (g))
end))
end
end)
in (match (_59_1884) with
| (when_clause, g_when) -> begin
(

let _59_1888 = (tc_term pat_env branch_exp)
in (match (_59_1888) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _153_673 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _153_672 -> Some (_153_672)) _153_673))
end)
in (

let _59_1946 = (

let eqs = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
None
end else begin
(FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _59_1906 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _153_677 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _153_676 -> Some (_153_676)) _153_677))
end))
end))) None))
end
in (

let _59_1914 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_59_1914) with
| (c, g_branch) -> begin
(

let _59_1941 = (match (((eqs), (when_condition))) with
| _59_1916 when (not ((FStar_TypeChecker_Env.should_verify env))) -> begin
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
in (let _153_680 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _153_679 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((_153_680), (_153_679))))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (let _153_681 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_153_681))
in (let _153_684 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _153_683 = (let _153_682 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _153_682 g_when))
in ((_153_684), (_153_683))))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _153_685 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in ((_153_685), (g_when)))))
end)
in (match (_59_1941) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _153_687 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _153_686 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in ((_153_687), (_153_686), (g_branch)))))
end))
end)))
in (match (_59_1946) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
FStar_Syntax_Util.t_true
end else begin
(

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> if ((let _153_697 = (let _153_696 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _153_696))
in (FStar_List.length _153_697)) > (Prims.parse_int "1")) then begin
(

let disc = (let _153_698 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _153_698 FStar_Syntax_Syntax.Delta_equational None))
in (

let disc = (let _153_700 = (let _153_699 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_153_699)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _153_700 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _153_701 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_153_701)::[])))
end else begin
[]
end)
in (

let fail = (fun _59_1956 -> (match (()) with
| () -> begin
(let _153_707 = (let _153_706 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _153_705 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _153_704 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _153_706 _153_705 _153_704))))
in (FStar_All.failwith _153_707))
end))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _59_1963) -> begin
(head_constructor t)
end
| _59_1967 -> begin
(fail ())
end))
in (

let pat_exp = (let _153_710 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _153_710 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_59_1992) -> begin
(let _153_715 = (let _153_714 = (let _153_713 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _153_712 = (let _153_711 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_153_711)::[])
in (_153_713)::_153_712))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _153_714 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_153_715)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _153_716 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _153_716))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(

let sub_term_guards = (let _153_723 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _59_2010 -> (match (_59_2010) with
| (ei, _59_2009) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _59_2014 -> begin
(

let sub_term = (let _153_722 = (let _153_719 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _153_719 FStar_Syntax_Syntax.Delta_equational None))
in (let _153_721 = (let _153_720 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_153_720)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _153_722 _153_721 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _153_723 FStar_List.flatten))
in (let _153_724 = (discriminate scrutinee_tm f)
in (FStar_List.append _153_724 sub_term_guards)))
end)
end
| _59_2018 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(

let t = (let _153_729 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _153_729))
in (

let _59_2026 = (FStar_Syntax_Util.type_u ())
in (match (_59_2026) with
| (k, _59_2025) -> begin
(

let _59_2032 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_59_2032) with
| (t, _59_2029, _59_2031) -> begin
t
end))
end)))
end)
in (

let branch_guard = (let _153_730 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _153_730 FStar_Syntax_Util.mk_disj_l))
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

let _59_2040 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_731 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _153_731))
end else begin
()
end
in (let _153_732 = (FStar_Syntax_Subst.close_branch ((pattern), (when_clause), (branch_exp)))
in ((_153_732), (branch_guard), (c), (guard))))))
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

let _59_2057 = (check_let_bound_def true env lb)
in (match (_59_2057) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let _59_2069 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
((g1), (e1), (univ_vars), (c1))
end else begin
(

let g1 = (let _153_735 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _153_735 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _59_2064 = (let _153_739 = (let _153_738 = (let _153_737 = (let _153_736 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (_153_736)))
in (_153_737)::[])
in (FStar_TypeChecker_Util.generalize env _153_738))
in (FStar_List.hd _153_739))
in (match (_59_2064) with
| (_59_2060, univs, e1, c1) -> begin
((g1), (e1), (univs), ((FStar_Syntax_Util.lcomp_of_comp c1)))
end)))
end
in (match (_59_2069) with
| (g1, e1, univ_vars, c1) -> begin
(

let _59_2079 = if (FStar_TypeChecker_Env.should_verify env) then begin
(

let _59_2072 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_59_2072) with
| (ok, c1) -> begin
if ok then begin
((e2), (c1))
end else begin
(

let _59_2073 = if (FStar_Options.warn_top_level_effects ()) then begin
(let _153_740 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _153_740 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _153_741 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) None e2.FStar_Syntax_Syntax.pos)
in ((_153_741), (c1))))
end
end))
end else begin
(

let _59_2075 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _153_742 = (c1.FStar_Syntax_Syntax.comp ())
in ((e2), (_153_742))))
end
in (match (_59_2079) with
| (e2, c1) -> begin
(

let cres = (let _153_743 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _153_743))
in (

let _59_2081 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _153_744 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((_153_744), (cres), (FStar_TypeChecker_Rel.trivial_guard))))))
end))
end))
end))
end
| _59_2085 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let _59_2096 = env
in {FStar_TypeChecker_Env.solver = _59_2096.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_2096.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_2096.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_2096.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_2096.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_2096.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_2096.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_2096.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_2096.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_2096.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_2096.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_2096.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_2096.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _59_2096.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_2096.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_2096.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_2096.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_2096.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _59_2096.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_2096.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_2096.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_2096.FStar_TypeChecker_Env.qname_and_index})
in (

let _59_2105 = (let _153_748 = (let _153_747 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _153_747 Prims.fst))
in (check_let_bound_def false _153_748 lb))
in (match (_59_2105) with
| (e1, _59_2101, c1, g1, annotated) -> begin
(

let x = (

let _59_2106 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _59_2106.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_2106.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let _59_2112 = (let _153_750 = (let _153_749 = (FStar_Syntax_Syntax.mk_binder x)
in (_153_749)::[])
in (FStar_Syntax_Subst.open_term _153_750 e2))
in (match (_59_2112) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _59_2118 = (let _153_751 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _153_751 e2))
in (match (_59_2118) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (x)), (c2)))
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e2 = (FStar_TypeChecker_Util.maybe_lift env e2 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e = (let _153_754 = (let _153_753 = (let _153_752 = (FStar_Syntax_Subst.close xb e2)
in ((((false), ((lb)::[]))), (_153_752)))
in FStar_Syntax_Syntax.Tm_let (_153_753))
in (FStar_Syntax_Syntax.mk _153_754 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (let _153_757 = (let _153_756 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _153_756 e1))
in (FStar_All.pipe_left (fun _153_755 -> FStar_TypeChecker_Common.NonTrivial (_153_755)) _153_757))
in (

let g2 = (let _153_759 = (let _153_758 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _153_758 g2))
in (FStar_TypeChecker_Rel.close_guard xb _153_759))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if (let _153_760 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome _153_760)) then begin
((e), (cres), (guard))
end else begin
(

let _59_2127 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in ((e), (cres), (guard)))
end))))))))
end))))
end))))
end)))
end
| _59_2130 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _59_2142 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_59_2142) with
| (lbs, e2) -> begin
(

let _59_2145 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_2145) with
| (env0, topt) -> begin
(

let _59_2148 = (build_let_rec_env true env0 lbs)
in (match (_59_2148) with
| (lbs, rec_env) -> begin
(

let _59_2151 = (check_let_recs rec_env lbs)
in (match (_59_2151) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (let _153_763 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _153_763 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _153_766 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _153_766 (fun _153_765 -> Some (_153_765))))
in (

let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(

let ecs = (let _153_770 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _153_769 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (_153_769))))))
in (FStar_TypeChecker_Util.generalize env _153_770))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _59_2162 -> (match (_59_2162) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _153_772 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _153_772))
in (

let _59_2165 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _59_2169 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_59_2169) with
| (lbs, e2) -> begin
(let _153_774 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _153_773 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in ((_153_774), (cres), (_153_773))))
end)))))))
end))
end))
end))
end))
end
| _59_2171 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _59_2183 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_59_2183) with
| (lbs, e2) -> begin
(

let _59_2186 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_2186) with
| (env0, topt) -> begin
(

let _59_2189 = (build_let_rec_env false env0 lbs)
in (match (_59_2189) with
| (lbs, rec_env) -> begin
(

let _59_2192 = (check_let_recs rec_env lbs)
in (match (_59_2192) with
| (lbs, g_lbs) -> begin
(

let _59_2204 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let _59_2195 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _59_2195.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_2195.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let _59_2198 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _59_2198.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _59_2198.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _59_2198.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _59_2198.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (lb.FStar_Syntax_Syntax.lbtyp)))
in ((env), (lb)))))) env))
in (match (_59_2204) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let _59_2210 = (tc_term env e2)
in (match (_59_2210) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _59_2214 = cres
in {FStar_Syntax_Syntax.eff_name = _59_2214.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _59_2214.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _59_2214.FStar_Syntax_Syntax.comp})
in (

let _59_2219 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_59_2219) with
| (lbs, e2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_59_2222) -> begin
((e), (cres), (guard))
end
| None -> begin
(

let _59_2225 = (check_no_escape None env bvs tres)
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
| _59_2228 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun t -> (

let _59_2238 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (_59_2238) with
| (_59_2236, c) -> begin
(

let quals = (FStar_TypeChecker_Env.lookup_effect_quals env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
end)))
in (

let _59_2268 = (FStar_List.fold_left (fun _59_2242 lb -> (match (_59_2242) with
| (lbs, env) -> begin
(

let _59_2247 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_59_2247) with
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

let _59_2256 = (let _153_788 = (let _153_787 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _153_787))
in (tc_check_tot_or_gtot_term (

let _59_2250 = env0
in {FStar_TypeChecker_Env.solver = _59_2250.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_2250.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_2250.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_2250.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_2250.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_2250.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_2250.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_2250.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_2250.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_2250.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_2250.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_2250.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_2250.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_2250.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _59_2250.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_2250.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_2250.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_2250.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _59_2250.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_2250.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_2250.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_2250.FStar_TypeChecker_Env.qname_and_index}) t _153_788))
in (match (_59_2256) with
| (t, _59_2254, g) -> begin
(

let _59_2257 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (

let env = if ((termination_check_enabled t) && (FStar_TypeChecker_Env.should_verify env)) then begin
(

let _59_2260 = env
in {FStar_TypeChecker_Env.solver = _59_2260.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_2260.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_2260.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_2260.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_2260.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_2260.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_2260.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_2260.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_2260.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_2260.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_2260.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_2260.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t)))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_2260.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_2260.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_2260.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_2260.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_2260.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_2260.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _59_2260.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_2260.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_2260.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_2260.FStar_TypeChecker_Env.qname_and_index})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (t)))
end
in (

let lb = (

let _59_2263 = lb
in {FStar_Syntax_Syntax.lbname = _59_2263.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _59_2263.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb)::lbs), (env)))))))
end))
end)) (([]), (env)) lbs)
in (match (_59_2268) with
| (lbs, env) -> begin
(((FStar_List.rev lbs)), (env))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _59_2281 = (let _153_793 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _59_2275 = (let _153_792 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _153_792 lb.FStar_Syntax_Syntax.lbdef))
in (match (_59_2275) with
| (e, c, g) -> begin
(

let _59_2276 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in ((lb), (g))))
end)))))
in (FStar_All.pipe_right _153_793 FStar_List.unzip))
in (match (_59_2281) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _59_2289 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_2289) with
| (env1, _59_2288) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _59_2295 = (check_lbtyp top_level env lb)
in (match (_59_2295) with
| (topt, wf_annot, univ_vars, env1) -> begin
(

let _59_2296 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _59_2303 = (tc_maybe_toplevel_term (

let _59_2298 = env1
in {FStar_TypeChecker_Env.solver = _59_2298.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_2298.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_2298.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_2298.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_2298.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_2298.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_2298.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_2298.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_2298.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_2298.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_2298.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_2298.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_2298.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _59_2298.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_2298.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_2298.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_2298.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_2298.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _59_2298.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_2298.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_2298.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_2298.FStar_TypeChecker_Env.qname_and_index}) e1)
in (match (_59_2303) with
| (e1, c1, g1) -> begin
(

let _59_2307 = (let _153_800 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _59_2304 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _153_800 e1 c1 wf_annot))
in (match (_59_2307) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _59_2309 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _153_801 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _153_801))
end else begin
()
end
in (let _153_802 = (FStar_Option.isSome topt)
in ((e1), (univ_vars), (c1), (g1), (_153_802)))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _59_2316 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in ((None), (FStar_TypeChecker_Rel.trivial_guard), ([]), (env)))
end
| _59_2319 -> begin
(

let _59_2322 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_59_2322) with
| (univ_vars, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _153_806 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars), (_153_806)))
end else begin
(

let _59_2327 = (FStar_Syntax_Util.type_u ())
in (match (_59_2327) with
| (k, _59_2326) -> begin
(

let _59_2332 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_59_2332) with
| (t, _59_2330, g) -> begin
(

let _59_2333 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _153_809 = (let _153_807 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _153_807))
in (let _153_808 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _153_809 _153_808)))
end else begin
()
end
in (

let t = (norm env1 t)
in (let _153_810 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (g), (univ_vars), (_153_810)))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _59_2339 -> (match (_59_2339) with
| (x, imp) -> begin
(

let _59_2342 = (FStar_Syntax_Util.type_u ())
in (match (_59_2342) with
| (tu, u) -> begin
(

let _59_2343 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _153_815 = (FStar_Syntax_Print.bv_to_string x)
in (let _153_814 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _153_813 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binders %s:%s at type %s\n" _153_815 _153_814 _153_813))))
end else begin
()
end
in (

let _59_2349 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_59_2349) with
| (t, _59_2347, g) -> begin
(

let x = (((

let _59_2350 = x
in {FStar_Syntax_Syntax.ppname = _59_2350.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_2350.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in (

let _59_2353 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_817 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _153_816 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _153_817 _153_816)))
end else begin
()
end
in (let _153_818 = (push_binding env x)
in ((x), (_153_818), (g), (u)))))
end)))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe Prims.list) = (fun env bs -> (

let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
(([]), (env), (FStar_TypeChecker_Rel.trivial_guard), ([]))
end
| (b)::bs -> begin
(

let _59_2368 = (tc_binder env b)
in (match (_59_2368) with
| (b, env', g, u) -> begin
(

let _59_2373 = (aux env' bs)
in (match (_59_2373) with
| (bs, env', g', us) -> begin
(let _153_826 = (let _153_825 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _153_825))
in (((b)::bs), (env'), (_153_826), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun _59_2381 _59_2384 -> (match (((_59_2381), (_59_2384))) with
| ((t, imp), (args, g)) -> begin
(

let _59_2389 = (tc_term env t)
in (match (_59_2389) with
| (t, _59_2387, g') -> begin
(let _153_835 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t), (imp)))::args), (_153_835)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p _59_2393 -> (match (_59_2393) with
| (pats, g) -> begin
(

let _59_2396 = (tc_args env p)
in (match (_59_2396) with
| (args, g') -> begin
(let _153_838 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats), (_153_838)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _59_2402 = (tc_maybe_toplevel_term env e)
in (match (_59_2402) with
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

let _59_2408 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _153_841 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in ((_153_841), (false)))
end else begin
(let _153_842 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in ((_153_842), (true)))
end
in (match (_59_2408) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _153_843 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (_153_843)))
end
| _59_2412 -> begin
if allow_ghost then begin
(let _153_846 = (let _153_845 = (let _153_844 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in ((_153_844), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_153_845))
in (Prims.raise _153_846))
end else begin
(let _153_849 = (let _153_848 = (let _153_847 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in ((_153_847), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_153_848))
in (Prims.raise _153_849))
end
end)
end)))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let _59_2422 = (tc_tot_or_gtot_term env t)
in (match (_59_2422) with
| (t, c, g) -> begin
(

let _59_2423 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in ((t), (c)))
end)))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let _59_2431 = (tc_check_tot_or_gtot_term env t k)
in (match (_59_2431) with
| (t, c, g) -> begin
(

let _59_2432 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _153_867 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _153_867)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _153_871 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (([]), (_153_871)))))


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let _59_2447 = (tc_binders env tps)
in (match (_59_2447) with
| (tps, env, g, us) -> begin
(

let _59_2448 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in ((tps), (env), (us)))
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (

let fail = (fun _59_2454 -> (match (()) with
| () -> begin
(let _153_886 = (let _153_885 = (let _153_884 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in ((_153_884), ((FStar_Ident.range_of_lid m))))
in FStar_Syntax_Syntax.Error (_153_885))
in (Prims.raise _153_886))
end))
in (

let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _59_2467))::((wp, _59_2463))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _59_2471 -> begin
(fail ())
end))
end
| _59_2473 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let _59_2480 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_59_2480) with
| (uvs, c) -> begin
((uvs), ([]), (c))
end))
end
| _59_2482 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let _59_2486 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_59_2486) with
| (uvs, t') -> begin
(match ((let _153_893 = (FStar_Syntax_Subst.compress t')
in _153_893.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
((uvs), (binders), (c))
end
| _59_2492 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))


let rec tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (

let _59_2495 = ()
in (

let _59_2500 = (FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_59_2500) with
| (effect_params_un, signature_un, opening) -> begin
(

let _59_2505 = (tc_tparams env0 effect_params_un)
in (match (_59_2505) with
| (effect_params, env, _59_2504) -> begin
(

let _59_2509 = (tc_trivial_guard env signature_un)
in (match (_59_2509) with
| (signature, _59_2508) -> begin
(

let ed = (

let _59_2510 = ed
in {FStar_Syntax_Syntax.qualifiers = _59_2510.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _59_2510.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _59_2510.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _59_2510.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _59_2510.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _59_2510.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _59_2510.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _59_2510.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _59_2510.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _59_2510.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _59_2510.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _59_2510.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _59_2510.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _59_2510.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _59_2510.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _59_2510.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _59_2510.FStar_Syntax_Syntax.actions})
in (

let ed = (match (effect_params) with
| [] -> begin
ed
end
| _59_2515 -> begin
(

let op = (fun ts -> (

let _59_2518 = ()
in (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in (([]), (t1)))))
in (

let _59_2521 = ed
in (let _153_936 = (op ed.FStar_Syntax_Syntax.ret_wp)
in (let _153_935 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _153_934 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _153_933 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _153_932 = (op ed.FStar_Syntax_Syntax.stronger)
in (let _153_931 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _153_930 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _153_929 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _153_928 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _153_927 = (op ed.FStar_Syntax_Syntax.trivial)
in (let _153_926 = (let _153_917 = (op (([]), (ed.FStar_Syntax_Syntax.repr)))
in (Prims.snd _153_917))
in (let _153_925 = (op ed.FStar_Syntax_Syntax.return_repr)
in (let _153_924 = (op ed.FStar_Syntax_Syntax.bind_repr)
in (let _153_923 = (FStar_List.map (fun a -> (

let _59_2524 = a
in (let _153_922 = (let _153_919 = (op (([]), (a.FStar_Syntax_Syntax.action_defn)))
in (Prims.snd _153_919))
in (let _153_921 = (let _153_920 = (op (([]), (a.FStar_Syntax_Syntax.action_typ)))
in (Prims.snd _153_920))
in {FStar_Syntax_Syntax.action_name = _59_2524.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = _59_2524.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _153_922; FStar_Syntax_Syntax.action_typ = _153_921})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = _59_2521.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _59_2521.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _59_2521.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _59_2521.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _59_2521.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _153_936; FStar_Syntax_Syntax.bind_wp = _153_935; FStar_Syntax_Syntax.if_then_else = _153_934; FStar_Syntax_Syntax.ite_wp = _153_933; FStar_Syntax_Syntax.stronger = _153_932; FStar_Syntax_Syntax.close_wp = _153_931; FStar_Syntax_Syntax.assert_p = _153_930; FStar_Syntax_Syntax.assume_p = _153_929; FStar_Syntax_Syntax.null_wp = _153_928; FStar_Syntax_Syntax.trivial = _153_927; FStar_Syntax_Syntax.repr = _153_926; FStar_Syntax_Syntax.return_repr = _153_925; FStar_Syntax_Syntax.bind_repr = _153_924; FStar_Syntax_Syntax.actions = _153_923}))))))))))))))))
end)
in (

let wp_with_fresh_result_type = (fun env mname signature -> (

let fail = (fun t -> (let _153_947 = (let _153_946 = (let _153_945 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in ((_153_945), ((FStar_Ident.range_of_lid mname))))
in FStar_Syntax_Syntax.Error (_153_946))
in (Prims.raise _153_947)))
in (match ((let _153_948 = (FStar_Syntax_Subst.compress signature)
in _153_948.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _59_2544))::((wp, _59_2540))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _59_2548 -> begin
(fail signature)
end))
end
| _59_2550 -> begin
(fail signature)
end)))
in (

let _59_2553 = (wp_with_fresh_result_type env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_59_2553) with
| (a, wp_a) -> begin
(

let fresh_effect_signature = (fun _59_2555 -> (match (()) with
| () -> begin
(

let _59_2559 = (tc_trivial_guard env signature_un)
in (match (_59_2559) with
| (signature, _59_2558) -> begin
(wp_with_fresh_result_type env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (

let env = (let _153_951 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _153_951))
in (

let _59_2561 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _153_957 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _153_956 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _153_955 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _153_954 = (let _153_952 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Print.term_to_string _153_952))
in (let _153_953 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort)
in (FStar_Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n" _153_957 _153_956 _153_955 _153_954 _153_953))))))
end else begin
()
end
in (

let check_and_gen' = (fun env _59_2568 k -> (match (_59_2568) with
| (_59_2566, t) -> begin
(check_and_gen env t k)
end))
in (

let return_wp = (

let expected_k = (let _153_969 = (let _153_967 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_966 = (let _153_965 = (let _153_964 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _153_964))
in (_153_965)::[])
in (_153_967)::_153_966))
in (let _153_968 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _153_969 _153_968)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let _59_2574 = (fresh_effect_signature ())
in (match (_59_2574) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _153_973 = (let _153_971 = (let _153_970 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _153_970))
in (_153_971)::[])
in (let _153_972 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _153_973 _153_972)))
in (

let expected_k = (let _153_984 = (let _153_982 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _153_981 = (let _153_980 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_979 = (let _153_978 = (FStar_Syntax_Syntax.mk_binder b)
in (let _153_977 = (let _153_976 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _153_975 = (let _153_974 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (_153_974)::[])
in (_153_976)::_153_975))
in (_153_978)::_153_977))
in (_153_980)::_153_979))
in (_153_982)::_153_981))
in (let _153_983 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _153_984 _153_983)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (let _153_986 = (let _153_985 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_985 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _153_986))
in (

let expected_k = (let _153_995 = (let _153_993 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_992 = (let _153_991 = (FStar_Syntax_Syntax.mk_binder p)
in (let _153_990 = (let _153_989 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _153_988 = (let _153_987 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_987)::[])
in (_153_989)::_153_988))
in (_153_991)::_153_990))
in (_153_993)::_153_992))
in (let _153_994 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_995 _153_994)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (let _153_1000 = (let _153_998 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_997 = (let _153_996 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_996)::[])
in (_153_998)::_153_997))
in (let _153_999 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_1000 _153_999)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let _59_2586 = (FStar_Syntax_Util.type_u ())
in (match (_59_2586) with
| (t, _59_2585) -> begin
(

let expected_k = (let _153_1007 = (let _153_1005 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_1004 = (let _153_1003 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _153_1002 = (let _153_1001 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_1001)::[])
in (_153_1003)::_153_1002))
in (_153_1005)::_153_1004))
in (let _153_1006 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _153_1007 _153_1006)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (let _153_1009 = (let _153_1008 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_1008 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _153_1009))
in (

let b_wp_a = (let _153_1013 = (let _153_1011 = (let _153_1010 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _153_1010))
in (_153_1011)::[])
in (let _153_1012 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_1013 _153_1012)))
in (

let expected_k = (let _153_1020 = (let _153_1018 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_1017 = (let _153_1016 = (FStar_Syntax_Syntax.mk_binder b)
in (let _153_1015 = (let _153_1014 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_153_1014)::[])
in (_153_1016)::_153_1015))
in (_153_1018)::_153_1017))
in (let _153_1019 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_1020 _153_1019)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (let _153_1029 = (let _153_1027 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_1026 = (let _153_1025 = (let _153_1022 = (let _153_1021 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_1021 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _153_1022))
in (let _153_1024 = (let _153_1023 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_1023)::[])
in (_153_1025)::_153_1024))
in (_153_1027)::_153_1026))
in (let _153_1028 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_1029 _153_1028)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _153_1038 = (let _153_1036 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_1035 = (let _153_1034 = (let _153_1031 = (let _153_1030 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_1030 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _153_1031))
in (let _153_1033 = (let _153_1032 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_1032)::[])
in (_153_1034)::_153_1033))
in (_153_1036)::_153_1035))
in (let _153_1037 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_1038 _153_1037)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _153_1041 = (let _153_1039 = (FStar_Syntax_Syntax.mk_binder a)
in (_153_1039)::[])
in (let _153_1040 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_1041 _153_1040)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let _59_2602 = (FStar_Syntax_Util.type_u ())
in (match (_59_2602) with
| (t, _59_2601) -> begin
(

let expected_k = (let _153_1046 = (let _153_1044 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_1043 = (let _153_1042 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_1042)::[])
in (_153_1044)::_153_1043))
in (let _153_1045 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _153_1046 _153_1045)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let _59_2743 = if ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) || (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable))) then begin
(

let repr = (

let _59_2608 = (FStar_Syntax_Util.type_u ())
in (match (_59_2608) with
| (t, _59_2607) -> begin
(

let expected_k = (let _153_1051 = (let _153_1049 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_1048 = (let _153_1047 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_1047)::[])
in (_153_1049)::_153_1048))
in (let _153_1050 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _153_1051 _153_1050)))
in (tc_check_trivial_guard env ed.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (

let repr = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env repr)
in (let _153_1061 = (let _153_1060 = (let _153_1059 = (let _153_1058 = (FStar_Syntax_Syntax.as_arg t)
in (let _153_1057 = (let _153_1056 = (FStar_Syntax_Syntax.as_arg wp)
in (_153_1056)::[])
in (_153_1058)::_153_1057))
in ((repr), (_153_1059)))
in FStar_Syntax_Syntax.Tm_app (_153_1060))
in (FStar_Syntax_Syntax.mk _153_1061 None FStar_Range.dummyRange))))
in (

let mk_repr = (fun a wp -> (let _153_1066 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_repr' _153_1066 wp)))
in (

let destruct_repr = (fun t -> (match ((let _153_1069 = (FStar_Syntax_Subst.compress t)
in _153_1069.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_59_2621, ((t, _59_2628))::((wp, _59_2624))::[]) -> begin
((t), (wp))
end
| _59_2634 -> begin
(FStar_All.failwith "Unexpected repr type")
end))
in (

let bind_repr = (

let r = (let _153_1070 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_0 FStar_Syntax_Syntax.Delta_constant None)
in (FStar_All.pipe_right _153_1070 FStar_Syntax_Syntax.fv_to_tm))
in (

let _59_2638 = (fresh_effect_signature ())
in (match (_59_2638) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _153_1074 = (let _153_1072 = (let _153_1071 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _153_1071))
in (_153_1072)::[])
in (let _153_1073 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _153_1074 _153_1073)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" None a_wp_b)
in (

let x_a = (let _153_1075 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _153_1075))
in (

let wp_g_x = (let _153_1079 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (let _153_1078 = (let _153_1077 = (let _153_1076 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _153_1076))
in (_153_1077)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _153_1079 _153_1078 None FStar_Range.dummyRange)))
in (

let res = (

let wp = (let _153_1091 = (let _153_1080 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right _153_1080 Prims.snd))
in (let _153_1090 = (let _153_1089 = (let _153_1088 = (let _153_1087 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _153_1086 = (let _153_1085 = (FStar_Syntax_Syntax.bv_to_name b)
in (let _153_1084 = (let _153_1083 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (let _153_1082 = (let _153_1081 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (_153_1081)::[])
in (_153_1083)::_153_1082))
in (_153_1085)::_153_1084))
in (_153_1087)::_153_1086))
in (r)::_153_1088)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _153_1089))
in (FStar_Syntax_Syntax.mk_Tm_app _153_1091 _153_1090 None FStar_Range.dummyRange)))
in (mk_repr b wp))
in (

let expected_k = (let _153_1111 = (let _153_1109 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_1108 = (let _153_1107 = (FStar_Syntax_Syntax.mk_binder b)
in (let _153_1106 = (let _153_1105 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (let _153_1104 = (let _153_1103 = (let _153_1093 = (let _153_1092 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a _153_1092))
in (FStar_Syntax_Syntax.null_binder _153_1093))
in (let _153_1102 = (let _153_1101 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (let _153_1100 = (let _153_1099 = (let _153_1098 = (let _153_1097 = (let _153_1094 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_153_1094)::[])
in (let _153_1096 = (let _153_1095 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _153_1095))
in (FStar_Syntax_Util.arrow _153_1097 _153_1096)))
in (FStar_Syntax_Syntax.null_binder _153_1098))
in (_153_1099)::[])
in (_153_1101)::_153_1100))
in (_153_1103)::_153_1102))
in (_153_1105)::_153_1104))
in (_153_1107)::_153_1106))
in (_153_1109)::_153_1108))
in (let _153_1110 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _153_1111 _153_1110)))
in (

let _59_2652 = (tc_tot_or_gtot_term env expected_k)
in (match (_59_2652) with
| (expected_k, _59_2649, _59_2651) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (

let env = (

let _59_2654 = env
in {FStar_TypeChecker_Env.solver = _59_2654.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_2654.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_2654.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_2654.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_2654.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_2654.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_2654.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_2654.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_2654.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_2654.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_2654.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_2654.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_2654.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_2654.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_2654.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_2654.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_2654.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_2654.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _59_2654.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_2654.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_2654.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_2654.FStar_TypeChecker_Env.qname_and_index})
in (

let br = (check_and_gen' env ed.FStar_Syntax_Syntax.bind_repr expected_k)
in br)))
end)))))))))
end)))
in (

let return_repr = (

let x_a = (let _153_1112 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _153_1112))
in (

let res = (

let wp = (let _153_1119 = (let _153_1113 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right _153_1113 Prims.snd))
in (let _153_1118 = (let _153_1117 = (let _153_1116 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _153_1115 = (let _153_1114 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (_153_1114)::[])
in (_153_1116)::_153_1115))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _153_1117))
in (FStar_Syntax_Syntax.mk_Tm_app _153_1119 _153_1118 None FStar_Range.dummyRange)))
in (mk_repr a wp))
in (

let expected_k = (let _153_1124 = (let _153_1122 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_1121 = (let _153_1120 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_153_1120)::[])
in (_153_1122)::_153_1121))
in (let _153_1123 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _153_1124 _153_1123)))
in (

let _59_2668 = (tc_tot_or_gtot_term env expected_k)
in (match (_59_2668) with
| (expected_k, _59_2665, _59_2667) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let _59_2672 = (check_and_gen' env ed.FStar_Syntax_Syntax.return_repr expected_k)
in (match (_59_2672) with
| (univs, repr) -> begin
(match (univs) with
| [] -> begin
(([]), (repr))
end
| _59_2675 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected universe-polymorphic return for effect"), (repr.FStar_Syntax_Syntax.pos)))))
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let _59_2683 = (tc_tot_or_gtot_term env act.FStar_Syntax_Syntax.action_typ)
in (match (_59_2683) with
| (act_typ, _59_2681, g_t) -> begin
(

let env' = (FStar_TypeChecker_Env.set_expected_typ env act_typ)
in (

let _59_2685 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _153_1128 = (FStar_Syntax_Print.term_to_string act.FStar_Syntax_Syntax.action_defn)
in (let _153_1127 = (FStar_Syntax_Print.term_to_string act_typ)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" (FStar_Ident.text_of_lid act.FStar_Syntax_Syntax.action_name) _153_1128 _153_1127)))
end else begin
()
end
in (

let _59_2691 = (tc_tot_or_gtot_term env' act.FStar_Syntax_Syntax.action_defn)
in (match (_59_2691) with
| (act_defn, _59_2689, g_a) -> begin
(

let act_defn = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env act_defn)
in (

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let _59_2714 = (

let act_typ = (FStar_Syntax_Subst.compress act_typ)
in (match (act_typ.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _59_2702 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_59_2702) with
| (bs, _59_2701) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (let _153_1129 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs _153_1129))
in (

let _59_2709 = (tc_tot_or_gtot_term env k)
in (match (_59_2709) with
| (k, _59_2707, g) -> begin
((k), (g))
end))))
end))
end
| _59_2711 -> begin
(let _153_1134 = (let _153_1133 = (let _153_1132 = (let _153_1131 = (FStar_Syntax_Print.term_to_string act_typ)
in (let _153_1130 = (FStar_Syntax_Print.tag_of_term act_typ)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" _153_1131 _153_1130)))
in ((_153_1132), (act_defn.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_153_1133))
in (Prims.raise _153_1134))
end))
in (match (_59_2714) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env act_typ expected_k)
in (

let _59_2716 = (let _153_1137 = (let _153_1136 = (let _153_1135 = (FStar_TypeChecker_Rel.conj_guard g_t g)
in (FStar_TypeChecker_Rel.conj_guard g_k _153_1135))
in (FStar_TypeChecker_Rel.conj_guard g_a _153_1136))
in (FStar_TypeChecker_Rel.force_trivial_guard env _153_1137))
in (

let act_typ = (match ((let _153_1138 = (FStar_Syntax_Subst.compress expected_k)
in _153_1138.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _59_2724 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_59_2724) with
| (bs, c) -> begin
(

let _59_2727 = (destruct_repr (FStar_Syntax_Util.comp_result c))
in (match (_59_2727) with
| (a, wp) -> begin
(

let c = (let _153_1140 = (let _153_1139 = (FStar_Syntax_Syntax.as_arg wp)
in (_153_1139)::[])
in {FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a; FStar_Syntax_Syntax.effect_args = _153_1140; FStar_Syntax_Syntax.flags = []})
in (let _153_1141 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Util.arrow bs _153_1141)))
end))
end))
end
| _59_2730 -> begin
(FStar_All.failwith "")
end)
in (

let _59_2734 = (FStar_TypeChecker_Util.generalize_universes env act_defn)
in (match (_59_2734) with
| (univs, act_defn) -> begin
(

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let _59_2736 = act
in {FStar_Syntax_Syntax.action_name = _59_2736.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = act_defn; FStar_Syntax_Syntax.action_typ = act_typ}))
end)))))
end))))
end))))
end)))
in (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.map check_action)))
in ((repr), (bind_repr), (return_repr), (actions)))))))))
end else begin
((ed.FStar_Syntax_Syntax.repr), (ed.FStar_Syntax_Syntax.bind_repr), (ed.FStar_Syntax_Syntax.return_repr), (ed.FStar_Syntax_Syntax.actions))
end
in (match (_59_2743) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t = (let _153_1142 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _153_1142))
in (

let _59_2747 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_59_2747) with
| (univs, t) -> begin
(

let signature = (match ((let _153_1144 = (let _153_1143 = (FStar_Syntax_Subst.compress t)
in _153_1143.FStar_Syntax_Syntax.n)
in ((effect_params), (_153_1144)))) with
| ([], _59_2750) -> begin
t
end
| (_59_2753, FStar_Syntax_Syntax.Tm_arrow (_59_2755, c)) -> begin
(FStar_Syntax_Util.comp_result c)
end
| _59_2761 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let close = (fun n ts -> (

let ts = (let _153_1149 = (FStar_Syntax_Subst.close_tscheme effect_params ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _153_1149))
in (

let _59_2767 = if (((n > (Prims.parse_int "0")) && (not ((FStar_Syntax_Util.is_unknown (Prims.snd ts))))) && ((FStar_List.length (Prims.fst ts)) <> n)) then begin
(let _153_1152 = (let _153_1151 = (FStar_Util.string_of_int n)
in (let _153_1150 = (FStar_Syntax_Print.tscheme_to_string ts)
in (FStar_Util.format2 "The effect combinator is not universe-polymorphic enough (n=%s) (%s)" _153_1151 _153_1150)))
in (FStar_All.failwith _153_1152))
end else begin
()
end
in ts)))
in (

let close_action = (fun act -> (

let _59_2773 = (close (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (_59_2773) with
| (univs, defn) -> begin
(

let _59_2776 = (close (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (_59_2776) with
| (univs', typ) -> begin
(

let _59_2777 = ()
in (

let _59_2779 = act
in {FStar_Syntax_Syntax.action_name = _59_2779.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ}))
end))
end)))
in (

let _59_2781 = ()
in (

let ed = (

let _59_2783 = ed
in (let _153_1169 = (close (Prims.parse_int "0") return_wp)
in (let _153_1168 = (close (Prims.parse_int "1") bind_wp)
in (let _153_1167 = (close (Prims.parse_int "0") if_then_else)
in (let _153_1166 = (close (Prims.parse_int "0") ite_wp)
in (let _153_1165 = (close (Prims.parse_int "0") stronger)
in (let _153_1164 = (close (Prims.parse_int "1") close_wp)
in (let _153_1163 = (close (Prims.parse_int "0") assert_p)
in (let _153_1162 = (close (Prims.parse_int "0") assume_p)
in (let _153_1161 = (close (Prims.parse_int "0") null_wp)
in (let _153_1160 = (close (Prims.parse_int "0") trivial_wp)
in (let _153_1159 = (let _153_1155 = (close (Prims.parse_int "0") (([]), (repr)))
in (Prims.snd _153_1155))
in (let _153_1158 = (close (Prims.parse_int "0") return_repr)
in (let _153_1157 = (close (Prims.parse_int "1") bind_repr)
in (let _153_1156 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.qualifiers = _59_2783.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _59_2783.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _153_1169; FStar_Syntax_Syntax.bind_wp = _153_1168; FStar_Syntax_Syntax.if_then_else = _153_1167; FStar_Syntax_Syntax.ite_wp = _153_1166; FStar_Syntax_Syntax.stronger = _153_1165; FStar_Syntax_Syntax.close_wp = _153_1164; FStar_Syntax_Syntax.assert_p = _153_1163; FStar_Syntax_Syntax.assume_p = _153_1162; FStar_Syntax_Syntax.null_wp = _153_1161; FStar_Syntax_Syntax.trivial = _153_1160; FStar_Syntax_Syntax.repr = _153_1159; FStar_Syntax_Syntax.return_repr = _153_1158; FStar_Syntax_Syntax.bind_repr = _153_1157; FStar_Syntax_Syntax.actions = _153_1156})))))))))))))))
in (

let _59_2786 = if ((FStar_TypeChecker_Env.debug env FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ED")))) then begin
(let _153_1170 = (FStar_Syntax_Print.eff_decl_to_string false ed)
in (FStar_Util.print_string _153_1170))
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

let _59_2792 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_59_2792) with
| (effect_binders_un, signature_un) -> begin
(

let _59_2797 = (tc_tparams env effect_binders_un)
in (match (_59_2797) with
| (effect_binders, env, _59_2796) -> begin
(

let _59_2801 = (tc_trivial_guard env signature_un)
in (match (_59_2801) with
| (signature, _59_2800) -> begin
(

let effect_binders = (FStar_List.map (fun _59_2804 -> (match (_59_2804) with
| (bv, qual) -> begin
(let _153_1175 = (

let _59_2805 = bv
in (let _153_1174 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _59_2805.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_2805.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _153_1174}))
in ((_153_1175), (qual)))
end)) effect_binders)
in (

let _59_2820 = (match ((let _153_1176 = (FStar_Syntax_Subst.compress signature_un)
in _153_1176.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (((a, _59_2810))::[], effect_marker) -> begin
((a), (effect_marker))
end
| _59_2817 -> begin
(FStar_All.failwith "bad shape for effect-for-free signature")
end)
in (match (_59_2820) with
| (a, effect_marker) -> begin
(

let open_and_check = (fun t -> (

let subst = (FStar_Syntax_Subst.opening_of_binders effect_binders)
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (

let _59_2829 = (tc_term env t)
in (match (_59_2829) with
| (t, comp, _59_2828) -> begin
((t), (comp))
end)))))
in (

let recheck_debug = (fun s env t -> (

let _59_2834 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _153_1185 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Term has been %s-transformed to:\n%s\n----------\n" s _153_1185))
end else begin
()
end
in (

let _59_2841 = (tc_term env t)
in (match (_59_2841) with
| (t', _59_2838, _59_2840) -> begin
(

let _59_2842 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _153_1186 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print1 "Re-checked; got:\n%s\n----------\n" _153_1186))
end else begin
()
end
in t)
end))))
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None signature.FStar_Syntax_Syntax.pos))
in (

let _59_2848 = (open_and_check ed.FStar_Syntax_Syntax.repr)
in (match (_59_2848) with
| (repr, _comp) -> begin
(

let _59_2849 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _153_1189 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" _153_1189))
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

let wp_a = (let _153_1196 = (let _153_1195 = (let _153_1194 = (let _153_1193 = (let _153_1192 = (let _153_1191 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _153_1190 = (FStar_Syntax_Syntax.as_implicit false)
in ((_153_1191), (_153_1190))))
in (_153_1192)::[])
in ((wp_type), (_153_1193)))
in FStar_Syntax_Syntax.Tm_app (_153_1194))
in (mk _153_1195))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _153_1196))
in (

let effect_signature = (

let binders = (let _153_1201 = (let _153_1197 = (FStar_Syntax_Syntax.as_implicit false)
in ((a), (_153_1197)))
in (let _153_1200 = (let _153_1199 = (let _153_1198 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" None wp_a)
in (FStar_All.pipe_right _153_1198 FStar_Syntax_Syntax.mk_binder))
in (_153_1199)::[])
in (_153_1201)::_153_1200))
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

let _59_2867 = item
in (match (_59_2867) with
| (u_item, item) -> begin
(

let _59_2870 = (open_and_check item)
in (match (_59_2870) with
| (item, item_comp) -> begin
(

let _59_2871 = if (not ((FStar_Syntax_Util.is_total_lcomp item_comp))) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Computation for [item] is not total!")))
end else begin
()
end
in (

let _59_2876 = (FStar_TypeChecker_DMFF.star_expr dmff_env item)
in (match (_59_2876) with
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

let _59_2884 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.bind_repr)
in (match (_59_2884) with
| (dmff_env, _59_2881, bind_wp, bind_elab) -> begin
(

let _59_2890 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.return_repr)
in (match (_59_2890) with
| (dmff_env, _59_2887, return_wp, return_elab) -> begin
(

let return_wp = (match ((let _153_1208 = (FStar_Syntax_Subst.compress return_wp)
in _153_1208.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(let _153_1209 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) _153_1209 (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_GTot_lid)))))
end
| _59_2901 -> begin
(FStar_All.failwith "unexpected shape for return")
end)
in (

let bind_wp = (match ((let _153_1210 = (FStar_Syntax_Subst.compress bind_wp)
in _153_1210.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_lid (FStar_Syntax_Syntax.Delta_unfoldable ((Prims.parse_int "1"))) None)
in (let _153_1214 = (let _153_1213 = (let _153_1212 = (let _153_1211 = (mk (FStar_Syntax_Syntax.Tm_fvar (r)))
in (FStar_Syntax_Syntax.null_binder _153_1211))
in (_153_1212)::[])
in (FStar_List.append _153_1213 binders))
in (FStar_Syntax_Util.abs _153_1214 body what)))
end
| _59_2910 -> begin
(FStar_All.failwith "unexpected shape for bind")
end)
in (

let apply_close = (fun t -> if ((FStar_List.length effect_binders) = (Prims.parse_int "0")) then begin
t
end else begin
(let _153_1221 = (let _153_1220 = (let _153_1219 = (let _153_1218 = (let _153_1217 = (FStar_Syntax_Util.args_of_binders effect_binders)
in (Prims.snd _153_1217))
in ((t), (_153_1218)))
in FStar_Syntax_Syntax.Tm_app (_153_1219))
in (mk _153_1220))
in (FStar_Syntax_Subst.close effect_binders _153_1221))
end)
in (

let register = (fun name item -> (

let _59_2919 = (let _153_1227 = (mk_lid name)
in (let _153_1226 = (FStar_Syntax_Util.abs effect_binders item None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env _153_1227 _153_1226)))
in (match (_59_2919) with
| (sigelt, fv) -> begin
(

let _59_2920 = (let _153_1229 = (let _153_1228 = (FStar_ST.read sigelts)
in (sigelt)::_153_1228)
in (FStar_ST.op_Colon_Equals sigelts _153_1229))
in fv)
end)))
in (

let return_wp = (register "return_wp" return_wp)
in (

let return_elab = (register "return_elab" return_elab)
in (

let bind_wp = (register "bind_wp" bind_wp)
in (

let _59_2925 = (let _153_1231 = (let _153_1230 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::_153_1230)
in (FStar_ST.op_Colon_Equals sigelts _153_1231))
in (

let bind_elab = (register "bind_elab" bind_elab)
in (

let _59_2928 = (let _153_1233 = (let _153_1232 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::_153_1232)
in (FStar_ST.op_Colon_Equals sigelts _153_1233))
in (

let _59_2947 = (FStar_List.fold_left (fun _59_2932 action -> (match (_59_2932) with
| (dmff_env, actions) -> begin
(

let _59_2938 = (elaborate_and_star dmff_env ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (_59_2938) with
| (dmff_env, action_t, action_wp, action_elab) -> begin
(

let name = action.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText
in (

let action_typ_with_wp = (FStar_TypeChecker_DMFF.trans_F dmff_env action_t action_wp)
in (

let action_elab = (register (Prims.strcat name "_elab") action_elab)
in (

let action_typ_with_wp = (register (Prims.strcat name "_complete_type") action_typ_with_wp)
in (let _153_1239 = (let _153_1238 = (

let _59_2943 = action
in (let _153_1237 = (apply_close action_elab)
in (let _153_1236 = (apply_close action_typ_with_wp)
in {FStar_Syntax_Syntax.action_name = _59_2943.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = _59_2943.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _153_1237; FStar_Syntax_Syntax.action_typ = _153_1236})))
in (_153_1238)::actions)
in ((dmff_env), (_153_1239)))))))
end))
end)) ((dmff_env), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (_59_2947) with
| (dmff_env, actions) -> begin
(

let actions = (FStar_List.rev actions)
in (

let repr = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" None wp_a)
in (

let binders = (let _153_1242 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_1241 = (let _153_1240 = (FStar_Syntax_Syntax.mk_binder wp)
in (_153_1240)::[])
in (_153_1242)::_153_1241))
in (let _153_1251 = (let _153_1250 = (let _153_1248 = (let _153_1247 = (let _153_1246 = (let _153_1245 = (let _153_1244 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _153_1243 = (FStar_Syntax_Syntax.as_implicit false)
in ((_153_1244), (_153_1243))))
in (_153_1245)::[])
in ((repr), (_153_1246)))
in FStar_Syntax_Syntax.Tm_app (_153_1247))
in (mk _153_1248))
in (let _153_1249 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env _153_1250 _153_1249)))
in (FStar_Syntax_Util.abs binders _153_1251 None))))
in (

let repr = (recheck_debug "FC" env repr)
in (

let repr = (register "repr" repr)
in (

let _59_2979 = (match ((let _153_1252 = (FStar_Syntax_Subst.compress wp_type)
in _153_1252.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (effect_param, arrow, _59_2957) -> begin
(

let _59_2962 = (FStar_Syntax_Subst.open_term effect_param arrow)
in (match (_59_2962) with
| (effect_param, arrow) -> begin
(match ((let _153_1253 = (FStar_Syntax_Subst.compress arrow)
in _153_1253.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let _59_2969 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (_59_2969) with
| (wp_binders, c) -> begin
(

let _59_2972 = (FStar_Util.prefix wp_binders)
in (match (_59_2972) with
| (pre_args, post) -> begin
(let _153_1255 = (FStar_Syntax_Util.arrow pre_args c)
in (let _153_1254 = (FStar_Syntax_Util.abs effect_param (Prims.fst post).FStar_Syntax_Syntax.sort None)
in ((_153_1255), (_153_1254))))
end))
end))
end
| _59_2974 -> begin
(let _153_1257 = (let _153_1256 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" _153_1256))
in (FStar_All.failwith _153_1257))
end)
end))
end
| _59_2976 -> begin
(let _153_1259 = (let _153_1258 = (FStar_Syntax_Print.term_to_string wp_type)
in (FStar_Util.format1 "Impossible: pre/post abs %s" _153_1258))
in (FStar_All.failwith _153_1259))
end)
in (match (_59_2979) with
| (pre, post) -> begin
(

let _59_2980 = (let _153_1260 = (register "pre" pre)
in (Prims.ignore _153_1260))
in (

let _59_2982 = (let _153_1261 = (register "post" post)
in (Prims.ignore _153_1261))
in (

let _59_2984 = (let _153_1262 = (register "wp" wp_type)
in (Prims.ignore _153_1262))
in (

let ed = (

let _59_2986 = ed
in (let _153_1273 = (FStar_Syntax_Subst.close_binders effect_binders)
in (let _153_1272 = (FStar_Syntax_Subst.close effect_binders effect_signature)
in (let _153_1271 = (let _153_1263 = (apply_close return_wp)
in (([]), (_153_1263)))
in (let _153_1270 = (let _153_1264 = (apply_close bind_wp)
in (([]), (_153_1264)))
in (let _153_1269 = (apply_close repr)
in (let _153_1268 = (let _153_1265 = (apply_close return_elab)
in (([]), (_153_1265)))
in (let _153_1267 = (let _153_1266 = (apply_close bind_elab)
in (([]), (_153_1266)))
in {FStar_Syntax_Syntax.qualifiers = _59_2986.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _59_2986.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _59_2986.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _153_1273; FStar_Syntax_Syntax.signature = _153_1272; FStar_Syntax_Syntax.ret_wp = _153_1271; FStar_Syntax_Syntax.bind_wp = _153_1270; FStar_Syntax_Syntax.if_then_else = _59_2986.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _59_2986.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _59_2986.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _59_2986.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _59_2986.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _59_2986.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _59_2986.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _59_2986.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _153_1269; FStar_Syntax_Syntax.return_repr = _153_1268; FStar_Syntax_Syntax.bind_repr = _153_1267; FStar_Syntax_Syntax.actions = actions}))))))))
in (

let _59_2991 = (FStar_TypeChecker_DMFF.gen_wps_for_free env effect_binders a wp_a ed)
in (match (_59_2991) with
| (sigelts', ed) -> begin
(

let _59_2992 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _153_1274 = (FStar_Syntax_Print.eff_decl_to_string true ed)
in (FStar_Util.print_string _153_1274))
end else begin
()
end
in (let _153_1277 = (let _153_1276 = (let _153_1275 = (FStar_ST.read sigelts)
in (FStar_List.rev _153_1275))
in (FStar_List.append _153_1276 sigelts'))
in ((_153_1277), (ed))))
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

let _59_2998 = ()
in (

let _59_3006 = ()
in (match (ses) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _59_3035, _59_3037, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, _153_1282, [], _59_3026, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, _153_1283, [], _59_3015, r2))::[] when (((_153_1282 = (Prims.parse_int "0")) && (_153_1283 = (Prims.parse_int "0"))) && (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid))) -> begin
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

let lex_top_t = (let _153_1287 = (let _153_1286 = (let _153_1285 = (let _153_1284 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _153_1284 FStar_Syntax_Syntax.Delta_constant None))
in ((_153_1285), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_153_1286))
in (FStar_Syntax_Syntax.mk _153_1287 None r1))
in (

let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (

let dc_lextop = FStar_Syntax_Syntax.Sig_datacon (((lex_top), ((utop)::[]), (lex_top_t), (FStar_Syntax_Const.lex_t_lid), ((Prims.parse_int "0")), ([]), ([]), (r1)))
in (

let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (

let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (

let lex_cons_t = (

let a = (let _153_1288 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _153_1288))
in (

let hd = (let _153_1289 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _153_1289))
in (

let tl = (let _153_1294 = (let _153_1293 = (let _153_1292 = (let _153_1291 = (let _153_1290 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _153_1290 FStar_Syntax_Syntax.Delta_constant None))
in ((_153_1291), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_153_1292))
in (FStar_Syntax_Syntax.mk _153_1293 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _153_1294))
in (

let res = (let _153_1298 = (let _153_1297 = (let _153_1296 = (let _153_1295 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _153_1295 FStar_Syntax_Syntax.Delta_constant None))
in ((_153_1296), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_153_1297))
in (FStar_Syntax_Syntax.mk _153_1298 None r2))
in (let _153_1299 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (Some (FStar_Syntax_Syntax.imp_tag))))::(((hd), (None)))::(((tl), (None)))::[]) _153_1299))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t), (FStar_Syntax_Const.lex_t_lid), ((Prims.parse_int "0")), ([]), ([]), (r2)))
in (let _153_1301 = (let _153_1300 = (FStar_TypeChecker_Env.get_range env)
in (((tc)::(dc_lextop)::(dc_lexcons)::[]), ([]), (lids), (_153_1300)))
in FStar_Syntax_Syntax.Sig_bundle (_153_1301)))))))))))))))
end
| _59_3061 -> begin
(let _153_1303 = (let _153_1302 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle (((ses), ([]), (lids), (FStar_Range.dummyRange)))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _153_1302))
in (FStar_All.failwith _153_1303))
end))))
and tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _59_3071 = (FStar_Syntax_Util.type_u ())
in (match (_59_3071) with
| (k, _59_3070) -> begin
(

let phi = (let _153_1309 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _153_1309 (norm env)))
in (

let _59_3073 = (FStar_TypeChecker_Util.check_uvars r phi)
in FStar_Syntax_Syntax.Sig_assume (((lid), (phi), (quals), (r)))))
end))))
and tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _153_1319 = (let _153_1318 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _153_1318))
in (FStar_TypeChecker_Errors.diag r _153_1319)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let _59_3096 = ()
in (

let _59_3098 = (warn_positivity tc r)
in (

let _59_3102 = (FStar_Syntax_Subst.open_term tps k)
in (match (_59_3102) with
| (tps, k) -> begin
(

let _59_3107 = (tc_binders env tps)
in (match (_59_3107) with
| (tps, env_tps, guard_params, us) -> begin
(

let _59_3110 = (FStar_Syntax_Util.arrow_formals k)
in (match (_59_3110) with
| (indices, t) -> begin
(

let _59_3115 = (tc_binders env_tps indices)
in (match (_59_3115) with
| (indices, env', guard_indices, us') -> begin
(

let _59_3123 = (

let _59_3120 = (tc_tot_or_gtot_term env' t)
in (match (_59_3120) with
| (t, _59_3118, g) -> begin
(let _153_1326 = (let _153_1325 = (let _153_1324 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params _153_1324))
in (FStar_TypeChecker_Rel.discharge_guard env' _153_1325))
in ((t), (_153_1326)))
end))
in (match (_59_3123) with
| (t, guard) -> begin
(

let k = (let _153_1327 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _153_1327))
in (

let _59_3127 = (FStar_Syntax_Util.type_u ())
in (match (_59_3127) with
| (t_type, u) -> begin
(

let _59_3128 = (let _153_1328 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _153_1328))
in (

let t_tc = (let _153_1329 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _153_1329))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _153_1330 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((_153_1330), (FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps), (k), (mutuals), (data), (quals), (r)))), (u), (guard))))))))
end)))
end))
end))
end))
end))
end))))
end
| _59_3135 -> begin
(FStar_All.failwith "impossible")
end))
in (

let positive_if_pure = (fun _59_3137 l -> ())
in (

let tc_data = (fun env tcs _59_7 -> (match (_59_7) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let _59_3154 = ()
in (

let _59_3189 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _59_3158 -> (match (_59_3158) with
| (se, u_tc) -> begin
if (let _153_1343 = (let _153_1342 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _153_1342))
in (FStar_Ident.lid_equals tc_lid _153_1343)) then begin
(

let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_3160, _59_3162, tps, _59_3165, _59_3167, _59_3169, _59_3171, _59_3173) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _59_3179 -> (match (_59_3179) with
| (x, _59_3178) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
end
| _59_3181 -> begin
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
in (match (_59_3189) with
| (tps, u_tc) -> begin
(

let _59_3209 = (match ((let _153_1345 = (FStar_Syntax_Subst.compress t)
in _153_1345.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _59_3197 = (FStar_Util.first_N ntps bs)
in (match (_59_3197) with
| (_59_3195, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res)))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _59_3203 -> (match (_59_3203) with
| (x, _59_3202) -> begin
FStar_Syntax_Syntax.DB ((((ntps - ((Prims.parse_int "1") + i))), (x)))
end))))
in (let _153_1348 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _153_1348))))
end))
end
| _59_3206 -> begin
(([]), (t))
end)
in (match (_59_3209) with
| (arguments, result) -> begin
(

let _59_3210 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_1351 = (FStar_Syntax_Print.lid_to_string c)
in (let _153_1350 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _153_1349 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _153_1351 _153_1350 _153_1349))))
end else begin
()
end
in (

let _59_3215 = (tc_tparams env arguments)
in (match (_59_3215) with
| (arguments, env', us) -> begin
(

let _59_3219 = (tc_trivial_guard env' result)
in (match (_59_3219) with
| (result, _59_3218) -> begin
(

let _59_3223 = (FStar_Syntax_Util.head_and_args result)
in (match (_59_3223) with
| (head, _59_3222) -> begin
(

let _59_3228 = (match ((let _153_1352 = (FStar_Syntax_Subst.compress head)
in _153_1352.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _59_3227 -> begin
(let _153_1357 = (let _153_1356 = (let _153_1355 = (let _153_1354 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _153_1353 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _153_1354 _153_1353)))
in ((_153_1355), (r)))
in FStar_Syntax_Syntax.Error (_153_1356))
in (Prims.raise _153_1357))
end)
in (

let g = (FStar_List.fold_left2 (fun g _59_3234 u_x -> (match (_59_3234) with
| (x, _59_3233) -> begin
(

let _59_3236 = ()
in (let _153_1361 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _153_1361)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _153_1365 = (let _153_1363 = (FStar_All.pipe_right tps (FStar_List.map (fun _59_3242 -> (match (_59_3242) with
| (x, _59_3241) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append _153_1363 arguments))
in (let _153_1364 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _153_1365 _153_1364)))
in ((FStar_Syntax_Syntax.Sig_datacon (((c), ([]), (t), (tc_lid), (ntps), (quals), ([]), (r)))), (g)))))
end))
end))
end)))
end))
end)))
end
| _59_3245 -> begin
(FStar_All.failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let _59_3251 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _59_8 -> (match (_59_8) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_3255, _59_3257, tps, k, _59_3261, _59_3263, _59_3265, _59_3267) -> begin
(let _153_1376 = (let _153_1375 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _153_1375))
in (FStar_Syntax_Syntax.null_binder _153_1376))
end
| _59_3271 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _59_9 -> (match (_59_9) with
| FStar_Syntax_Syntax.Sig_datacon (_59_3275, _59_3277, t, _59_3280, _59_3282, _59_3284, _59_3286, _59_3288) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _59_3292 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let t = (let _153_1378 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _153_1378))
in (

let _59_3295 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_1379 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _153_1379))
end else begin
()
end
in (

let _59_3299 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_59_3299) with
| (uvs, t) -> begin
(

let _59_3301 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_1383 = (let _153_1381 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _153_1381 (FStar_String.concat ", ")))
in (let _153_1382 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _153_1383 _153_1382)))
end else begin
()
end
in (

let _59_3305 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_59_3305) with
| (uvs, t) -> begin
(

let _59_3309 = (FStar_Syntax_Util.arrow_formals t)
in (match (_59_3309) with
| (args, _59_3308) -> begin
(

let _59_3312 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_59_3312) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _59_3316 se -> (match (_59_3316) with
| (x, _59_3315) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _59_3320, tps, _59_3323, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let _59_3346 = (match ((let _153_1386 = (FStar_Syntax_Subst.compress ty)
in _153_1386.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _59_3337 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_59_3337) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _59_3340 -> begin
(let _153_1387 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) _153_1387 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps), (t)))
end))
end
| _59_3343 -> begin
(([]), (ty))
end)
in (match (_59_3346) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs), (tps), (t), (mutuals), (datas), (quals), (r)))
end)))
end
| _59_3348 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| _59_3352 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _153_1388 -> FStar_Syntax_Syntax.U_name (_153_1388))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _59_10 -> (match (_59_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _59_3357, _59_3359, _59_3361, _59_3363, _59_3365, _59_3367, _59_3369) -> begin
((tc), (uvs_universes))
end
| _59_3373 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _59_3378 d -> (match (_59_3378) with
| (t, _59_3377) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _59_3382, _59_3384, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _153_1392 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _153_1392 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon (((l), (uvs), (ty), (tc), (ntps), (quals), (mutuals), (r))))
end
| _59_3394 -> begin
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

let _59_3404 = (FStar_All.pipe_right ses (FStar_List.partition (fun _59_11 -> (match (_59_11) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_3398) -> begin
true
end
| _59_3401 -> begin
false
end))))
in (match (_59_3404) with
| (tys, datas) -> begin
(

let _59_3411 = if (FStar_All.pipe_right datas (FStar_Util.for_some (fun _59_12 -> (match (_59_12) with
| FStar_Syntax_Syntax.Sig_datacon (_59_3407) -> begin
false
end
| _59_3410 -> begin
true
end)))) then begin
(let _153_1397 = (let _153_1396 = (let _153_1395 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (_153_1395)))
in FStar_Syntax_Syntax.Error (_153_1396))
in (Prims.raise _153_1397))
end else begin
()
end
in (

let env0 = env
in (

let _59_3430 = (FStar_List.fold_right (fun tc _59_3418 -> (match (_59_3418) with
| (env, all_tcs, g) -> begin
(

let _59_3423 = (tc_tycon env tc)
in (match (_59_3423) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (

let _59_3425 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_1400 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _153_1400))
end else begin
()
end
in (let _153_1402 = (let _153_1401 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g _153_1401))
in ((env), ((((tc), (tc_u)))::all_tcs), (_153_1402)))))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_59_3430) with
| (env, tcs, g) -> begin
(

let _59_3440 = (FStar_List.fold_right (fun se _59_3434 -> (match (_59_3434) with
| (datas, g) -> begin
(

let _59_3437 = (tc_data env tcs se)
in (match (_59_3437) with
| (data, g') -> begin
(let _153_1405 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((data)::datas), (_153_1405)))
end))
end)) datas (([]), (g)))
in (match (_59_3440) with
| (datas, g) -> begin
(

let _59_3443 = (let _153_1406 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _153_1406 datas))
in (match (_59_3443) with
| (tcs, datas) -> begin
(

let sig_bndle = (let _153_1408 = (let _153_1407 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_153_1407)))
in FStar_Syntax_Syntax.Sig_bundle (_153_1408))
in (

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (_59_3448, _59_3450, t, _59_3453, _59_3455, _59_3457, _59_3459, _59_3461) -> begin
t
end
| _59_3465 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let dr = FStar_Range.dummyRange
in (

let optimized_haseq_scheme = (fun _59_3468 -> (

let haseq_ty = (fun usubst us acc ty -> (

let _59_3495 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _59_3477, bs, t, _59_3481, d_lids, _59_3484, _59_3486) -> begin
((lid), (bs), (t), (d_lids))
end
| _59_3490 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_59_3495) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _153_1421 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _153_1421 t))
in (

let _59_3500 = (FStar_Syntax_Subst.open_term bs t)
in (match (_59_3500) with
| (bs, t) -> begin
(

let ibs = (match ((let _153_1422 = (FStar_Syntax_Subst.compress t)
in _153_1422.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _59_3503) -> begin
ibs
end
| _59_3507 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _153_1425 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _153_1424 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _153_1425 _153_1424)))
in (

let ind = (let _153_1428 = (FStar_List.map (fun _59_3514 -> (match (_59_3514) with
| (bv, aq) -> begin
(let _153_1427 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_153_1427), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _153_1428 None dr))
in (

let ind = (let _153_1431 = (FStar_List.map (fun _59_3518 -> (match (_59_3518) with
| (bv, aq) -> begin
(let _153_1430 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_153_1430), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _153_1431 None dr))
in (

let haseq_ind = (let _153_1433 = (let _153_1432 = (FStar_Syntax_Syntax.as_arg ind)
in (_153_1432)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _153_1433 None dr))
in (

let bs' = (FStar_List.filter (fun b -> (

let _59_3529 = acc
in (match (_59_3529) with
| (_59_3523, en, _59_3526, _59_3528) -> begin
(

let opt = (let _153_1436 = (let _153_1435 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _153_1435))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort _153_1436 false))
in (match (opt) with
| None -> begin
false
end
| Some (_59_3533) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (let _153_1442 = (let _153_1441 = (let _153_1440 = (let _153_1439 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg _153_1439))
in (_153_1440)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _153_1441 None dr))
in (FStar_Syntax_Util.mk_conj t _153_1442))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let _59_3540 = fml
in (let _153_1448 = (let _153_1447 = (let _153_1446 = (let _153_1445 = (let _153_1444 = (let _153_1443 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_153_1443)::[])
in (_153_1444)::[])
in FStar_Syntax_Syntax.Meta_pattern (_153_1445))
in ((fml), (_153_1446)))
in FStar_Syntax_Syntax.Tm_meta (_153_1447))
in {FStar_Syntax_Syntax.n = _153_1448; FStar_Syntax_Syntax.tk = _59_3540.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _59_3540.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _59_3540.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _153_1454 = (let _153_1453 = (let _153_1452 = (let _153_1451 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_1451 None))
in (FStar_Syntax_Syntax.as_arg _153_1452))
in (_153_1453)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_1454 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _153_1460 = (let _153_1459 = (let _153_1458 = (let _153_1457 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_1457 None))
in (FStar_Syntax_Syntax.as_arg _153_1458))
in (_153_1459)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_1460 None dr))) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let _59_3554 = acc
in (match (_59_3554) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_59_3559, _59_3561, _59_3563, t_lid, _59_3566, _59_3568, _59_3570, _59_3572) -> begin
(t_lid = lid)
end
| _59_3576 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let haseq_data = (fun data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (match ((let _153_1464 = (FStar_Syntax_Subst.compress dt)
in _153_1464.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _59_3584) -> begin
(

let dbs = (let _153_1465 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _153_1465))
in (

let dbs = (let _153_1466 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _153_1466 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = (let _153_1470 = (let _153_1469 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_153_1469)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _153_1470 None dr))
in (

let sort_range = (Prims.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b = (let _153_1472 = (let _153_1471 = (FStar_Syntax_Print.term_to_string ind)
in (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add the \'noeq\' qualifier" _153_1471))
in (FStar_TypeChecker_Util.label _153_1472 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b))))) FStar_Syntax_Util.t_true dbs)
in (FStar_List.fold_right (fun b t -> (let _153_1478 = (let _153_1477 = (let _153_1476 = (let _153_1475 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_1475 None))
in (FStar_Syntax_Syntax.as_arg _153_1476))
in (_153_1477)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_1478 None dr))) dbs cond)))))
end
| _59_3599 -> begin
FStar_Syntax_Util.t_true
end))))
in (

let cond = (FStar_List.fold_left (fun acc d -> (let _153_1481 = (haseq_data d)
in (FStar_Syntax_Util.mk_conj acc _153_1481))) FStar_Syntax_Util.t_true t_datas)
in (

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (let _153_1483 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _153_1482 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env), (_153_1483), (_153_1482))))))))))
end)))))))))))))))
end))))
end)))
in (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_3606, us, _59_3609, _59_3611, _59_3613, _59_3615, _59_3617, _59_3619) -> begin
us
end
| _59_3623 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let _59_3627 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_59_3627) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _59_3629 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _59_3631 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let _59_3638 = (FStar_List.fold_left (haseq_ty usubst us) (([]), (env), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (_59_3638) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let _59_3643 = (tc_trivial_guard env phi)
in (match (_59_3643) with
| (phi, _59_3642) -> begin
(

let _59_3644 = if (FStar_TypeChecker_Env.should_verify env) then begin
(let _153_1484 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _153_1484))
end else begin
()
end
in (

let ses = (FStar_List.fold_left (fun l _59_3649 -> (match (_59_3649) with
| (lid, fml) -> begin
(

let se = (tc_assume env lid fml [] dr)
in (FStar_List.append l ((se)::[])))
end)) [] axioms)
in (

let _59_3652 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in ses)))
end)))
end))))))
end)))))
in (

let unoptimized_haseq_scheme = (fun _59_3655 -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _59_3660, _59_3662, _59_3664, _59_3666, _59_3668, _59_3670, _59_3672) -> begin
lid
end
| _59_3676 -> begin
(FStar_All.failwith "Impossible!")
end)) tcs)
in (

let haseq_ty = (fun usubst us acc ty -> (

let _59_3703 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _59_3685, bs, t, _59_3689, d_lids, _59_3692, _59_3694) -> begin
((lid), (bs), (t), (d_lids))
end
| _59_3698 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_59_3703) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _153_1498 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _153_1498 t))
in (

let _59_3708 = (FStar_Syntax_Subst.open_term bs t)
in (match (_59_3708) with
| (bs, t) -> begin
(

let ibs = (match ((let _153_1499 = (FStar_Syntax_Subst.compress t)
in _153_1499.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _59_3711) -> begin
ibs
end
| _59_3715 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _153_1502 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _153_1501 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _153_1502 _153_1501)))
in (

let ind = (let _153_1505 = (FStar_List.map (fun _59_3722 -> (match (_59_3722) with
| (bv, aq) -> begin
(let _153_1504 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_153_1504), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _153_1505 None dr))
in (

let ind = (let _153_1508 = (FStar_List.map (fun _59_3726 -> (match (_59_3726) with
| (bv, aq) -> begin
(let _153_1507 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_153_1507), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _153_1508 None dr))
in (

let haseq_ind = (let _153_1510 = (let _153_1509 = (FStar_Syntax_Syntax.as_arg ind)
in (_153_1509)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _153_1510 None dr))
in (

let rec is_mutual = (fun t -> (match ((let _153_1514 = (FStar_Syntax_Subst.compress t)
in _153_1514.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', _59_3737) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
if (is_mutual t') then begin
true
end else begin
(let _153_1516 = (FStar_List.map Prims.fst args)
in (exists_mutual _153_1516))
end
end
| FStar_Syntax_Syntax.Tm_meta (t', _59_3750) -> begin
(is_mutual t')
end
| _59_3754 -> begin
false
end))
and exists_mutual = (fun _59_13 -> (match (_59_13) with
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
in (match ((let _153_1522 = (FStar_Syntax_Subst.compress dt)
in _153_1522.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _59_3767) -> begin
(

let dbs = (let _153_1523 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _153_1523))
in (

let dbs = (let _153_1524 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _153_1524 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = (let _153_1528 = (let _153_1527 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_153_1527)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _153_1528 None dr))
in (

let haseq_sort = if (is_mutual sort) then begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end else begin
haseq_sort
end
in (FStar_Syntax_Util.mk_conj t haseq_sort))))) FStar_Syntax_Util.t_true dbs)
in (

let cond = (FStar_List.fold_right (fun b t -> (let _153_1534 = (let _153_1533 = (let _153_1532 = (let _153_1531 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_1531 None))
in (FStar_Syntax_Syntax.as_arg _153_1532))
in (_153_1533)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_1534 None dr))) dbs cond)
in (FStar_Syntax_Util.mk_conj acc cond))))))
end
| _59_3783 -> begin
acc
end))))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_59_3786, _59_3788, _59_3790, t_lid, _59_3793, _59_3795, _59_3797, _59_3799) -> begin
(t_lid = lid)
end
| _59_3803 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let data_cond = (FStar_List.fold_left haseq_data FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml = (

let _59_3807 = fml
in (let _153_1541 = (let _153_1540 = (let _153_1539 = (let _153_1538 = (let _153_1537 = (let _153_1536 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_153_1536)::[])
in (_153_1537)::[])
in FStar_Syntax_Syntax.Meta_pattern (_153_1538))
in ((fml), (_153_1539)))
in FStar_Syntax_Syntax.Tm_meta (_153_1540))
in {FStar_Syntax_Syntax.n = _153_1541; FStar_Syntax_Syntax.tk = _59_3807.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _59_3807.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _59_3807.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _153_1547 = (let _153_1546 = (let _153_1545 = (let _153_1544 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_1544 None))
in (FStar_Syntax_Syntax.as_arg _153_1545))
in (_153_1546)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_1547 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _153_1553 = (let _153_1552 = (let _153_1551 = (let _153_1550 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_1550 None))
in (FStar_Syntax_Syntax.as_arg _153_1551))
in (_153_1552)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_1553 None dr))) bs fml)
in (FStar_Syntax_Util.mk_conj acc fml)))))))))))))))
end))))
end)))
in (

let _59_3837 = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, _59_3820, _59_3822, _59_3824, _59_3826, _59_3828, _59_3830) -> begin
((lid), (us))
end
| _59_3834 -> begin
(FStar_All.failwith "Impossible!")
end))
in (match (_59_3837) with
| (lid, us) -> begin
(

let _59_3840 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_59_3840) with
| (usubst, us) -> begin
(

let fml = (FStar_List.fold_left (haseq_ty usubst us) FStar_Syntax_Util.t_true tcs)
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _59_3843 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _59_3845 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let se = (let _153_1554 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (tc_assume env _153_1554 fml [] dr))
in (se)::[]))))))
end))
end)))))
in (

let is_noeq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Noeq)) quals)
in if (((FStar_Ident.lid_equals env.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid) || is_noeq) || ((FStar_List.length tcs) = (Prims.parse_int "0"))) then begin
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
in (let _153_1559 = (let _153_1558 = (let _153_1557 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_153_1557)))
in FStar_Syntax_Syntax.Sig_bundle (_153_1558))
in (_153_1559)::ses)))
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
in (let _153_1562 = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (_153_1562)))))
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

let _59_3895 = (set_options FStar_Options.Set o)
in (((se)::[]), (env)))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(

let _59_3899 = (let _153_1569 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _153_1569 Prims.ignore))
in (

let _59_3904 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _59_3906 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (((se)::[]), (env)))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_59_3909) -> begin
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

let _59_3925 = (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun _59_3920 a -> (match (_59_3920) with
| (env, ses) -> begin
(

let se_let = (FStar_Syntax_Util.action_as_lb a)
in (let _153_1572 = (FStar_TypeChecker_Env.push_sigelt env se_let)
in ((_153_1572), ((se_let)::ses))))
end)) ((env), ((se)::[]))))
in (match (_59_3925) with
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

let _59_3934 = (let _153_1573 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _153_1573))
in (match (_59_3934) with
| (a, wp_a_src) -> begin
(

let _59_3937 = (let _153_1574 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _153_1574))
in (match (_59_3937) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _153_1578 = (let _153_1577 = (let _153_1576 = (let _153_1575 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (_153_1575)))
in FStar_Syntax_Syntax.NT (_153_1576))
in (_153_1577)::[])
in (FStar_Syntax_Subst.subst _153_1578 wp_b_tgt))
in (

let expected_k = (let _153_1583 = (let _153_1581 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_1580 = (let _153_1579 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_153_1579)::[])
in (_153_1581)::_153_1580))
in (let _153_1582 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _153_1583 _153_1582)))
in (

let lift_wp = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift_wp) expected_k)
in (

let repr_type = (fun eff_name a wp -> (

let no_reify = (fun l -> (let _153_1595 = (let _153_1594 = (let _153_1593 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _153_1592 = (FStar_TypeChecker_Env.get_range env)
in ((_153_1593), (_153_1592))))
in FStar_Syntax_Syntax.Error (_153_1594))
in (Prims.raise _153_1595)))
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
(let _153_1602 = (let _153_1600 = (let _153_1599 = (let _153_1598 = (FStar_Syntax_Syntax.as_arg a)
in (let _153_1597 = (let _153_1596 = (FStar_Syntax_Syntax.as_arg wp)
in (_153_1596)::[])
in (_153_1598)::_153_1597))
in ((repr), (_153_1599)))
in FStar_Syntax_Syntax.Tm_app (_153_1600))
in (let _153_1601 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _153_1602 None _153_1601)))
end)
end)))
in (

let lift = (match (sub.FStar_Syntax_Syntax.lift) with
| None -> begin
None
end
| Some (_59_3953, lift) -> begin
(

let _59_3959 = (let _153_1603 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _153_1603))
in (match (_59_3959) with
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

let lift_wp_a = (let _153_1610 = (let _153_1608 = (let _153_1607 = (let _153_1606 = (FStar_Syntax_Syntax.as_arg a_typ)
in (let _153_1605 = (let _153_1604 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (_153_1604)::[])
in (_153_1606)::_153_1605))
in (((Prims.snd sub.FStar_Syntax_Syntax.lift_wp)), (_153_1607)))
in FStar_Syntax_Syntax.Tm_app (_153_1608))
in (let _153_1609 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _153_1610 None _153_1609)))
in (repr_type sub.FStar_Syntax_Syntax.target a_typ lift_wp_a))
in (

let expected_k = (let _153_1617 = (let _153_1615 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_1614 = (let _153_1613 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (let _153_1612 = (let _153_1611 = (FStar_Syntax_Syntax.null_binder repr_f)
in (_153_1611)::[])
in (_153_1613)::_153_1612))
in (_153_1615)::_153_1614))
in (let _153_1616 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow _153_1617 _153_1616)))
in (

let _59_3972 = (tc_tot_or_gtot_term env expected_k)
in (match (_59_3972) with
| (expected_k, _59_3969, _59_3971) -> begin
(

let lift = (check_and_gen env lift expected_k)
in Some (lift))
end))))))))
end))
end)
in (

let sub = (

let _59_3975 = sub
in {FStar_Syntax_Syntax.source = _59_3975.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _59_3975.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift})
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

let _59_3988 = ()
in (

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _59_3994 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_59_3994) with
| (tps, c) -> begin
(

let _59_3998 = (tc_tparams env tps)
in (match (_59_3998) with
| (tps, env, us) -> begin
(

let _59_4002 = (tc_comp env c)
in (match (_59_4002) with
| (c, u, g) -> begin
(

let _59_4003 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let _59_4009 = (let _153_1618 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _153_1618))
in (match (_59_4009) with
| (uvs, t) -> begin
(

let _59_4028 = (match ((let _153_1620 = (let _153_1619 = (FStar_Syntax_Subst.compress t)
in _153_1619.FStar_Syntax_Syntax.n)
in ((tps), (_153_1620)))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_59_4012, c)) -> begin
(([]), (c))
end
| (_59_4018, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
((tps), (c))
end
| _59_4025 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_59_4028) with
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

let _59_4039 = ()
in (

let _59_4043 = (let _153_1622 = (let _153_1621 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _153_1621))
in (check_and_gen env t _153_1622))
in (match (_59_4043) with
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

let _59_4063 = (tc_term env e)
in (match (_59_4063) with
| (e, c, g1) -> begin
(

let _59_4068 = (let _153_1626 = (let _153_1623 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_153_1623))
in (let _153_1625 = (let _153_1624 = (c.FStar_Syntax_Syntax.comp ())
in ((e), (_153_1624)))
in (check_expected_effect env _153_1626 _153_1625)))
in (match (_59_4068) with
| (e, _59_4066, g) -> begin
(

let _59_4069 = (let _153_1627 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _153_1627))
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
(let _153_1639 = (let _153_1638 = (let _153_1637 = (let _153_1636 = (FStar_Syntax_Print.lid_to_string l)
in (let _153_1635 = (FStar_Syntax_Print.quals_to_string q)
in (let _153_1634 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _153_1636 _153_1635 _153_1634))))
in ((_153_1637), (r)))
in FStar_Syntax_Syntax.Error (_153_1638))
in (Prims.raise _153_1639))
end
end))
in (

let _59_4113 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _59_4090 lb -> (match (_59_4090) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _59_4109 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
((gen), (lb), (quals_opt))
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (

let _59_4104 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _59_4103 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _153_1642 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Syntax_Const.effect_ALL_lid), (tval), (lb.FStar_Syntax_Syntax.lbdef)))
in ((false), (_153_1642), (quals_opt)))))
end)
in (match (_59_4109) with
| (gen, lb, quals_opt) -> begin
((gen), ((lb)::lbs), (quals_opt))
end)))
end)) ((true), ([]), (if (quals = []) then begin
None
end else begin
Some (quals)
end))))
in (match (_59_4113) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _59_14 -> (match (_59_14) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _59_4122 -> begin
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

let e = (let _153_1646 = (let _153_1645 = (let _153_1644 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((((Prims.fst lbs)), (lbs'))), (_153_1644)))
in FStar_Syntax_Syntax.Tm_let (_153_1645))
in (FStar_Syntax_Syntax.mk _153_1646 None r))
in (

let _59_4156 = (match ((tc_maybe_toplevel_term (

let _59_4126 = env
in {FStar_TypeChecker_Env.solver = _59_4126.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_4126.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_4126.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_4126.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_4126.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_4126.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_4126.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_4126.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_4126.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_4126.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_4126.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _59_4126.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _59_4126.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_4126.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_4126.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_4126.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_4126.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _59_4126.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_4126.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_4126.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_4126.FStar_TypeChecker_Env.qname_and_index}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _59_4133; FStar_Syntax_Syntax.pos = _59_4131; FStar_Syntax_Syntax.vars = _59_4129}, _59_4140, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_59_4144, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _59_4150 -> begin
quals
end)
in ((FStar_Syntax_Syntax.Sig_let (((lbs), (r), (lids), (quals)))), (lbs)))
end
| _59_4153 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_59_4156) with
| (se, lbs) -> begin
(

let _59_4162 = if (log env) then begin
(let _153_1654 = (let _153_1653 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _153_1650 = (let _153_1649 = (let _153_1648 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _153_1648.FStar_Syntax_Syntax.fv_name)
in _153_1649.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _153_1650))) with
| None -> begin
true
end
| _59_4160 -> begin
false
end)
in if should_log then begin
(let _153_1652 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _153_1651 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _153_1652 _153_1651)))
end else begin
""
end))))
in (FStar_All.pipe_right _153_1653 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _153_1654))
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

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _59_15 -> (match (_59_15) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _59_4172 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _59_4182 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_59_4184) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _59_4195, _59_4197) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _59_4203 -> (match (_59_4203) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _59_4209, _59_4211, quals, r) -> begin
(

let dec = (let _153_1668 = (let _153_1667 = (let _153_1666 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow bs _153_1666))
in ((l), (us), (_153_1667), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_153_1668))
in (((dec)::out), (hidden)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _59_4221, _59_4223, _59_4225, _59_4227, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r)))
in (((dec)::out), ((l)::hidden)))
end
| _59_4233 -> begin
((out), (hidden))
end)
end)) ses (([]), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end
| FStar_Syntax_Syntax.Sig_assume (_59_4235, _59_4237, quals, _59_4240) -> begin
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
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _59_16 -> (match (_59_16) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _59_4259 -> begin
false
end)))) then begin
(((se)::[]), (hidden))
end else begin
(([]), (hidden))
end
end
end
| FStar_Syntax_Syntax.Sig_main (_59_4261) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _59_4280, _59_4282, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
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
(let _153_1675 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _153_1674 = (let _153_1673 = (let _153_1672 = (let _153_1671 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _153_1671.FStar_Syntax_Syntax.fv_name)
in _153_1672.FStar_Syntax_Syntax.v)
in ((_153_1673), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_153_1674)))))
in ((_153_1675), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let process_one_decl = (fun _59_4303 se -> (match (_59_4303) with
| (ses, exports, env, hidden) -> begin
(

let _59_4305 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_1684 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _153_1684))
end else begin
()
end
in (

let _59_4309 = (tc_decl env se)
in (match (_59_4309) with
| (ses', env) -> begin
(

let _59_4312 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _153_1689 = (FStar_List.fold_left (fun s se -> (let _153_1688 = (let _153_1687 = (FStar_Syntax_Print.sigelt_to_string se)
in (Prims.strcat _153_1687 "\n"))
in (Prims.strcat s _153_1688))) "" ses')
in (FStar_Util.print1 "Checked: %s\n" _153_1689))
end else begin
()
end
in (

let _59_4315 = (FStar_List.iter (fun se -> (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)) ses')
in (

let _59_4324 = (FStar_List.fold_left (fun _59_4319 se -> (match (_59_4319) with
| (le, lh) -> begin
(

let tup = (for_export hidden se)
in (((FStar_List.rev_append (Prims.fst tup) le)), ((FStar_List.rev_append (Prims.snd tup) lh))))
end)) (([]), ([])) ses')
in (match (_59_4324) with
| (exported, hidden) -> begin
(((FStar_List.rev_append ses' ses)), (((FStar_List.rev_append exported []))::exports), (env), (hidden))
end))))
end)))
end))
in (

let _59_4350 = (FStar_List.fold_left (fun acc se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(

let _59_4338 = acc
in (match (_59_4338) with
| (_59_4332, _59_4334, env, _59_4337) -> begin
(

let _59_4341 = (cps_and_elaborate env ne)
in (match (_59_4341) with
| (ses, ne) -> begin
(

let ses = (FStar_List.append ses ((FStar_Syntax_Syntax.Sig_new_effect (((ne), (r))))::[]))
in (FStar_List.fold_left process_one_decl acc ses))
end))
end))
end
| _59_4344 -> begin
(process_one_decl acc se)
end)) (([]), ([]), (env), ([])) ses)
in (match (_59_4350) with
| (ses, exports, env, _59_4349) -> begin
(let _153_1695 = (FStar_All.pipe_right (FStar_List.rev_append exports []) FStar_List.flatten)
in (((FStar_List.rev_append ses [])), (_153_1695), (env)))
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

let _59_4355 = env
in (let _153_1700 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _59_4355.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_4355.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_4355.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_4355.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_4355.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_4355.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_4355.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_4355.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_4355.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_4355.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_4355.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_4355.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_4355.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_4355.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_4355.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_4355.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _153_1700; FStar_TypeChecker_Env.lax = _59_4355.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _59_4355.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_4355.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_4355.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_4355.FStar_TypeChecker_Env.qname_and_index}))
in (

let _59_4358 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
in (

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let _59_4364 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_59_4364) with
| (ses, exports, env) -> begin
(((

let _59_4365 = modul
in {FStar_Syntax_Syntax.name = _59_4365.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _59_4365.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _59_4365.FStar_Syntax_Syntax.is_interface})), (exports), (env))
end))))))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let _59_4373 = (tc_decls env decls)
in (match (_59_4373) with
| (ses, exports, env) -> begin
(

let modul = (

let _59_4374 = modul
in {FStar_Syntax_Syntax.name = _59_4374.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _59_4374.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _59_4374.FStar_Syntax_Syntax.is_interface})
in ((modul), (exports), (env)))
end)))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul = (

let _59_4380 = modul
in {FStar_Syntax_Syntax.name = _59_4380.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _59_4380.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in (

let _59_4384 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let _59_4386 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (

let _59_4388 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (

let _59_4390 = (let _153_1713 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _153_1713 Prims.ignore))
in ((modul), (env)))))))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let _59_4397 = (tc_partial_modul env modul)
in (match (_59_4397) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _59_4400 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _153_1722 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _153_1722))
end else begin
()
end
in (

let env = (

let _59_4402 = env
in {FStar_TypeChecker_Env.solver = _59_4402.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_4402.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_4402.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_4402.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_4402.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_4402.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_4402.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_4402.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_4402.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_4402.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_4402.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_4402.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_4402.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _59_4402.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_4402.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_4402.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_4402.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_4402.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _59_4402.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_4402.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_4402.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_4402.FStar_TypeChecker_Env.qname_and_index})
in (

let _59_4418 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _59_4410) -> begin
(let _153_1727 = (let _153_1726 = (let _153_1725 = (FStar_TypeChecker_Env.get_range env)
in (((Prims.strcat "Implicit argument: " msg)), (_153_1725)))
in FStar_Syntax_Syntax.Error (_153_1726))
in (Prims.raise _153_1727))
end
in (match (_59_4418) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end else begin
(let _153_1732 = (let _153_1731 = (let _153_1730 = (let _153_1728 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _153_1728))
in (let _153_1729 = (FStar_TypeChecker_Env.get_range env)
in ((_153_1730), (_153_1729))))
in FStar_Syntax_Syntax.Error (_153_1731))
in (Prims.raise _153_1732))
end
end)))))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
FStar_Syntax_Syntax.U_zero
end else begin
(

let _59_4421 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _153_1737 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print1 "universe_of %s\n" _153_1737))
end else begin
()
end
in (

let _59_4426 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_4426) with
| (env, _59_4425) -> begin
(

let env = (

let _59_4427 = env
in {FStar_TypeChecker_Env.solver = _59_4427.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_4427.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_4427.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_4427.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_4427.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_4427.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_4427.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_4427.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_4427.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_4427.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_4427.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_4427.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_4427.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _59_4427.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_4427.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_4427.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_4427.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _59_4427.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_4427.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _59_4427.FStar_TypeChecker_Env.qname_and_index})
in (

let fail = (fun e t -> (let _153_1747 = (let _153_1746 = (let _153_1745 = (let _153_1743 = (FStar_Syntax_Print.term_to_string e)
in (let _153_1742 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" _153_1743 _153_1742)))
in (let _153_1744 = (FStar_TypeChecker_Env.get_range env)
in ((_153_1745), (_153_1744))))
in FStar_Syntax_Syntax.Error (_153_1746))
in (Prims.raise _153_1747)))
in (

let ok = (fun u -> (

let _59_4435 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _153_1751 = (FStar_Syntax_Print.tag_of_term e)
in (let _153_1750 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.print2 "<end> universe_of %s is %s\n" _153_1751 _153_1750)))
end else begin
()
end
in u))
in (

let universe_of_type = (fun e t -> (match ((let _153_1756 = (FStar_Syntax_Util.unrefine t)
in _153_1756.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(ok u)
end
| _59_4443 -> begin
(fail e t)
end))
in (

let _59_4446 = (FStar_Syntax_Util.head_and_args e)
in (match (_59_4446) with
| (head, args) -> begin
(match ((let _153_1757 = (FStar_Syntax_Subst.compress head)
in _153_1757.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_59_4448, t) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _153_1758 = (FStar_Syntax_Subst.compress t)
in _153_1758.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_59_4454, t) -> begin
(universe_of_type e (FStar_Syntax_Util.comp_result t))
end
| _59_4459 -> begin
(universe_of_type e t)
end))
end
| _59_4461 -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoInline)::[]) env e)
in (

let _59_4474 = (tc_term env e)
in (match (_59_4474) with
| (_59_4464, {FStar_Syntax_Syntax.eff_name = _59_4471; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _59_4468; FStar_Syntax_Syntax.comp = _59_4466}, g) -> begin
(

let _59_4475 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (let _153_1760 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (FStar_All.pipe_left (universe_of_type e) _153_1760)))
end)))
end)
end))))))
end)))
end)


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

let _59_4479 = if (FStar_Options.debug_any ()) then begin
(let _153_1765 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _153_1765))
end else begin
()
end
in (

let _59_4483 = (tc_modul env m)
in (match (_59_4483) with
| (m, env) -> begin
(

let _59_4484 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _153_1766 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _153_1766))
end else begin
()
end
in ((m), (env)))
end))))




