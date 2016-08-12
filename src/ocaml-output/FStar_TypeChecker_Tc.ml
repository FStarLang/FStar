
open Prims

let set_hint_correlator : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env = (fun env se -> (match ((FStar_Options.reuse_hint_for ())) with
| Some (l) -> begin
(

let lid = (let _150_5 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_add_suffix _150_5 l))
in (

let _58_21 = env
in {FStar_TypeChecker_Env.solver = _58_21.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_21.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_21.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_21.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_21.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_21.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_21.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_21.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_21.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_21.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_21.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_21.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_21.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_21.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_21.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_21.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_21.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_21.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_21.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_21.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_21.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_21.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), (0)))}))
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
| (l)::_58_27 -> begin
l
end)
in (

let _58_31 = env
in {FStar_TypeChecker_Env.solver = _58_31.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_31.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_31.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_31.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_31.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_31.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_31.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_31.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_31.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_31.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_31.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_31.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_31.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_31.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_31.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_31.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_31.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_31.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_31.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_31.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_31.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_31.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), (0)))})))
end))


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (not ((let _150_11 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _150_11))))))


let rng : FStar_TypeChecker_Env.env  ->  FStar_Range.range = (fun env -> (FStar_TypeChecker_Env.get_range env))


let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _58_36 = env
in {FStar_TypeChecker_Env.solver = _58_36.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_36.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_36.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_36.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_36.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_36.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_36.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_36.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_36.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _58_36.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_36.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_36.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_36.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_36.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_36.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_36.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_36.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_36.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_36.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_36.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_36.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_36.FStar_TypeChecker_Env.qname_and_index}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _58_39 = env
in {FStar_TypeChecker_Env.solver = _58_39.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_39.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_39.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_39.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_39.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_39.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_39.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_39.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_39.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _58_39.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_39.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_39.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_39.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_39.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_39.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_39.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_39.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_39.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_39.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_39.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_39.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_39.FStar_TypeChecker_Env.qname_and_index}))


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
| _58_49 -> begin
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
| _58_66 -> begin
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

let fail = (fun _58_73 -> (match (()) with
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
| _58_82 -> begin
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
| _58_92 -> begin
[]
end))


let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.subst_t = (fun s b v -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
s
end else begin
(FStar_Syntax_Syntax.NT ((((Prims.fst b)), (v))))::s
end)


let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (

let _58_98 = lc
in {FStar_Syntax_Syntax.eff_name = _58_98.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_98.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _58_100 -> (match (()) with
| () -> begin
(let _150_79 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _150_79 t))
end))}))


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let should_return = (fun t -> (match ((let _150_90 = (FStar_Syntax_Subst.compress t)
in _150_90.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_108, c) -> begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(

let t = (FStar_All.pipe_left FStar_Syntax_Util.unrefine (FStar_Syntax_Util.comp_result c))
in (match ((let _150_91 = (FStar_Syntax_Subst.compress t)
in _150_91.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (_58_116) -> begin
false
end
| _58_119 -> begin
true
end))
end else begin
false
end
end
| _58_121 -> begin
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

let _58_149 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
((e), (lc), (guard))
end
| Some (t') -> begin
(

let _58_131 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_94 = (FStar_Syntax_Print.term_to_string t)
in (let _150_93 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _150_94 _150_93)))
end else begin
()
end
in (

let _58_135 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_58_135) with
| (e, lc) -> begin
(

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _58_139 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_58_139) with
| (e, g) -> begin
(

let _58_140 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_96 = (FStar_Syntax_Print.term_to_string t)
in (let _150_95 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _150_96 _150_95)))
end else begin
()
end
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let _58_145 = (let _150_102 = (FStar_All.pipe_left (fun _150_101 -> Some (_150_101)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _150_102 env e lc g))
in (match (_58_145) with
| (lc, g) -> begin
((e), ((set_lcomp_result lc t')), (g))
end))))
end)))
end)))
end)
in (match (_58_149) with
| (e, lc, g) -> begin
(

let _58_150 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
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

let _58_160 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_58_160) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _58_165 -> (match (_58_165) with
| (e, c) -> begin
(

let expected_c_opt = (match (copt) with
| Some (_58_167) -> begin
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

let _58_174 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
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

let _58_177 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_125 = (FStar_Syntax_Print.term_to_string e)
in (let _150_124 = (FStar_Syntax_Print.comp_to_string c)
in (let _150_123 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _150_125 _150_124 _150_123))))
end else begin
()
end
in (

let _58_183 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_58_183) with
| (e, _58_181, g) -> begin
(

let g = (let _150_126 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _150_126 "could not prove post-condition" g))
in (

let _58_185 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
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


let no_logical_guard = (fun env _58_192 -> (match (_58_192) with
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
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _58_216; FStar_Syntax_Syntax.result_typ = _58_214; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, _58_208))::[]; FStar_Syntax_Syntax.flags = _58_205}) -> begin
(

let pat_vars = (FStar_Syntax_Free.names pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _58_223 -> (match (_58_223) with
| (b, _58_222) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _58_227) -> begin
(let _150_144 = (let _150_143 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _150_143))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _150_144))
end))
end
| _58_231 -> begin
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

let _58_238 = env
in {FStar_TypeChecker_Env.solver = _58_238.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_238.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_238.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_238.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_238.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_238.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_238.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_238.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_238.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_238.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_238.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_238.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _58_238.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_238.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_238.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_238.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_238.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_238.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_238.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_238.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_238.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_238.FStar_TypeChecker_Env.qname_and_index})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _58_250 -> (match (_58_250) with
| (b, _58_249) -> begin
(

let t = (let _150_158 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _150_158))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _58_259 -> begin
(let _150_159 = (FStar_Syntax_Syntax.bv_to_name b)
in (_150_159)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let _58_265 = (FStar_Syntax_Util.head_and_args dec)
in (match (_58_265) with
| (head, _58_264) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _58_269 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _58_3 -> (match (_58_3) with
| FStar_Syntax_Syntax.DECREASES (_58_273) -> begin
true
end
| _58_276 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _58_281 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| _58_286 -> begin
(mk_lex_list xs)
end))
end)))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun _58_291 -> (match (_58_291) with
| (l, t) -> begin
(match ((let _150_165 = (FStar_Syntax_Subst.compress t)
in _150_165.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _58_298 -> (match (_58_298) with
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

let _58_302 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_58_302) with
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

let _58_309 = (FStar_Util.prefix formals)
in (match (_58_309) with
| (bs, (last, imp)) -> begin
(

let last = (

let _58_310 = last
in (let _150_174 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _58_310.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_310.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_174}))
in (

let refined_formals = (FStar_List.append bs ((((last), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (

let _58_315 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
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
| _58_318 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end)
end)


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let _58_321 = env
in {FStar_TypeChecker_Env.solver = _58_321.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_321.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_321.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_321.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_321.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_321.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_321.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_321.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_321.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_321.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_321.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_321.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_321.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_321.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_321.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_321.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_321.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_321.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_321.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_321.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_321.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_321.FStar_TypeChecker_Env.qname_and_index}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (

let _58_326 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
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
| FStar_Syntax_Syntax.Tm_delayed (_58_330) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let _58_371 = (tc_tot_or_gtot_term env e)
in (match (_58_371) with
| (e, c, g) -> begin
(

let g = (

let _58_372 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_372.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_372.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_372.FStar_TypeChecker_Env.implicits})
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let _58_382 = (FStar_Syntax_Util.type_u ())
in (match (_58_382) with
| (t, u) -> begin
(

let _58_386 = (tc_check_tot_or_gtot_term env e t)
in (match (_58_386) with
| (e, c, g) -> begin
(

let _58_393 = (

let _58_390 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_390) with
| (env, _58_389) -> begin
(tc_pats env pats)
end))
in (match (_58_393) with
| (pats, g') -> begin
(

let g' = (

let _58_394 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_394.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_394.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_394.FStar_TypeChecker_Env.implicits})
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
| FStar_Syntax_Syntax.Tm_let ((_58_403, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _58_410; FStar_Syntax_Syntax.lbtyp = _58_408; FStar_Syntax_Syntax.lbeff = _58_406; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _58_421 = (let _150_254 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _150_254 e1))
in (match (_58_421) with
| (e1, c1, g1) -> begin
(

let _58_425 = (tc_term env e2)
in (match (_58_425) with
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
| _58_430 -> begin
(

let _58_434 = (tc_term env e)
in (match (_58_434) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (_58_438)) -> begin
(tc_term env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let _58_449 = (tc_term env e)
in (match (_58_449) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (m)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _58_455) -> begin
(

let _58_461 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_461) with
| (env0, _58_460) -> begin
(

let _58_466 = (tc_comp env0 expected_c)
in (match (_58_466) with
| (expected_c, _58_464, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (

let _58_471 = (let _150_261 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term _150_261 e))
in (match (_58_471) with
| (e, c', g') -> begin
(

let _58_475 = (let _150_263 = (let _150_262 = (c'.FStar_Syntax_Syntax.comp ())
in ((e), (_150_262)))
in (check_expected_effect env0 (Some (expected_c)) _150_263))
in (match (_58_475) with
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
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _58_480) -> begin
(

let _58_485 = (FStar_Syntax_Util.type_u ())
in (match (_58_485) with
| (k, u) -> begin
(

let _58_490 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_490) with
| (t, _58_488, f) -> begin
(

let _58_494 = (let _150_267 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _150_267 e))
in (match (_58_494) with
| (e, c, g) -> begin
(

let _58_498 = (let _150_271 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_495 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _150_271 e c f))
in (match (_58_498) with
| (c, f) -> begin
(

let _58_502 = (let _150_272 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t)), (Some (c.FStar_Syntax_Syntax.eff_name))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _150_272 c))
in (match (_58_502) with
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

let _58_538 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_538) with
| (unary_op, _58_537) -> begin
(

let head = (let _150_275 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (Prims.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) None _150_275))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), (rest)))) None top.FStar_Syntax_Syntax.pos)
in (tc_term env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _58_546; FStar_Syntax_Syntax.pos = _58_544; FStar_Syntax_Syntax.vars = _58_542}, ((e, aqual))::[]) -> begin
(

let _58_556 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end else begin
()
end
in (

let _58_565 = (

let _58_561 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_561) with
| (env0, _58_560) -> begin
(tc_term env0 e)
end))
in (match (_58_565) with
| (e, c, g) -> begin
(

let _58_569 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_569) with
| (reify_op, _58_568) -> begin
(

let u_c = (

let _58_575 = (tc_term env c.FStar_Syntax_Syntax.res_typ)
in (match (_58_575) with
| (_58_571, c, _58_574) -> begin
(match ((let _150_276 = (FStar_Syntax_Subst.compress c.FStar_Syntax_Syntax.res_typ)
in _150_276.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| _58_579 -> begin
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

let _58_587 = (comp_check_expected_typ env e c)
in (match (_58_587) with
| (e, c, g') -> begin
(let _150_278 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), (c), (_150_278)))
end))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.tk = _58_593; FStar_Syntax_Syntax.pos = _58_591; FStar_Syntax_Syntax.vars = _58_589}, ((e, aqual))::[]) -> begin
(

let _58_604 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end else begin
()
end
in (

let no_reflect = (fun _58_607 -> (match (()) with
| () -> begin
(let _150_283 = (let _150_282 = (let _150_281 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((_150_281), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_282))
in (Prims.raise _150_283))
end))
in (

let _58_611 = (FStar_Syntax_Util.head_and_args top)
in (match (_58_611) with
| (reflect_op, _58_610) -> begin
(match ((FStar_TypeChecker_Env.effect_decl_opt env l)) with
| None -> begin
(no_reflect ())
end
| Some (ed) -> begin
if (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable)))) then begin
(no_reflect ())
end else begin
(

let _58_617 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_617) with
| (env_no_ex, topt) -> begin
(

let _58_645 = (

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

let _58_625 = (let _150_291 = (let _150_290 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _150_290 Prims.fst))
in (tc_tot_or_gtot_term _150_291 t))
in (match (_58_625) with
| (t, _58_623, g) -> begin
(match ((let _150_292 = (FStar_Syntax_Subst.compress t)
in _150_292.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_58_627, ((res, _58_634))::((wp, _58_630))::[]) -> begin
((t), (res), (wp), (g))
end
| _58_640 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))
in (match (_58_645) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let _58_659 = (

let _58_649 = (tc_tot_or_gtot_term env_no_ex e)
in (match (_58_649) with
| (e, c, g) -> begin
(

let _58_650 = if (let _150_293 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation _150_293)) then begin
(FStar_TypeChecker_Errors.add_errors env (((("Expected Tot, got a GTot computation"), (e.FStar_Syntax_Syntax.pos)))::[]))
end else begin
()
end
in (match ((FStar_TypeChecker_Rel.try_teq env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)) with
| None -> begin
(

let _58_653 = (let _150_298 = (let _150_297 = (let _150_296 = (let _150_295 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
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
in (match (_58_659) with
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

let _58_665 = (comp_check_expected_typ env e c)
in (match (_58_665) with
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

let _58_672 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_310 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _150_309 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _150_310 _150_309)))
end else begin
()
end
in (

let _58_677 = (tc_term (no_inst env) head)
in (match (_58_677) with
| (head, chead, g_head) -> begin
(

let _58_681 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _150_311 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _150_311))
end else begin
(let _150_312 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _150_312))
end
in (match (_58_681) with
| (e, c, g) -> begin
(

let _58_682 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
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

let _58_688 = (comp_check_expected_typ env0 e c)
in (match (_58_688) with
| (e, c, g') -> begin
(

let gimp = (match ((let _150_314 = (FStar_Syntax_Subst.compress head)
in _150_314.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _58_691) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e), (c.FStar_Syntax_Syntax.res_typ), (head.FStar_Syntax_Syntax.pos))
in (

let _58_695 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_695.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_695.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_695.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _58_698 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (

let gres = (let _150_315 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _150_315))
in (

let _58_701 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
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

let _58_709 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_709) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let _58_714 = (tc_term env1 e1)
in (match (_58_714) with
| (e1, c1, g1) -> begin
(

let _58_725 = (match (topt) with
| Some (t) -> begin
((env), (t))
end
| None -> begin
(

let _58_721 = (FStar_Syntax_Util.type_u ())
in (match (_58_721) with
| (k, _58_720) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _150_318 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in ((_150_318), (res_t))))
end))
end)
in (match (_58_725) with
| (env_branches, res_t) -> begin
(

let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let _58_742 = (

let _58_739 = (FStar_List.fold_right (fun _58_733 _58_736 -> (match (((_58_733), (_58_736))) with
| ((_58_729, f, c, g), (caccum, gaccum)) -> begin
(let _150_321 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (_150_321)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_58_739) with
| (cases, g) -> begin
(let _150_322 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in ((_150_322), (g)))
end))
in (match (_58_742) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (guard_x)), (c_branches)))
in (

let e = (

let mk_match = (fun scrutinee -> (

let branches = (FStar_List.map (fun _58_753 -> (match (_58_753) with
| (f, _58_748, _58_750, _58_752) -> begin
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

let _58_759 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
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
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_771); FStar_Syntax_Syntax.lbunivs = _58_769; FStar_Syntax_Syntax.lbtyp = _58_767; FStar_Syntax_Syntax.lbeff = _58_765; FStar_Syntax_Syntax.lbdef = _58_763})::[]), _58_777) -> begin
(

let _58_780 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_337 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _150_337))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _58_784), _58_787) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_58_802); FStar_Syntax_Syntax.lbunivs = _58_800; FStar_Syntax_Syntax.lbtyp = _58_798; FStar_Syntax_Syntax.lbeff = _58_796; FStar_Syntax_Syntax.lbdef = _58_794})::_58_792), _58_808) -> begin
(

let _58_811 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_338 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _150_338))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _58_815), _58_818) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let _58_832 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_832) with
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
| _58_842 -> begin
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
| FStar_Syntax_Syntax.Tm_arrow (_58_853) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _58_856 -> begin
(

let imp = (("uvar in term"), (env), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let _58_858 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _58_858.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_858.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_858.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _58_873 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(

let _58_866 = (FStar_Syntax_Util.type_u ())
in (match (_58_866) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
end))
end
| Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end)
in (match (_58_873) with
| (t, _58_871, g0) -> begin
(

let _58_878 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (_58_878) with
| (e, _58_876, g1) -> begin
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

let _58_882 = x
in {FStar_Syntax_Syntax.ppname = _58_882.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_882.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let _58_888 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_58_888) with
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
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _58_895; FStar_Syntax_Syntax.pos = _58_893; FStar_Syntax_Syntax.vars = _58_891}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let _58_905 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_905) with
| (us', t) -> begin
(

let _58_912 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _150_369 = (let _150_368 = (let _150_367 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (_150_367)))
in FStar_Syntax_Syntax.Error (_150_368))
in (Prims.raise _150_369))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _58_911 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (

let fv' = (

let _58_914 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _58_916 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_916.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_916.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_914.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_914.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _150_372 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_372 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let _58_924 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_924) with
| (us, t) -> begin
(

let fv' = (

let _58_925 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _58_927 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _58_927.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _58_927.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _58_925.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _58_925.FStar_Syntax_Syntax.fv_qual})
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

let _58_941 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_941) with
| (bs, c) -> begin
(

let env0 = env
in (

let _58_946 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_946) with
| (env, _58_945) -> begin
(

let _58_951 = (tc_binders env bs)
in (match (_58_951) with
| (bs, env, g, us) -> begin
(

let _58_955 = (tc_comp env c)
in (match (_58_955) with
| (c, uc, f) -> begin
(

let e = (

let _58_956 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _58_956.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_956.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_956.FStar_Syntax_Syntax.vars})
in (

let _58_959 = (check_smt_pat env e bs c)
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

let _58_975 = (let _150_376 = (let _150_375 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_375)::[])
in (FStar_Syntax_Subst.open_term _150_376 phi))
in (match (_58_975) with
| (x, phi) -> begin
(

let env0 = env
in (

let _58_980 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_980) with
| (env, _58_979) -> begin
(

let _58_985 = (let _150_377 = (FStar_List.hd x)
in (tc_binder env _150_377))
in (match (_58_985) with
| (x, env, f1, u) -> begin
(

let _58_986 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_380 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _150_379 = (FStar_Syntax_Print.term_to_string phi)
in (let _150_378 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _150_380 _150_379 _150_378))))
end else begin
()
end
in (

let _58_991 = (FStar_Syntax_Util.type_u ())
in (match (_58_991) with
| (t_phi, _58_990) -> begin
(

let _58_996 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_58_996) with
| (phi, _58_994, f2) -> begin
(

let e = (

let _58_997 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _58_997.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _58_997.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_997.FStar_Syntax_Syntax.vars})
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
| FStar_Syntax_Syntax.Tm_abs (bs, body, _58_1005) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (

let _58_1011 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_382 = (FStar_Syntax_Print.term_to_string (

let _58_1009 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))); FStar_Syntax_Syntax.tk = _58_1009.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _58_1009.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_1009.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _150_382))
end else begin
()
end
in (

let _58_1015 = (FStar_Syntax_Subst.open_term bs body)
in (match (_58_1015) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _58_1017 -> begin
(let _150_385 = (let _150_384 = (FStar_Syntax_Print.term_to_string top)
in (let _150_383 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" _150_384 _150_383)))
in (FStar_All.failwith _150_385))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_58_1022) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_58_1025, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_58_1030, Some (_58_1032)) -> begin
(FStar_All.failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (_58_1037) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_58_1040) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_58_1043) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_58_1047) -> begin
FStar_TypeChecker_Common.t_range
end
| _58_1050 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(

let _58_1058 = (FStar_Syntax_Util.type_u ())
in (match (_58_1058) with
| (k, u) -> begin
(

let _58_1063 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_1063) with
| (t, _58_1061, g) -> begin
(let _150_390 = (FStar_Syntax_Syntax.mk_Total t)
in ((_150_390), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(

let _58_1068 = (FStar_Syntax_Util.type_u ())
in (match (_58_1068) with
| (k, u) -> begin
(

let _58_1073 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_1073) with
| (t, _58_1071, g) -> begin
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

let _58_1082 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_58_1082) with
| (tc, _58_1080, f) -> begin
(

let _58_1086 = (FStar_Syntax_Util.head_and_args tc)
in (match (_58_1086) with
| (_58_1084, args) -> begin
(

let _58_1089 = (let _150_395 = (FStar_List.hd args)
in (let _150_394 = (FStar_List.tl args)
in ((_150_395), (_150_394))))
in (match (_58_1089) with
| (res, args) -> begin
(

let _58_1105 = (let _150_397 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _58_5 -> (match (_58_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _58_1096 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1096) with
| (env, _58_1095) -> begin
(

let _58_1101 = (tc_tot_or_gtot_term env e)
in (match (_58_1101) with
| (e, _58_1099, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e)), (g))
end))
end))
end
| f -> begin
((f), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right _150_397 FStar_List.unzip))
in (match (_58_1105) with
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
| _58_1116 -> begin
(FStar_All.failwith "Impossible:Unexpected sort for computation")
end)))
end
| _58_1118 -> begin
(FStar_All.failwith "Impossible:Unexpected sort for computation")
end)
in (let _150_399 = (FStar_Syntax_Syntax.mk_Comp (

let _58_1120 = c
in {FStar_Syntax_Syntax.effect_name = _58_1120.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _58_1120.FStar_Syntax_Syntax.flags}))
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
| FStar_Syntax_Syntax.U_bvar (_58_1128) -> begin
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
| _58_1143 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _150_419 = (let _150_418 = (let _150_417 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in ((_150_417), (top.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_418))
in (Prims.raise _150_419)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun _58_1161 bs bs_expected -> (match (_58_1161) with
| (env, out, g, subst) -> begin
(match (((bs), (bs_expected))) with
| ([], []) -> begin
((env), ((FStar_List.rev out)), (None), (g), (subst))
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
(

let _58_1192 = (match (((imp), (imp'))) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _150_436 = (let _150_435 = (let _150_434 = (let _150_432 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _150_432))
in (let _150_433 = (FStar_Syntax_Syntax.range_of_bv hd)
in ((_150_434), (_150_433))))
in FStar_Syntax_Syntax.Error (_150_435))
in (Prims.raise _150_436))
end
| _58_1191 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _58_1209 = (match ((let _150_437 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _150_437.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| _58_1197 -> begin
(

let _58_1198 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_438 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _150_438))
end else begin
()
end
in (

let _58_1204 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_58_1204) with
| (t, _58_1202, g1) -> begin
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
in (match (_58_1209) with
| (t, g) -> begin
(

let hd = (

let _58_1210 = hd
in {FStar_Syntax_Syntax.ppname = _58_1210.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1210.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
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

let _58_1231 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _58_1230 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (

let _58_1238 = (tc_binders env bs)
in (match (_58_1238) with
| (bs, envbody, g, _58_1237) -> begin
(

let _58_1256 = (match ((let _150_449 = (FStar_Syntax_Subst.compress body)
in _150_449.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _58_1243) -> begin
(

let _58_1250 = (tc_comp envbody c)
in (match (_58_1250) with
| (c, _58_1248, g') -> begin
(let _150_450 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((Some (c)), (body), (_150_450)))
end))
end
| _58_1252 -> begin
((None), (body), (g))
end)
in (match (_58_1256) with
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

let _58_1283 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _58_1282 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _58_1290 = (tc_binders env bs)
in (match (_58_1290) with
| (bs, envbody, g, _58_1289) -> begin
(

let _58_1294 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_58_1294) with
| (envbody, _58_1293) -> begin
((Some (((t), (true)))), (bs), ([]), (None), (envbody), (body), (g))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _58_1297) -> begin
(

let _58_1308 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_58_1308) with
| (_58_1301, bs, bs', copt, env, body, g) -> begin
((Some (((t), (false)))), (bs), (bs'), (copt), (env), (body), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _58_1315 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_58_1315) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun _58_1326 c_expected -> (match (_58_1326) with
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

let _58_1347 = (check_binders env more_bs bs_expected)
in (match (_58_1347) with
| (env, bs', more, guard', subst) -> begin
(let _150_470 = (let _150_469 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env), ((FStar_List.append bs bs')), (more), (_150_469), (subst)))
in (handle_more _150_470 c_expected))
end))
end
| _58_1349 -> begin
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

let _58_1355 = envbody
in {FStar_TypeChecker_Env.solver = _58_1355.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1355.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1355.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1355.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1355.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1355.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1355.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1355.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1355.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1355.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1355.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1355.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _58_1355.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1355.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1355.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1355.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1355.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1355.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1355.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1355.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1355.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1355.FStar_TypeChecker_Env.qname_and_index})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _58_1360 _58_1363 -> (match (((_58_1360), (_58_1363))) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _58_1369 = (let _150_483 = (let _150_482 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _150_482 Prims.fst))
in (tc_term _150_483 t))
in (match (_58_1369) with
| (t, _58_1366, _58_1368) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l (([]), (t)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _150_484 = (FStar_Syntax_Syntax.mk_binder (

let _58_1373 = x
in {FStar_Syntax_Syntax.ppname = _58_1373.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1373.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_150_484)::letrec_binders)
end
| _58_1376 -> begin
letrec_binders
end)
in ((env), (lb))))
end))
end)) ((envbody), ([])))))))
in (

let _58_1382 = (check_actuals_against_formals env bs bs_expected)
in (match (_58_1382) with
| (envbody, bs, g, c) -> begin
(

let _58_1385 = if (FStar_TypeChecker_Env.should_verify env) then begin
(mk_letrec_env envbody bs c)
end else begin
((envbody), ([]))
end
in (match (_58_1385) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in ((Some (((t), (false)))), (bs), (letrecs), (Some (c)), (envbody), (body), (g)))
end))
end))))
end))
end
| _58_1388 -> begin
if (not (norm)) then begin
(let _150_485 = (unfold_whnf env t)
in (as_function_typ true _150_485))
end else begin
(

let _58_1398 = (expected_function_typ env None body)
in (match (_58_1398) with
| (_58_1390, bs, _58_1393, c_opt, envbody, body, g) -> begin
((Some (((t), (false)))), (bs), ([]), (c_opt), (envbody), (body), (g))
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let _58_1402 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_1402) with
| (env, topt) -> begin
(

let _58_1406 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
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

let _58_1415 = (expected_function_typ env topt body)
in (match (_58_1415) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let _58_1421 = (tc_term (

let _58_1416 = envbody
in {FStar_TypeChecker_Env.solver = _58_1416.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1416.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1416.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1416.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1416.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1416.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1416.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1416.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1416.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1416.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1416.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1416.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1416.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_1416.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1416.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1416.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1416.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1416.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1416.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1416.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1416.FStar_TypeChecker_Env.qname_and_index}) body)
in (match (_58_1421) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _58_1423 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _150_489 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _150_488 = (let _150_487 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _150_487))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _150_489 _150_488)))
end else begin
()
end
in (

let _58_1430 = (let _150_491 = (let _150_490 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body), (_150_490)))
in (check_expected_effect (

let _58_1425 = envbody
in {FStar_TypeChecker_Env.solver = _58_1425.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1425.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1425.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1425.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1425.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1425.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1425.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1425.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1425.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1425.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1425.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1425.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1425.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1425.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1425.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _58_1425.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1425.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1425.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1425.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1425.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1425.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1425.FStar_TypeChecker_Env.qname_and_index}) c_opt _150_491))
in (match (_58_1430) with
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

let _58_1453 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_58_1442) -> begin
((e), (t), (guard))
end
| _58_1445 -> begin
(

let _58_1448 = if use_teq then begin
(let _150_497 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in ((e), (_150_497)))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_58_1448) with
| (e, guard') -> begin
(let _150_498 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((e), (t), (_150_498)))
end))
end))
end
| None -> begin
((e), (tfun_computed), (guard))
end)
in (match (_58_1453) with
| (e, tfun, guard) -> begin
(

let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (

let _58_1457 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_58_1457) with
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

let _58_1467 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_507 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _150_506 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _150_507 _150_506)))
end else begin
()
end
in (

let monadic_application = (fun _58_1474 subst arg_comps_rev arg_rets guard fvs bs -> (match (_58_1474) with
| (head, chead, ghead, cres) -> begin
(

let _58_1481 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let _58_1509 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun _58_6 -> (match (_58_6) with
| (_58_1488, _58_1490, None) -> begin
false
end
| (_58_1494, _58_1496, Some (c)) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _150_523 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _150_523 cres))
end else begin
(

let _58_1501 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
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
| _58_1505 -> begin
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
in (match (_58_1509) with
| (cres, guard) -> begin
(

let _58_1510 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_533 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _150_533))
end else begin
()
end
in (

let _58_1532 = (FStar_List.fold_left (fun _58_1515 _58_1521 -> (match (((_58_1515), (_58_1521))) with
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
in (match (_58_1532) with
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

let _58_1538 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (_58_1538) with
| (comp, g) -> begin
((app), (comp), (g))
end)))))
end)))
end)))
end))
in (

let rec tc_args = (fun head_info _58_1546 bs args -> (match (_58_1546) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args))) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (_58_1552))))::rest, ((_58_1560, None))::_58_1558) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _58_1566 = (check_no_escape (Some (head)) env fvs t)
in (

let _58_1572 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_58_1572) with
| (varg, _58_1570, implicits) -> begin
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

let _58_1604 = (match (((aqual), (aq))) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _58_1603 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifier"), (e.FStar_Syntax_Syntax.pos)))))
end)
in (

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let _58_1607 = x
in {FStar_Syntax_Syntax.ppname = _58_1607.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1607.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (

let _58_1610 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_548 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _150_548))
end else begin
()
end
in (

let _58_1612 = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let _58_1615 = env
in {FStar_TypeChecker_Env.solver = _58_1615.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1615.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1615.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1615.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1615.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1615.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1615.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1615.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1615.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1615.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1615.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1615.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1615.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1615.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1615.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _58_1615.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1615.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1615.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1615.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1615.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1615.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1615.FStar_TypeChecker_Env.qname_and_index})
in (

let _58_1618 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_551 = (FStar_Syntax_Print.tag_of_term e)
in (let _150_550 = (FStar_Syntax_Print.term_to_string e)
in (let _150_549 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _150_551 _150_550 _150_549))))
end else begin
()
end
in (

let _58_1623 = (tc_term env e)
in (match (_58_1623) with
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
| (_58_1631, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::_58_1636) -> begin
(

let _58_1643 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (_58_1643) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _150_564 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _150_564 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let _58_1654 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (_58_1654) with
| (bs, cres') -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp cres')))
in (

let _58_1656 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_565 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _150_565))
end else begin
()
end
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args)))
end))
end
| _58_1659 when (not (norm)) -> begin
(let _150_566 = (unfold_whnf env tres)
in (aux true _150_566))
end
| _58_1661 -> begin
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

let _58_1694 = (tc_term env e)
in (match (_58_1694) with
| (e, c, g_e) -> begin
(

let _58_1698 = (tc_args env tl)
in (match (_58_1698) with
| (args, comps, g_rest) -> begin
(let _150_582 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e), (imp)))::args), ((((e.FStar_Syntax_Syntax.pos), (c)))::comps), (_150_582)))
end))
end))
end))
in (

let _58_1702 = (tc_args env args)
in (match (_58_1702) with
| (args, comps, g_args) -> begin
(

let bs = (let _150_584 = (FStar_All.pipe_right comps (FStar_List.map (fun _58_1706 -> (match (_58_1706) with
| (_58_1704, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks _150_584))
in (

let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _58_1712 -> begin
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
| FStar_Syntax_Syntax.Tm_type (_58_1718) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _58_1723 -> begin
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

let _58_1727 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_607 = (FStar_Syntax_Print.term_to_string head)
in (let _150_606 = (FStar_Syntax_Print.term_to_string tf)
in (let _150_605 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _150_607 _150_606 _150_605))))
end else begin
()
end
in (

let _58_1729 = (let _150_608 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _150_608))
in (

let comp = (let _150_611 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _58_1733 out -> (match (_58_1733) with
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

let _58_1742 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_1742) with
| (bs, c) -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp c)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args))
end))
end
| _58_1745 -> begin
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

let _58_1781 = (FStar_List.fold_left2 (fun _58_1762 _58_1765 _58_1768 -> (match (((_58_1762), (_58_1765), (_58_1768))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(

let _58_1769 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifiers"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _58_1774 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_58_1774) with
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
in (match (_58_1781) with
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

let _58_1786 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_58_1786) with
| (c, g) -> begin
((e), (c), (g))
end))))
end)))
end
| _58_1788 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let _58_1795 = (FStar_Syntax_Subst.open_branch branch)
in (match (_58_1795) with
| (pattern, when_clause, branch_exp) -> begin
(

let _58_1800 = branch
in (match (_58_1800) with
| (cpat, _58_1798, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _58_1808 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_58_1808) with
| (pat_bvs, exps, p) -> begin
(

let _58_1809 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_646 = (FStar_Syntax_Print.pat_to_string p0)
in (let _150_645 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _150_646 _150_645)))
end else begin
()
end
in (

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let _58_1815 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_58_1815) with
| (env1, _58_1814) -> begin
(

let env1 = (

let _58_1816 = env1
in {FStar_TypeChecker_Env.solver = _58_1816.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1816.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1816.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1816.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1816.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1816.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1816.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1816.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _58_1816.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1816.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1816.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1816.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1816.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1816.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_1816.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_1816.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1816.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1816.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_1816.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1816.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1816.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1816.FStar_TypeChecker_Env.qname_and_index})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _58_1855 = (let _150_669 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _58_1821 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_649 = (FStar_Syntax_Print.term_to_string e)
in (let _150_648 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _150_649 _150_648)))
end else begin
()
end
in (

let _58_1826 = (tc_term env1 e)
in (match (_58_1826) with
| (e, lc, g) -> begin
(

let _58_1827 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
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

let _58_1833 = (let _150_652 = (FStar_TypeChecker_Rel.discharge_guard env (

let _58_1831 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_1831.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_1831.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_1831.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _150_652 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _150_657 = (let _150_656 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _150_656 (FStar_List.map (fun _58_1841 -> (match (_58_1841) with
| (u, _58_1840) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _150_657 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _58_1849 = if (let _150_658 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _150_658)) then begin
(

let unresolved = (let _150_659 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _150_659 FStar_Util.set_elements))
in (let _150_667 = (let _150_666 = (let _150_665 = (let _150_664 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _150_663 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _150_662 = (let _150_661 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _58_1848 -> (match (_58_1848) with
| (u, _58_1847) -> begin
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

let _58_1851 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_668 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _150_668))
end else begin
()
end
in ((e), (e'))))))))))))
end))))))
in (FStar_All.pipe_right _150_669 FStar_List.unzip))
in (match (_58_1855) with
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

let _58_1862 = (let _150_670 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _150_670 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_58_1862) with
| (scrutinee_env, _58_1861) -> begin
(

let _58_1868 = (tc_pat true pat_t pattern)
in (match (_58_1868) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let _58_1878 = (match (when_clause) with
| None -> begin
((None), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (e) -> begin
if (FStar_TypeChecker_Env.should_verify env) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("When clauses are not yet supported in --verify mode; they will be some day"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
(

let _58_1875 = (let _150_671 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _150_671 e))
in (match (_58_1875) with
| (e, c, g) -> begin
((Some (e)), (g))
end))
end
end)
in (match (_58_1878) with
| (when_clause, g_when) -> begin
(

let _58_1882 = (tc_term pat_env branch_exp)
in (match (_58_1882) with
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

let _58_1940 = (

let eqs = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
None
end else begin
(FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _58_1900 -> begin
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

let _58_1908 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_58_1908) with
| (c, g_branch) -> begin
(

let _58_1935 = (match (((eqs), (when_condition))) with
| _58_1910 when (not ((FStar_TypeChecker_Env.should_verify env))) -> begin
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
in (match (_58_1935) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _150_687 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _150_686 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in ((_150_687), (_150_686), (g_branch)))))
end))
end)))
in (match (_58_1940) with
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

let fail = (fun _58_1950 -> (match (()) with
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
| FStar_Syntax_Syntax.Tm_uinst (t, _58_1957) -> begin
(head_constructor t)
end
| _58_1961 -> begin
(fail ())
end))
in (

let pat_exp = (let _150_710 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _150_710 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_58_1986) -> begin
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

let sub_term_guards = (let _150_723 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _58_2004 -> (match (_58_2004) with
| (ei, _58_2003) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _58_2008 -> begin
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
| _58_2012 -> begin
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

let _58_2020 = (FStar_Syntax_Util.type_u ())
in (match (_58_2020) with
| (k, _58_2019) -> begin
(

let _58_2026 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_58_2026) with
| (t, _58_2023, _58_2025) -> begin
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

let _58_2034 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
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

let _58_2051 = (check_let_bound_def true env lb)
in (match (_58_2051) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let _58_2063 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
((g1), (e1), (univ_vars), (c1))
end else begin
(

let g1 = (let _150_735 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _150_735 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _58_2058 = (let _150_739 = (let _150_738 = (let _150_737 = (let _150_736 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (_150_736)))
in (_150_737)::[])
in (FStar_TypeChecker_Util.generalize env _150_738))
in (FStar_List.hd _150_739))
in (match (_58_2058) with
| (_58_2054, univs, e1, c1) -> begin
((g1), (e1), (univs), ((FStar_Syntax_Util.lcomp_of_comp c1)))
end)))
end
in (match (_58_2063) with
| (g1, e1, univ_vars, c1) -> begin
(

let _58_2073 = if (FStar_TypeChecker_Env.should_verify env) then begin
(

let _58_2066 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_58_2066) with
| (ok, c1) -> begin
if ok then begin
((e2), (c1))
end else begin
(

let _58_2067 = if (FStar_Options.warn_top_level_effects ()) then begin
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

let _58_2069 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _150_742 = (c1.FStar_Syntax_Syntax.comp ())
in ((e2), (_150_742))))
end
in (match (_58_2073) with
| (e2, c1) -> begin
(

let cres = (let _150_743 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_743))
in (

let _58_2075 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _150_744 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((_150_744), (cres), (FStar_TypeChecker_Rel.trivial_guard))))))
end))
end))
end))
end
| _58_2079 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let _58_2090 = env
in {FStar_TypeChecker_Env.solver = _58_2090.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2090.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2090.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2090.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2090.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2090.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2090.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2090.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2090.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2090.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2090.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2090.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2090.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_2090.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2090.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2090.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2090.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2090.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2090.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2090.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2090.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2090.FStar_TypeChecker_Env.qname_and_index})
in (

let _58_2099 = (let _150_748 = (let _150_747 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _150_747 Prims.fst))
in (check_let_bound_def false _150_748 lb))
in (match (_58_2099) with
| (e1, _58_2095, c1, g1, annotated) -> begin
(

let x = (

let _58_2100 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_2100.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2100.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let _58_2106 = (let _150_750 = (let _150_749 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_749)::[])
in (FStar_Syntax_Subst.open_term _150_750 e2))
in (match (_58_2106) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _58_2112 = (let _150_751 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _150_751 e2))
in (match (_58_2112) with
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

let _58_2121 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in ((e), (cres), (guard)))
end))))))))
end))))
end))))
end)))
end
| _58_2124 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _58_2136 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_58_2136) with
| (lbs, e2) -> begin
(

let _58_2139 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2139) with
| (env0, topt) -> begin
(

let _58_2142 = (build_let_rec_env true env0 lbs)
in (match (_58_2142) with
| (lbs, rec_env) -> begin
(

let _58_2145 = (check_let_recs rec_env lbs)
in (match (_58_2145) with
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
in (FStar_All.pipe_right ecs (FStar_List.map (fun _58_2156 -> (match (_58_2156) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _150_772 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_772))
in (

let _58_2159 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _58_2163 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_2163) with
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
| _58_2165 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _58_2177 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_58_2177) with
| (lbs, e2) -> begin
(

let _58_2180 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2180) with
| (env0, topt) -> begin
(

let _58_2183 = (build_let_rec_env false env0 lbs)
in (match (_58_2183) with
| (lbs, rec_env) -> begin
(

let _58_2186 = (check_let_recs rec_env lbs)
in (match (_58_2186) with
| (lbs, g_lbs) -> begin
(

let _58_2198 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let _58_2189 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _58_2189.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2189.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let _58_2192 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _58_2192.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _58_2192.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _58_2192.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _58_2192.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (lb.FStar_Syntax_Syntax.lbtyp)))
in ((env), (lb)))))) env))
in (match (_58_2198) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let _58_2204 = (tc_term env e2)
in (match (_58_2204) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _58_2208 = cres
in {FStar_Syntax_Syntax.eff_name = _58_2208.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _58_2208.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_2208.FStar_Syntax_Syntax.comp})
in (

let _58_2213 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_58_2213) with
| (lbs, e2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_58_2216) -> begin
((e), (cres), (guard))
end
| None -> begin
(

let _58_2219 = (check_no_escape None env bvs tres)
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
| _58_2222 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let _58_2255 = (FStar_List.fold_left (fun _58_2229 lb -> (match (_58_2229) with
| (lbs, env) -> begin
(

let _58_2234 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_58_2234) with
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

let _58_2243 = (let _150_786 = (let _150_785 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _150_785))
in (tc_check_tot_or_gtot_term (

let _58_2237 = env0
in {FStar_TypeChecker_Env.solver = _58_2237.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2237.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2237.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2237.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2237.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2237.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2237.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2237.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2237.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2237.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2237.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2237.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2237.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2237.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _58_2237.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2237.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2237.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2237.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2237.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2237.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2237.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2237.FStar_TypeChecker_Env.qname_and_index}) t _150_786))
in (match (_58_2243) with
| (t, _58_2241, g) -> begin
(

let _58_2244 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (

let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_TypeChecker_Env.should_verify env)) then begin
(

let _58_2247 = env
in {FStar_TypeChecker_Env.solver = _58_2247.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2247.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2247.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2247.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2247.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2247.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2247.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2247.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2247.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2247.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2247.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2247.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t)))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2247.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_2247.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2247.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2247.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2247.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2247.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2247.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2247.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2247.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2247.FStar_TypeChecker_Env.qname_and_index})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (t)))
end
in (

let lb = (

let _58_2250 = lb
in {FStar_Syntax_Syntax.lbname = _58_2250.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _58_2250.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb)::lbs), (env)))))))
end))
end)) (([]), (env)) lbs)
in (match (_58_2255) with
| (lbs, env) -> begin
(((FStar_List.rev lbs)), (env))
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _58_2268 = (let _150_791 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _58_2262 = (let _150_790 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _150_790 lb.FStar_Syntax_Syntax.lbdef))
in (match (_58_2262) with
| (e, c, g) -> begin
(

let _58_2263 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in ((lb), (g))))
end)))))
in (FStar_All.pipe_right _150_791 FStar_List.unzip))
in (match (_58_2268) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _58_2276 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_2276) with
| (env1, _58_2275) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _58_2282 = (check_lbtyp top_level env lb)
in (match (_58_2282) with
| (topt, wf_annot, univ_vars, env1) -> begin
(

let _58_2283 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _58_2290 = (tc_maybe_toplevel_term (

let _58_2285 = env1
in {FStar_TypeChecker_Env.solver = _58_2285.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2285.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2285.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2285.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2285.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2285.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2285.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2285.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2285.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2285.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2285.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2285.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2285.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _58_2285.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2285.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2285.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2285.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_2285.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_2285.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2285.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2285.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2285.FStar_TypeChecker_Env.qname_and_index}) e1)
in (match (_58_2290) with
| (e1, c1, g1) -> begin
(

let _58_2294 = (let _150_798 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _58_2291 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _150_798 e1 c1 wf_annot))
in (match (_58_2294) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _58_2296 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
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

let _58_2303 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in ((None), (FStar_TypeChecker_Rel.trivial_guard), ([]), (env)))
end
| _58_2306 -> begin
(

let _58_2309 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_58_2309) with
| (univ_vars, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _150_804 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars), (_150_804)))
end else begin
(

let _58_2314 = (FStar_Syntax_Util.type_u ())
in (match (_58_2314) with
| (k, _58_2313) -> begin
(

let _58_2319 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_58_2319) with
| (t, _58_2317, g) -> begin
(

let _58_2320 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
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
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _58_2326 -> (match (_58_2326) with
| (x, imp) -> begin
(

let _58_2329 = (FStar_Syntax_Util.type_u ())
in (match (_58_2329) with
| (tu, u) -> begin
(

let _58_2334 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_58_2334) with
| (t, _58_2332, g) -> begin
(

let x = (((

let _58_2335 = x
in {FStar_Syntax_Syntax.ppname = _58_2335.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2335.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in (

let _58_2338 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
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

let _58_2353 = (tc_binder env b)
in (match (_58_2353) with
| (b, env', g, u) -> begin
(

let _58_2358 = (aux env' bs)
in (match (_58_2358) with
| (bs, env', g', us) -> begin
(let _150_821 = (let _150_820 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _150_820))
in (((b)::bs), (env'), (_150_821), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun _58_2366 _58_2369 -> (match (((_58_2366), (_58_2369))) with
| ((t, imp), (args, g)) -> begin
(

let _58_2374 = (tc_term env t)
in (match (_58_2374) with
| (t, _58_2372, g') -> begin
(let _150_830 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t), (imp)))::args), (_150_830)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p _58_2378 -> (match (_58_2378) with
| (pats, g) -> begin
(

let _58_2381 = (tc_args env p)
in (match (_58_2381) with
| (args, g') -> begin
(let _150_833 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats), (_150_833)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _58_2387 = (tc_maybe_toplevel_term env e)
in (match (_58_2387) with
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

let _58_2393 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _150_836 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in ((_150_836), (false)))
end else begin
(let _150_837 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in ((_150_837), (true)))
end
in (match (_58_2393) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _150_838 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (_150_838)))
end
| _58_2397 -> begin
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

let _58_2407 = (tc_tot_or_gtot_term env t)
in (match (_58_2407) with
| (t, c, g) -> begin
(

let _58_2408 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in ((t), (c)))
end)))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let _58_2416 = (tc_check_tot_or_gtot_term env t k)
in (match (_58_2416) with
| (t, c, g) -> begin
(

let _58_2417 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _150_862 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _150_862)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _150_866 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (([]), (_150_866)))))


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let _58_2432 = (tc_binders env tps)
in (match (_58_2432) with
| (tps, env, g, us) -> begin
(

let _58_2433 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in ((tps), (env), (us)))
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (

let fail = (fun _58_2439 -> (match (()) with
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
| ((a, _58_2452))::((wp, _58_2448))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _58_2456 -> begin
(fail ())
end))
end
| _58_2458 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let _58_2465 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_58_2465) with
| (uvs, c) -> begin
((uvs), ([]), (c))
end))
end
| _58_2467 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let _58_2471 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_58_2471) with
| (uvs, t') -> begin
(match ((let _150_888 = (FStar_Syntax_Subst.compress t')
in _150_888.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
((uvs), (binders), (c))
end
| _58_2477 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))


let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (

let fail = (fun t -> (let _150_899 = (let _150_898 = (let _150_897 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in ((_150_897), ((FStar_Ident.range_of_lid mname))))
in FStar_Syntax_Syntax.Error (_150_898))
in (Prims.raise _150_899)))
in (match ((let _150_900 = (FStar_Syntax_Subst.compress signature)
in _150_900.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _58_2494))::((wp, _58_2490))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _58_2498 -> begin
(fail signature)
end))
end
| _58_2500 -> begin
(fail signature)
end)))


let open_effect_binders = (fun env ed -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _58_2505 -> begin
(

let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (

let op = (fun ts -> (

let _58_2509 = ()
in (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in (([]), (t1)))))
in (

let _58_2512 = ed
in (let _150_924 = (op ed.FStar_Syntax_Syntax.ret_wp)
in (let _150_923 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _150_922 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _150_921 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _150_920 = (op ed.FStar_Syntax_Syntax.stronger)
in (let _150_919 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _150_918 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _150_917 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _150_916 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _150_915 = (op ed.FStar_Syntax_Syntax.trivial)
in (let _150_914 = (let _150_905 = (op (([]), (ed.FStar_Syntax_Syntax.repr)))
in (Prims.snd _150_905))
in (let _150_913 = (op ed.FStar_Syntax_Syntax.return_repr)
in (let _150_912 = (op ed.FStar_Syntax_Syntax.bind_repr)
in (let _150_911 = (FStar_List.map (fun a -> (

let _58_2515 = a
in (let _150_910 = (let _150_907 = (op (([]), (a.FStar_Syntax_Syntax.action_defn)))
in (Prims.snd _150_907))
in (let _150_909 = (let _150_908 = (op (([]), (a.FStar_Syntax_Syntax.action_typ)))
in (Prims.snd _150_908))
in {FStar_Syntax_Syntax.action_name = _58_2515.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = _58_2515.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _150_910; FStar_Syntax_Syntax.action_typ = _150_909})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = _58_2512.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2512.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _58_2512.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _58_2512.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _58_2512.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _150_924; FStar_Syntax_Syntax.bind_wp = _150_923; FStar_Syntax_Syntax.if_then_else = _150_922; FStar_Syntax_Syntax.ite_wp = _150_921; FStar_Syntax_Syntax.stronger = _150_920; FStar_Syntax_Syntax.close_wp = _150_919; FStar_Syntax_Syntax.assert_p = _150_918; FStar_Syntax_Syntax.assume_p = _150_917; FStar_Syntax_Syntax.null_wp = _150_916; FStar_Syntax_Syntax.trivial = _150_915; FStar_Syntax_Syntax.repr = _150_914; FStar_Syntax_Syntax.return_repr = _150_913; FStar_Syntax_Syntax.bind_repr = _150_912; FStar_Syntax_Syntax.actions = _150_911})))))))))))))))))
end))


let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (

let _58_2521 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_58_2521) with
| (a, wp) -> begin
(

let ed = (open_effect_binders env ed)
in ((ed), (a), (wp)))
end)))


let rec tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (

let _58_2525 = ()
in (

let _58_2529 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_58_2529) with
| (binders_un, signature_un) -> begin
(

let _58_2534 = (tc_tparams env0 binders_un)
in (match (_58_2534) with
| (binders, env, _58_2533) -> begin
(

let _58_2538 = (tc_trivial_guard env signature_un)
in (match (_58_2538) with
| (signature, _58_2537) -> begin
(

let ed = (

let _58_2539 = ed
in {FStar_Syntax_Syntax.qualifiers = _58_2539.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2539.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _58_2539.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _58_2539.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _58_2539.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _58_2539.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _58_2539.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _58_2539.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _58_2539.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _58_2539.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _58_2539.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _58_2539.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _58_2539.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _58_2539.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _58_2539.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _58_2539.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _58_2539.FStar_Syntax_Syntax.actions})
in (

let _58_2545 = (open_effect_decl env ed)
in (match (_58_2545) with
| (ed, a, wp_a) -> begin
(

let get_effect_signature = (fun _58_2547 -> (match (()) with
| () -> begin
(

let _58_2551 = (tc_trivial_guard env signature_un)
in (match (_58_2551) with
| (signature, _58_2550) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (

let env = (let _150_952 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _150_952))
in (

let _58_2553 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _150_958 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _150_957 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _150_956 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _150_955 = (let _150_953 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Print.term_to_string _150_953))
in (let _150_954 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort)
in (FStar_Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n" _150_958 _150_957 _150_956 _150_955 _150_954))))))
end else begin
()
end
in (

let check_and_gen' = (fun env _58_2560 k -> (match (_58_2560) with
| (_58_2558, t) -> begin
(check_and_gen env t k)
end))
in (

let return_wp = (

let expected_k = (let _150_970 = (let _150_968 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_967 = (let _150_966 = (let _150_965 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _150_965))
in (_150_966)::[])
in (_150_968)::_150_967))
in (let _150_969 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _150_970 _150_969)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let _58_2566 = (get_effect_signature ())
in (match (_58_2566) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _150_974 = (let _150_972 = (let _150_971 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _150_971))
in (_150_972)::[])
in (let _150_973 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _150_974 _150_973)))
in (

let expected_k = (let _150_985 = (let _150_983 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _150_982 = (let _150_981 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_980 = (let _150_979 = (FStar_Syntax_Syntax.mk_binder b)
in (let _150_978 = (let _150_977 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _150_976 = (let _150_975 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (_150_975)::[])
in (_150_977)::_150_976))
in (_150_979)::_150_978))
in (_150_981)::_150_980))
in (_150_983)::_150_982))
in (let _150_984 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _150_985 _150_984)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (let _150_987 = (let _150_986 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_986 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _150_987))
in (

let expected_k = (let _150_996 = (let _150_994 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_993 = (let _150_992 = (FStar_Syntax_Syntax.mk_binder p)
in (let _150_991 = (let _150_990 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _150_989 = (let _150_988 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_988)::[])
in (_150_990)::_150_989))
in (_150_992)::_150_991))
in (_150_994)::_150_993))
in (let _150_995 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_996 _150_995)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (let _150_1001 = (let _150_999 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_998 = (let _150_997 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_997)::[])
in (_150_999)::_150_998))
in (let _150_1000 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_1001 _150_1000)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let _58_2578 = (FStar_Syntax_Util.type_u ())
in (match (_58_2578) with
| (t, _58_2577) -> begin
(

let expected_k = (let _150_1008 = (let _150_1006 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1005 = (let _150_1004 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _150_1003 = (let _150_1002 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_1002)::[])
in (_150_1004)::_150_1003))
in (_150_1006)::_150_1005))
in (let _150_1007 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _150_1008 _150_1007)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (let _150_1010 = (let _150_1009 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_1009 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _150_1010))
in (

let b_wp_a = (let _150_1014 = (let _150_1012 = (let _150_1011 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _150_1011))
in (_150_1012)::[])
in (let _150_1013 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_1014 _150_1013)))
in (

let expected_k = (let _150_1021 = (let _150_1019 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1018 = (let _150_1017 = (FStar_Syntax_Syntax.mk_binder b)
in (let _150_1016 = (let _150_1015 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_150_1015)::[])
in (_150_1017)::_150_1016))
in (_150_1019)::_150_1018))
in (let _150_1020 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_1021 _150_1020)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (let _150_1030 = (let _150_1028 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1027 = (let _150_1026 = (let _150_1023 = (let _150_1022 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_1022 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _150_1023))
in (let _150_1025 = (let _150_1024 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_1024)::[])
in (_150_1026)::_150_1025))
in (_150_1028)::_150_1027))
in (let _150_1029 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_1030 _150_1029)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _150_1039 = (let _150_1037 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1036 = (let _150_1035 = (let _150_1032 = (let _150_1031 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _150_1031 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _150_1032))
in (let _150_1034 = (let _150_1033 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_1033)::[])
in (_150_1035)::_150_1034))
in (_150_1037)::_150_1036))
in (let _150_1038 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_1039 _150_1038)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _150_1042 = (let _150_1040 = (FStar_Syntax_Syntax.mk_binder a)
in (_150_1040)::[])
in (let _150_1041 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_1042 _150_1041)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let _58_2594 = (FStar_Syntax_Util.type_u ())
in (match (_58_2594) with
| (t, _58_2593) -> begin
(

let expected_k = (let _150_1047 = (let _150_1045 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1044 = (let _150_1043 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_1043)::[])
in (_150_1045)::_150_1044))
in (let _150_1046 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _150_1047 _150_1046)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let _58_2735 = if ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) || (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable))) then begin
(

let repr = (

let _58_2600 = (FStar_Syntax_Util.type_u ())
in (match (_58_2600) with
| (t, _58_2599) -> begin
(

let expected_k = (let _150_1052 = (let _150_1050 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1049 = (let _150_1048 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_1048)::[])
in (_150_1050)::_150_1049))
in (let _150_1051 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _150_1052 _150_1051)))
in (tc_check_trivial_guard env ed.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (

let repr = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env repr)
in (let _150_1062 = (let _150_1061 = (let _150_1060 = (let _150_1059 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_1058 = (let _150_1057 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_1057)::[])
in (_150_1059)::_150_1058))
in ((repr), (_150_1060)))
in FStar_Syntax_Syntax.Tm_app (_150_1061))
in (FStar_Syntax_Syntax.mk _150_1062 None FStar_Range.dummyRange))))
in (

let mk_repr = (fun a wp -> (let _150_1067 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_repr' _150_1067 wp)))
in (

let destruct_repr = (fun t -> (match ((let _150_1070 = (FStar_Syntax_Subst.compress t)
in _150_1070.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_58_2613, ((t, _58_2620))::((wp, _58_2616))::[]) -> begin
((t), (wp))
end
| _58_2626 -> begin
(FStar_All.failwith "Unexpected repr type")
end))
in (

let bind_repr = (

let r = (let _150_1071 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_0 FStar_Syntax_Syntax.Delta_constant None)
in (FStar_All.pipe_right _150_1071 FStar_Syntax_Syntax.fv_to_tm))
in (

let _58_2630 = (get_effect_signature ())
in (match (_58_2630) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _150_1075 = (let _150_1073 = (let _150_1072 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _150_1072))
in (_150_1073)::[])
in (let _150_1074 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _150_1075 _150_1074)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" None a_wp_b)
in (

let x_a = (let _150_1076 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _150_1076))
in (

let wp_g_x = (let _150_1080 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (let _150_1079 = (let _150_1078 = (let _150_1077 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_1077))
in (_150_1078)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _150_1080 _150_1079 None FStar_Range.dummyRange)))
in (

let res = (

let wp = (let _150_1092 = (let _150_1081 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right _150_1081 Prims.snd))
in (let _150_1091 = (let _150_1090 = (let _150_1089 = (let _150_1088 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_1087 = (let _150_1086 = (FStar_Syntax_Syntax.bv_to_name b)
in (let _150_1085 = (let _150_1084 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (let _150_1083 = (let _150_1082 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (_150_1082)::[])
in (_150_1084)::_150_1083))
in (_150_1086)::_150_1085))
in (_150_1088)::_150_1087))
in (r)::_150_1089)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _150_1090))
in (FStar_Syntax_Syntax.mk_Tm_app _150_1092 _150_1091 None FStar_Range.dummyRange)))
in (mk_repr b wp))
in (

let expected_k = (let _150_1112 = (let _150_1110 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1109 = (let _150_1108 = (FStar_Syntax_Syntax.mk_binder b)
in (let _150_1107 = (let _150_1106 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (let _150_1105 = (let _150_1104 = (let _150_1094 = (let _150_1093 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a _150_1093))
in (FStar_Syntax_Syntax.null_binder _150_1094))
in (let _150_1103 = (let _150_1102 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (let _150_1101 = (let _150_1100 = (let _150_1099 = (let _150_1098 = (let _150_1095 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_150_1095)::[])
in (let _150_1097 = (let _150_1096 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _150_1096))
in (FStar_Syntax_Util.arrow _150_1098 _150_1097)))
in (FStar_Syntax_Syntax.null_binder _150_1099))
in (_150_1100)::[])
in (_150_1102)::_150_1101))
in (_150_1104)::_150_1103))
in (_150_1106)::_150_1105))
in (_150_1108)::_150_1107))
in (_150_1110)::_150_1109))
in (let _150_1111 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _150_1112 _150_1111)))
in (

let _58_2644 = (tc_tot_or_gtot_term env expected_k)
in (match (_58_2644) with
| (expected_k, _58_2641, _58_2643) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (

let env = (

let _58_2646 = env
in {FStar_TypeChecker_Env.solver = _58_2646.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_2646.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_2646.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_2646.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_2646.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_2646.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_2646.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_2646.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_2646.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_2646.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_2646.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_2646.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_2646.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_2646.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_2646.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_2646.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_2646.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_2646.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _58_2646.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_2646.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_2646.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_2646.FStar_TypeChecker_Env.qname_and_index})
in (

let br = (check_and_gen' env ed.FStar_Syntax_Syntax.bind_repr expected_k)
in br)))
end)))))))))
end)))
in (

let return_repr = (

let x_a = (let _150_1113 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _150_1113))
in (

let res = (

let wp = (let _150_1120 = (let _150_1114 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right _150_1114 Prims.snd))
in (let _150_1119 = (let _150_1118 = (let _150_1117 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_1116 = (let _150_1115 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (_150_1115)::[])
in (_150_1117)::_150_1116))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _150_1118))
in (FStar_Syntax_Syntax.mk_Tm_app _150_1120 _150_1119 None FStar_Range.dummyRange)))
in (mk_repr a wp))
in (

let expected_k = (let _150_1125 = (let _150_1123 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1122 = (let _150_1121 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_150_1121)::[])
in (_150_1123)::_150_1122))
in (let _150_1124 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _150_1125 _150_1124)))
in (

let _58_2660 = (tc_tot_or_gtot_term env expected_k)
in (match (_58_2660) with
| (expected_k, _58_2657, _58_2659) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let _58_2664 = (check_and_gen' env ed.FStar_Syntax_Syntax.return_repr expected_k)
in (match (_58_2664) with
| (univs, repr) -> begin
(match (univs) with
| [] -> begin
(([]), (repr))
end
| _58_2667 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected universe-polymorphic return for effect"), (repr.FStar_Syntax_Syntax.pos)))))
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let _58_2675 = (tc_tot_or_gtot_term env act.FStar_Syntax_Syntax.action_typ)
in (match (_58_2675) with
| (act_typ, _58_2673, g_t) -> begin
(

let env' = (FStar_TypeChecker_Env.set_expected_typ env act_typ)
in (

let _58_2677 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _150_1129 = (FStar_Syntax_Print.term_to_string act.FStar_Syntax_Syntax.action_defn)
in (let _150_1128 = (FStar_Syntax_Print.term_to_string act_typ)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" (FStar_Ident.text_of_lid act.FStar_Syntax_Syntax.action_name) _150_1129 _150_1128)))
end else begin
()
end
in (

let _58_2683 = (tc_tot_or_gtot_term env' act.FStar_Syntax_Syntax.action_defn)
in (match (_58_2683) with
| (act_defn, _58_2681, g_a) -> begin
(

let act_defn = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env act_defn)
in (

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let _58_2706 = (

let act_typ = (FStar_Syntax_Subst.compress act_typ)
in (match (act_typ.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _58_2694 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_2694) with
| (bs, _58_2693) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (let _150_1130 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs _150_1130))
in (

let _58_2701 = (tc_tot_or_gtot_term env k)
in (match (_58_2701) with
| (k, _58_2699, g) -> begin
((k), (g))
end))))
end))
end
| _58_2703 -> begin
(let _150_1135 = (let _150_1134 = (let _150_1133 = (let _150_1132 = (FStar_Syntax_Print.term_to_string act_typ)
in (let _150_1131 = (FStar_Syntax_Print.tag_of_term act_typ)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" _150_1132 _150_1131)))
in ((_150_1133), (act_defn.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_150_1134))
in (Prims.raise _150_1135))
end))
in (match (_58_2706) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env act_typ expected_k)
in (

let _58_2708 = (let _150_1138 = (let _150_1137 = (let _150_1136 = (FStar_TypeChecker_Rel.conj_guard g_t g)
in (FStar_TypeChecker_Rel.conj_guard g_k _150_1136))
in (FStar_TypeChecker_Rel.conj_guard g_a _150_1137))
in (FStar_TypeChecker_Rel.force_trivial_guard env _150_1138))
in (

let act_typ = (match ((let _150_1139 = (FStar_Syntax_Subst.compress expected_k)
in _150_1139.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _58_2716 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_2716) with
| (bs, c) -> begin
(

let _58_2719 = (destruct_repr (FStar_Syntax_Util.comp_result c))
in (match (_58_2719) with
| (a, wp) -> begin
(

let c = (let _150_1141 = (let _150_1140 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_1140)::[])
in {FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a; FStar_Syntax_Syntax.effect_args = _150_1141; FStar_Syntax_Syntax.flags = []})
in (let _150_1142 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Util.arrow bs _150_1142)))
end))
end))
end
| _58_2722 -> begin
(FStar_All.failwith "")
end)
in (

let _58_2726 = (FStar_TypeChecker_Util.generalize_universes env act_defn)
in (match (_58_2726) with
| (univs, act_defn) -> begin
(

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let _58_2728 = act
in {FStar_Syntax_Syntax.action_name = _58_2728.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = act_defn; FStar_Syntax_Syntax.action_typ = act_typ}))
end)))))
end))))
end))))
end)))
in (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.map check_action)))
in ((repr), (bind_repr), (return_repr), (actions)))))))))
end else begin
((ed.FStar_Syntax_Syntax.repr), (ed.FStar_Syntax_Syntax.bind_repr), (ed.FStar_Syntax_Syntax.return_repr), (ed.FStar_Syntax_Syntax.actions))
end
in (match (_58_2735) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t = (let _150_1143 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _150_1143))
in (

let _58_2739 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_58_2739) with
| (univs, t) -> begin
(

let _58_2755 = (match ((let _150_1145 = (let _150_1144 = (FStar_Syntax_Subst.compress t)
in _150_1144.FStar_Syntax_Syntax.n)
in ((binders), (_150_1145)))) with
| ([], _58_2742) -> begin
(([]), (t))
end
| (_58_2745, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
((binders), ((FStar_Syntax_Util.comp_result c)))
end
| _58_2752 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_58_2755) with
| (binders, signature) -> begin
(

let close = (fun n ts -> (

let ts = (let _150_1150 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _150_1150))
in (

let _58_2760 = if (((n > 0) && (not ((FStar_Syntax_Util.is_unknown (Prims.snd ts))))) && ((FStar_List.length (Prims.fst ts)) <> n)) then begin
(let _150_1153 = (let _150_1152 = (FStar_Util.string_of_int n)
in (let _150_1151 = (FStar_Syntax_Print.tscheme_to_string ts)
in (FStar_Util.format2 "The effect combinator is not universe-polymorphic enough (n=%s) (%s)" _150_1152 _150_1151)))
in (FStar_All.failwith _150_1153))
end else begin
()
end
in ts)))
in (

let close_action = (fun act -> (

let _58_2766 = (close (- (1)) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (_58_2766) with
| (univs, defn) -> begin
(

let _58_2769 = (close (- (1)) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (_58_2769) with
| (univs', typ) -> begin
(

let _58_2770 = ()
in (

let _58_2772 = act
in {FStar_Syntax_Syntax.action_name = _58_2772.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ}))
end))
end)))
in (

let _58_2774 = ()
in (

let ed = (

let _58_2776 = ed
in (let _150_1170 = (close 0 return_wp)
in (let _150_1169 = (close 1 bind_wp)
in (let _150_1168 = (close 0 if_then_else)
in (let _150_1167 = (close 0 ite_wp)
in (let _150_1166 = (close 0 stronger)
in (let _150_1165 = (close 1 close_wp)
in (let _150_1164 = (close 0 assert_p)
in (let _150_1163 = (close 0 assume_p)
in (let _150_1162 = (close 0 null_wp)
in (let _150_1161 = (close 0 trivial_wp)
in (let _150_1160 = (let _150_1156 = (close 0 (([]), (repr)))
in (Prims.snd _150_1156))
in (let _150_1159 = (close 0 return_repr)
in (let _150_1158 = (close 1 bind_repr)
in (let _150_1157 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.qualifiers = _58_2776.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2776.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _150_1170; FStar_Syntax_Syntax.bind_wp = _150_1169; FStar_Syntax_Syntax.if_then_else = _150_1168; FStar_Syntax_Syntax.ite_wp = _150_1167; FStar_Syntax_Syntax.stronger = _150_1166; FStar_Syntax_Syntax.close_wp = _150_1165; FStar_Syntax_Syntax.assert_p = _150_1164; FStar_Syntax_Syntax.assume_p = _150_1163; FStar_Syntax_Syntax.null_wp = _150_1162; FStar_Syntax_Syntax.trivial = _150_1161; FStar_Syntax_Syntax.repr = _150_1160; FStar_Syntax_Syntax.return_repr = _150_1159; FStar_Syntax_Syntax.bind_repr = _150_1158; FStar_Syntax_Syntax.actions = _150_1157})))))))))))))))
in (

let _58_2779 = if ((FStar_TypeChecker_Env.debug env FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EffDecl")))) then begin
(let _150_1171 = (FStar_Syntax_Print.eff_decl_to_string false ed)
in (FStar_Util.print_string _150_1171))
end else begin
()
end
in ed)))))
end))
end)))
end))))))))))))))))
end)))
end))
end))
end))))
and cps_and_elaborate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl) = (fun env ed -> (

let _58_2785 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_58_2785) with
| (effect_binders_un, signature_un) -> begin
(

let _58_2790 = (tc_tparams env effect_binders_un)
in (match (_58_2790) with
| (effect_binders, env, _58_2789) -> begin
(

let _58_2794 = (tc_trivial_guard env signature_un)
in (match (_58_2794) with
| (signature, _58_2793) -> begin
(

let effect_binders = (FStar_List.map (fun _58_2797 -> (match (_58_2797) with
| (bv, qual) -> begin
(let _150_1176 = (

let _58_2798 = bv
in (let _150_1175 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _58_2798.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_2798.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_1175}))
in ((_150_1176), (qual)))
end)) effect_binders)
in (

let _58_2813 = (match ((let _150_1177 = (FStar_Syntax_Subst.compress signature_un)
in _150_1177.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (((a, _58_2803))::[], effect_marker) -> begin
((a), (effect_marker))
end
| _58_2810 -> begin
(FStar_All.failwith "bad shape for effect-for-free signature")
end)
in (match (_58_2813) with
| (a, effect_marker) -> begin
(

let open_and_check = (fun t -> (

let subst = (FStar_Syntax_Subst.opening_of_binders effect_binders)
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (

let _58_2822 = (tc_term env t)
in (match (_58_2822) with
| (t, comp, _58_2821) -> begin
((t), (comp))
end)))))
in (

let recheck_debug = (fun s env t -> (

let _58_2827 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _150_1186 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Term has been %s-transformed to:\n%s\n----------\n" s _150_1186))
end else begin
()
end
in (

let _58_2834 = (tc_term env t)
in (match (_58_2834) with
| (t', _58_2831, _58_2833) -> begin
(

let _58_2835 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _150_1187 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print1 "Re-checked; got:\n%s\n----------\n" _150_1187))
end else begin
()
end
in t)
end))))
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None signature.FStar_Syntax_Syntax.pos))
in (

let _58_2841 = (open_and_check ed.FStar_Syntax_Syntax.repr)
in (match (_58_2841) with
| (repr, _comp) -> begin
(

let _58_2842 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _150_1190 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" _150_1190))
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

let wp_a = (let _150_1197 = (let _150_1196 = (let _150_1195 = (let _150_1194 = (let _150_1193 = (let _150_1192 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_1191 = (FStar_Syntax_Syntax.as_implicit false)
in ((_150_1192), (_150_1191))))
in (_150_1193)::[])
in ((wp_type), (_150_1194)))
in FStar_Syntax_Syntax.Tm_app (_150_1195))
in (mk _150_1196))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _150_1197))
in (

let effect_signature = (

let binders = (let _150_1202 = (let _150_1198 = (FStar_Syntax_Syntax.as_implicit false)
in ((a), (_150_1198)))
in (let _150_1201 = (let _150_1200 = (let _150_1199 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" None wp_a)
in (FStar_All.pipe_right _150_1199 FStar_Syntax_Syntax.mk_binder))
in (_150_1200)::[])
in (_150_1202)::_150_1201))
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

let _58_2860 = item
in (match (_58_2860) with
| (u_item, item) -> begin
(

let _58_2863 = (open_and_check item)
in (match (_58_2863) with
| (item, item_comp) -> begin
(

let _58_2864 = if (not ((FStar_Syntax_Util.is_total_lcomp item_comp))) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Computation for [item] is not total!")))
end else begin
()
end
in (

let _58_2869 = (FStar_TypeChecker_DMFF.star_expr dmff_env item)
in (match (_58_2869) with
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

let _58_2877 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.bind_repr)
in (match (_58_2877) with
| (dmff_env, _58_2874, bind_wp, bind_elab) -> begin
(

let _58_2883 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.return_repr)
in (match (_58_2883) with
| (dmff_env, _58_2880, return_wp, return_elab) -> begin
(

let return_wp = (match ((let _150_1209 = (FStar_Syntax_Subst.compress return_wp)
in _150_1209.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(let _150_1210 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) _150_1210 (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_GTot_lid)))))
end
| _58_2894 -> begin
(FStar_All.failwith "unexpected shape for return")
end)
in (

let bind_wp = (match ((let _150_1211 = (FStar_Syntax_Subst.compress bind_wp)
in _150_1211.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (let _150_1215 = (let _150_1214 = (let _150_1213 = (let _150_1212 = (mk (FStar_Syntax_Syntax.Tm_fvar (r)))
in (FStar_Syntax_Syntax.null_binder _150_1212))
in (_150_1213)::[])
in (FStar_List.append _150_1214 binders))
in (FStar_Syntax_Util.abs _150_1215 body what)))
end
| _58_2903 -> begin
(FStar_All.failwith "unexpected shape for bind")
end)
in (

let apply_close = (fun t -> if ((FStar_List.length effect_binders) = 0) then begin
t
end else begin
(let _150_1222 = (let _150_1221 = (let _150_1220 = (let _150_1219 = (let _150_1218 = (FStar_Syntax_Util.args_of_binders effect_binders)
in (Prims.snd _150_1218))
in ((t), (_150_1219)))
in FStar_Syntax_Syntax.Tm_app (_150_1220))
in (mk _150_1221))
in (FStar_Syntax_Subst.close effect_binders _150_1222))
end)
in (

let register = (fun name item -> (

let _58_2912 = (let _150_1228 = (mk_lid name)
in (let _150_1227 = (FStar_Syntax_Util.abs effect_binders item None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env _150_1228 _150_1227)))
in (match (_58_2912) with
| (sigelt, fv) -> begin
(

let _58_2913 = (let _150_1230 = (let _150_1229 = (FStar_ST.read sigelts)
in (sigelt)::_150_1229)
in (FStar_ST.op_Colon_Equals sigelts _150_1230))
in fv)
end)))
in (

let return_wp = (register "return_wp" return_wp)
in (

let return_elab = (register "return_elab" return_elab)
in (

let bind_wp = (register "bind_wp" bind_wp)
in (

let _58_2918 = (let _150_1232 = (let _150_1231 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::_150_1231)
in (FStar_ST.op_Colon_Equals sigelts _150_1232))
in (

let bind_elab = (register "bind_elab" bind_elab)
in (

let _58_2921 = (let _150_1234 = (let _150_1233 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::_150_1233)
in (FStar_ST.op_Colon_Equals sigelts _150_1234))
in (

let _58_2940 = (FStar_List.fold_left (fun _58_2925 action -> (match (_58_2925) with
| (dmff_env, actions) -> begin
(

let _58_2931 = (elaborate_and_star dmff_env ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (_58_2931) with
| (dmff_env, action_t, action_wp, action_elab) -> begin
(

let name = action.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText
in (

let action_typ_with_wp = (FStar_TypeChecker_DMFF.trans_F dmff_env action_t action_wp)
in (

let action_elab = (register (Prims.strcat name "_elab") action_elab)
in (

let action_typ_with_wp = (register (Prims.strcat name "_complete_type") action_typ_with_wp)
in (let _150_1240 = (let _150_1239 = (

let _58_2936 = action
in (let _150_1238 = (apply_close action_elab)
in (let _150_1237 = (apply_close action_typ_with_wp)
in {FStar_Syntax_Syntax.action_name = _58_2936.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = _58_2936.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _150_1238; FStar_Syntax_Syntax.action_typ = _150_1237})))
in (_150_1239)::actions)
in ((dmff_env), (_150_1240)))))))
end))
end)) ((dmff_env), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (_58_2940) with
| (dmff_env, actions) -> begin
(

let actions = (FStar_List.rev actions)
in (

let repr = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" None wp_a)
in (

let binders = (let _150_1243 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1242 = (let _150_1241 = (FStar_Syntax_Syntax.mk_binder wp)
in (_150_1241)::[])
in (_150_1243)::_150_1242))
in (let _150_1252 = (let _150_1251 = (let _150_1249 = (let _150_1248 = (let _150_1247 = (let _150_1246 = (let _150_1245 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_1244 = (FStar_Syntax_Syntax.as_implicit false)
in ((_150_1245), (_150_1244))))
in (_150_1246)::[])
in ((repr), (_150_1247)))
in FStar_Syntax_Syntax.Tm_app (_150_1248))
in (mk _150_1249))
in (let _150_1250 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env _150_1251 _150_1250)))
in (FStar_Syntax_Util.abs binders _150_1252 None))))
in (

let repr = (recheck_debug "FC" env repr)
in (

let repr = (register "repr" repr)
in (

let _58_2972 = (match ((let _150_1253 = (FStar_Syntax_Subst.compress wp_type)
in _150_1253.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (effect_param, arrow, _58_2950) -> begin
(

let _58_2955 = (FStar_Syntax_Subst.open_term effect_param arrow)
in (match (_58_2955) with
| (effect_param, arrow) -> begin
(match ((let _150_1254 = (FStar_Syntax_Subst.compress arrow)
in _150_1254.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let _58_2962 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (_58_2962) with
| (wp_binders, c) -> begin
(

let _58_2965 = (FStar_Util.prefix wp_binders)
in (match (_58_2965) with
| (pre_args, post) -> begin
(let _150_1256 = (FStar_Syntax_Util.arrow pre_args c)
in (let _150_1255 = (FStar_Syntax_Util.abs effect_param (Prims.fst post).FStar_Syntax_Syntax.sort None)
in ((_150_1256), (_150_1255))))
end))
end))
end
| _58_2967 -> begin
(let _150_1258 = (let _150_1257 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" _150_1257))
in (FStar_All.failwith _150_1258))
end)
end))
end
| _58_2969 -> begin
(let _150_1260 = (let _150_1259 = (FStar_Syntax_Print.term_to_string wp_type)
in (FStar_Util.format1 "Impossible: pre/post abs %s" _150_1259))
in (FStar_All.failwith _150_1260))
end)
in (match (_58_2972) with
| (pre, post) -> begin
(

let _58_2973 = (let _150_1261 = (register "pre" pre)
in (Prims.ignore _150_1261))
in (

let _58_2975 = (let _150_1262 = (register "post" post)
in (Prims.ignore _150_1262))
in (

let _58_2977 = (let _150_1263 = (register "wp" wp_type)
in (Prims.ignore _150_1263))
in (

let ed = (

let _58_2979 = ed
in (let _150_1274 = (FStar_Syntax_Subst.close_binders effect_binders)
in (let _150_1273 = (FStar_Syntax_Subst.close effect_binders effect_signature)
in (let _150_1272 = (let _150_1264 = (apply_close return_wp)
in (([]), (_150_1264)))
in (let _150_1271 = (let _150_1265 = (apply_close bind_wp)
in (([]), (_150_1265)))
in (let _150_1270 = (apply_close repr)
in (let _150_1269 = (let _150_1266 = (apply_close return_elab)
in (([]), (_150_1266)))
in (let _150_1268 = (let _150_1267 = (apply_close bind_elab)
in (([]), (_150_1267)))
in {FStar_Syntax_Syntax.qualifiers = _58_2979.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_2979.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _58_2979.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _150_1274; FStar_Syntax_Syntax.signature = _150_1273; FStar_Syntax_Syntax.ret_wp = _150_1272; FStar_Syntax_Syntax.bind_wp = _150_1271; FStar_Syntax_Syntax.if_then_else = _58_2979.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _58_2979.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _58_2979.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _58_2979.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _58_2979.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _58_2979.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _58_2979.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _58_2979.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _150_1270; FStar_Syntax_Syntax.return_repr = _150_1269; FStar_Syntax_Syntax.bind_repr = _150_1268; FStar_Syntax_Syntax.actions = actions}))))))))
in (

let _58_2984 = (FStar_TypeChecker_DMFF.gen_wps_for_free env effect_binders a wp_a ed)
in (match (_58_2984) with
| (sigelts', ed) -> begin
(

let _58_2985 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _150_1275 = (FStar_Syntax_Print.eff_decl_to_string true ed)
in (FStar_Util.print_string _150_1275))
end else begin
()
end
in (let _150_1278 = (let _150_1277 = (let _150_1276 = (FStar_ST.read sigelts)
in (FStar_List.rev _150_1276))
in (FStar_List.append _150_1277 sigelts'))
in ((_150_1278), (ed))))
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

let _58_2991 = ()
in (

let _58_2999 = ()
in (match (ses) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _58_3028, _58_3030, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _58_3019, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _58_3008, r2))::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
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

let lex_top_t = (let _150_1286 = (let _150_1285 = (let _150_1284 = (let _150_1283 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _150_1283 FStar_Syntax_Syntax.Delta_constant None))
in ((_150_1284), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_150_1285))
in (FStar_Syntax_Syntax.mk _150_1286 None r1))
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

let a = (let _150_1287 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _150_1287))
in (

let hd = (let _150_1288 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _150_1288))
in (

let tl = (let _150_1293 = (let _150_1292 = (let _150_1291 = (let _150_1290 = (let _150_1289 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _150_1289 FStar_Syntax_Syntax.Delta_constant None))
in ((_150_1290), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_150_1291))
in (FStar_Syntax_Syntax.mk _150_1292 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _150_1293))
in (

let res = (let _150_1297 = (let _150_1296 = (let _150_1295 = (let _150_1294 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _150_1294 FStar_Syntax_Syntax.Delta_constant None))
in ((_150_1295), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_150_1296))
in (FStar_Syntax_Syntax.mk _150_1297 None r2))
in (let _150_1298 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (Some (FStar_Syntax_Syntax.imp_tag))))::(((hd), (None)))::(((tl), (None)))::[]) _150_1298))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t), (FStar_Syntax_Const.lex_t_lid), (0), ([]), ([]), (r2)))
in (let _150_1300 = (let _150_1299 = (FStar_TypeChecker_Env.get_range env)
in (((tc)::(dc_lextop)::(dc_lexcons)::[]), ([]), (lids), (_150_1299)))
in FStar_Syntax_Syntax.Sig_bundle (_150_1300)))))))))))))))
end
| _58_3054 -> begin
(let _150_1302 = (let _150_1301 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle (((ses), ([]), (lids), (FStar_Range.dummyRange)))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _150_1301))
in (FStar_All.failwith _150_1302))
end))))
and tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _58_3064 = (FStar_Syntax_Util.type_u ())
in (match (_58_3064) with
| (k, _58_3063) -> begin
(

let phi = (let _150_1308 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _150_1308 (norm env)))
in (

let _58_3066 = (FStar_TypeChecker_Util.check_uvars r phi)
in FStar_Syntax_Syntax.Sig_assume (((lid), (phi), (quals), (r)))))
end))))
and tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _150_1318 = (let _150_1317 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _150_1317))
in (FStar_TypeChecker_Errors.diag r _150_1318)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let _58_3089 = ()
in (

let _58_3091 = (warn_positivity tc r)
in (

let _58_3095 = (FStar_Syntax_Subst.open_term tps k)
in (match (_58_3095) with
| (tps, k) -> begin
(

let _58_3100 = (tc_binders env tps)
in (match (_58_3100) with
| (tps, env_tps, guard_params, us) -> begin
(

let _58_3103 = (FStar_Syntax_Util.arrow_formals k)
in (match (_58_3103) with
| (indices, t) -> begin
(

let _58_3108 = (tc_binders env_tps indices)
in (match (_58_3108) with
| (indices, env', guard_indices, us') -> begin
(

let _58_3116 = (

let _58_3113 = (tc_tot_or_gtot_term env' t)
in (match (_58_3113) with
| (t, _58_3111, g) -> begin
(let _150_1325 = (let _150_1324 = (let _150_1323 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params _150_1323))
in (FStar_TypeChecker_Rel.discharge_guard env' _150_1324))
in ((t), (_150_1325)))
end))
in (match (_58_3116) with
| (t, guard) -> begin
(

let k = (let _150_1326 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _150_1326))
in (

let _58_3120 = (FStar_Syntax_Util.type_u ())
in (match (_58_3120) with
| (t_type, u) -> begin
(

let _58_3121 = (let _150_1327 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _150_1327))
in (

let t_tc = (let _150_1328 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _150_1328))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _150_1329 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((_150_1329), (FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps), (k), (mutuals), (data), (quals), (r)))), (u), (guard))))))))
end)))
end))
end))
end))
end))
end))))
end
| _58_3128 -> begin
(FStar_All.failwith "impossible")
end))
in (

let positive_if_pure = (fun _58_3130 l -> ())
in (

let tc_data = (fun env tcs _58_7 -> (match (_58_7) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let _58_3147 = ()
in (

let _58_3182 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _58_3151 -> (match (_58_3151) with
| (se, u_tc) -> begin
if (let _150_1342 = (let _150_1341 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _150_1341))
in (FStar_Ident.lid_equals tc_lid _150_1342)) then begin
(

let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_3153, _58_3155, tps, _58_3158, _58_3160, _58_3162, _58_3164, _58_3166) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _58_3172 -> (match (_58_3172) with
| (x, _58_3171) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
end
| _58_3174 -> begin
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
in (match (_58_3182) with
| (tps, u_tc) -> begin
(

let _58_3202 = (match ((let _150_1344 = (FStar_Syntax_Subst.compress t)
in _150_1344.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _58_3190 = (FStar_Util.first_N ntps bs)
in (match (_58_3190) with
| (_58_3188, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res)))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _58_3196 -> (match (_58_3196) with
| (x, _58_3195) -> begin
FStar_Syntax_Syntax.DB ((((ntps - (1 + i))), (x)))
end))))
in (let _150_1347 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _150_1347))))
end))
end
| _58_3199 -> begin
(([]), (t))
end)
in (match (_58_3202) with
| (arguments, result) -> begin
(

let _58_3203 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1350 = (FStar_Syntax_Print.lid_to_string c)
in (let _150_1349 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _150_1348 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _150_1350 _150_1349 _150_1348))))
end else begin
()
end
in (

let _58_3208 = (tc_tparams env arguments)
in (match (_58_3208) with
| (arguments, env', us) -> begin
(

let _58_3212 = (tc_trivial_guard env' result)
in (match (_58_3212) with
| (result, _58_3211) -> begin
(

let _58_3216 = (FStar_Syntax_Util.head_and_args result)
in (match (_58_3216) with
| (head, _58_3215) -> begin
(

let _58_3221 = (match ((let _150_1351 = (FStar_Syntax_Subst.compress head)
in _150_1351.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _58_3220 -> begin
(let _150_1356 = (let _150_1355 = (let _150_1354 = (let _150_1353 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _150_1352 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _150_1353 _150_1352)))
in ((_150_1354), (r)))
in FStar_Syntax_Syntax.Error (_150_1355))
in (Prims.raise _150_1356))
end)
in (

let g = (FStar_List.fold_left2 (fun g _58_3227 u_x -> (match (_58_3227) with
| (x, _58_3226) -> begin
(

let _58_3229 = ()
in (let _150_1360 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _150_1360)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _150_1364 = (let _150_1362 = (FStar_All.pipe_right tps (FStar_List.map (fun _58_3235 -> (match (_58_3235) with
| (x, _58_3234) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append _150_1362 arguments))
in (let _150_1363 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _150_1364 _150_1363)))
in ((FStar_Syntax_Syntax.Sig_datacon (((c), ([]), (t), (tc_lid), (ntps), (quals), ([]), (r)))), (g)))))
end))
end))
end)))
end))
end)))
end
| _58_3238 -> begin
(FStar_All.failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let _58_3244 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _58_8 -> (match (_58_8) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_3248, _58_3250, tps, k, _58_3254, _58_3256, _58_3258, _58_3260) -> begin
(let _150_1375 = (let _150_1374 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _150_1374))
in (FStar_Syntax_Syntax.null_binder _150_1375))
end
| _58_3264 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _58_9 -> (match (_58_9) with
| FStar_Syntax_Syntax.Sig_datacon (_58_3268, _58_3270, t, _58_3273, _58_3275, _58_3277, _58_3279, _58_3281) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _58_3285 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let t = (let _150_1377 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _150_1377))
in (

let _58_3288 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1378 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _150_1378))
end else begin
()
end
in (

let _58_3292 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_58_3292) with
| (uvs, t) -> begin
(

let _58_3294 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1382 = (let _150_1380 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _150_1380 (FStar_String.concat ", ")))
in (let _150_1381 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _150_1382 _150_1381)))
end else begin
()
end
in (

let _58_3298 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_58_3298) with
| (uvs, t) -> begin
(

let _58_3302 = (FStar_Syntax_Util.arrow_formals t)
in (match (_58_3302) with
| (args, _58_3301) -> begin
(

let _58_3305 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_58_3305) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _58_3309 se -> (match (_58_3309) with
| (x, _58_3308) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _58_3313, tps, _58_3316, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let _58_3339 = (match ((let _150_1385 = (FStar_Syntax_Subst.compress ty)
in _150_1385.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _58_3330 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_58_3330) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _58_3333 -> begin
(let _150_1386 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) _150_1386 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps), (t)))
end))
end
| _58_3336 -> begin
(([]), (ty))
end)
in (match (_58_3339) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs), (tps), (t), (mutuals), (datas), (quals), (r)))
end)))
end
| _58_3341 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| _58_3345 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _150_1387 -> FStar_Syntax_Syntax.U_name (_150_1387))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _58_10 -> (match (_58_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _58_3350, _58_3352, _58_3354, _58_3356, _58_3358, _58_3360, _58_3362) -> begin
((tc), (uvs_universes))
end
| _58_3366 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _58_3371 d -> (match (_58_3371) with
| (t, _58_3370) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _58_3375, _58_3377, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _150_1391 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _150_1391 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon (((l), (uvs), (ty), (tc), (ntps), (quals), (mutuals), (r))))
end
| _58_3387 -> begin
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

let _58_3397 = (FStar_All.pipe_right ses (FStar_List.partition (fun _58_11 -> (match (_58_11) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_3391) -> begin
true
end
| _58_3394 -> begin
false
end))))
in (match (_58_3397) with
| (tys, datas) -> begin
(

let _58_3404 = if (FStar_All.pipe_right datas (FStar_Util.for_some (fun _58_12 -> (match (_58_12) with
| FStar_Syntax_Syntax.Sig_datacon (_58_3400) -> begin
false
end
| _58_3403 -> begin
true
end)))) then begin
(let _150_1396 = (let _150_1395 = (let _150_1394 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (_150_1394)))
in FStar_Syntax_Syntax.Error (_150_1395))
in (Prims.raise _150_1396))
end else begin
()
end
in (

let env0 = env
in (

let _58_3423 = (FStar_List.fold_right (fun tc _58_3411 -> (match (_58_3411) with
| (env, all_tcs, g) -> begin
(

let _58_3416 = (tc_tycon env tc)
in (match (_58_3416) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (

let _58_3418 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1399 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _150_1399))
end else begin
()
end
in (let _150_1401 = (let _150_1400 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g _150_1400))
in ((env), ((((tc), (tc_u)))::all_tcs), (_150_1401)))))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_58_3423) with
| (env, tcs, g) -> begin
(

let _58_3433 = (FStar_List.fold_right (fun se _58_3427 -> (match (_58_3427) with
| (datas, g) -> begin
(

let _58_3430 = (tc_data env tcs se)
in (match (_58_3430) with
| (data, g') -> begin
(let _150_1404 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((data)::datas), (_150_1404)))
end))
end)) datas (([]), (g)))
in (match (_58_3433) with
| (datas, g) -> begin
(

let _58_3436 = (let _150_1405 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _150_1405 datas))
in (match (_58_3436) with
| (tcs, datas) -> begin
(

let sig_bndle = (let _150_1407 = (let _150_1406 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_150_1406)))
in FStar_Syntax_Syntax.Sig_bundle (_150_1407))
in (

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (_58_3441, _58_3443, t, _58_3446, _58_3448, _58_3450, _58_3452, _58_3454) -> begin
t
end
| _58_3458 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let dr = FStar_Range.dummyRange
in (

let haseq_ty = (fun usubst us acc ty -> (

let _58_3485 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _58_3467, bs, t, _58_3471, d_lids, _58_3474, _58_3476) -> begin
((lid), (bs), (t), (d_lids))
end
| _58_3480 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_58_3485) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _150_1418 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _150_1418 t))
in (

let _58_3490 = (FStar_Syntax_Subst.open_term bs t)
in (match (_58_3490) with
| (bs, t) -> begin
(

let ibs = (match ((let _150_1419 = (FStar_Syntax_Subst.compress t)
in _150_1419.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _58_3493) -> begin
ibs
end
| _58_3497 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _150_1422 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _150_1421 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_1422 _150_1421)))
in (

let ind = (let _150_1425 = (FStar_List.map (fun _58_3504 -> (match (_58_3504) with
| (bv, aq) -> begin
(let _150_1424 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_150_1424), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _150_1425 None dr))
in (

let ind = (let _150_1428 = (FStar_List.map (fun _58_3508 -> (match (_58_3508) with
| (bv, aq) -> begin
(let _150_1427 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_150_1427), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _150_1428 None dr))
in (

let haseq_ind = (let _150_1430 = (let _150_1429 = (FStar_Syntax_Syntax.as_arg ind)
in (_150_1429)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _150_1430 None dr))
in (

let bs' = (FStar_List.filter (fun b -> (

let _58_3519 = acc
in (match (_58_3519) with
| (_58_3513, en, _58_3516, _58_3518) -> begin
(

let opt = (let _150_1433 = (let _150_1432 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _150_1432))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort _150_1433 false))
in (match (opt) with
| None -> begin
false
end
| Some (_58_3523) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (let _150_1439 = (let _150_1438 = (let _150_1437 = (let _150_1436 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg _150_1436))
in (_150_1437)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _150_1438 None dr))
in (FStar_Syntax_Util.mk_conj t _150_1439))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let _58_3530 = fml
in (let _150_1445 = (let _150_1444 = (let _150_1443 = (let _150_1442 = (let _150_1441 = (let _150_1440 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_150_1440)::[])
in (_150_1441)::[])
in FStar_Syntax_Syntax.Meta_pattern (_150_1442))
in ((fml), (_150_1443)))
in FStar_Syntax_Syntax.Tm_meta (_150_1444))
in {FStar_Syntax_Syntax.n = _150_1445; FStar_Syntax_Syntax.tk = _58_3530.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _58_3530.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_3530.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _150_1451 = (let _150_1450 = (let _150_1449 = (let _150_1448 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _150_1448 None))
in (FStar_Syntax_Syntax.as_arg _150_1449))
in (_150_1450)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _150_1451 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _150_1457 = (let _150_1456 = (let _150_1455 = (let _150_1454 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _150_1454 None))
in (FStar_Syntax_Syntax.as_arg _150_1455))
in (_150_1456)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _150_1457 None dr))) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let _58_3544 = acc
in (match (_58_3544) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_58_3549, _58_3551, _58_3553, t_lid, _58_3556, _58_3558, _58_3560, _58_3562) -> begin
(t_lid = lid)
end
| _58_3566 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let haseq_data = (fun acc data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (match ((let _150_1463 = (FStar_Syntax_Subst.compress dt)
in _150_1463.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _58_3575) -> begin
(

let dbs = (let _150_1464 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _150_1464))
in (

let dbs = (let _150_1465 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _150_1465 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = (let _150_1469 = (let _150_1468 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_150_1468)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _150_1469 None dr))
in (

let sort_range = (Prims.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b = (let _150_1471 = (let _150_1470 = (FStar_Syntax_Print.term_to_string ind)
in (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add the \'noeq\' qualifier" _150_1470))
in (FStar_TypeChecker_Util.label _150_1471 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b))))) FStar_Syntax_Util.t_true dbs)
in (

let _58_3589 = acc
in (match (_58_3589) with
| (env, cond') -> begin
(let _150_1473 = (FStar_TypeChecker_Env.push_binders env dbs)
in (let _150_1472 = (FStar_Syntax_Util.mk_conj cond' cond)
in ((_150_1473), (_150_1472))))
end))))))
end
| _58_3591 -> begin
acc
end))))
in (

let _58_3594 = (FStar_List.fold_left haseq_data ((env), (FStar_Syntax_Util.t_true)) t_datas)
in (match (_58_3594) with
| (env, cond) -> begin
(

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (let _150_1475 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _150_1474 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env), (_150_1475), (_150_1474)))))
end))))))
end)))))))))))))))
end))))
end)))
in (

let is_noeq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Noeq)) quals)
in if (((not ((FStar_Ident.lid_equals env.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid))) && (not (is_noeq))) && ((FStar_List.length tcs) > 0)) then begin
(

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_3600, us, _58_3603, _58_3605, _58_3607, _58_3609, _58_3611, _58_3613) -> begin
us
end
| _58_3617 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let _58_3621 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_58_3621) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _58_3623 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _58_3625 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let _58_3632 = (FStar_List.fold_left (haseq_ty usubst us) (([]), (env), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (_58_3632) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let _58_3637 = (tc_trivial_guard env phi)
in (match (_58_3637) with
| (phi, _58_3636) -> begin
(

let _58_3638 = if (FStar_TypeChecker_Env.should_verify env) then begin
(let _150_1477 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _150_1477))
end else begin
()
end
in (

let _58_3640 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env0 us)
in (

let ses = (FStar_List.fold_left (fun l _58_3646 -> (match (_58_3646) with
| (lid, fml) -> begin
(

let se = (tc_assume env lid fml [] dr)
in (FStar_List.append l ((se)::[])))
end)) [] axioms)
in (let _150_1482 = (let _150_1481 = (let _150_1480 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_150_1480)))
in FStar_Syntax_Syntax.Sig_bundle (_150_1481))
in (_150_1482)::ses)))))
end)))
end))))))
end)))
end else begin
(sig_bndle)::[]
end)))))
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
in (let _150_1485 = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (_150_1485)))))
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

let _58_3690 = (set_options FStar_Options.Set o)
in (((se)::[]), (env)))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(

let _58_3694 = (let _150_1492 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _150_1492 Prims.ignore))
in (

let _58_3699 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _58_3701 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (((se)::[]), (env)))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_58_3704) -> begin
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

let _58_3720 = (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun _58_3715 a -> (match (_58_3715) with
| (env, ses) -> begin
(

let se_let = (FStar_Syntax_Util.action_as_lb a)
in (let _150_1495 = (FStar_TypeChecker_Env.push_sigelt env se_let)
in ((_150_1495), ((se_let)::ses))))
end)) ((env), ((se)::[]))))
in (match (_58_3720) with
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

let _58_3729 = (let _150_1496 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _150_1496))
in (match (_58_3729) with
| (a, wp_a_src) -> begin
(

let _58_3732 = (let _150_1497 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _150_1497))
in (match (_58_3732) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _150_1501 = (let _150_1500 = (let _150_1499 = (let _150_1498 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (_150_1498)))
in FStar_Syntax_Syntax.NT (_150_1499))
in (_150_1500)::[])
in (FStar_Syntax_Subst.subst _150_1501 wp_b_tgt))
in (

let expected_k = (let _150_1506 = (let _150_1504 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1503 = (let _150_1502 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_150_1502)::[])
in (_150_1504)::_150_1503))
in (let _150_1505 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _150_1506 _150_1505)))
in (

let lift_wp = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift_wp) expected_k)
in (

let repr_type = (fun eff_name a wp -> (

let no_reify = (fun l -> (let _150_1518 = (let _150_1517 = (let _150_1516 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _150_1515 = (FStar_TypeChecker_Env.get_range env)
in ((_150_1516), (_150_1515))))
in FStar_Syntax_Syntax.Error (_150_1517))
in (Prims.raise _150_1518)))
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
(let _150_1525 = (let _150_1523 = (let _150_1522 = (let _150_1521 = (FStar_Syntax_Syntax.as_arg a)
in (let _150_1520 = (let _150_1519 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_1519)::[])
in (_150_1521)::_150_1520))
in ((repr), (_150_1522)))
in FStar_Syntax_Syntax.Tm_app (_150_1523))
in (let _150_1524 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _150_1525 None _150_1524)))
end)
end)))
in (

let lift = (match (sub.FStar_Syntax_Syntax.lift) with
| None -> begin
None
end
| Some (_58_3748, lift) -> begin
(

let _58_3754 = (let _150_1526 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _150_1526))
in (match (_58_3754) with
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

let lift_wp_a = (let _150_1533 = (let _150_1531 = (let _150_1530 = (let _150_1529 = (FStar_Syntax_Syntax.as_arg a_typ)
in (let _150_1528 = (let _150_1527 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (_150_1527)::[])
in (_150_1529)::_150_1528))
in (((Prims.snd sub.FStar_Syntax_Syntax.lift_wp)), (_150_1530)))
in FStar_Syntax_Syntax.Tm_app (_150_1531))
in (let _150_1532 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _150_1533 None _150_1532)))
in (repr_type sub.FStar_Syntax_Syntax.target a_typ lift_wp_a))
in (

let expected_k = (let _150_1540 = (let _150_1538 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_1537 = (let _150_1536 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (let _150_1535 = (let _150_1534 = (FStar_Syntax_Syntax.null_binder repr_f)
in (_150_1534)::[])
in (_150_1536)::_150_1535))
in (_150_1538)::_150_1537))
in (let _150_1539 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow _150_1540 _150_1539)))
in (

let _58_3767 = (tc_tot_or_gtot_term env expected_k)
in (match (_58_3767) with
| (expected_k, _58_3764, _58_3766) -> begin
(

let lift = (check_and_gen env lift expected_k)
in Some (lift))
end))))))))
end))
end)
in (

let sub = (

let _58_3770 = sub
in {FStar_Syntax_Syntax.source = _58_3770.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _58_3770.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift})
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

let _58_3783 = ()
in (

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _58_3789 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_58_3789) with
| (tps, c) -> begin
(

let _58_3793 = (tc_tparams env tps)
in (match (_58_3793) with
| (tps, env, us) -> begin
(

let _58_3797 = (tc_comp env c)
in (match (_58_3797) with
| (c, u, g) -> begin
(

let _58_3798 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let _58_3804 = (let _150_1541 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _150_1541))
in (match (_58_3804) with
| (uvs, t) -> begin
(

let _58_3823 = (match ((let _150_1543 = (let _150_1542 = (FStar_Syntax_Subst.compress t)
in _150_1542.FStar_Syntax_Syntax.n)
in ((tps), (_150_1543)))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_58_3807, c)) -> begin
(([]), (c))
end
| (_58_3813, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
((tps), (c))
end
| _58_3820 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_58_3823) with
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

let _58_3834 = ()
in (

let _58_3838 = (let _150_1545 = (let _150_1544 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _150_1544))
in (check_and_gen env t _150_1545))
in (match (_58_3838) with
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

let _58_3858 = (tc_term env e)
in (match (_58_3858) with
| (e, c, g1) -> begin
(

let _58_3863 = (let _150_1549 = (let _150_1546 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_150_1546))
in (let _150_1548 = (let _150_1547 = (c.FStar_Syntax_Syntax.comp ())
in ((e), (_150_1547)))
in (check_expected_effect env _150_1549 _150_1548)))
in (match (_58_3863) with
| (e, _58_3861, g) -> begin
(

let _58_3864 = (let _150_1550 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _150_1550))
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
(let _150_1562 = (let _150_1561 = (let _150_1560 = (let _150_1559 = (FStar_Syntax_Print.lid_to_string l)
in (let _150_1558 = (FStar_Syntax_Print.quals_to_string q)
in (let _150_1557 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _150_1559 _150_1558 _150_1557))))
in ((_150_1560), (r)))
in FStar_Syntax_Syntax.Error (_150_1561))
in (Prims.raise _150_1562))
end
end))
in (

let _58_3908 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _58_3885 lb -> (match (_58_3885) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _58_3904 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
((gen), (lb), (quals_opt))
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (

let _58_3899 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _58_3898 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _150_1565 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Syntax_Const.effect_ALL_lid), (tval), (lb.FStar_Syntax_Syntax.lbdef)))
in ((false), (_150_1565), (quals_opt)))))
end)
in (match (_58_3904) with
| (gen, lb, quals_opt) -> begin
((gen), ((lb)::lbs), (quals_opt))
end)))
end)) ((true), ([]), (if (quals = []) then begin
None
end else begin
Some (quals)
end))))
in (match (_58_3908) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _58_13 -> (match (_58_13) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _58_3917 -> begin
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

let e = (let _150_1569 = (let _150_1568 = (let _150_1567 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((((Prims.fst lbs)), (lbs'))), (_150_1567)))
in FStar_Syntax_Syntax.Tm_let (_150_1568))
in (FStar_Syntax_Syntax.mk _150_1569 None r))
in (

let _58_3951 = (match ((tc_maybe_toplevel_term (

let _58_3921 = env
in {FStar_TypeChecker_Env.solver = _58_3921.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_3921.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_3921.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_3921.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_3921.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_3921.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_3921.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_3921.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_3921.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_3921.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_3921.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _58_3921.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _58_3921.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_3921.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_3921.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_3921.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_3921.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_3921.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_3921.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_3921.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_3921.FStar_TypeChecker_Env.qname_and_index}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _58_3928; FStar_Syntax_Syntax.pos = _58_3926; FStar_Syntax_Syntax.vars = _58_3924}, _58_3935, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_58_3939, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _58_3945 -> begin
quals
end)
in ((FStar_Syntax_Syntax.Sig_let (((lbs), (r), (lids), (quals)))), (lbs)))
end
| _58_3948 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_58_3951) with
| (se, lbs) -> begin
(

let _58_3957 = if (log env) then begin
(let _150_1577 = (let _150_1576 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _150_1573 = (let _150_1572 = (let _150_1571 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _150_1571.FStar_Syntax_Syntax.fv_name)
in _150_1572.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _150_1573))) with
| None -> begin
true
end
| _58_3955 -> begin
false
end)
in if should_log then begin
(let _150_1575 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _150_1574 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _150_1575 _150_1574)))
end else begin
""
end))))
in (FStar_All.pipe_right _150_1576 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _150_1577))
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

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _58_14 -> (match (_58_14) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _58_3967 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _58_3977 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_58_3979) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _58_3990, _58_3992) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _58_3998 -> (match (_58_3998) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _58_4004, _58_4006, quals, r) -> begin
(

let dec = (let _150_1593 = (let _150_1592 = (let _150_1591 = (let _150_1590 = (let _150_1589 = (FStar_Syntax_Syntax.mk_Total t)
in ((bs), (_150_1589)))
in FStar_Syntax_Syntax.Tm_arrow (_150_1590))
in (FStar_Syntax_Syntax.mk _150_1591 None r))
in ((l), (us), (_150_1592), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_150_1593))
in (((dec)::out), (hidden)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _58_4016, _58_4018, _58_4020, _58_4022, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r)))
in (((dec)::out), ((l)::hidden)))
end
| _58_4028 -> begin
((out), (hidden))
end)
end)) ses (([]), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end
| FStar_Syntax_Syntax.Sig_assume (_58_4030, _58_4032, quals, _58_4035) -> begin
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
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _58_15 -> (match (_58_15) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _58_4054 -> begin
false
end)))) then begin
(((se)::[]), (hidden))
end else begin
(([]), (hidden))
end
end
end
| FStar_Syntax_Syntax.Sig_main (_58_4056) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _58_4075, _58_4077, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
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
(let _150_1600 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _150_1599 = (let _150_1598 = (let _150_1597 = (let _150_1596 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _150_1596.FStar_Syntax_Syntax.fv_name)
in _150_1597.FStar_Syntax_Syntax.v)
in ((_150_1598), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_150_1599)))))
in ((_150_1600), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let process_one_decl = (fun _58_4098 se -> (match (_58_4098) with
| (ses, exports, env, hidden) -> begin
(

let _58_4100 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_1609 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _150_1609))
end else begin
()
end
in (

let _58_4104 = (tc_decl env se)
in (match (_58_4104) with
| (ses', env) -> begin
(

let _58_4107 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _150_1614 = (FStar_List.fold_left (fun s se -> (let _150_1613 = (let _150_1612 = (FStar_Syntax_Print.sigelt_to_string se)
in (Prims.strcat _150_1612 "\n"))
in (Prims.strcat s _150_1613))) "" ses')
in (FStar_Util.print1 "Checked: %s\n" _150_1614))
end else begin
()
end
in (

let _58_4110 = (FStar_List.iter (fun se -> (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)) ses')
in (

let _58_4119 = (FStar_List.fold_left (fun _58_4114 se -> (match (_58_4114) with
| (le, lh) -> begin
(

let tup = (for_export hidden se)
in (((FStar_List.rev_append (Prims.fst tup) le)), ((FStar_List.rev_append (Prims.snd tup) lh))))
end)) (([]), ([])) ses')
in (match (_58_4119) with
| (exported, hidden) -> begin
(((FStar_List.rev_append ses' ses)), (((FStar_List.rev_append exported []))::exports), (env), (hidden))
end))))
end)))
end))
in (

let _58_4145 = (FStar_List.fold_left (fun acc se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(

let _58_4133 = acc
in (match (_58_4133) with
| (_58_4127, _58_4129, env, _58_4132) -> begin
(

let _58_4136 = (cps_and_elaborate env ne)
in (match (_58_4136) with
| (ses, ne) -> begin
(

let ses = (FStar_List.append ses ((FStar_Syntax_Syntax.Sig_new_effect (((ne), (r))))::[]))
in (FStar_List.fold_left process_one_decl acc ses))
end))
end))
end
| _58_4139 -> begin
(process_one_decl acc se)
end)) (([]), ([]), (env), ([])) ses)
in (match (_58_4145) with
| (ses, exports, env, _58_4144) -> begin
(let _150_1620 = (FStar_All.pipe_right (FStar_List.rev_append exports []) FStar_List.flatten)
in (((FStar_List.rev_append ses [])), (_150_1620), (env)))
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

let _58_4150 = env
in (let _150_1625 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _58_4150.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_4150.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_4150.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_4150.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_4150.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_4150.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_4150.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_4150.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_4150.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_4150.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_4150.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_4150.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_4150.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_4150.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_4150.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_4150.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _150_1625; FStar_TypeChecker_Env.lax = _58_4150.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_4150.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_4150.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_4150.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_4150.FStar_TypeChecker_Env.qname_and_index}))
in (

let _58_4153 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
in (

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let _58_4159 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_58_4159) with
| (ses, exports, env) -> begin
(((

let _58_4160 = modul
in {FStar_Syntax_Syntax.name = _58_4160.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _58_4160.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _58_4160.FStar_Syntax_Syntax.is_interface})), (exports), (env))
end))))))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let _58_4168 = (tc_decls env decls)
in (match (_58_4168) with
| (ses, exports, env) -> begin
(

let modul = (

let _58_4169 = modul
in {FStar_Syntax_Syntax.name = _58_4169.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _58_4169.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _58_4169.FStar_Syntax_Syntax.is_interface})
in ((modul), (exports), (env)))
end)))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul = (

let _58_4175 = modul
in {FStar_Syntax_Syntax.name = _58_4175.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _58_4175.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in (

let _58_4179 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let _58_4181 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (

let _58_4183 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (

let _58_4185 = (let _150_1638 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _150_1638 Prims.ignore))
in ((modul), (env)))))))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let _58_4192 = (tc_partial_modul env modul)
in (match (_58_4192) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _58_4195 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _150_1647 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _150_1647))
end else begin
()
end
in (

let env = (

let _58_4197 = env
in {FStar_TypeChecker_Env.solver = _58_4197.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_4197.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_4197.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_4197.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_4197.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_4197.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_4197.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_4197.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_4197.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_4197.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_4197.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_4197.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_4197.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_4197.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_4197.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_4197.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_4197.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_4197.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _58_4197.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_4197.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_4197.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_4197.FStar_TypeChecker_Env.qname_and_index})
in (

let _58_4213 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _58_4205) -> begin
(let _150_1652 = (let _150_1651 = (let _150_1650 = (FStar_TypeChecker_Env.get_range env)
in (((Prims.strcat "Implicit argument: " msg)), (_150_1650)))
in FStar_Syntax_Syntax.Error (_150_1651))
in (Prims.raise _150_1652))
end
in (match (_58_4213) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end else begin
(let _150_1657 = (let _150_1656 = (let _150_1655 = (let _150_1653 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _150_1653))
in (let _150_1654 = (FStar_TypeChecker_Env.get_range env)
in ((_150_1655), (_150_1654))))
in FStar_Syntax_Syntax.Error (_150_1656))
in (Prims.raise _150_1657))
end
end)))))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
FStar_Syntax_Syntax.U_zero
end else begin
(

let _58_4216 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_1662 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print1 "universe_of %s\n" _150_1662))
end else begin
()
end
in (

let _58_4221 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_58_4221) with
| (env, _58_4220) -> begin
(

let env = (

let _58_4222 = env
in {FStar_TypeChecker_Env.solver = _58_4222.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_4222.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_4222.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_4222.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_4222.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_4222.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_4222.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_4222.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_4222.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_4222.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_4222.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_4222.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_4222.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _58_4222.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _58_4222.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _58_4222.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_4222.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _58_4222.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_4222.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _58_4222.FStar_TypeChecker_Env.qname_and_index})
in (

let fail = (fun e t -> (let _150_1672 = (let _150_1671 = (let _150_1670 = (let _150_1668 = (FStar_Syntax_Print.term_to_string e)
in (let _150_1667 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" _150_1668 _150_1667)))
in (let _150_1669 = (FStar_TypeChecker_Env.get_range env)
in ((_150_1670), (_150_1669))))
in FStar_Syntax_Syntax.Error (_150_1671))
in (Prims.raise _150_1672)))
in (

let ok = (fun u -> (

let _58_4230 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_1676 = (FStar_Syntax_Print.tag_of_term e)
in (let _150_1675 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.print2 "<end> universe_of %s is %s\n" _150_1676 _150_1675)))
end else begin
()
end
in u))
in (

let universe_of_type = (fun e t -> (match ((let _150_1681 = (FStar_Syntax_Util.unrefine t)
in _150_1681.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(ok u)
end
| _58_4238 -> begin
(fail e t)
end))
in (

let _58_4241 = (FStar_Syntax_Util.head_and_args e)
in (match (_58_4241) with
| (head, args) -> begin
(match ((let _150_1682 = (FStar_Syntax_Subst.compress head)
in _150_1682.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_58_4243, t) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _150_1683 = (FStar_Syntax_Subst.compress t)
in _150_1683.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_4249, t) -> begin
(universe_of_type e (FStar_Syntax_Util.comp_result t))
end
| _58_4254 -> begin
(universe_of_type e t)
end))
end
| _58_4256 -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoInline)::[]) env e)
in (

let _58_4269 = (tc_term env e)
in (match (_58_4269) with
| (_58_4259, {FStar_Syntax_Syntax.eff_name = _58_4266; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_4263; FStar_Syntax_Syntax.comp = _58_4261}, g) -> begin
(

let _58_4270 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (let _150_1685 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (FStar_All.pipe_left (universe_of_type e) _150_1685)))
end)))
end)
end))))))
end)))
end)


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

let _58_4274 = if (FStar_Options.debug_any ()) then begin
(let _150_1690 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _150_1690))
end else begin
()
end
in (

let _58_4278 = (tc_modul env m)
in (match (_58_4278) with
| (m, env) -> begin
(

let _58_4279 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _150_1691 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _150_1691))
end else begin
()
end
in ((m), (env)))
end))))




