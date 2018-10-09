
open Prims
open FStar_Pervasives

let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___354_6 = env
in {FStar_TypeChecker_Env.solver = uu___354_6.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___354_6.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___354_6.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___354_6.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___354_6.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___354_6.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___354_6.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___354_6.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___354_6.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___354_6.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___354_6.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = uu___354_6.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___354_6.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___354_6.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___354_6.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___354_6.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___354_6.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___354_6.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___354_6.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___354_6.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___354_6.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___354_6.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___354_6.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___354_6.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___354_6.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___354_6.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___354_6.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___354_6.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___354_6.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___354_6.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___354_6.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___354_6.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___354_6.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___354_6.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___354_6.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___354_6.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___354_6.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___354_6.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___354_6.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___354_6.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___354_6.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___354_6.FStar_TypeChecker_Env.nbe}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let uu___355_12 = env
in {FStar_TypeChecker_Env.solver = uu___355_12.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___355_12.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___355_12.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___355_12.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___355_12.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___355_12.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___355_12.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___355_12.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___355_12.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___355_12.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___355_12.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___355_12.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___355_12.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___355_12.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___355_12.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___355_12.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___355_12.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___355_12.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___355_12.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___355_12.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___355_12.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___355_12.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___355_12.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___355_12.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___355_12.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___355_12.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___355_12.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___355_12.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___355_12.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___355_12.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___355_12.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___355_12.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___355_12.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___355_12.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___355_12.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___355_12.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___355_12.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___355_12.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___355_12.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___355_12.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___355_12.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___355_12.FStar_TypeChecker_Env.nbe}))


let mk_lex_list : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v1 tl1 -> (

let r = (match ((Prims.op_Equality tl1.FStar_Syntax_Syntax.pos FStar_Range.dummyRange)) with
| true -> begin
v1.FStar_Syntax_Syntax.pos
end
| uu____45 -> begin
(FStar_Range.union_ranges v1.FStar_Syntax_Syntax.pos tl1.FStar_Syntax_Syntax.pos)
end)
in (

let uu____46 = (

let uu____51 = (

let uu____52 = (FStar_Syntax_Syntax.as_arg v1)
in (

let uu____61 = (

let uu____72 = (FStar_Syntax_Syntax.as_arg tl1)
in (uu____72)::[])
in (uu____52)::uu____61))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair uu____51))
in (uu____46 FStar_Pervasives_Native.None r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  Prims.bool = (fun uu___347_113 -> (match (uu___347_113) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| uu____116 -> begin
false
end))


let steps : 'Auu____123 . 'Auu____123  ->  FStar_TypeChecker_Env.step Prims.list = (fun env -> (FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.NoFullNorm)::[])


let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize (steps env) env t))


let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (FStar_TypeChecker_Normalize.normalize_comp (steps env) env c))


let check_no_escape : FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun head_opt env fvs kt -> (

let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
((t), (FStar_TypeChecker_Env.trivial_guard))
end
| uu____206 -> begin
(

let t1 = (match (try_norm) with
| true -> begin
(norm env t)
end
| uu____214 -> begin
t
end)
in (

let fvs' = (FStar_Syntax_Free.names t1)
in (

let uu____218 = (FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)
in (match (uu____218) with
| FStar_Pervasives_Native.None -> begin
((t1), (FStar_TypeChecker_Env.trivial_guard))
end
| FStar_Pervasives_Native.Some (x) -> begin
(match ((not (try_norm))) with
| true -> begin
(aux true t1)
end
| uu____232 -> begin
(

let fail1 = (fun uu____242 -> (

let msg = (match (head_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____244 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" uu____244))
end
| FStar_Pervasives_Native.Some (head1) -> begin
(

let uu____246 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____247 = (FStar_TypeChecker_Normalize.term_to_string env head1)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" uu____246 uu____247)))
end)
in (

let uu____248 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_EscapedBoundVar), (msg)) uu____248))))
in (

let uu____253 = (

let uu____266 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____267 = (

let uu____268 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____268))
in (FStar_TypeChecker_Util.new_implicit_var "no escape" uu____266 env uu____267)))
in (match (uu____253) with
| (s, uu____282, g0) -> begin
(

let uu____296 = (FStar_TypeChecker_Rel.try_teq true env t1 s)
in (match (uu____296) with
| FStar_Pervasives_Native.Some (g) -> begin
(

let g1 = (

let uu____305 = (FStar_TypeChecker_Env.conj_guard g g0)
in (FStar_TypeChecker_Rel.solve_deferred_constraints env uu____305))
in ((s), (g1)))
end
| uu____306 -> begin
(fail1 ())
end))
end)))
end)
end))))
end))
in (aux false kt)))


let push_binding : 'Auu____315 . FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * 'Auu____315)  ->  FStar_TypeChecker_Env.env = (fun env b -> (FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)))


let maybe_extend_subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.subst_t = (fun s b v1 -> (

let uu____369 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____369) with
| true -> begin
s
end
| uu____370 -> begin
(FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst b)), (v1))))::s
end)))


let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t lc.FStar_Syntax_Syntax.cflags (fun uu____391 -> (

let uu____392 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (FStar_Syntax_Util.set_result_typ uu____392 t)))))


let memo_tk : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun e t -> e)


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> ((FStar_TypeChecker_Env.def_check_guard_wf e.FStar_Syntax_Syntax.pos "value_check_expected_typ" env guard);
(

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(

let uu____448 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____448))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let uu____451 = (

let uu____458 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____458) with
| FStar_Pervasives_Native.None -> begin
(((memo_tk e t)), (lc), (guard))
end
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____468 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (uu____468) with
| (e1, lc1) -> begin
(

let t1 = lc1.FStar_Syntax_Syntax.res_typ
in (

let uu____482 = (FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t')
in (match (uu____482) with
| (e2, g) -> begin
((

let uu____496 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____496) with
| true -> begin
(

let uu____497 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____498 = (FStar_Syntax_Print.term_to_string t')
in (

let uu____499 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (

let uu____500 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_Util.print4 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n" uu____497 uu____498 uu____499 uu____500)))))
end
| uu____501 -> begin
()
end));
(

let msg = (

let uu____508 = (FStar_TypeChecker_Env.is_trivial_guard_formula g)
in (match (uu____508) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____517 -> begin
(FStar_All.pipe_left (fun _0_1 -> FStar_Pervasives_Native.Some (_0_1)) (FStar_TypeChecker_Err.subtyping_failed env t1 t'))
end))
in (

let g1 = (FStar_TypeChecker_Env.conj_guard g guard)
in (

let lc2 = (

let uu____531 = ((FStar_All.pipe_right tlc FStar_Util.is_left) && (FStar_TypeChecker_Util.should_return env (FStar_Pervasives_Native.Some (e2)) lc1))
in (match (uu____531) with
| true -> begin
(

let uu____536 = (

let uu____537 = (FStar_TypeChecker_Util.lcomp_univ_opt lc1)
in (FStar_TypeChecker_Util.return_value env uu____537 t1 e2))
in (FStar_All.pipe_right uu____536 FStar_Syntax_Util.lcomp_of_comp))
end
| uu____540 -> begin
lc1
end))
in (

let uu____541 = (FStar_TypeChecker_Util.strengthen_precondition msg env e2 lc2 g1)
in (match (uu____541) with
| (lc3, g2) -> begin
(

let uu____554 = (set_lcomp_result lc3 t')
in (((memo_tk e2 t')), (uu____554), (g2)))
end)))));
)
end)))
end))
end))
in (match (uu____451) with
| (e1, lc1, g) -> begin
((e1), (lc1), (g))
end))));
))


let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (

let uu____591 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____591) with
| FStar_Pervasives_Native.None -> begin
((e), (lc), (FStar_TypeChecker_Env.trivial_guard))
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____601 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (uu____601) with
| (e1, lc1) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t)
end))
end)))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt ec -> (

let uu____653 = ec
in (match (uu____653) with
| (e, c) -> begin
(

let tot_or_gtot = (fun c1 -> (

let uu____676 = (FStar_Syntax_Util.is_pure_comp c1)
in (match (uu____676) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c1))
end
| uu____677 -> begin
(

let uu____678 = (FStar_Syntax_Util.is_pure_or_ghost_comp c1)
in (match (uu____678) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c1))
end
| uu____679 -> begin
(failwith "Impossible: Expected pure_or_ghost comp")
end))
end)))
in (

let uu____680 = (match (copt) with
| FStar_Pervasives_Native.Some (uu____693) -> begin
((copt), (c))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____696 = (((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Parser_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) || (((FStar_Options.ml_ish ()) && env.FStar_TypeChecker_Env.lax) && (

let uu____698 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (not (uu____698)))))
in (match (uu____696) with
| true -> begin
(

let uu____705 = (

let uu____708 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in FStar_Pervasives_Native.Some (uu____708))
in ((uu____705), (c)))
end
| uu____711 -> begin
(

let uu____712 = (FStar_Syntax_Util.is_tot_or_gtot_comp c)
in (match (uu____712) with
| true -> begin
(

let uu____719 = (tot_or_gtot c)
in ((FStar_Pervasives_Native.None), (uu____719)))
end
| uu____722 -> begin
(

let uu____723 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (match (uu____723) with
| true -> begin
(

let uu____730 = (

let uu____733 = (tot_or_gtot c)
in FStar_Pervasives_Native.Some (uu____733))
in ((uu____730), (c)))
end
| uu____736 -> begin
((FStar_Pervasives_Native.None), (c))
end))
end))
end))
end)
in (match (uu____680) with
| (expected_c_opt, c1) -> begin
(

let c2 = (norm_c env c1)
in (match (expected_c_opt) with
| FStar_Pervasives_Native.None -> begin
((e), (c2), (FStar_TypeChecker_Env.trivial_guard))
end
| FStar_Pervasives_Native.Some (expected_c) -> begin
(

let c3 = (

let uu____760 = (FStar_Syntax_Util.lcomp_of_comp c2)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e uu____760))
in (

let c4 = (FStar_Syntax_Syntax.lcomp_comp c3)
in ((

let uu____763 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Low)
in (match (uu____763) with
| true -> begin
(

let uu____764 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____765 = (FStar_Syntax_Print.comp_to_string c4)
in (

let uu____766 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "In check_expected_effect, asking rel to solve the problem on e=(%s) and c=(%s) and expected_c=(%s)\n" uu____764 uu____765 uu____766))))
end
| uu____767 -> begin
()
end));
(

let uu____768 = (FStar_TypeChecker_Util.check_comp env e c4 expected_c)
in (match (uu____768) with
| (e1, uu____782, g) -> begin
(

let g1 = (

let uu____785 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard uu____785 "could not prove post-condition" g))
in ((

let uu____787 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____787) with
| true -> begin
(

let uu____788 = (FStar_Range.string_of_range e1.FStar_Syntax_Syntax.pos)
in (

let uu____789 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print2 "(%s) DONE check_expected_effect;\n\tguard is: %s\n" uu____788 uu____789)))
end
| uu____790 -> begin
()
end));
(

let e2 = (FStar_TypeChecker_Util.maybe_lift env e1 (FStar_Syntax_Util.comp_effect_name c4) (FStar_Syntax_Util.comp_effect_name expected_c) (FStar_Syntax_Util.comp_result c4))
in ((e2), (expected_c), (g1)));
))
end));
)))
end))
end)))
end)))


let no_logical_guard : 'Auu____800 'Auu____801 . FStar_TypeChecker_Env.env  ->  ('Auu____800 * 'Auu____801 * FStar_TypeChecker_Env.guard_t)  ->  ('Auu____800 * 'Auu____801 * FStar_TypeChecker_Env.guard_t) = (fun env uu____823 -> (match (uu____823) with
| (te, kt, f) -> begin
(

let uu____833 = (FStar_TypeChecker_Env.guard_form f)
in (match (uu____833) with
| FStar_TypeChecker_Common.Trivial -> begin
((te), (kt), (f))
end
| FStar_TypeChecker_Common.NonTrivial (f1) -> begin
(

let uu____841 = (FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term env f1)
in (

let uu____846 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____841 uu____846)))
end))
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  unit = (fun env -> (

let uu____858 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____858) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.print_string "Expected type is None\n")
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____862 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" uu____862))
end)))


let rec get_pat_vars' : FStar_Syntax_Syntax.bv Prims.list  ->  Prims.bool  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun all andlist pats -> (

let pats1 = (FStar_Syntax_Util.unmeta pats)
in (

let uu____899 = (FStar_Syntax_Util.head_and_args pats1)
in (match (uu____899) with
| (head1, args) -> begin
(

let uu____944 = (

let uu____959 = (

let uu____960 = (FStar_Syntax_Util.un_uinst head1)
in uu____960.FStar_Syntax_Syntax.n)
in ((uu____959), (args)))
in (match (uu____944) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____976) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
(match (andlist) with
| true -> begin
(FStar_Util.as_set all FStar_Syntax_Syntax.order_bv)
end
| uu____999 -> begin
(FStar_Util.new_set FStar_Syntax_Syntax.order_bv)
end)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____1001, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____1002))))::((hd1, FStar_Pervasives_Native.None))::((tl1, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let hdvs = (get_pat_vars' all false hd1)
in (

let tlvs = (get_pat_vars' all andlist tl1)
in (match (andlist) with
| true -> begin
(FStar_Util.set_intersect hdvs tlvs)
end
| uu____1073 -> begin
(FStar_Util.set_union hdvs tlvs)
end)))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____1075, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____1076))))::((pat, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid) -> begin
(FStar_Syntax_Free.names pat)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((subpats, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpatOr_lid) -> begin
(get_pat_vars' all true subpats)
end
| uu____1158 -> begin
(FStar_Util.new_set FStar_Syntax_Syntax.order_bv)
end))
end))))
and get_pat_vars : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun all pats -> (get_pat_vars' all false pats))


let check_pat_fvs : 'Auu____1187 . FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * 'Auu____1187) Prims.list  ->  unit = (fun rng env pats bs -> (

let pat_vars = (

let uu____1223 = (FStar_List.map FStar_Pervasives_Native.fst bs)
in (

let uu____1230 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env pats)
in (get_pat_vars uu____1223 uu____1230)))
in (

let uu____1231 = (FStar_All.pipe_right bs (FStar_Util.find_opt (fun uu____1258 -> (match (uu____1258) with
| (b, uu____1264) -> begin
(

let uu____1265 = (FStar_Util.set_mem b pat_vars)
in (not (uu____1265)))
end))))
in (match (uu____1231) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (x, uu____1271) -> begin
(

let uu____1276 = (

let uu____1281 = (

let uu____1282 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" uu____1282))
in ((FStar_Errors.Warning_PatternMissingBoundVar), (uu____1281)))
in (FStar_Errors.log_issue rng uu____1276))
end))))


let check_smt_pat : 'Auu____1293 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.bv * 'Auu____1293) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  unit = (fun env t bs c -> (

let uu____1334 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____1334) with
| true -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____1335; FStar_Syntax_Syntax.effect_name = uu____1336; FStar_Syntax_Syntax.result_typ = uu____1337; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, uu____1341))::[]; FStar_Syntax_Syntax.flags = uu____1342}) -> begin
(check_pat_fvs t.FStar_Syntax_Syntax.pos env pats bs)
end
| uu____1403 -> begin
(failwith "Impossible")
end)
end
| uu____1404 -> begin
()
end)))


let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.univ_names) Prims.list = (fun env actuals expected_c -> (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let env1 = (

let uu___356_1463 = env
in {FStar_TypeChecker_Env.solver = uu___356_1463.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___356_1463.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___356_1463.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___356_1463.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___356_1463.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___356_1463.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___356_1463.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___356_1463.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___356_1463.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___356_1463.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___356_1463.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___356_1463.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___356_1463.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___356_1463.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___356_1463.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___356_1463.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___356_1463.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___356_1463.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___356_1463.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___356_1463.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___356_1463.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___356_1463.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___356_1463.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___356_1463.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___356_1463.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___356_1463.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___356_1463.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___356_1463.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___356_1463.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___356_1463.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___356_1463.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___356_1463.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___356_1463.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___356_1463.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___356_1463.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___356_1463.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___356_1463.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___356_1463.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___356_1463.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___356_1463.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___356_1463.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___356_1463.FStar_TypeChecker_Env.nbe})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env1 FStar_Parser_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> ((

let uu____1489 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____1489) with
| true -> begin
(

let uu____1490 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (

let uu____1491 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print2 "Building a decreases clause over (%s) and %s\n" uu____1490 uu____1491)))
end
| uu____1492 -> begin
()
end));
(

let filter_types_and_functions = (fun bs1 -> (FStar_All.pipe_right bs1 (FStar_List.collect (fun uu____1522 -> (match (uu____1522) with
| (b, uu____1532) -> begin
(

let t = (

let uu____1538 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (FStar_TypeChecker_Normalize.unfold_whnf env1 uu____1538))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_type (uu____1541) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1542) -> begin
[]
end
| uu____1557 -> begin
(

let uu____1558 = (FStar_Syntax_Syntax.bv_to_name b)
in (uu____1558)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let uu____1571 = (FStar_Syntax_Util.head_and_args dec)
in (match (uu____1571) with
| (head1, uu____1591) -> begin
(match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
dec
end
| uu____1619 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let cflags = (FStar_Syntax_Util.comp_flags c)
in (

let uu____1627 = (FStar_All.pipe_right cflags (FStar_List.tryFind (fun uu___348_1636 -> (match (uu___348_1636) with
| FStar_Syntax_Syntax.DECREASES (uu____1637) -> begin
true
end
| uu____1640 -> begin
false
end))))
in (match (uu____1627) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| uu____1646 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| uu____1667 -> begin
(mk_lex_list xs)
end))
end)))));
))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun uu____1696 -> (match (uu____1696) with
| (l, t, u_names) -> begin
(

let uu____1720 = (

let uu____1721 = (FStar_Syntax_Subst.compress t)
in uu____1721.FStar_Syntax_Syntax.n)
in (match (uu____1720) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals1 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____1780 -> (match (uu____1780) with
| (x, imp) -> begin
(

let uu____1799 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____1799) with
| true -> begin
(

let uu____1806 = (

let uu____1807 = (

let uu____1810 = (FStar_Syntax_Syntax.range_of_bv x)
in FStar_Pervasives_Native.Some (uu____1810))
in (FStar_Syntax_Syntax.new_bv uu____1807 x.FStar_Syntax_Syntax.sort))
in ((uu____1806), (imp)))
end
| uu____1813 -> begin
((x), (imp))
end))
end))))
in (

let uu____1816 = (FStar_Syntax_Subst.open_comp formals1 c)
in (match (uu____1816) with
| (formals2, c1) -> begin
(

let dec = (decreases_clause formals2 c1)
in (

let precedes1 = (

let uu____1837 = (

let uu____1842 = (

let uu____1843 = (FStar_Syntax_Syntax.as_arg dec)
in (

let uu____1852 = (

let uu____1863 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (uu____1863)::[])
in (uu____1843)::uu____1852))
in (FStar_Syntax_Syntax.mk_Tm_app precedes uu____1842))
in (uu____1837 FStar_Pervasives_Native.None r))
in (

let precedes2 = (FStar_TypeChecker_Util.label "Could not prove termination of this recursive call" r precedes1)
in (

let uu____1899 = (FStar_Util.prefix formals2)
in (match (uu____1899) with
| (bs, (last1, imp)) -> begin
(

let last2 = (

let uu___357_1962 = last1
in (

let uu____1963 = (FStar_Syntax_Util.refine last1 precedes2)
in {FStar_Syntax_Syntax.ppname = uu___357_1962.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___357_1962.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1963}))
in (

let refined_formals = (FStar_List.append bs ((((last2), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c1)
in ((

let uu____1999 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____1999) with
| true -> begin
(

let uu____2000 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____2001 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____2002 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" uu____2000 uu____2001 uu____2002))))
end
| uu____2003 -> begin
()
end));
((l), (t'), (u_names));
))))
end)))))
end)))
end
| uu____2006 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ExpectedArrowAnnotatedType), ("Annotated type of \'let rec\' must be an arrow")) t.FStar_Syntax_Syntax.pos)
end))
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end))


let wrap_guard_with_tactic_opt : FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun topt g -> (match (topt) with
| FStar_Pervasives_Native.None -> begin
g
end
| FStar_Pervasives_Native.Some (tactic) -> begin
(FStar_TypeChecker_Env.always_map_guard g (fun g1 -> (

let uu____2067 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero g1)
in (FStar_TypeChecker_Common.mk_by_tactic tactic uu____2067))))
end))


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> ((

let uu____2662 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____2662) with
| true -> begin
(

let uu____2663 = (

let uu____2664 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____2664))
in (

let uu____2665 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____2666 = (

let uu____2667 = (FStar_Syntax_Subst.compress e)
in (FStar_Syntax_Print.tag_of_term uu____2667))
in (FStar_Util.print3 "(%s) Starting tc_term of %s (%s) {\n" uu____2663 uu____2665 uu____2666))))
end
| uu____2668 -> begin
()
end));
(

let uu____2669 = (FStar_Util.record_time (fun uu____2687 -> (tc_maybe_toplevel_term (

let uu___358_2690 = env
in {FStar_TypeChecker_Env.solver = uu___358_2690.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___358_2690.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___358_2690.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___358_2690.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___358_2690.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___358_2690.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___358_2690.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___358_2690.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___358_2690.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___358_2690.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___358_2690.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___358_2690.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___358_2690.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___358_2690.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___358_2690.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___358_2690.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___358_2690.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___358_2690.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___358_2690.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___358_2690.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___358_2690.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___358_2690.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___358_2690.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___358_2690.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___358_2690.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___358_2690.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___358_2690.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___358_2690.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___358_2690.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___358_2690.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___358_2690.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___358_2690.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___358_2690.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___358_2690.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___358_2690.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___358_2690.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___358_2690.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___358_2690.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___358_2690.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___358_2690.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___358_2690.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___358_2690.FStar_TypeChecker_Env.nbe}) e)))
in (match (uu____2669) with
| (r, ms) -> begin
((

let uu____2712 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____2712) with
| true -> begin
((

let uu____2714 = (

let uu____2715 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____2715))
in (

let uu____2716 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____2717 = (

let uu____2718 = (FStar_Syntax_Subst.compress e)
in (FStar_Syntax_Print.tag_of_term uu____2718))
in (

let uu____2719 = (FStar_Util.string_of_int ms)
in (FStar_Util.print4 "(%s) } tc_term of %s (%s) took %sms\n" uu____2714 uu____2716 uu____2717 uu____2719)))));
(

let uu____2720 = r
in (match (uu____2720) with
| (e1, uu____2728, uu____2729) -> begin
(

let uu____2730 = (

let uu____2731 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____2731))
in (

let uu____2732 = (FStar_Syntax_Print.term_to_string e1)
in (

let uu____2733 = (

let uu____2734 = (FStar_Syntax_Subst.compress e1)
in (FStar_Syntax_Print.tag_of_term uu____2734))
in (FStar_Util.print3 "(%s) Result is: %s (%s)\n" uu____2730 uu____2732 uu____2733))))
end));
)
end
| uu____2735 -> begin
()
end));
r;
)
end));
))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env1 = (match ((Prims.op_Equality e.FStar_Syntax_Syntax.pos FStar_Range.dummyRange)) with
| true -> begin
env
end
| uu____2745 -> begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end)
in (

let top = (FStar_Syntax_Subst.compress e)
in ((

let uu____2748 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Medium)
in (match (uu____2748) with
| true -> begin
(

let uu____2749 = (

let uu____2750 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____2750))
in (

let uu____2751 = (FStar_Syntax_Print.tag_of_term top)
in (

let uu____2752 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print3 "Typechecking %s (%s): %s\n" uu____2749 uu____2751 uu____2752))))
end
| uu____2753 -> begin
()
end));
(match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____2760) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_uinst (uu____2789) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____2796) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____2809) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_name (uu____2810) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____2811) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_constant (uu____2812) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_abs (uu____2813) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____2832) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_refine (uu____2847) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_type (uu____2854) -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(tc_value env1 e)
end
| FStar_Syntax_Syntax.Tm_quoted (qt, qi) -> begin
(

let projl = (fun uu___349_2870 -> (match (uu___349_2870) with
| FStar_Util.Inl (x) -> begin
x
end
| FStar_Util.Inr (uu____2876) -> begin
(failwith "projl fail")
end))
in (

let non_trivial_antiquotes = (fun qi1 -> (

let is_name1 = (fun t -> (

let uu____2889 = (

let uu____2890 = (FStar_Syntax_Subst.compress t)
in uu____2890.FStar_Syntax_Syntax.n)
in (match (uu____2889) with
| FStar_Syntax_Syntax.Tm_name (uu____2893) -> begin
true
end
| uu____2894 -> begin
false
end)))
in (FStar_Util.for_some (fun uu____2903 -> (match (uu____2903) with
| (uu____2908, t) -> begin
(

let uu____2910 = (is_name1 t)
in (not (uu____2910)))
end)) qi1.FStar_Syntax_Syntax.antiquotes)))
in (match (qi.FStar_Syntax_Syntax.qkind) with
| FStar_Syntax_Syntax.Quote_static when (non_trivial_antiquotes qi) -> begin
(

let e0 = e
in (

let newbvs = (FStar_List.map (fun uu____2928 -> (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_term)) qi.FStar_Syntax_Syntax.antiquotes)
in (

let z = (FStar_List.zip qi.FStar_Syntax_Syntax.antiquotes newbvs)
in (

let lbs = (FStar_List.map (fun uu____2971 -> (match (uu____2971) with
| ((bv, t), bv') -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding FStar_Pervasives_Native.None (FStar_Util.Inl (bv')) [] FStar_Syntax_Syntax.t_term FStar_Parser_Const.effect_Tot_lid t [] t.FStar_Syntax_Syntax.pos)
end)) z)
in (

let qi1 = (

let uu___359_3000 = qi
in (

let uu____3001 = (FStar_List.map (fun uu____3029 -> (match (uu____3029) with
| ((bv, uu____3045), bv') -> begin
(

let uu____3057 = (FStar_Syntax_Syntax.bv_to_name bv')
in ((bv), (uu____3057)))
end)) z)
in {FStar_Syntax_Syntax.qkind = uu___359_3000.FStar_Syntax_Syntax.qkind; FStar_Syntax_Syntax.antiquotes = uu____3001}))
in (

let nq = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (((qt), (qi1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let e1 = (FStar_List.fold_left (fun t lb -> (

let uu____3072 = (

let uu____3079 = (

let uu____3080 = (

let uu____3093 = (

let uu____3096 = (

let uu____3097 = (

let uu____3104 = (projl lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.mk_binder uu____3104))
in (uu____3097)::[])
in (FStar_Syntax_Subst.close uu____3096 t))
in ((((false), ((lb)::[]))), (uu____3093)))
in FStar_Syntax_Syntax.Tm_let (uu____3080))
in (FStar_Syntax_Syntax.mk uu____3079))
in (uu____3072 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))) nq lbs)
in (tc_maybe_toplevel_term env1 e1))))))))
end
| FStar_Syntax_Syntax.Quote_static -> begin
(

let aqs = qi.FStar_Syntax_Syntax.antiquotes
in (

let env_tm = (FStar_TypeChecker_Env.set_expected_typ env1 FStar_Syntax_Syntax.t_term)
in (

let uu____3140 = (FStar_List.fold_right (fun uu____3176 uu____3177 -> (match (((uu____3176), (uu____3177))) with
| ((bv, tm), (aqs_rev, guard)) -> begin
(

let uu____3246 = (tc_term env_tm tm)
in (match (uu____3246) with
| (tm1, uu____3264, g) -> begin
(

let uu____3266 = (FStar_TypeChecker_Env.conj_guard g guard)
in (((((bv), (tm1)))::aqs_rev), (uu____3266)))
end))
end)) aqs (([]), (FStar_TypeChecker_Env.trivial_guard)))
in (match (uu____3140) with
| (aqs_rev, guard) -> begin
(

let qi1 = (

let uu___360_3308 = qi
in {FStar_Syntax_Syntax.qkind = uu___360_3308.FStar_Syntax_Syntax.qkind; FStar_Syntax_Syntax.antiquotes = (FStar_List.rev aqs_rev)})
in (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (((qt), (qi1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env1 tm (FStar_Util.Inl (FStar_Syntax_Syntax.t_term)) guard)))
end))))
end
| FStar_Syntax_Syntax.Quote_dynamic -> begin
(

let c = (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_zero)::[]; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_Tac_lid; FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_term; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.SOMETRIVIAL)::(FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION)::[]})
in (

let uu____3327 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____3327) with
| (env', uu____3341) -> begin
(

let uu____3346 = (tc_term (

let uu___361_3355 = env'
in {FStar_TypeChecker_Env.solver = uu___361_3355.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___361_3355.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___361_3355.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___361_3355.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___361_3355.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___361_3355.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___361_3355.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___361_3355.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___361_3355.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___361_3355.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___361_3355.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___361_3355.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___361_3355.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___361_3355.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___361_3355.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___361_3355.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___361_3355.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___361_3355.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___361_3355.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___361_3355.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___361_3355.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___361_3355.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___361_3355.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___361_3355.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___361_3355.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___361_3355.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___361_3355.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___361_3355.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___361_3355.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___361_3355.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___361_3355.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___361_3355.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___361_3355.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___361_3355.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___361_3355.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___361_3355.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___361_3355.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___361_3355.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___361_3355.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___361_3355.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___361_3355.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___361_3355.FStar_TypeChecker_Env.nbe}) qt)
in (match (uu____3346) with
| (qt1, uu____3363, uu____3364) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (((qt1), (qi)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____3370 = (

let uu____3377 = (

let uu____3382 = (FStar_Syntax_Util.lcomp_of_comp c)
in FStar_Util.Inr (uu____3382))
in (value_check_expected_typ env1 top uu____3377 FStar_TypeChecker_Env.trivial_guard))
in (match (uu____3370) with
| (t1, lc, g) -> begin
(

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((t1), (FStar_Syntax_Syntax.Meta_monadic_lift (((FStar_Parser_Const.effect_PURE_lid), (FStar_Parser_Const.effect_TAC_lid), (FStar_Syntax_Syntax.t_term))))))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in ((t2), (lc), (g)))
end)))
end))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_lazy ({FStar_Syntax_Syntax.blob = uu____3399; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding (uu____3400); FStar_Syntax_Syntax.ltyp = uu____3401; FStar_Syntax_Syntax.rng = uu____3402}) -> begin
(

let uu____3413 = (FStar_Syntax_Util.unlazy top)
in (tc_term env1 uu____3413))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(value_check_expected_typ env1 top (FStar_Util.Inl (i.FStar_Syntax_Syntax.ltyp)) FStar_TypeChecker_Env.trivial_guard)
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let uu____3420 = (tc_tot_or_gtot_term env1 e1)
in (match (uu____3420) with
| (e2, c, g) -> begin
(

let g1 = (

let uu___362_3437 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___362_3437.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___362_3437.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___362_3437.FStar_TypeChecker_Env.implicits})
in (

let uu____3438 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((uu____3438), (c), (g1))))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let uu____3459 = (FStar_Syntax_Util.type_u ())
in (match (uu____3459) with
| (t, u) -> begin
(

let uu____3472 = (tc_check_tot_or_gtot_term env1 e1 t)
in (match (uu____3472) with
| (e2, c, g) -> begin
(

let uu____3488 = (

let uu____3505 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____3505) with
| (env2, uu____3529) -> begin
(tc_smt_pats env2 pats)
end))
in (match (uu____3488) with
| (pats1, g') -> begin
(

let g'1 = (

let uu___363_3567 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = uu___363_3567.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___363_3567.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu___363_3567.FStar_TypeChecker_Env.implicits})
in (

let uu____3568 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_pattern (pats1))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____3571 = (FStar_TypeChecker_Env.conj_guard g g'1)
in ((uu____3568), (c), (uu____3571)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(

let uu____3577 = (

let uu____3578 = (FStar_Syntax_Subst.compress e1)
in uu____3578.FStar_Syntax_Syntax.n)
in (match (uu____3577) with
| FStar_Syntax_Syntax.Tm_let ((uu____3587, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = uu____3589; FStar_Syntax_Syntax.lbtyp = uu____3590; FStar_Syntax_Syntax.lbeff = uu____3591; FStar_Syntax_Syntax.lbdef = e11; FStar_Syntax_Syntax.lbattrs = uu____3593; FStar_Syntax_Syntax.lbpos = uu____3594})::[]), e2) -> begin
(

let uu____3622 = (

let uu____3629 = (FStar_TypeChecker_Env.set_expected_typ env1 FStar_Syntax_Syntax.t_unit)
in (tc_term uu____3629 e11))
in (match (uu____3622) with
| (e12, c1, g1) -> begin
(

let uu____3639 = (tc_term env1 e2)
in (match (uu____3639) with
| (e21, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.maybe_return_e2_and_bind e12.FStar_Syntax_Syntax.pos env1 (FStar_Pervasives_Native.Some (e12)) c1 e21 ((FStar_Pervasives_Native.None), (c2)))
in (

let e13 = (FStar_TypeChecker_Util.maybe_lift env1 e12 c1.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let e22 = (FStar_TypeChecker_Util.maybe_lift env1 e21 c2.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.res_typ)
in (

let e3 = (

let uu____3663 = (

let uu____3670 = (

let uu____3671 = (

let uu____3684 = (

let uu____3691 = (

let uu____3694 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_Syntax_Syntax.t_unit), (e13), (e13.FStar_Syntax_Syntax.pos)))
in (uu____3694)::[])
in ((false), (uu____3691)))
in ((uu____3684), (e22)))
in FStar_Syntax_Syntax.Tm_let (uu____3671))
in (FStar_Syntax_Syntax.mk uu____3670))
in (uu____3663 FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos))
in (

let e4 = (FStar_TypeChecker_Util.maybe_monadic env1 e3 c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let e5 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e4), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____3716 = (FStar_TypeChecker_Env.conj_guard g1 g2)
in ((e5), (c), (uu____3716)))))))))
end))
end))
end
| uu____3717 -> begin
(

let uu____3718 = (tc_term env1 e1)
in (match (uu____3718) with
| (e2, c, g) -> begin
(

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((e3), (c), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic (uu____3740)) -> begin
(tc_term env1 e1)
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic_lift (uu____3752)) -> begin
(tc_term env1 e1)
end
| FStar_Syntax_Syntax.Tm_meta (e1, m) -> begin
(

let uu____3771 = (tc_term env1 e1)
in (match (uu____3771) with
| (e2, c, g) -> begin
(

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (m)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((e3), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, (FStar_Util.Inr (expected_c), topt), uu____3795) -> begin
(

let uu____3842 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____3842) with
| (env0, uu____3856) -> begin
(

let uu____3861 = (tc_comp env0 expected_c)
in (match (uu____3861) with
| (expected_c1, uu____3875, g) -> begin
(

let uu____3877 = (

let uu____3884 = (FStar_All.pipe_right (FStar_Syntax_Util.comp_result expected_c1) (FStar_TypeChecker_Env.set_expected_typ env0))
in (tc_term uu____3884 e1))
in (match (uu____3877) with
| (e2, c', g') -> begin
(

let uu____3894 = (

let uu____3901 = (

let uu____3906 = (FStar_Syntax_Syntax.lcomp_comp c')
in ((e2), (uu____3906)))
in (check_expected_effect env0 (FStar_Pervasives_Native.Some (expected_c1)) uu____3901))
in (match (uu____3894) with
| (e3, expected_c2, g'') -> begin
(

let uu____3916 = (tc_tactic_opt env0 topt)
in (match (uu____3916) with
| (topt1, gtac) -> begin
(

let e4 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e3), (((FStar_Util.Inr (expected_c2)), (topt1))), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_effect_name expected_c2)))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let lc = (FStar_Syntax_Util.lcomp_of_comp expected_c2)
in (

let f = (

let uu____3976 = (FStar_TypeChecker_Env.conj_guard g' g'')
in (FStar_TypeChecker_Env.conj_guard g uu____3976))
in (

let uu____3977 = (comp_check_expected_typ env1 e4 lc)
in (match (uu____3977) with
| (e5, c, f2) -> begin
(

let final_guard = (

let uu____3994 = (FStar_TypeChecker_Env.conj_guard f f2)
in (wrap_guard_with_tactic_opt topt1 uu____3994))
in (

let uu____3995 = (FStar_TypeChecker_Env.conj_guard final_guard gtac)
in ((e5), (c), (uu____3995))))
end)))))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e1, (FStar_Util.Inl (t), topt), uu____3999) -> begin
(

let uu____4046 = (FStar_Syntax_Util.type_u ())
in (match (uu____4046) with
| (k, u) -> begin
(

let uu____4059 = (tc_check_tot_or_gtot_term env1 t k)
in (match (uu____4059) with
| (t1, uu____4073, f) -> begin
(

let uu____4075 = (tc_tactic_opt env1 topt)
in (match (uu____4075) with
| (topt1, gtac) -> begin
(

let uu____4094 = (

let uu____4101 = (FStar_TypeChecker_Env.set_expected_typ env1 t1)
in (tc_term uu____4101 e1))
in (match (uu____4094) with
| (e2, c, g) -> begin
(

let uu____4111 = (

let uu____4116 = (FStar_TypeChecker_Env.set_range env1 t1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (FStar_Pervasives_Native.Some ((fun uu____4121 -> (FStar_Util.return_all FStar_TypeChecker_Err.ill_kinded_type)))) uu____4116 e2 c f))
in (match (uu____4111) with
| (c1, f1) -> begin
(

let uu____4130 = (

let uu____4137 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e2), (((FStar_Util.Inl (t1)), (topt1))), (FStar_Pervasives_Native.Some (c1.FStar_Syntax_Syntax.eff_name))))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env1 uu____4137 c1))
in (match (uu____4130) with
| (e3, c2, f2) -> begin
(

let final_guard = (

let uu____4184 = (FStar_TypeChecker_Env.conj_guard g f2)
in (FStar_TypeChecker_Env.conj_guard f1 uu____4184))
in (

let final_guard1 = (wrap_guard_with_tactic_opt topt1 final_guard)
in (

let uu____4186 = (FStar_TypeChecker_Env.conj_guard final_guard1 gtac)
in ((e3), (c2), (uu____4186)))))
end))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____4187; FStar_Syntax_Syntax.vars = uu____4188}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____4267 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____4267) with
| (unary_op1, uu____4291) -> begin
(

let head1 = (

let uu____4319 = (FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op1), ((a)::[])))) FStar_Pervasives_Native.None uu____4319))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____4367; FStar_Syntax_Syntax.vars = uu____4368}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____4447 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____4447) with
| (unary_op1, uu____4471) -> begin
(

let head1 = (

let uu____4499 = (FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op1), ((a)::[])))) FStar_Pervasives_Native.None uu____4499))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____4547)); FStar_Syntax_Syntax.pos = uu____4548; FStar_Syntax_Syntax.vars = uu____4549}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____4628 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____4628) with
| (unary_op1, uu____4652) -> begin
(

let head1 = (

let uu____4680 = (FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op1), ((a)::[])))) FStar_Pervasives_Native.None uu____4680))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____4728; FStar_Syntax_Syntax.vars = uu____4729}, (a1)::(a2)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____4825 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____4825) with
| (unary_op1, uu____4849) -> begin
(

let head1 = (

let uu____4877 = (FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op1), ((a1)::(a2)::[])))) FStar_Pervasives_Native.None uu____4877))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (tc_term env1 t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____4933; FStar_Syntax_Syntax.vars = uu____4934}, ((e1, FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____4972 = (

let uu____4979 = (

let uu____4980 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____4980))
in (tc_term uu____4979 e1))
in (match (uu____4972) with
| (e2, c, g) -> begin
(

let uu____5004 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____5004) with
| (head1, uu____5028) -> begin
(

let uu____5053 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), ((((e2), (FStar_Pervasives_Native.None)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____5086 = (

let uu____5087 = (

let uu____5088 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid)
in (FStar_Syntax_Syntax.mk_Total uu____5088))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____5087))
in ((uu____5053), (uu____5086), (g))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____5089; FStar_Syntax_Syntax.vars = uu____5090}, ((t, FStar_Pervasives_Native.None))::((r, FStar_Pervasives_Native.None))::[]) -> begin
(

let uu____5143 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____5143) with
| (head1, uu____5167) -> begin
(

let env' = (

let uu____5193 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid)
in (FStar_TypeChecker_Env.set_expected_typ env1 uu____5193))
in (

let uu____5194 = (tc_term env' r)
in (match (uu____5194) with
| (er, uu____5208, gr) -> begin
(

let uu____5210 = (tc_term env1 t)
in (match (uu____5210) with
| (t1, tt, gt1) -> begin
(

let g = (FStar_TypeChecker_Env.conj_guard gr gt1)
in (

let uu____5227 = (

let uu____5228 = (

let uu____5233 = (

let uu____5234 = (FStar_Syntax_Syntax.as_arg t1)
in (

let uu____5243 = (

let uu____5254 = (FStar_Syntax_Syntax.as_arg r)
in (uu____5254)::[])
in (uu____5234)::uu____5243))
in (FStar_Syntax_Syntax.mk_Tm_app head1 uu____5233))
in (uu____5228 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in ((uu____5227), (tt), (g))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____5289; FStar_Syntax_Syntax.vars = uu____5290}, uu____5291) -> begin
(

let uu____5316 = (

let uu____5321 = (

let uu____5322 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Ill-applied constant %s" uu____5322))
in ((FStar_Errors.Fatal_IllAppliedConstant), (uu____5321)))
in (FStar_Errors.raise_error uu____5316 e.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____5329; FStar_Syntax_Syntax.vars = uu____5330}, uu____5331) -> begin
(

let uu____5356 = (

let uu____5361 = (

let uu____5362 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Ill-applied constant %s" uu____5362))
in ((FStar_Errors.Fatal_IllAppliedConstant), (uu____5361)))
in (FStar_Errors.raise_error uu____5356 e.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____5369; FStar_Syntax_Syntax.vars = uu____5370}, ((e1, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify), ("Qualifier on argument to reify is irrelevant and will be ignored")))
end
| uu____5412 -> begin
()
end);
(

let uu____5413 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____5413) with
| (env0, uu____5427) -> begin
(

let uu____5432 = (tc_term env0 e1)
in (match (uu____5432) with
| (e2, c, g) -> begin
(

let uu____5448 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____5448) with
| (reify_op, uu____5472) -> begin
(

let u_c = (

let uu____5498 = (tc_term env0 c.FStar_Syntax_Syntax.res_typ)
in (match (uu____5498) with
| (uu____5505, c', uu____5507) -> begin
(

let uu____5508 = (

let uu____5509 = (FStar_Syntax_Subst.compress c'.FStar_Syntax_Syntax.res_typ)
in uu____5509.FStar_Syntax_Syntax.n)
in (match (uu____5508) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____5513 -> begin
(

let uu____5514 = (FStar_Syntax_Util.type_u ())
in (match (uu____5514) with
| (t, u) -> begin
(

let g_opt = (FStar_TypeChecker_Rel.try_teq true env1 c'.FStar_Syntax_Syntax.res_typ t)
in ((match (g_opt) with
| FStar_Pervasives_Native.Some (g') -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g')
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5526 = (

let uu____5527 = (FStar_Syntax_Print.lcomp_to_string c')
in (

let uu____5528 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (

let uu____5529 = (FStar_Syntax_Print.term_to_string c'.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format3 "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s" uu____5527 uu____5528 uu____5529))))
in (failwith uu____5526))
end);
u;
))
end))
end))
end))
in (

let ef = (

let uu____5531 = (FStar_Syntax_Syntax.lcomp_comp c)
in (FStar_Syntax_Util.comp_effect_name uu____5531))
in ((

let uu____5535 = (

let uu____5536 = (FStar_TypeChecker_Env.is_user_reifiable_effect env1 ef)
in (not (uu____5536)))
in (match (uu____5535) with
| true -> begin
(

let uu____5537 = (

let uu____5542 = (FStar_Util.format1 "Effect %s cannot be reified" ef.FStar_Ident.str)
in ((FStar_Errors.Fatal_EffectCannotBeReified), (uu____5542)))
in (FStar_Errors.raise_error uu____5537 e2.FStar_Syntax_Syntax.pos))
end
| uu____5543 -> begin
()
end));
(

let repr = (

let uu____5545 = (FStar_Syntax_Syntax.lcomp_comp c)
in (FStar_TypeChecker_Env.reify_comp env1 uu____5545 u_c))
in (

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e2), (aqual)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let c1 = (

let uu____5582 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right uu____5582 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____5583 = (comp_check_expected_typ env1 e3 c1)
in (match (uu____5583) with
| (e4, c2, g') -> begin
(

let uu____5599 = (FStar_TypeChecker_Env.conj_guard g g')
in ((e4), (c2), (uu____5599)))
end)))));
)))
end))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.pos = uu____5601; FStar_Syntax_Syntax.vars = uu____5602}, ((e1, aqual))::[]) -> begin
((match ((FStar_Option.isSome aqual)) with
| true -> begin
(FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect), ("Qualifier on argument to reflect is irrelevant and will be ignored")))
end
| uu____5644 -> begin
()
end);
(

let uu____5646 = (

let uu____5647 = (FStar_TypeChecker_Env.is_user_reifiable_effect env1 l)
in (not (uu____5647)))
in (match (uu____5646) with
| true -> begin
(

let uu____5648 = (

let uu____5653 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((FStar_Errors.Fatal_EffectCannotBeReified), (uu____5653)))
in (FStar_Errors.raise_error uu____5648 e1.FStar_Syntax_Syntax.pos))
end
| uu____5654 -> begin
()
end));
(

let uu____5655 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____5655) with
| (reflect_op, uu____5679) -> begin
(

let uu____5704 = (FStar_TypeChecker_Env.effect_decl_opt env1 l)
in (match (uu____5704) with
| FStar_Pervasives_Native.None -> begin
(failwith "internal error: user reifiable effect has no decl?")
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____5743 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____5743) with
| (env_no_ex, topt) -> begin
(

let uu____5762 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env1 ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (

let uu____5782 = (

let uu____5789 = (

let uu____5790 = (

let uu____5807 = (

let uu____5818 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____5827 = (

let uu____5838 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (uu____5838)::[])
in (uu____5818)::uu____5827))
in ((repr), (uu____5807)))
in FStar_Syntax_Syntax.Tm_app (uu____5790))
in (FStar_Syntax_Syntax.mk uu____5789))
in (uu____5782 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in (

let uu____5886 = (

let uu____5893 = (

let uu____5894 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_right uu____5894 FStar_Pervasives_Native.fst))
in (tc_tot_or_gtot_term uu____5893 t))
in (match (uu____5886) with
| (t1, uu____5920, g) -> begin
(

let uu____5922 = (

let uu____5923 = (FStar_Syntax_Subst.compress t1)
in uu____5923.FStar_Syntax_Syntax.n)
in (match (uu____5922) with
| FStar_Syntax_Syntax.Tm_app (uu____5936, ((res, uu____5938))::((wp, uu____5940))::[]) -> begin
((t1), (res), (wp), (g))
end
| uu____5997 -> begin
(failwith "Impossible")
end))
end)))))
in (match (uu____5762) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let uu____6022 = (

let uu____6029 = (tc_tot_or_gtot_term env_no_ex e1)
in (match (uu____6029) with
| (e2, c, g) -> begin
((

let uu____6046 = (

let uu____6047 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation uu____6047))
in (match (uu____6046) with
| true -> begin
(FStar_TypeChecker_Err.add_errors env1 ((((FStar_Errors.Error_UnexpectedGTotComputation), ("Expected Tot, got a GTot computation"), (e2.FStar_Syntax_Syntax.pos)))::[]))
end
| uu____6060 -> begin
()
end));
(

let uu____6061 = (FStar_TypeChecker_Rel.try_teq true env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)
in (match (uu____6061) with
| FStar_Pervasives_Native.None -> begin
((

let uu____6071 = (

let uu____6080 = (

let uu____6087 = (

let uu____6088 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____6089 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" uu____6088 uu____6089)))
in ((FStar_Errors.Error_UnexpectedInstance), (uu____6087), (e2.FStar_Syntax_Syntax.pos)))
in (uu____6080)::[])
in (FStar_TypeChecker_Err.add_errors env1 uu____6071));
(

let uu____6102 = (FStar_TypeChecker_Env.conj_guard g g0)
in ((e2), (uu____6102)));
)
end
| FStar_Pervasives_Native.Some (g') -> begin
(

let uu____6106 = (

let uu____6107 = (FStar_TypeChecker_Env.conj_guard g g0)
in (FStar_TypeChecker_Env.conj_guard g' uu____6107))
in ((e2), (uu____6106)))
end));
)
end))
in (match (uu____6022) with
| (e2, g) -> begin
(

let c = (

let uu____6123 = (

let uu____6124 = (

let uu____6125 = (

let uu____6126 = (env1.FStar_TypeChecker_Env.universe_of env1 res_typ)
in (uu____6126)::[])
in (

let uu____6127 = (

let uu____6138 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____6138)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____6125; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = uu____6127; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp uu____6124))
in (FStar_All.pipe_right uu____6123 FStar_Syntax_Util.lcomp_of_comp))
in (

let e3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e2), (aqual)))::[])))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let uu____6198 = (comp_check_expected_typ env1 e3 c)
in (match (uu____6198) with
| (e4, c1, g') -> begin
(

let e5 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e4), (FStar_Syntax_Syntax.Meta_monadic (((c1.FStar_Syntax_Syntax.eff_name), (c1.FStar_Syntax_Syntax.res_typ))))))) FStar_Pervasives_Native.None e4.FStar_Syntax_Syntax.pos)
in (

let uu____6221 = (FStar_TypeChecker_Env.conj_guard g' g)
in ((e5), (c1), (uu____6221))))
end))))
end))
end))
end))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app (head1, ((tau, FStar_Pervasives_Native.None))::[]) when ((FStar_Syntax_Util.is_synth_by_tactic head1) && (not (env1.FStar_TypeChecker_Env.phase1))) -> begin
(

let uu____6260 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____6260) with
| (head2, args) -> begin
(tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, ((uu____6310, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____6311))))::((tau, FStar_Pervasives_Native.None))::[]) when ((FStar_Syntax_Util.is_synth_by_tactic head1) && (not (env1.FStar_TypeChecker_Env.phase1))) -> begin
(

let uu____6363 = (FStar_Syntax_Util.head_and_args top)
in (match (uu____6363) with
| (head2, args) -> begin
(tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) when ((FStar_Syntax_Util.is_synth_by_tactic head1) && (not (env1.FStar_TypeChecker_Env.phase1))) -> begin
(

let uu____6438 = (match (args) with
| ((tau, FStar_Pervasives_Native.None))::rest -> begin
(((((tau), (FStar_Pervasives_Native.None)))::[]), (rest))
end
| ((a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (b))))::((tau, FStar_Pervasives_Native.None))::rest -> begin
(((((a), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (b)))))::(((tau), (FStar_Pervasives_Native.None)))::[]), (rest))
end
| uu____6647 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_SynthByTacticError), ("synth_by_tactic: bad application")) top.FStar_Syntax_Syntax.pos)
end)
in (match (uu____6438) with
| (args1, args2) -> begin
(

let t1 = (FStar_Syntax_Util.mk_app head1 args1)
in (

let t2 = (FStar_Syntax_Util.mk_app t1 args2)
in (tc_term env1 t2)))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let env0 = env1
in (

let env2 = (

let uu____6764 = (

let uu____6765 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (FStar_All.pipe_right uu____6765 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____6764 instantiate_both))
in ((

let uu____6781 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____6781) with
| true -> begin
(

let uu____6782 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____6783 = (FStar_Syntax_Print.term_to_string top)
in (

let uu____6784 = (

let uu____6785 = (FStar_TypeChecker_Env.expected_typ env0)
in (FStar_All.pipe_right uu____6785 (fun uu___350_6791 -> (match (uu___350_6791) with
| FStar_Pervasives_Native.None -> begin
"none"
end
| FStar_Pervasives_Native.Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end))))
in (FStar_Util.print3 "(%s) Checking app %s, expected type is %s\n" uu____6782 uu____6783 uu____6784))))
end
| uu____6795 -> begin
()
end));
(

let uu____6796 = (tc_term (no_inst env2) head1)
in (match (uu____6796) with
| (head2, chead, g_head) -> begin
(

let uu____6812 = (

let uu____6819 = (((not (env2.FStar_TypeChecker_Env.lax)) && (

let uu____6821 = (FStar_Options.lax ())
in (not (uu____6821)))) && (FStar_TypeChecker_Util.short_circuit_head head2))
in (match (uu____6819) with
| true -> begin
(

let uu____6828 = (

let uu____6835 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env2 head2 chead g_head args uu____6835))
in (match (uu____6828) with
| (e1, c, g) -> begin
((e1), (c), (g))
end))
end
| uu____6847 -> begin
(

let uu____6848 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env2 head2 chead g_head args uu____6848))
end))
in (match (uu____6812) with
| (e1, c, g) -> begin
(

let uu____6860 = (

let uu____6867 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____6867) with
| true -> begin
(

let uu____6874 = (FStar_TypeChecker_Util.maybe_instantiate env0 e1 c.FStar_Syntax_Syntax.res_typ)
in (match (uu____6874) with
| (e2, res_typ, implicits) -> begin
(

let uu____6890 = (FStar_Syntax_Util.set_result_typ_lc c res_typ)
in ((e2), (uu____6890), (implicits)))
end))
end
| uu____6891 -> begin
((e1), (c), (FStar_TypeChecker_Env.trivial_guard))
end))
in (match (uu____6860) with
| (e2, c1, implicits) -> begin
((

let uu____6902 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Extreme)
in (match (uu____6902) with
| true -> begin
(

let uu____6903 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" uu____6903))
end
| uu____6904 -> begin
()
end));
(

let uu____6905 = (comp_check_expected_typ env0 e2 c1)
in (match (uu____6905) with
| (e3, c2, g') -> begin
(

let gres = (FStar_TypeChecker_Env.conj_guard g g')
in (

let gres1 = (FStar_TypeChecker_Env.conj_guard gres implicits)
in ((

let uu____6924 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Extreme)
in (match (uu____6924) with
| true -> begin
(

let uu____6925 = (FStar_Syntax_Print.term_to_string e3)
in (

let uu____6926 = (FStar_TypeChecker_Rel.guard_to_string env2 gres1)
in (FStar_Util.print2 "Guard from application node %s is %s\n" uu____6925 uu____6926)))
end
| uu____6927 -> begin
()
end));
((e3), (c2), (gres1));
)))
end));
)
end))
end))
end));
)))
end
| FStar_Syntax_Syntax.Tm_match (e1, eqns) -> begin
(

let uu____6966 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____6966) with
| (env11, topt) -> begin
(

let env12 = (instantiate_both env11)
in (

let uu____6986 = (tc_term env12 e1)
in (match (uu____6986) with
| (e11, c1, g1) -> begin
(

let uu____7002 = (match (topt) with
| FStar_Pervasives_Native.Some (t) -> begin
((env1), (t), (g1))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____7016 = (FStar_Syntax_Util.type_u ())
in (match (uu____7016) with
| (k, uu____7028) -> begin
(

let uu____7029 = (FStar_TypeChecker_Util.new_implicit_var "match result" e.FStar_Syntax_Syntax.pos env1 k)
in (match (uu____7029) with
| (res_t, uu____7049, g) -> begin
(

let uu____7063 = (FStar_TypeChecker_Env.set_expected_typ env1 res_t)
in (

let uu____7064 = (FStar_TypeChecker_Env.conj_guard g1 g)
in ((uu____7063), (res_t), (uu____7064))))
end))
end))
end)
in (match (uu____7002) with
| (env_branches, res_t, g11) -> begin
((

let uu____7075 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Extreme)
in (match (uu____7075) with
| true -> begin
(

let uu____7076 = (FStar_Syntax_Print.term_to_string res_t)
in (FStar_Util.print1 "Tm_match: expected type of branches is %s\n" uu____7076))
end
| uu____7077 -> begin
()
end));
(

let guard_x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (e11.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let uu____7197 = (

let uu____7202 = (FStar_List.fold_right (fun uu____7281 uu____7282 -> (match (((uu____7281), (uu____7282))) with
| ((branch1, f, eff_label, cflags, c, g), (caccum, gaccum)) -> begin
(

let uu____7516 = (FStar_TypeChecker_Env.conj_guard g gaccum)
in (((((f), (eff_label), (cflags), (c)))::caccum), (uu____7516)))
end)) t_eqns (([]), (FStar_TypeChecker_Env.trivial_guard)))
in (match (uu____7202) with
| (cases, g) -> begin
(

let uu____7614 = (FStar_TypeChecker_Util.bind_cases env1 res_t cases)
in ((uu____7614), (g)))
end))
in (match (uu____7197) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e11.FStar_Syntax_Syntax.pos env1 (FStar_Pervasives_Native.Some (e11)) c1 ((FStar_Pervasives_Native.Some (guard_x)), (c_branches)))
in (

let e2 = (

let mk_match = (fun scrutinee -> (

let branches = (FStar_All.pipe_right t_eqns (FStar_List.map (fun uu____7754 -> (match (uu____7754) with
| ((pat, wopt, br), uu____7798, eff_label, uu____7800, uu____7801, uu____7802) -> begin
(

let uu____7837 = (FStar_TypeChecker_Util.maybe_lift env1 br eff_label cres.FStar_Syntax_Syntax.eff_name res_t)
in ((pat), (wopt), (uu____7837)))
end))))
in (

let e2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let e3 = (FStar_TypeChecker_Util.maybe_monadic env1 e2 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e3), (((FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.Some (cres.FStar_Syntax_Syntax.eff_name))))) FStar_Pervasives_Native.None e3.FStar_Syntax_Syntax.pos)))))
in (

let uu____7904 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env1 c1.FStar_Syntax_Syntax.eff_name)
in (match (uu____7904) with
| true -> begin
(mk_match e11)
end
| uu____7905 -> begin
(

let e_match = (

let uu____7909 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match uu____7909))
in (

let lb = (

let uu____7913 = (FStar_TypeChecker_Env.norm_eff_name env1 c1.FStar_Syntax_Syntax.eff_name)
in (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (guard_x)) [] c1.FStar_Syntax_Syntax.res_typ uu____7913 e11 [] e11.FStar_Syntax_Syntax.pos))
in (

let e2 = (

let uu____7919 = (

let uu____7926 = (

let uu____7927 = (

let uu____7940 = (

let uu____7943 = (

let uu____7944 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (uu____7944)::[])
in (FStar_Syntax_Subst.close uu____7943 e_match))
in ((((false), ((lb)::[]))), (uu____7940)))
in FStar_Syntax_Syntax.Tm_let (uu____7927))
in (FStar_Syntax_Syntax.mk uu____7926))
in (uu____7919 FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Util.maybe_monadic env1 e2 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ))))
end)))
in ((

let uu____7977 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Extreme)
in (match (uu____7977) with
| true -> begin
(

let uu____7978 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____7979 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print2 "(%s) comp type = %s\n" uu____7978 uu____7979)))
end
| uu____7980 -> begin
()
end));
(

let uu____7981 = (FStar_TypeChecker_Env.conj_guard g11 g_branches)
in ((e2), (cres), (uu____7981)));
)))
end))));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____7982); FStar_Syntax_Syntax.lbunivs = uu____7983; FStar_Syntax_Syntax.lbtyp = uu____7984; FStar_Syntax_Syntax.lbeff = uu____7985; FStar_Syntax_Syntax.lbdef = uu____7986; FStar_Syntax_Syntax.lbattrs = uu____7987; FStar_Syntax_Syntax.lbpos = uu____7988})::[]), uu____7989) -> begin
(check_top_level_let env1 top)
end
| FStar_Syntax_Syntax.Tm_let ((false, uu____8012), uu____8013) -> begin
(check_inner_let env1 top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____8028); FStar_Syntax_Syntax.lbunivs = uu____8029; FStar_Syntax_Syntax.lbtyp = uu____8030; FStar_Syntax_Syntax.lbeff = uu____8031; FStar_Syntax_Syntax.lbdef = uu____8032; FStar_Syntax_Syntax.lbattrs = uu____8033; FStar_Syntax_Syntax.lbpos = uu____8034})::uu____8035), uu____8036) -> begin
(check_top_level_let_rec env1 top)
end
| FStar_Syntax_Syntax.Tm_let ((true, uu____8061), uu____8062) -> begin
(check_inner_let_rec env1 top)
end);
))))
and tc_synth : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun head1 env args rng -> (

let uu____8093 = (match (args) with
| ((tau, FStar_Pervasives_Native.None))::[] -> begin
((tau), (FStar_Pervasives_Native.None))
end
| ((a, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____8132))))::((tau, FStar_Pervasives_Native.None))::[] -> begin
((tau), (FStar_Pervasives_Native.Some (a)))
end
| uu____8172 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_SynthByTacticError), ("synth_by_tactic: bad application")) rng)
end)
in (match (uu____8093) with
| (tau, atyp) -> begin
(

let typ = (match (atyp) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8203 = (FStar_TypeChecker_Env.expected_typ env)
in (match (uu____8203) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8207 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_SynthByTacticError), ("synth_by_tactic: need a type annotation when no expected type is present")) uu____8207))
end))
end)
in (

let uu____8208 = (

let uu____8215 = (

let uu____8216 = (

let uu____8217 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8217))
in (FStar_TypeChecker_Env.set_expected_typ env uu____8216))
in (tc_term uu____8215 typ))
in (match (uu____8208) with
| (typ1, uu____8233, g1) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g1);
(

let uu____8236 = (tc_tactic env tau)
in (match (uu____8236) with
| (tau1, uu____8250, g2) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g2);
(

let t = (env.FStar_TypeChecker_Env.synth_hook env typ1 (

let uu___364_8255 = tau1
in {FStar_Syntax_Syntax.n = uu___364_8255.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = rng; FStar_Syntax_Syntax.vars = uu___364_8255.FStar_Syntax_Syntax.vars}))
in ((

let uu____8257 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Tac")))
in (match (uu____8257) with
| true -> begin
(

let uu____8258 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Got %s\n" uu____8258))
end
| uu____8259 -> begin
()
end));
(FStar_TypeChecker_Util.check_uvars tau1.FStar_Syntax_Syntax.pos t);
(

let uu____8261 = (

let uu____8262 = (FStar_Syntax_Syntax.mk_Total typ1)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____8262))
in ((t), (uu____8261), (FStar_TypeChecker_Env.trivial_guard)));
));
)
end));
)
end)))
end)))
and tc_tactic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env tau -> (

let env1 = (

let uu___365_8266 = env
in {FStar_TypeChecker_Env.solver = uu___365_8266.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___365_8266.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___365_8266.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___365_8266.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___365_8266.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___365_8266.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___365_8266.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___365_8266.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___365_8266.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___365_8266.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___365_8266.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___365_8266.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___365_8266.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___365_8266.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___365_8266.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___365_8266.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___365_8266.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___365_8266.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___365_8266.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___365_8266.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___365_8266.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___365_8266.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___365_8266.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = true; FStar_TypeChecker_Env.nosynth = uu___365_8266.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___365_8266.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___365_8266.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___365_8266.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___365_8266.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___365_8266.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___365_8266.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___365_8266.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___365_8266.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___365_8266.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___365_8266.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___365_8266.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___365_8266.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___365_8266.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___365_8266.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___365_8266.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___365_8266.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___365_8266.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___365_8266.FStar_TypeChecker_Env.nbe})
in (tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tactic_unit)))
and tc_tactic_opt : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_TypeChecker_Env.guard_t) = (fun env topt -> (match (topt) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_TypeChecker_Env.trivial_guard))
end
| FStar_Pervasives_Native.Some (tactic) -> begin
(

let uu____8288 = (tc_tactic env tactic)
in (match (uu____8288) with
| (tactic1, uu____8302, g) -> begin
((FStar_Pervasives_Native.Some (tactic1)), (g))
end))
end))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env1 v1 dc e1 t0 -> (

let uu____8354 = (FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0)
in (match (uu____8354) with
| (e2, t, implicits) -> begin
(

let tc = (

let uu____8375 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____8375) with
| true -> begin
FStar_Util.Inl (t)
end
| uu____8380 -> begin
(

let uu____8381 = (

let uu____8382 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____8382))
in FStar_Util.Inr (uu____8381))
end))
in (

let is_data_ctor = (fun uu___351_8390 -> (match (uu___351_8390) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor) -> begin
true
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____8393)) -> begin
true
end
| uu____8400 -> begin
false
end))
in (

let uu____8403 = ((is_data_ctor dc) && (

let uu____8405 = (FStar_TypeChecker_Env.is_datacon env1 v1.FStar_Syntax_Syntax.v)
in (not (uu____8405))))
in (match (uu____8403) with
| true -> begin
(

let uu____8412 = (

let uu____8417 = (FStar_Util.format1 "Expected a data constructor; got %s" v1.FStar_Syntax_Syntax.v.FStar_Ident.str)
in ((FStar_Errors.Fatal_MissingDataConstructor), (uu____8417)))
in (

let uu____8418 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error uu____8412 uu____8418)))
end
| uu____8425 -> begin
(value_check_expected_typ env1 e2 tc implicits)
end))))
end)))
in (

let env1 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____8435 = (

let uu____8436 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" uu____8436))
in (failwith uu____8435))
end
| FStar_Syntax_Syntax.Tm_uvar (u, s) -> begin
(

let uu____8461 = (

let uu____8466 = (FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ)
in FStar_Util.Inl (uu____8466))
in (value_check_expected_typ env1 e uu____8461 FStar_TypeChecker_Env.trivial_guard))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____8468 = (

let uu____8481 = (FStar_TypeChecker_Env.expected_typ env1)
in (match (uu____8481) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8496 = (FStar_Syntax_Util.type_u ())
in (match (uu____8496) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env1 k)
end))
end
| FStar_Pervasives_Native.Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Env.trivial_guard))
end))
in (match (uu____8468) with
| (t, uu____8533, g0) -> begin
(

let uu____8547 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env1 t)
in (match (uu____8547) with
| (e1, uu____8567, g1) -> begin
(

let uu____8581 = (

let uu____8582 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right uu____8582 FStar_Syntax_Util.lcomp_of_comp))
in (

let uu____8583 = (FStar_TypeChecker_Env.conj_guard g0 g1)
in ((e1), (uu____8581), (uu____8583))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____8585 = (match (env1.FStar_TypeChecker_Env.use_bv_sorts) with
| true -> begin
(

let uu____8594 = (FStar_Syntax_Syntax.range_of_bv x)
in ((x.FStar_Syntax_Syntax.sort), (uu____8594)))
end
| uu____8595 -> begin
(FStar_TypeChecker_Env.lookup_bv env1 x)
end)
in (match (uu____8585) with
| (t, rng) -> begin
(

let x1 = (FStar_Syntax_Syntax.set_range_of_bv (

let uu___366_8607 = x
in {FStar_Syntax_Syntax.ppname = uu___366_8607.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___366_8607.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}) rng)
in ((FStar_TypeChecker_Env.insert_bv_info env1 x1 t);
(

let e1 = (FStar_Syntax_Syntax.bv_to_name x1)
in (

let uu____8610 = (FStar_TypeChecker_Util.maybe_instantiate env1 e1 t)
in (match (uu____8610) with
| (e2, t1, implicits) -> begin
(

let tc = (

let uu____8631 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____8631) with
| true -> begin
FStar_Util.Inl (t1)
end
| uu____8636 -> begin
(

let uu____8637 = (

let uu____8638 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____8638))
in FStar_Util.Inr (uu____8637))
end))
in (value_check_expected_typ env1 e2 tc implicits))
end)));
))
end))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____8640; FStar_Syntax_Syntax.vars = uu____8641}, uu____8642) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) && (not (env1.FStar_TypeChecker_Env.phase1))) -> begin
(

let uu____8647 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic), ("Badly instantiated synth_by_tactic")) uu____8647))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) && (not (env1.FStar_TypeChecker_Env.phase1))) -> begin
(

let uu____8655 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic), ("Badly instantiated synth_by_tactic")) uu____8655))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____8663; FStar_Syntax_Syntax.vars = uu____8664}, us) -> begin
(

let us1 = (FStar_List.map (tc_universe env1) us)
in (

let uu____8673 = (FStar_TypeChecker_Env.lookup_lid env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____8673) with
| ((us', t), range) -> begin
((match ((Prims.op_disEquality (FStar_List.length us1) (FStar_List.length us'))) with
| true -> begin
(

let uu____8696 = (

let uu____8701 = (

let uu____8702 = (FStar_Syntax_Print.fv_to_string fv)
in (

let uu____8703 = (FStar_Util.string_of_int (FStar_List.length us1))
in (

let uu____8704 = (FStar_Util.string_of_int (FStar_List.length us'))
in (FStar_Util.format3 "Unexpected number of universe instantiations for \"%s\" (%s vs %s)" uu____8702 uu____8703 uu____8704))))
in ((FStar_Errors.Fatal_UnexpectedNumberOfUniverse), (uu____8701)))
in (

let uu____8705 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error uu____8696 uu____8705)))
end
| uu____8706 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____8721 -> begin
(failwith "Impossible")
end)) us' us1)
end);
(

let fv' = (FStar_Syntax_Syntax.set_range_of_fv fv range)
in ((FStar_TypeChecker_Env.insert_fv_info env1 fv' t);
(

let e1 = (

let uu____8725 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____8725 us1))
in (check_instantiated_fvar env1 fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e1 t));
));
)
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____8727 = (FStar_TypeChecker_Env.lookup_lid env1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____8727) with
| ((us, t), range) -> begin
((

let uu____8750 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Range")))
in (match (uu____8750) with
| true -> begin
(

let uu____8751 = (

let uu____8752 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Syntax_Print.lid_to_string uu____8752))
in (

let uu____8753 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (

let uu____8754 = (FStar_Range.string_of_range range)
in (

let uu____8755 = (FStar_Range.string_of_use_range range)
in (

let uu____8756 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print5 "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s" uu____8751 uu____8753 uu____8754 uu____8755 uu____8756))))))
end
| uu____8757 -> begin
()
end));
(

let fv' = (FStar_Syntax_Syntax.set_range_of_fv fv range)
in ((FStar_TypeChecker_Env.insert_fv_info env1 fv' t);
(

let e1 = (

let uu____8761 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____8761 us))
in (check_instantiated_fvar env1 fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e1 t));
));
)
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let t = (tc_constant env1 top.FStar_Syntax_Syntax.pos c)
in (

let e1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env1 e1 (FStar_Util.Inl (t)) FStar_TypeChecker_Env.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____8789 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____8789) with
| (bs1, c1) -> begin
(

let env0 = env1
in (

let uu____8803 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____8803) with
| (env2, uu____8817) -> begin
(

let uu____8822 = (tc_binders env2 bs1)
in (match (uu____8822) with
| (bs2, env3, g, us) -> begin
(

let uu____8841 = (tc_comp env3 c1)
in (match (uu____8841) with
| (c2, uc, f) -> begin
(

let e1 = (

let uu___367_8860 = (FStar_Syntax_Util.arrow bs2 c2)
in {FStar_Syntax_Syntax.n = uu___367_8860.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___367_8860.FStar_Syntax_Syntax.vars})
in ((check_smt_pat env3 e1 bs2 c2);
(

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let g1 = (

let uu____8871 = (FStar_TypeChecker_Env.close_guard_univs us bs2 f)
in (FStar_TypeChecker_Env.conj_guard g uu____8871))
in (

let g2 = (FStar_TypeChecker_Util.close_guard_implicits env3 bs2 g1)
in (value_check_expected_typ env0 e1 (FStar_Util.Inl (t)) g2)))));
))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u1 = (tc_universe env1 u)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u1))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let e1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u1)) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env1 e1 (FStar_Util.Inl (t)) FStar_TypeChecker_Env.trivial_guard))))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let uu____8887 = (

let uu____8892 = (

let uu____8893 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____8893)::[])
in (FStar_Syntax_Subst.open_term uu____8892 phi))
in (match (uu____8887) with
| (x1, phi1) -> begin
(

let env0 = env1
in (

let uu____8921 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____8921) with
| (env2, uu____8935) -> begin
(

let uu____8940 = (

let uu____8955 = (FStar_List.hd x1)
in (tc_binder env2 uu____8955))
in (match (uu____8940) with
| (x2, env3, f1, u) -> begin
((

let uu____8991 = (FStar_TypeChecker_Env.debug env3 FStar_Options.High)
in (match (uu____8991) with
| true -> begin
(

let uu____8992 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____8993 = (FStar_Syntax_Print.term_to_string phi1)
in (

let uu____8994 = (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst x2))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" uu____8992 uu____8993 uu____8994))))
end
| uu____8997 -> begin
()
end));
(

let uu____8998 = (FStar_Syntax_Util.type_u ())
in (match (uu____8998) with
| (t_phi, uu____9010) -> begin
(

let uu____9011 = (tc_check_tot_or_gtot_term env3 phi1 t_phi)
in (match (uu____9011) with
| (phi2, uu____9025, f2) -> begin
(

let e1 = (

let uu___368_9030 = (FStar_Syntax_Util.refine (FStar_Pervasives_Native.fst x2) phi2)
in {FStar_Syntax_Syntax.n = uu___368_9030.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___368_9030.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (

let g = (

let uu____9039 = (FStar_TypeChecker_Env.close_guard_univs ((u)::[]) ((x2)::[]) f2)
in (FStar_TypeChecker_Env.conj_guard f1 uu____9039))
in (

let g1 = (FStar_TypeChecker_Util.close_guard_implicits env3 ((x2)::[]) g)
in (value_check_expected_typ env0 e1 (FStar_Util.Inl (t)) g1)))))
end))
end));
)
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____9067) -> begin
(

let bs1 = (FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs)
in ((

let uu____9094 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____9094) with
| true -> begin
(

let uu____9095 = (FStar_Syntax_Print.term_to_string (

let uu___369_9098 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs1), (body), (FStar_Pervasives_Native.None))); FStar_Syntax_Syntax.pos = uu___369_9098.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___369_9098.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" uu____9095))
end
| uu____9111 -> begin
()
end));
(

let uu____9112 = (FStar_Syntax_Subst.open_term bs1 body)
in (match (uu____9112) with
| (bs2, body1) -> begin
(tc_abs env1 top bs2 body1)
end));
))
end
| uu____9125 -> begin
(

let uu____9126 = (

let uu____9127 = (FStar_Syntax_Print.term_to_string top)
in (

let uu____9128 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" uu____9127 uu____9128)))
in (failwith uu____9126))
end)))))
and tc_constant : FStar_TypeChecker_Env.env  ->  FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun env r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_Syntax_Syntax.t_unit
end
| FStar_Const.Const_bool (uu____9138) -> begin
FStar_Syntax_Util.t_bool
end
| FStar_Const.Const_int (uu____9139, FStar_Pervasives_Native.None) -> begin
FStar_Syntax_Syntax.t_int
end
| FStar_Const.Const_int (uu____9150, FStar_Pervasives_Native.Some (msize)) -> begin
(FStar_Syntax_Syntax.tconst (match (msize) with
| (FStar_Const.Signed, FStar_Const.Int8) -> begin
FStar_Parser_Const.int8_lid
end
| (FStar_Const.Signed, FStar_Const.Int16) -> begin
FStar_Parser_Const.int16_lid
end
| (FStar_Const.Signed, FStar_Const.Int32) -> begin
FStar_Parser_Const.int32_lid
end
| (FStar_Const.Signed, FStar_Const.Int64) -> begin
FStar_Parser_Const.int64_lid
end
| (FStar_Const.Unsigned, FStar_Const.Int8) -> begin
FStar_Parser_Const.uint8_lid
end
| (FStar_Const.Unsigned, FStar_Const.Int16) -> begin
FStar_Parser_Const.uint16_lid
end
| (FStar_Const.Unsigned, FStar_Const.Int32) -> begin
FStar_Parser_Const.uint32_lid
end
| (FStar_Const.Unsigned, FStar_Const.Int64) -> begin
FStar_Parser_Const.uint64_lid
end))
end
| FStar_Const.Const_string (uu____9166) -> begin
FStar_Syntax_Syntax.t_string
end
| FStar_Const.Const_float (uu____9171) -> begin
FStar_Syntax_Syntax.t_float
end
| FStar_Const.Const_char (uu____9172) -> begin
(

let uu____9174 = (FStar_Syntax_DsEnv.try_lookup_lid env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid)
in (FStar_All.pipe_right uu____9174 FStar_Util.must))
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (uu____9179) -> begin
FStar_Syntax_Syntax.t_range
end
| FStar_Const.Const_range_of -> begin
(

let uu____9180 = (

let uu____9185 = (

let uu____9186 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____9186))
in ((FStar_Errors.Fatal_IllTyped), (uu____9185)))
in (FStar_Errors.raise_error uu____9180 r))
end
| FStar_Const.Const_set_range_of -> begin
(

let uu____9187 = (

let uu____9192 = (

let uu____9193 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____9193))
in ((FStar_Errors.Fatal_IllTyped), (uu____9192)))
in (FStar_Errors.raise_error uu____9187 r))
end
| FStar_Const.Const_reify -> begin
(

let uu____9194 = (

let uu____9199 = (

let uu____9200 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____9200))
in ((FStar_Errors.Fatal_IllTyped), (uu____9199)))
in (FStar_Errors.raise_error uu____9194 r))
end
| FStar_Const.Const_reflect (uu____9201) -> begin
(

let uu____9202 = (

let uu____9207 = (

let uu____9208 = (FStar_Parser_Const.const_to_string c)
in (FStar_Util.format1 "Ill-typed %s: this constant must be fully applied" uu____9208))
in ((FStar_Errors.Fatal_IllTyped), (uu____9207)))
in (FStar_Errors.raise_error uu____9202 r))
end
| uu____9209 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnsupportedConstant), ("Unsupported constant")) r)
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____9226) -> begin
(

let uu____9235 = (FStar_Syntax_Util.type_u ())
in (match (uu____9235) with
| (k, u) -> begin
(

let uu____9248 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____9248) with
| (t1, uu____9262, g) -> begin
(

let uu____9264 = (FStar_Syntax_Syntax.mk_Total' t1 (FStar_Pervasives_Native.Some (u)))
in ((uu____9264), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t, uu____9266) -> begin
(

let uu____9275 = (FStar_Syntax_Util.type_u ())
in (match (uu____9275) with
| (k, u) -> begin
(

let uu____9288 = (tc_check_tot_or_gtot_term env t k)
in (match (uu____9288) with
| (t1, uu____9302, g) -> begin
(

let uu____9304 = (FStar_Syntax_Syntax.mk_GTotal' t1 (FStar_Pervasives_Native.Some (u)))
in ((uu____9304), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let head1 = (FStar_Syntax_Syntax.fvar c1.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let head2 = (match (c1.FStar_Syntax_Syntax.comp_univs) with
| [] -> begin
head1
end
| us -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((head1), (us)))) FStar_Pervasives_Native.None c0.FStar_Syntax_Syntax.pos)
end)
in (

let tc = (

let uu____9314 = (

let uu____9319 = (

let uu____9320 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (uu____9320)::c1.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head2 uu____9319))
in (uu____9314 FStar_Pervasives_Native.None c1.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let uu____9339 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (uu____9339) with
| (tc1, uu____9353, f) -> begin
(

let uu____9355 = (FStar_Syntax_Util.head_and_args tc1)
in (match (uu____9355) with
| (head3, args) -> begin
(

let comp_univs = (

let uu____9405 = (

let uu____9406 = (FStar_Syntax_Subst.compress head3)
in uu____9406.FStar_Syntax_Syntax.n)
in (match (uu____9405) with
| FStar_Syntax_Syntax.Tm_uinst (uu____9409, us) -> begin
us
end
| uu____9415 -> begin
[]
end))
in (

let uu____9416 = (FStar_Syntax_Util.head_and_args tc1)
in (match (uu____9416) with
| (uu____9439, args1) -> begin
(

let uu____9465 = (

let uu____9488 = (FStar_List.hd args1)
in (

let uu____9505 = (FStar_List.tl args1)
in ((uu____9488), (uu____9505))))
in (match (uu____9465) with
| (res, args2) -> begin
(

let uu____9586 = (

let uu____9595 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___352_9623 -> (match (uu___352_9623) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____9631 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____9631) with
| (env1, uu____9643) -> begin
(

let uu____9648 = (tc_tot_or_gtot_term env1 e)
in (match (uu____9648) with
| (e1, uu____9660, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e1)), (g))
end))
end))
end
| f1 -> begin
((f1), (FStar_TypeChecker_Env.trivial_guard))
end))))
in (FStar_All.pipe_right uu____9595 FStar_List.unzip))
in (match (uu____9586) with
| (flags1, guards) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (FStar_Pervasives_Native.fst res))
in (

let c2 = (FStar_Syntax_Syntax.mk_Comp (

let uu___370_9701 = c1
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = uu___370_9701.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (FStar_Pervasives_Native.fst res); FStar_Syntax_Syntax.effect_args = args2; FStar_Syntax_Syntax.flags = uu___370_9701.FStar_Syntax_Syntax.flags}))
in (

let u_c = (

let uu____9707 = (FStar_TypeChecker_Env.effect_repr env c2 u)
in (match (uu____9707) with
| FStar_Pervasives_Native.None -> begin
u
end
| FStar_Pervasives_Native.Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end))
in (

let uu____9711 = (FStar_List.fold_left FStar_TypeChecker_Env.conj_guard f guards)
in ((c2), (u_c), (uu____9711))))))
end))
end))
end)))
end))
end)))))
end)))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let rec aux = (fun u1 -> (

let u2 = (FStar_Syntax_Subst.compress_univ u1)
in (match (u2) with
| FStar_Syntax_Syntax.U_bvar (uu____9721) -> begin
(failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(failwith "Unknown universe")
end
| FStar_Syntax_Syntax.U_unif (uu____9722) -> begin
u2
end
| FStar_Syntax_Syntax.U_zero -> begin
u2
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____9732 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____9732))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____9736 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____9736))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
(

let uu____9740 = (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x))
in (match (uu____9740) with
| true -> begin
u2
end
| uu____9741 -> begin
(

let uu____9742 = (

let uu____9743 = (

let uu____9744 = (FStar_Syntax_Print.univ_to_string u2)
in (Prims.strcat uu____9744 " not found"))
in (Prims.strcat "Universe variable " uu____9743))
in (failwith uu____9742))
end))
end)))
in (match (env.FStar_TypeChecker_Env.lax_universes) with
| true -> begin
FStar_Syntax_Syntax.U_zero
end
| uu____9745 -> begin
(match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(

let uu____9746 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____9746 FStar_Pervasives_Native.snd))
end
| uu____9755 -> begin
(aux u)
end)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail1 = (fun msg t -> (

let uu____9784 = (FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function env msg t top)
in (FStar_Errors.raise_error uu____9784 top.FStar_Syntax_Syntax.pos)))
in (

let check_binders = (fun env1 bs1 bs_expected -> (

let rec aux = (fun uu____9872 bs2 bs_expected1 -> (match (uu____9872) with
| (env2, subst1) -> begin
(match (((bs2), (bs_expected1))) with
| ([], []) -> begin
((env2), ([]), (FStar_Pervasives_Native.None), (FStar_TypeChecker_Env.trivial_guard), (subst1))
end
| (((hd1, imp))::bs3, ((hd_expected, imp'))::bs_expected2) -> begin
((

let special = (fun q1 q2 -> (match (((q1), (q2))) with
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (uu____10061)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (uu____10062))) -> begin
true
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality)) -> begin
true
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10075)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (uu____10076))) -> begin
true
end
| uu____10083 -> begin
false
end))
in (

let uu____10092 = ((not ((special imp imp'))) && (

let uu____10094 = (FStar_Syntax_Util.eq_aqual imp imp')
in (Prims.op_disEquality uu____10094 FStar_Syntax_Util.Equal)))
in (match (uu____10092) with
| true -> begin
(

let uu____10095 = (

let uu____10100 = (

let uu____10101 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" uu____10101))
in ((FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation), (uu____10100)))
in (

let uu____10102 = (FStar_Syntax_Syntax.range_of_bv hd1)
in (FStar_Errors.raise_error uu____10095 uu____10102)))
end
| uu____10103 -> begin
()
end)));
(

let expected_t = (FStar_Syntax_Subst.subst subst1 hd_expected.FStar_Syntax_Syntax.sort)
in (

let uu____10105 = (

let uu____10112 = (

let uu____10113 = (FStar_Syntax_Util.unmeta hd1.FStar_Syntax_Syntax.sort)
in uu____10113.FStar_Syntax_Syntax.n)
in (match (uu____10112) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (FStar_TypeChecker_Env.trivial_guard))
end
| uu____10124 -> begin
((

let uu____10126 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____10126) with
| true -> begin
(

let uu____10127 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print1 "Checking binder %s\n" uu____10127))
end
| uu____10128 -> begin
()
end));
(

let uu____10129 = (tc_tot_or_gtot_term env2 hd1.FStar_Syntax_Syntax.sort)
in (match (uu____10129) with
| (t, uu____10143, g1_env) -> begin
(

let g2_env = (

let uu____10146 = (FStar_TypeChecker_Rel.teq_nosmt_force env2 t expected_t)
in (match (uu____10146) with
| true -> begin
FStar_TypeChecker_Env.trivial_guard
end
| uu____10147 -> begin
(

let uu____10148 = (FStar_TypeChecker_Rel.get_subtyping_prop env2 expected_t t)
in (match (uu____10148) with
| FStar_Pervasives_Native.None -> begin
(

let uu____10151 = (FStar_TypeChecker_Err.basic_type_error env2 FStar_Pervasives_Native.None expected_t t)
in (

let uu____10156 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Errors.raise_error uu____10151 uu____10156)))
end
| FStar_Pervasives_Native.Some (g_env) -> begin
(

let uu____10158 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_TypeChecker_Util.label_guard uu____10158 "Type annotation on parameter incompatible with the expected type" g_env))
end))
end))
in (

let uu____10159 = (FStar_TypeChecker_Env.conj_guard g1_env g2_env)
in ((t), (uu____10159))))
end));
)
end))
in (match (uu____10105) with
| (t, g_env) -> begin
(

let hd2 = (

let uu___371_10185 = hd1
in {FStar_Syntax_Syntax.ppname = uu___371_10185.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___371_10185.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd2), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env_b = (push_binding env2 b)
in (

let subst2 = (

let uu____10208 = (FStar_Syntax_Syntax.bv_to_name hd2)
in (maybe_extend_subst subst1 b_expected uu____10208))
in (

let uu____10211 = (aux ((env_b), (subst2)) bs3 bs_expected2)
in (match (uu____10211) with
| (env_bs, bs4, rest, g'_env_b, subst3) -> begin
(

let g'_env = (FStar_TypeChecker_Env.close_guard env_bs ((b)::[]) g'_env_b)
in (

let uu____10276 = (FStar_TypeChecker_Env.conj_guard g_env g'_env)
in ((env_bs), ((b)::bs4), (rest), (uu____10276), (subst3))))
end)))))))
end)));
)
end
| (rest, []) -> begin
((env2), ([]), (FStar_Pervasives_Native.Some (FStar_Util.Inl (rest))), (FStar_TypeChecker_Env.trivial_guard), (subst1))
end
| ([], rest) -> begin
((env2), ([]), (FStar_Pervasives_Native.Some (FStar_Util.Inr (rest))), (FStar_TypeChecker_Env.trivial_guard), (subst1))
end)
end))
in (aux ((env1), ([])) bs1 bs_expected)))
in (

let rec expected_function_typ1 = (fun env1 t0 body1 -> (match (t0) with
| FStar_Pervasives_Native.None -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____10448 -> begin
(failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end);
(

let uu____10457 = (tc_binders env1 bs)
in (match (uu____10457) with
| (bs1, envbody, g_env, uu____10487) -> begin
((FStar_Pervasives_Native.None), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody), (body1), (g_env))
end));
)
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm1 t2 -> (

let uu____10541 = (

let uu____10542 = (FStar_Syntax_Subst.compress t2)
in uu____10542.FStar_Syntax_Syntax.n)
in (match (uu____10541) with
| FStar_Syntax_Syntax.Tm_uvar (uu____10575) -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____10595 -> begin
(failwith "Impossible")
end);
(

let uu____10604 = (tc_binders env1 bs)
in (match (uu____10604) with
| (bs1, envbody, g_env, uu____10646) -> begin
(

let uu____10647 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____10647) with
| (envbody1, uu____10685) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody1), (body1), (g_env))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____10706); FStar_Syntax_Syntax.pos = uu____10707; FStar_Syntax_Syntax.vars = uu____10708}, uu____10709) -> begin
((match (env1.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| uu____10753 -> begin
(failwith "Impossible")
end);
(

let uu____10762 = (tc_binders env1 bs)
in (match (uu____10762) with
| (bs1, envbody, g_env, uu____10804) -> begin
(

let uu____10805 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (uu____10805) with
| (envbody1, uu____10843) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (FStar_Pervasives_Native.None), (envbody1), (body1), (g_env))
end))
end));
)
end
| FStar_Syntax_Syntax.Tm_refine (b, uu____10865) -> begin
(

let uu____10870 = (as_function_typ norm1 b.FStar_Syntax_Syntax.sort)
in (match (uu____10870) with
| (uu____10931, bs1, bs', copt, env_body, body2, g_env) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), (bs'), (copt), (env_body), (body2), (g_env))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let uu____11008 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (uu____11008) with
| (bs_expected1, c_expected1) -> begin
(

let check_actuals_against_formals = (fun env2 bs1 bs_expected2 body2 -> (

let rec handle_more = (fun uu____11153 c_expected2 body3 -> (match (uu____11153) with
| (env_bs, bs2, more, guard_env, subst1) -> begin
(match (more) with
| FStar_Pervasives_Native.None -> begin
(

let uu____11267 = (FStar_Syntax_Subst.subst_comp subst1 c_expected2)
in ((env_bs), (bs2), (guard_env), (uu____11267), (body3)))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (

let uu____11284 = (FStar_Syntax_Util.arrow more_bs_expected c_expected2)
in (FStar_Syntax_Syntax.mk_Total uu____11284))
in (

let uu____11285 = (FStar_Syntax_Subst.subst_comp subst1 c)
in ((env_bs), (bs2), (guard_env), (uu____11285), (body3))))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (more_bs)) -> begin
(

let c = (FStar_Syntax_Subst.subst_comp subst1 c_expected2)
in (

let uu____11302 = ((FStar_Options.ml_ish ()) || (FStar_Syntax_Util.is_named_tot c))
in (match (uu____11302) with
| true -> begin
(

let t3 = (FStar_TypeChecker_Normalize.unfold_whnf env_bs (FStar_Syntax_Util.comp_result c))
in (match (t3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected3, c_expected3) -> begin
(

let uu____11366 = (FStar_Syntax_Subst.open_comp bs_expected3 c_expected3)
in (match (uu____11366) with
| (bs_expected4, c_expected4) -> begin
(

let uu____11393 = (check_binders env_bs more_bs bs_expected4)
in (match (uu____11393) with
| (env_bs_bs', bs', more1, guard'_env_bs, subst2) -> begin
(

let guard'_env = (FStar_TypeChecker_Env.close_guard env_bs bs2 guard'_env_bs)
in (

let uu____11448 = (

let uu____11475 = (FStar_TypeChecker_Env.conj_guard guard_env guard'_env)
in ((env_bs_bs'), ((FStar_List.append bs2 bs')), (more1), (uu____11475), (subst2)))
in (handle_more uu____11448 c_expected4 body3)))
end))
end))
end
| uu____11498 -> begin
(

let body4 = (FStar_Syntax_Util.abs more_bs body3 FStar_Pervasives_Native.None)
in ((env_bs), (bs2), (guard_env), (c), (body4)))
end))
end
| uu____11512 -> begin
(

let body4 = (FStar_Syntax_Util.abs more_bs body3 FStar_Pervasives_Native.None)
in ((env_bs), (bs2), (guard_env), (c), (body4)))
end)))
end)
end))
in (

let uu____11526 = (check_binders env2 bs1 bs_expected2)
in (handle_more uu____11526 c_expected1 body2))))
in (

let mk_letrec_env = (fun envbody bs1 c -> (

let letrecs = (guard_letrecs envbody bs1 c)
in (

let envbody1 = (

let uu___372_11589 = envbody
in {FStar_TypeChecker_Env.solver = uu___372_11589.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___372_11589.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___372_11589.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___372_11589.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___372_11589.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___372_11589.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___372_11589.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___372_11589.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___372_11589.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___372_11589.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___372_11589.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___372_11589.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___372_11589.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___372_11589.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = uu___372_11589.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___372_11589.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___372_11589.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___372_11589.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___372_11589.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___372_11589.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___372_11589.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___372_11589.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___372_11589.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___372_11589.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___372_11589.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___372_11589.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___372_11589.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___372_11589.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___372_11589.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___372_11589.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___372_11589.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___372_11589.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___372_11589.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___372_11589.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___372_11589.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___372_11589.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___372_11589.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___372_11589.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___372_11589.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___372_11589.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___372_11589.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___372_11589.FStar_TypeChecker_Env.nbe})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun uu____11647 uu____11648 -> (match (((uu____11647), (uu____11648))) with
| ((env2, letrec_binders), (l, t3, u_names)) -> begin
(

let uu____11730 = (

let uu____11737 = (

let uu____11738 = (FStar_TypeChecker_Env.clear_expected_typ env2)
in (FStar_All.pipe_right uu____11738 FStar_Pervasives_Native.fst))
in (tc_term uu____11737 t3))
in (match (uu____11730) with
| (t4, uu____11760, uu____11761) -> begin
(

let env3 = (FStar_TypeChecker_Env.push_let_binding env2 l ((u_names), (t4)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(

let uu____11773 = (FStar_Syntax_Syntax.mk_binder (

let uu___373_11776 = x
in {FStar_Syntax_Syntax.ppname = uu___373_11776.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___373_11776.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t4}))
in (uu____11773)::letrec_binders)
end
| uu____11777 -> begin
letrec_binders
end)
in ((env3), (lb))))
end))
end)) ((envbody1), ([])))))))
in (

let uu____11786 = (check_actuals_against_formals env1 bs bs_expected1 body1)
in (match (uu____11786) with
| (envbody, bs1, g_env, c, body2) -> begin
(

let uu____11862 = (mk_letrec_env envbody bs1 c)
in (match (uu____11862) with
| (envbody1, letrecs) -> begin
(

let envbody2 = (FStar_TypeChecker_Env.set_expected_typ envbody1 (FStar_Syntax_Util.comp_result c))
in ((FStar_Pervasives_Native.Some (t2)), (bs1), (letrecs), (FStar_Pervasives_Native.Some (c)), (envbody2), (body2), (g_env)))
end))
end))))
end))
end
| uu____11922 -> begin
(match ((not (norm1))) with
| true -> begin
(

let uu____11953 = (FStar_TypeChecker_Normalize.unfold_whnf env1 t2)
in (as_function_typ true uu____11953))
end
| uu____11954 -> begin
(

let uu____11955 = (expected_function_typ1 env1 FStar_Pervasives_Native.None body1)
in (match (uu____11955) with
| (uu____12004, bs1, uu____12006, c_opt, envbody, body2, g_env) -> begin
((FStar_Pervasives_Native.Some (t2)), (bs1), ([]), (c_opt), (envbody), (body2), (g_env))
end))
end)
end)))
in (as_function_typ false t1)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let uu____12036 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____12036) with
| (env1, topt) -> begin
((

let uu____12056 = (FStar_TypeChecker_Env.debug env1 FStar_Options.High)
in (match (uu____12056) with
| true -> begin
(

let uu____12057 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" uu____12057 (match (env1.FStar_TypeChecker_Env.top_level) with
| true -> begin
"true"
end
| uu____12059 -> begin
"false"
end)))
end
| uu____12060 -> begin
()
end));
(

let uu____12061 = (expected_function_typ1 env1 topt body)
in (match (uu____12061) with
| (tfun_opt, bs1, letrec_binders, c_opt, envbody, body1, g_env) -> begin
((

let uu____12102 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("NYC")))
in (match (uu____12102) with
| true -> begin
(

let uu____12103 = (FStar_Syntax_Print.binders_to_string ", " bs1)
in (

let uu____12104 = (FStar_TypeChecker_Rel.guard_to_string env1 g_env)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n" uu____12103 uu____12104)))
end
| uu____12105 -> begin
()
end));
(

let envbody1 = (FStar_TypeChecker_Env.set_range envbody body1.FStar_Syntax_Syntax.pos)
in (

let uu____12107 = (

let should_check_expected_effect = (

let uu____12119 = (

let uu____12126 = (

let uu____12127 = (FStar_Syntax_Subst.compress body1)
in uu____12127.FStar_Syntax_Syntax.n)
in ((c_opt), (uu____12126)))
in (match (uu____12119) with
| (FStar_Pervasives_Native.None, FStar_Syntax_Syntax.Tm_ascribed (uu____12132, (FStar_Util.Inr (expected_c), uu____12134), uu____12135)) -> begin
false
end
| uu____12184 -> begin
true
end))
in (

let uu____12191 = (tc_term (

let uu___374_12200 = envbody1
in {FStar_TypeChecker_Env.solver = uu___374_12200.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___374_12200.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___374_12200.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___374_12200.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___374_12200.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___374_12200.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___374_12200.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___374_12200.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___374_12200.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___374_12200.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___374_12200.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___374_12200.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___374_12200.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___374_12200.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___374_12200.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___374_12200.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___374_12200.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___374_12200.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___374_12200.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___374_12200.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___374_12200.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___374_12200.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___374_12200.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___374_12200.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___374_12200.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___374_12200.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___374_12200.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___374_12200.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___374_12200.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___374_12200.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___374_12200.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___374_12200.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___374_12200.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___374_12200.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___374_12200.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___374_12200.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___374_12200.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___374_12200.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___374_12200.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___374_12200.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___374_12200.FStar_TypeChecker_Env.nbe}) body1)
in (match (uu____12191) with
| (body2, cbody, guard_body) -> begin
(

let guard_body1 = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody1 guard_body)
in (match (should_check_expected_effect) with
| true -> begin
(

let uu____12225 = (

let uu____12232 = (

let uu____12237 = (FStar_Syntax_Syntax.lcomp_comp cbody)
in ((body2), (uu____12237)))
in (check_expected_effect (

let uu___375_12240 = envbody1
in {FStar_TypeChecker_Env.solver = uu___375_12240.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___375_12240.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___375_12240.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___375_12240.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___375_12240.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___375_12240.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___375_12240.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___375_12240.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___375_12240.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___375_12240.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___375_12240.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___375_12240.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___375_12240.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___375_12240.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___375_12240.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___375_12240.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___375_12240.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = uu___375_12240.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___375_12240.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___375_12240.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___375_12240.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___375_12240.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___375_12240.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___375_12240.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___375_12240.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___375_12240.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___375_12240.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___375_12240.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___375_12240.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___375_12240.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___375_12240.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___375_12240.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___375_12240.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___375_12240.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___375_12240.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___375_12240.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___375_12240.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___375_12240.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___375_12240.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___375_12240.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___375_12240.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___375_12240.FStar_TypeChecker_Env.nbe}) c_opt uu____12232))
in (match (uu____12225) with
| (body3, cbody1, guard) -> begin
(

let uu____12254 = (FStar_TypeChecker_Env.conj_guard guard_body1 guard)
in ((body3), (cbody1), (uu____12254)))
end))
end
| uu____12259 -> begin
(

let uu____12260 = (FStar_Syntax_Syntax.lcomp_comp cbody)
in ((body2), (uu____12260), (guard_body1)))
end))
end)))
in (match (uu____12107) with
| (body2, cbody, guard_body) -> begin
(

let guard = (

let uu____12285 = (env1.FStar_TypeChecker_Env.top_level || (

let uu____12287 = (FStar_TypeChecker_Env.should_verify env1)
in (not (uu____12287))))
in (match (uu____12285) with
| true -> begin
(

let uu____12288 = (FStar_TypeChecker_Rel.discharge_guard env1 g_env)
in (

let uu____12289 = (FStar_TypeChecker_Rel.discharge_guard envbody1 guard_body)
in (FStar_TypeChecker_Env.conj_guard uu____12288 uu____12289)))
end
| uu____12290 -> begin
(

let guard = (

let uu____12292 = (FStar_TypeChecker_Env.close_guard env1 (FStar_List.append bs1 letrec_binders) guard_body)
in (FStar_TypeChecker_Env.conj_guard g_env uu____12292))
in guard)
end))
in (

let guard1 = (FStar_TypeChecker_Util.close_guard_implicits env1 bs1 guard)
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs1 cbody)
in (

let e = (FStar_Syntax_Util.abs bs1 body2 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp (FStar_Util.dflt cbody c_opt)))))
in (

let uu____12306 = (match (tfun_opt) with
| FStar_Pervasives_Native.Some (t) -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____12327) -> begin
((e), (t1), (guard1))
end
| uu____12342 -> begin
(

let uu____12343 = (FStar_TypeChecker_Util.check_and_ascribe env1 e tfun_computed t1)
in (match (uu____12343) with
| (e1, guard') -> begin
(

let uu____12356 = (FStar_TypeChecker_Env.conj_guard guard1 guard')
in ((e1), (t1), (uu____12356)))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
((e), (tfun_computed), (guard1))
end)
in (match (uu____12306) with
| (e1, tfun, guard2) -> begin
(

let c = (FStar_Syntax_Syntax.mk_Total tfun)
in (

let uu____12367 = (

let uu____12372 = (FStar_Syntax_Util.lcomp_of_comp c)
in (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env1 e1 uu____12372 guard2))
in (match (uu____12367) with
| (c1, g) -> begin
((e1), (c1), (g))
end)))
end))))))
end)));
)
end));
)
end)))))))
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head1 chead ghead args expected_topt -> (

let n_args = (FStar_List.length args)
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let thead = chead.FStar_Syntax_Syntax.res_typ
in ((

let uu____12420 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____12420) with
| true -> begin
(

let uu____12421 = (FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos)
in (

let uu____12422 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" uu____12421 uu____12422)))
end
| uu____12423 -> begin
()
end));
(

let monadic_application = (fun uu____12499 subst1 arg_comps_rev arg_rets_rev guard fvs bs -> (match (uu____12499) with
| (head2, chead1, ghead1, cres) -> begin
(

let uu____12566 = (check_no_escape (FStar_Pervasives_Native.Some (head2)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (match (uu____12566) with
| (rt, g0) -> begin
(

let cres1 = (

let uu___376_12580 = cres
in {FStar_Syntax_Syntax.eff_name = uu___376_12580.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = rt; FStar_Syntax_Syntax.cflags = uu___376_12580.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___376_12580.FStar_Syntax_Syntax.comp_thunk})
in (

let uu____12581 = (match (bs) with
| [] -> begin
(

let g = (

let uu____12597 = (FStar_TypeChecker_Env.conj_guard ghead1 guard)
in (FStar_All.pipe_left (FStar_TypeChecker_Env.conj_guard g0) uu____12597))
in ((cres1), (g)))
end
| uu____12598 -> begin
(

let g = (

let uu____12608 = (

let uu____12609 = (FStar_TypeChecker_Env.conj_guard ghead1 guard)
in (FStar_All.pipe_right uu____12609 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (FStar_TypeChecker_Env.conj_guard g0 uu____12608))
in (

let uu____12610 = (

let uu____12611 = (

let uu____12612 = (

let uu____12613 = (FStar_Syntax_Syntax.lcomp_comp cres1)
in (FStar_Syntax_Util.arrow bs uu____12613))
in (FStar_Syntax_Syntax.mk_Total uu____12612))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____12611))
in ((uu____12610), (g))))
end)
in (match (uu____12581) with
| (cres2, guard1) -> begin
((

let uu____12625 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____12625) with
| true -> begin
(

let uu____12626 = (FStar_Syntax_Print.lcomp_to_string cres2)
in (FStar_Util.print1 "\t Type of result cres is %s\n" uu____12626))
end
| uu____12627 -> begin
()
end));
(

let cres3 = (

let head_is_pure_and_some_arg_is_effectful = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp chead1) && (FStar_Util.for_some (fun uu____12642 -> (match (uu____12642) with
| (uu____12651, uu____12652, lc) -> begin
((

let uu____12660 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
in (not (uu____12660))) || (FStar_TypeChecker_Util.should_not_inline_lc lc))
end)) arg_comps_rev))
in (

let term = (FStar_Syntax_Syntax.mk_Tm_app head2 (FStar_List.rev arg_rets_rev) FStar_Pervasives_Native.None head2.FStar_Syntax_Syntax.pos)
in (

let uu____12672 = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres2) && head_is_pure_and_some_arg_is_effectful)
in (match (uu____12672) with
| true -> begin
((

let uu____12674 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____12674) with
| true -> begin
(

let uu____12675 = (FStar_Syntax_Print.term_to_string term)
in (FStar_Util.print1 "(a) Monadic app: Return inserted in monadic application: %s\n" uu____12675))
end
| uu____12676 -> begin
()
end));
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env term cres2);
)
end
| uu____12677 -> begin
((

let uu____12679 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____12679) with
| true -> begin
(

let uu____12680 = (FStar_Syntax_Print.term_to_string term)
in (FStar_Util.print1 "(a) Monadic app: No return inserted in monadic application: %s\n" uu____12680))
end
| uu____12681 -> begin
()
end));
cres2;
)
end))))
in (

let comp = (FStar_List.fold_left (fun out_c uu____12708 -> (match (uu____12708) with
| ((e, q), x, c) -> begin
((

let uu____12750 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____12750) with
| true -> begin
(

let uu____12751 = (match (x) with
| FStar_Pervasives_Native.None -> begin
"_"
end
| FStar_Pervasives_Native.Some (x1) -> begin
(FStar_Syntax_Print.bv_to_string x1)
end)
in (

let uu____12753 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____12754 = (FStar_Syntax_Print.lcomp_to_string c)
in (FStar_Util.print3 "(b) Monadic app: Binding argument %s : %s of type (%s)\n" uu____12751 uu____12753 uu____12754))))
end
| uu____12755 -> begin
()
end));
(

let uu____12756 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (match (uu____12756) with
| true -> begin
(FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (e)) c ((x), (out_c)))
end
| uu____12759 -> begin
(FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None c ((x), (out_c)))
end));
)
end)) cres3 arg_comps_rev)
in (

let comp1 = ((

let uu____12764 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____12764) with
| true -> begin
(

let uu____12765 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print1 "(c) Monadic app: Binding head %s\n" uu____12765))
end
| uu____12766 -> begin
()
end));
(

let uu____12767 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp chead1)
in (match (uu____12767) with
| true -> begin
(FStar_TypeChecker_Util.bind head2.FStar_Syntax_Syntax.pos env (FStar_Pervasives_Native.Some (head2)) chead1 ((FStar_Pervasives_Native.None), (comp)))
end
| uu____12770 -> begin
(FStar_TypeChecker_Util.bind head2.FStar_Syntax_Syntax.pos env FStar_Pervasives_Native.None chead1 ((FStar_Pervasives_Native.None), (comp)))
end));
)
in (

let comp2 = (FStar_TypeChecker_Util.subst_lcomp subst1 comp1)
in (

let shortcuts_evaluation_order = (

let uu____12775 = (

let uu____12776 = (FStar_Syntax_Subst.compress head2)
in uu____12776.FStar_Syntax_Syntax.n)
in (match (uu____12775) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_And) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Or))
end
| uu____12780 -> begin
false
end))
in (

let app = (match (shortcuts_evaluation_order) with
| true -> begin
(

let args1 = (FStar_List.fold_left (fun args1 uu____12801 -> (match (uu____12801) with
| (arg, uu____12815, uu____12816) -> begin
(arg)::args1
end)) [] arg_comps_rev)
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head2 args1 FStar_Pervasives_Native.None r)
in (

let app1 = (FStar_TypeChecker_Util.maybe_lift env app cres3.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ)
in (FStar_TypeChecker_Util.maybe_monadic env app1 comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ))))
end
| uu____12825 -> begin
(

let uu____12826 = (

let map_fun = (fun uu____12888 -> (match (uu____12888) with
| ((e, q), uu____12925, c) -> begin
((

let uu____12942 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____12942) with
| true -> begin
(

let uu____12943 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____12944 = (FStar_Syntax_Print.lcomp_to_string c)
in (FStar_Util.print2 "For arg e=(%s) c=(%s)... " uu____12943 uu____12944)))
end
| uu____12945 -> begin
()
end));
(

let uu____12946 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)
in (match (uu____12946) with
| true -> begin
((

let uu____12968 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____12968) with
| true -> begin
(FStar_Util.print_string "... not lifting\n")
end
| uu____12969 -> begin
()
end));
((FStar_Pervasives_Native.None), (((e), (q))));
)
end
| uu____12996 -> begin
((

let uu____12998 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____12998) with
| true -> begin
(FStar_Util.print_string "... lifting!\n")
end
| uu____12999 -> begin
()
end));
(

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.res_typ)
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e c.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let uu____13002 = (

let uu____13009 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____13009), (q)))
in ((FStar_Pervasives_Native.Some (((x), (c.FStar_Syntax_Syntax.eff_name), (c.FStar_Syntax_Syntax.res_typ), (e1)))), (uu____13002)))));
)
end));
)
end))
in (

let uu____13036 = (

let uu____13065 = (

let uu____13092 = (

let uu____13103 = (

let uu____13112 = (FStar_Syntax_Syntax.as_arg head2)
in ((uu____13112), (FStar_Pervasives_Native.None), (chead1)))
in (uu____13103)::arg_comps_rev)
in (FStar_List.map map_fun uu____13092))
in (FStar_All.pipe_left FStar_List.split uu____13065))
in (match (uu____13036) with
| (lifted_args, reverse_args) -> begin
(

let uu____13301 = (

let uu____13302 = (FStar_List.hd reverse_args)
in (FStar_Pervasives_Native.fst uu____13302))
in (

let uu____13317 = (

let uu____13318 = (FStar_List.tl reverse_args)
in (FStar_List.rev uu____13318))
in ((lifted_args), (uu____13301), (uu____13317))))
end)))
in (match (uu____12826) with
| (lifted_args, head3, args1) -> begin
(

let app = (FStar_Syntax_Syntax.mk_Tm_app head3 args1 FStar_Pervasives_Native.None r)
in (

let app1 = (FStar_TypeChecker_Util.maybe_lift env app cres3.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ)
in (

let app2 = (FStar_TypeChecker_Util.maybe_monadic env app1 comp2.FStar_Syntax_Syntax.eff_name comp2.FStar_Syntax_Syntax.res_typ)
in (

let bind_lifted_args = (fun e uu___353_13423 -> (match (uu___353_13423) with
| FStar_Pervasives_Native.None -> begin
e
end
| FStar_Pervasives_Native.Some (x, m, t, e1) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] t m e1 [] e1.FStar_Syntax_Syntax.pos)
in (

let letbinding = (

let uu____13484 = (

let uu____13491 = (

let uu____13492 = (

let uu____13505 = (

let uu____13508 = (

let uu____13509 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____13509)::[])
in (FStar_Syntax_Subst.close uu____13508 e))
in ((((false), ((lb)::[]))), (uu____13505)))
in FStar_Syntax_Syntax.Tm_let (uu____13492))
in (FStar_Syntax_Syntax.mk uu____13491))
in (uu____13484 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((letbinding), (FStar_Syntax_Syntax.Meta_monadic (((m), (comp2.FStar_Syntax_Syntax.res_typ))))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))
end))
in (FStar_List.fold_left bind_lifted_args app2 lifted_args)))))
end))
end)
in (

let uu____13561 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env app comp2 guard1)
in (match (uu____13561) with
| (comp3, g) -> begin
((

let uu____13578 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____13578) with
| true -> begin
(

let uu____13579 = (FStar_Syntax_Print.term_to_string app)
in (

let uu____13580 = (FStar_Syntax_Print.lcomp_to_string comp3)
in (FStar_Util.print2 "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n" uu____13579 uu____13580)))
end
| uu____13581 -> begin
()
end));
((app), (comp3), (g));
)
end))))))));
)
end)))
end))
end))
in (

let rec tc_args = (fun head_info uu____13658 bs args1 -> (match (uu____13658) with
| (subst1, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args1))) with
| (((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____13797))))::rest, ((uu____13799, FStar_Pervasives_Native.None))::uu____13800) -> begin
(

let t = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____13860 = (check_no_escape (FStar_Pervasives_Native.Some (head1)) env fvs t)
in (match (uu____13860) with
| (t1, g_ex) -> begin
(

let uu____13873 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head1.FStar_Syntax_Syntax.pos env t1)
in (match (uu____13873) with
| (varg, uu____13893, implicits) -> begin
(

let subst2 = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst1
in (

let arg = (

let uu____13921 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (uu____13921)))
in (

let guard = (FStar_List.fold_right FStar_TypeChecker_Env.conj_guard ((g_ex)::(g)::[]) implicits)
in (

let uu____13929 = (

let uu____13964 = (

let uu____13975 = (

let uu____13984 = (

let uu____13985 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_right uu____13985 FStar_Syntax_Util.lcomp_of_comp))
in ((arg), (FStar_Pervasives_Native.None), (uu____13984)))
in (uu____13975)::outargs)
in ((subst2), (uu____13964), ((arg)::arg_rets), (guard), (fvs)))
in (tc_args head_info uu____13929 rest args1)))))
end))
end)))
end
| (((x, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (tau))))::rest, ((uu____14031, FStar_Pervasives_Native.None))::uu____14032) -> begin
(

let tau1 = (FStar_Syntax_Subst.subst subst1 tau)
in (

let uu____14094 = (tc_tactic env tau1)
in (match (uu____14094) with
| (tau2, uu____14108, g_tau) -> begin
(

let t = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____14111 = (check_no_escape (FStar_Pervasives_Native.Some (head1)) env fvs t)
in (match (uu____14111) with
| (t1, g_ex) -> begin
(

let uu____14124 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating meta argument in application" head1.FStar_Syntax_Syntax.pos env t1)
in (match (uu____14124) with
| (varg, uu____14144, implicits) -> begin
(

let mark_meta_implicits = (fun tau3 g1 -> (

let uu___377_14169 = g1
in (

let uu____14170 = (FStar_List.map (fun imp -> (

let uu___378_14176 = imp
in {FStar_TypeChecker_Env.imp_reason = uu___378_14176.FStar_TypeChecker_Env.imp_reason; FStar_TypeChecker_Env.imp_uvar = uu___378_14176.FStar_TypeChecker_Env.imp_uvar; FStar_TypeChecker_Env.imp_tm = uu___378_14176.FStar_TypeChecker_Env.imp_tm; FStar_TypeChecker_Env.imp_range = uu___378_14176.FStar_TypeChecker_Env.imp_range; FStar_TypeChecker_Env.imp_meta = FStar_Pervasives_Native.Some (((env), (tau3)))})) g1.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = uu___377_14169.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___377_14169.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___377_14169.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = uu____14170})))
in (

let implicits1 = (mark_meta_implicits tau2 implicits)
in (

let subst2 = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst1
in (

let arg = (

let uu____14196 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (uu____14196)))
in (

let guard = (FStar_List.fold_right FStar_TypeChecker_Env.conj_guard ((g_ex)::(g)::(g_tau)::[]) implicits1)
in (

let uu____14204 = (

let uu____14239 = (

let uu____14250 = (

let uu____14259 = (

let uu____14260 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_All.pipe_right uu____14260 FStar_Syntax_Util.lcomp_of_comp))
in ((arg), (FStar_Pervasives_Native.None), (uu____14259)))
in (uu____14250)::outargs)
in ((subst2), (uu____14239), ((arg)::arg_rets), (guard), (fvs)))
in (tc_args head_info uu____14204 rest args1)))))))
end))
end)))
end)))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
((match (((aqual), (aq))) with
| (uu____14376, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (uu____14377))) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_InconsistentImplicitQualifier), ("Inconsistent implicit qualifier; cannot apply meta arguments, just use #")) e.FStar_Syntax_Syntax.pos)
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (uu____14386)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____14387))) -> begin
()
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____14394)), FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____14395))) -> begin
()
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
()
end
| (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality), FStar_Pervasives_Native.None) -> begin
()
end
| uu____14408 -> begin
(

let uu____14417 = (

let uu____14422 = (

let uu____14423 = (FStar_Syntax_Print.aqual_to_string aqual)
in (

let uu____14424 = (FStar_Syntax_Print.aqual_to_string aq)
in (

let uu____14425 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____14426 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format4 "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s" uu____14423 uu____14424 uu____14425 uu____14426)))))
in ((FStar_Errors.Fatal_InconsistentImplicitQualifier), (uu____14422)))
in (FStar_Errors.raise_error uu____14417 e.FStar_Syntax_Syntax.pos))
end);
(

let targ = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let aqual1 = (FStar_Syntax_Subst.subst_imp subst1 aqual)
in (

let x1 = (

let uu___379_14430 = x
in {FStar_Syntax_Syntax.ppname = uu___379_14430.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___379_14430.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in ((

let uu____14432 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____14432) with
| true -> begin
(

let uu____14433 = (FStar_Syntax_Print.bv_to_string x1)
in (

let uu____14434 = (FStar_Syntax_Print.term_to_string x1.FStar_Syntax_Syntax.sort)
in (

let uu____14435 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____14436 = (FStar_Syntax_Print.subst_to_string subst1)
in (

let uu____14437 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print5 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n" uu____14433 uu____14434 uu____14435 uu____14436 uu____14437))))))
end
| uu____14438 -> begin
()
end));
(

let uu____14439 = (check_no_escape (FStar_Pervasives_Native.Some (head1)) env fvs targ)
in (match (uu____14439) with
| (targ1, g_ex) -> begin
(

let env1 = (FStar_TypeChecker_Env.set_expected_typ env targ1)
in (

let env2 = (

let uu___380_14454 = env1
in {FStar_TypeChecker_Env.solver = uu___380_14454.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___380_14454.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___380_14454.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___380_14454.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___380_14454.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___380_14454.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___380_14454.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___380_14454.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___380_14454.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___380_14454.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___380_14454.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___380_14454.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___380_14454.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___380_14454.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___380_14454.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___380_14454.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___380_14454.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual1); FStar_TypeChecker_Env.is_iface = uu___380_14454.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___380_14454.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___380_14454.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___380_14454.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___380_14454.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___380_14454.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___380_14454.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___380_14454.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___380_14454.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___380_14454.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___380_14454.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___380_14454.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___380_14454.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___380_14454.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___380_14454.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___380_14454.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___380_14454.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___380_14454.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___380_14454.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___380_14454.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___380_14454.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___380_14454.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___380_14454.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___380_14454.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___380_14454.FStar_TypeChecker_Env.nbe})
in ((

let uu____14456 = (FStar_TypeChecker_Env.debug env2 FStar_Options.High)
in (match (uu____14456) with
| true -> begin
(

let uu____14457 = (FStar_Syntax_Print.tag_of_term e)
in (

let uu____14458 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____14459 = (FStar_Syntax_Print.term_to_string targ1)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" uu____14457 uu____14458 uu____14459))))
end
| uu____14460 -> begin
()
end));
(

let uu____14461 = (tc_term env2 e)
in (match (uu____14461) with
| (e1, c, g_e) -> begin
(

let g1 = (

let uu____14478 = (FStar_TypeChecker_Env.conj_guard g g_e)
in (FStar_All.pipe_left (FStar_TypeChecker_Env.conj_guard g_ex) uu____14478))
in (

let arg = ((e1), (aq))
in (

let xterm = (

let uu____14501 = (

let uu____14504 = (

let uu____14513 = (FStar_Syntax_Syntax.bv_to_name x1)
in (FStar_Syntax_Syntax.as_arg uu____14513))
in (FStar_Pervasives_Native.fst uu____14504))
in ((uu____14501), (aq)))
in (

let uu____14522 = ((FStar_Syntax_Util.is_tot_or_gtot_lcomp c) || (FStar_TypeChecker_Util.is_pure_or_ghost_effect env2 c.FStar_Syntax_Syntax.eff_name))
in (match (uu____14522) with
| true -> begin
(

let subst2 = (

let uu____14530 = (FStar_List.hd bs)
in (maybe_extend_subst subst1 uu____14530 e1))
in (tc_args head_info ((subst2), ((((arg), (FStar_Pervasives_Native.Some (x1)), (c)))::outargs), ((xterm)::arg_rets), (g1), (fvs)) rest rest'))
end
| uu____14585 -> begin
(tc_args head_info ((subst1), ((((arg), (FStar_Pervasives_Native.Some (x1)), (c)))::outargs), ((xterm)::arg_rets), (g1), ((x1)::fvs)) rest rest')
end)))))
end));
)))
end));
))));
)
end
| (uu____14628, []) -> begin
(monadic_application head_info subst1 outargs arg_rets g fvs bs)
end
| ([], (arg)::uu____14664) -> begin
(

let uu____14715 = (monadic_application head_info subst1 outargs arg_rets g fvs [])
in (match (uu____14715) with
| (head2, chead1, ghead1) -> begin
(

let rec aux = (fun norm1 solve ghead2 tres -> (

let tres1 = (

let uu____14767 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right uu____14767 FStar_Syntax_Util.unrefine))
in (match (tres1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, cres') -> begin
(

let uu____14798 = (FStar_Syntax_Subst.open_comp bs1 cres')
in (match (uu____14798) with
| (bs2, cres'1) -> begin
(

let head_info1 = (

let uu____14820 = (FStar_Syntax_Util.lcomp_of_comp cres'1)
in ((head2), (chead1), (ghead2), (uu____14820)))
in ((

let uu____14822 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____14822) with
| true -> begin
(FStar_Errors.log_issue tres1.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_RedundantExplicitCurrying), ("Potentially redundant explicit currying of a function type")))
end
| uu____14823 -> begin
()
end));
(tc_args head_info1 (([]), ([]), ([]), (FStar_TypeChecker_Env.trivial_guard), ([])) bs2 args1);
))
end))
end
| uu____14864 when (not (norm1)) -> begin
(

let rec norm_tres = (fun tres2 -> (

let tres3 = (FStar_TypeChecker_Normalize.unfold_whnf env tres2)
in (

let uu____14872 = (

let uu____14873 = (FStar_Syntax_Subst.compress tres3)
in uu____14873.FStar_Syntax_Syntax.n)
in (match (uu____14872) with
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____14876; FStar_Syntax_Syntax.index = uu____14877; FStar_Syntax_Syntax.sort = tres4}, uu____14879) -> begin
(norm_tres tres4)
end
| uu____14886 -> begin
tres3
end))))
in (

let uu____14887 = (norm_tres tres1)
in (aux true solve ghead2 uu____14887)))
end
| uu____14888 when (not (solve)) -> begin
(

let ghead3 = (FStar_TypeChecker_Rel.solve_deferred_constraints env ghead2)
in (aux norm1 true ghead3 tres1))
end
| uu____14890 -> begin
(

let uu____14891 = (

let uu____14896 = (

let uu____14897 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (

let uu____14898 = (FStar_Util.string_of_int n_args)
in (

let uu____14905 = (FStar_Syntax_Print.term_to_string tres1)
in (FStar_Util.format3 "Too many arguments to function of type %s; got %s arguments, remaining type is %s" uu____14897 uu____14898 uu____14905))))
in ((FStar_Errors.Fatal_ToManyArgumentToFunction), (uu____14896)))
in (

let uu____14906 = (FStar_Syntax_Syntax.argpos arg)
in (FStar_Errors.raise_error uu____14891 uu____14906)))
end)))
in (aux false false ghead1 chead1.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun tf guard -> (

let uu____14934 = (

let uu____14935 = (FStar_TypeChecker_Normalize.unfold_whnf env tf)
in uu____14935.FStar_Syntax_Syntax.n)
in (match (uu____14934) with
| FStar_Syntax_Syntax.Tm_uvar (uu____14944) -> begin
(

let uu____14957 = (FStar_List.fold_right (fun uu____14988 uu____14989 -> (match (uu____14989) with
| (bs, guard1) -> begin
(

let uu____15016 = (

let uu____15029 = (

let uu____15030 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____15030 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_implicit_var "formal parameter" tf.FStar_Syntax_Syntax.pos env uu____15029))
in (match (uu____15016) with
| (t, uu____15046, g) -> begin
(

let uu____15060 = (

let uu____15063 = (FStar_Syntax_Syntax.null_binder t)
in (uu____15063)::bs)
in (

let uu____15064 = (FStar_TypeChecker_Env.conj_guard g guard1)
in ((uu____15060), (uu____15064))))
end))
end)) args (([]), (guard)))
in (match (uu____14957) with
| (bs, guard1) -> begin
(

let uu____15081 = (

let uu____15088 = (

let uu____15101 = (

let uu____15102 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____15102 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_implicit_var "result type" tf.FStar_Syntax_Syntax.pos env uu____15101))
in (match (uu____15088) with
| (t, uu____15118, g) -> begin
(

let uu____15132 = (FStar_Options.ml_ish ())
in (match (uu____15132) with
| true -> begin
(

let uu____15139 = (FStar_Syntax_Util.ml_comp t r)
in (

let uu____15142 = (FStar_TypeChecker_Env.conj_guard guard1 g)
in ((uu____15139), (uu____15142))))
end
| uu____15145 -> begin
(

let uu____15146 = (FStar_Syntax_Syntax.mk_Total t)
in (

let uu____15149 = (FStar_TypeChecker_Env.conj_guard guard1 g)
in ((uu____15146), (uu____15149))))
end))
end))
in (match (uu____15081) with
| (cres, guard2) -> begin
(

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____15168 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____15168) with
| true -> begin
(

let uu____15169 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____15170 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____15171 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____15169 uu____15170 uu____15171))))
end
| uu____15172 -> begin
()
end));
(

let g = (

let uu____15174 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_TypeChecker_Rel.solve_deferred_constraints env uu____15174))
in (

let uu____15175 = (FStar_TypeChecker_Env.conj_guard g guard2)
in (check_function_app bs_cres uu____15175)));
))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____15176); FStar_Syntax_Syntax.pos = uu____15177; FStar_Syntax_Syntax.vars = uu____15178}, uu____15179) -> begin
(

let uu____15216 = (FStar_List.fold_right (fun uu____15247 uu____15248 -> (match (uu____15248) with
| (bs, guard1) -> begin
(

let uu____15275 = (

let uu____15288 = (

let uu____15289 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____15289 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_implicit_var "formal parameter" tf.FStar_Syntax_Syntax.pos env uu____15288))
in (match (uu____15275) with
| (t, uu____15305, g) -> begin
(

let uu____15319 = (

let uu____15322 = (FStar_Syntax_Syntax.null_binder t)
in (uu____15322)::bs)
in (

let uu____15323 = (FStar_TypeChecker_Env.conj_guard g guard1)
in ((uu____15319), (uu____15323))))
end))
end)) args (([]), (guard)))
in (match (uu____15216) with
| (bs, guard1) -> begin
(

let uu____15340 = (

let uu____15347 = (

let uu____15360 = (

let uu____15361 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____15361 FStar_Pervasives_Native.fst))
in (FStar_TypeChecker_Util.new_implicit_var "result type" tf.FStar_Syntax_Syntax.pos env uu____15360))
in (match (uu____15347) with
| (t, uu____15377, g) -> begin
(

let uu____15391 = (FStar_Options.ml_ish ())
in (match (uu____15391) with
| true -> begin
(

let uu____15398 = (FStar_Syntax_Util.ml_comp t r)
in (

let uu____15401 = (FStar_TypeChecker_Env.conj_guard guard1 g)
in ((uu____15398), (uu____15401))))
end
| uu____15404 -> begin
(

let uu____15405 = (FStar_Syntax_Syntax.mk_Total t)
in (

let uu____15408 = (FStar_TypeChecker_Env.conj_guard guard1 g)
in ((uu____15405), (uu____15408))))
end))
end))
in (match (uu____15340) with
| (cres, guard2) -> begin
(

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in ((

let uu____15427 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme)
in (match (uu____15427) with
| true -> begin
(

let uu____15428 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____15429 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____15430 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" uu____15428 uu____15429 uu____15430))))
end
| uu____15431 -> begin
()
end));
(

let g = (

let uu____15433 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_TypeChecker_Rel.solve_deferred_constraints env uu____15433))
in (

let uu____15434 = (FStar_TypeChecker_Env.conj_guard g guard2)
in (check_function_app bs_cres uu____15434)));
))
end))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____15457 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____15457) with
| (bs1, c1) -> begin
(

let head_info = (

let uu____15479 = (FStar_Syntax_Util.lcomp_of_comp c1)
in ((head1), (chead), (ghead), (uu____15479)))
in ((

let uu____15481 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____15481) with
| true -> begin
(

let uu____15482 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____15483 = (FStar_Syntax_Print.term_to_string tf)
in (

let uu____15484 = (FStar_Syntax_Print.binders_to_string ", " bs1)
in (

let uu____15485 = (FStar_Syntax_Print.comp_to_string c1)
in (FStar_Util.print4 "######tc_args of head %s @ %s with formals=%s and result type=%s\n" uu____15482 uu____15483 uu____15484 uu____15485)))))
end
| uu____15486 -> begin
()
end));
(tc_args head_info (([]), ([]), ([]), (guard), ([])) bs1 args);
))
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____15528) -> begin
(check_function_app bv.FStar_Syntax_Syntax.sort guard)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____15534, uu____15535) -> begin
(check_function_app t guard)
end
| uu____15576 -> begin
(

let uu____15577 = (FStar_TypeChecker_Err.expected_function_typ env tf)
in (FStar_Errors.raise_error uu____15577 head1.FStar_Syntax_Syntax.pos))
end)))
in (check_function_app thead FStar_TypeChecker_Env.trivial_guard))));
)))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head1 chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && (Prims.op_Equality (FStar_List.length bs) (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let uu____15659 = (FStar_List.fold_left2 (fun uu____15726 uu____15727 uu____15728 -> (match (((uu____15726), (uu____15727), (uu____15728))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
((

let uu____15875 = (

let uu____15876 = (FStar_Syntax_Util.eq_aqual aq aq')
in (Prims.op_disEquality uu____15876 FStar_Syntax_Util.Equal))
in (match (uu____15875) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_InconsistentImplicitQualifier), ("Inconsistent implicit qualifiers")) e.FStar_Syntax_Syntax.pos)
end
| uu____15877 -> begin
()
end));
(

let uu____15878 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (uu____15878) with
| (e1, c1, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head1 seen)
in (

let g1 = (

let uu____15906 = (FStar_TypeChecker_Env.guard_of_guard_formula short)
in (FStar_TypeChecker_Env.imp_guard uu____15906 g))
in (

let ghost1 = (ghost || ((

let uu____15910 = (FStar_Syntax_Util.is_total_lcomp c1)
in (not (uu____15910))) && (

let uu____15912 = (FStar_TypeChecker_Util.is_pure_effect env c1.FStar_Syntax_Syntax.eff_name)
in (not (uu____15912)))))
in (

let uu____15913 = (

let uu____15924 = (

let uu____15935 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____15935)::[])
in (FStar_List.append seen uu____15924))
in (

let uu____15968 = (FStar_TypeChecker_Env.conj_guard guard g1)
in ((uu____15913), (uu____15968), (ghost1)))))))
end));
)
end)) (([]), (g_head), (false)) args bs)
in (match (uu____15659) with
| (args1, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head1 args1 FStar_Pervasives_Native.None r)
in (

let c1 = (match (ghost) with
| true -> begin
(

let uu____16030 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right uu____16030 FStar_Syntax_Util.lcomp_of_comp))
end
| uu____16031 -> begin
(FStar_Syntax_Util.lcomp_of_comp c)
end)
in (

let uu____16032 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env e c1 guard)
in (match (uu____16032) with
| (c2, g) -> begin
((e), (c2), (g))
end))))
end)))
end
| uu____16048 -> begin
(check_application_args env head1 chead g_head args expected_topt)
end))))
and tc_pat : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.bv Prims.list * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env pat_t p0 -> (

let fail1 = (fun msg -> (FStar_Errors.raise_error ((FStar_Errors.Fatal_MismatchedPatternType), (msg)) p0.FStar_Syntax_Syntax.p))
in (

let expected_pat_typ = (fun env1 pos scrutinee_t -> (

let rec aux = (fun norm1 t -> (

let t1 = (FStar_Syntax_Util.unrefine t)
in (

let uu____16134 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____16134) with
| (head1, args) -> begin
(

let uu____16177 = (

let uu____16178 = (FStar_Syntax_Subst.compress head1)
in uu____16178.FStar_Syntax_Syntax.n)
in (match (uu____16177) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.pos = uu____16182; FStar_Syntax_Syntax.vars = uu____16183}, us) -> begin
(unfold_once t1 f us args)
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(unfold_once t1 f [] args)
end
| uu____16190 -> begin
(match (norm1) with
| true -> begin
t1
end
| uu____16191 -> begin
(

let uu____16192 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.HNF)::(FStar_TypeChecker_Env.Unmeta)::(FStar_TypeChecker_Env.Unascribe)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) env1 t1)
in (aux true uu____16192))
end)
end))
end))))
and unfold_once = (fun t f us args -> (

let uu____16209 = (FStar_TypeChecker_Env.is_type_constructor env1 f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____16209) with
| true -> begin
t
end
| uu____16210 -> begin
(

let uu____16211 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.delta_constant))::[]) env1 f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____16211) with
| FStar_Pervasives_Native.None -> begin
t
end
| FStar_Pervasives_Native.Some (head_def_ts) -> begin
(

let uu____16231 = (FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us)
in (match (uu____16231) with
| (uu____16236, head_def) -> begin
(

let t' = (FStar_Syntax_Syntax.mk_Tm_app head_def args FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in (

let t'1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Iota)::[]) env1 t')
in (aux false t'1)))
end))
end))
end)))
in (

let uu____16242 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Iota)::[]) env1 scrutinee_t)
in (aux false uu____16242))))
in (

let pat_typ_ok = (fun env1 pat_t1 scrutinee_t -> ((

let uu____16260 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Patterns")))
in (match (uu____16260) with
| true -> begin
(

let uu____16261 = (FStar_Syntax_Print.term_to_string pat_t1)
in (

let uu____16262 = (FStar_Syntax_Print.term_to_string scrutinee_t)
in (FStar_Util.print2 "$$$$$$$$$$$$pat_typ_ok? %s vs. %s\n" uu____16261 uu____16262)))
end
| uu____16263 -> begin
()
end));
(

let fail2 = (fun msg -> (

let msg1 = (

let uu____16276 = (FStar_Syntax_Print.term_to_string pat_t1)
in (

let uu____16277 = (FStar_Syntax_Print.term_to_string scrutinee_t)
in (FStar_Util.format3 "Type of pattern (%s) does not match type of scrutinee (%s)%s" uu____16276 uu____16277 msg)))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_MismatchedPatternType), (msg1)) p0.FStar_Syntax_Syntax.p)))
in (

let uu____16278 = (FStar_Syntax_Util.head_and_args scrutinee_t)
in (match (uu____16278) with
| (head_s, args_s) -> begin
(

let pat_t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env1 pat_t1)
in (

let uu____16322 = (FStar_Syntax_Util.un_uinst head_s)
in (match (uu____16322) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (uu____16323); FStar_Syntax_Syntax.pos = uu____16324; FStar_Syntax_Syntax.vars = uu____16325} -> begin
(

let uu____16328 = (FStar_Syntax_Util.head_and_args pat_t2)
in (match (uu____16328) with
| (head_p, args_p) -> begin
(

let uu____16371 = (FStar_TypeChecker_Rel.teq_nosmt_force env1 head_p head_s)
in (match (uu____16371) with
| true -> begin
(

let uu____16372 = (

let uu____16373 = (FStar_Syntax_Util.un_uinst head_p)
in uu____16373.FStar_Syntax_Syntax.n)
in (match (uu____16372) with
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
((

let uu____16378 = (

let uu____16379 = (

let uu____16380 = (FStar_Syntax_Syntax.lid_of_fv f)
in (FStar_TypeChecker_Env.is_type_constructor env1 uu____16380))
in (FStar_All.pipe_left Prims.op_Negation uu____16379))
in (match (uu____16378) with
| true -> begin
(fail2 "Pattern matching a non-inductive type")
end
| uu____16381 -> begin
()
end));
(match ((Prims.op_disEquality (FStar_List.length args_p) (FStar_List.length args_s))) with
| true -> begin
(fail2 "")
end
| uu____16399 -> begin
()
end);
(

let uu____16400 = (

let uu____16425 = (

let uu____16428 = (FStar_Syntax_Syntax.lid_of_fv f)
in (FStar_TypeChecker_Env.num_inductive_ty_params env1 uu____16428))
in (match (uu____16425) with
| FStar_Pervasives_Native.None -> begin
((args_p), (args_s))
end
| FStar_Pervasives_Native.Some (n1) -> begin
(

let uu____16474 = (FStar_Util.first_N n1 args_p)
in (match (uu____16474) with
| (params_p, uu____16532) -> begin
(

let uu____16573 = (FStar_Util.first_N n1 args_s)
in (match (uu____16573) with
| (params_s, uu____16631) -> begin
((params_p), (params_s))
end))
end))
end))
in (match (uu____16400) with
| (params_p, params_s) -> begin
(FStar_List.fold_left2 (fun out uu____16760 uu____16761 -> (match (((uu____16760), (uu____16761))) with
| ((p, uu____16795), (s, uu____16797)) -> begin
(

let uu____16830 = (FStar_TypeChecker_Rel.teq_nosmt env1 p s)
in (match (uu____16830) with
| FStar_Pervasives_Native.None -> begin
(

let uu____16833 = (

let uu____16834 = (FStar_Syntax_Print.term_to_string p)
in (

let uu____16835 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "; parameter %s <> parameter %s" uu____16834 uu____16835)))
in (fail2 uu____16833))
end
| FStar_Pervasives_Native.Some (g) -> begin
(

let g1 = (FStar_TypeChecker_Rel.discharge_guard_no_smt env1 g)
in (FStar_TypeChecker_Env.conj_guard g1 out))
end))
end)) FStar_TypeChecker_Env.trivial_guard params_p params_s)
end));
)
end
| uu____16838 -> begin
(fail2 "Pattern matching a non-inductive type")
end))
end
| uu____16839 -> begin
(

let uu____16840 = (

let uu____16841 = (FStar_Syntax_Print.term_to_string head_p)
in (

let uu____16842 = (FStar_Syntax_Print.term_to_string head_s)
in (FStar_Util.format2 "; head mismatch %s vs %s" uu____16841 uu____16842)))
in (fail2 uu____16840))
end))
end))
end
| uu____16843 -> begin
(

let uu____16844 = (FStar_TypeChecker_Rel.teq_nosmt env1 pat_t2 scrutinee_t)
in (match (uu____16844) with
| FStar_Pervasives_Native.None -> begin
(fail2 "")
end
| FStar_Pervasives_Native.Some (g) -> begin
(

let g1 = (FStar_TypeChecker_Rel.discharge_guard_no_smt env1 g)
in g1)
end))
end)))
end)));
))
in (

let type_of_simple_pat = (fun env1 e -> (

let uu____16880 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____16880) with
| (head1, args) -> begin
(match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(

let uu____16944 = (FStar_TypeChecker_Env.lookup_datacon env1 f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____16944) with
| (us, t_f) -> begin
(

let uu____16961 = (FStar_Syntax_Util.arrow_formals t_f)
in (match (uu____16961) with
| (formals, t) -> begin
((match ((Prims.op_disEquality (FStar_List.length formals) (FStar_List.length args))) with
| true -> begin
(fail1 "Pattern is not a fully-applied data constructor")
end
| uu____17023 -> begin
()
end);
(

let rec aux = (fun uu____17087 formals1 args1 -> (match (uu____17087) with
| (subst1, args_out, bvs, guard) -> begin
(match (((formals1), (args1))) with
| ([], []) -> begin
(

let head2 = (FStar_Syntax_Syntax.mk_Tm_uinst head1 us)
in (

let pat_e = (FStar_Syntax_Syntax.mk_Tm_app head2 args_out FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (

let uu____17232 = (FStar_Syntax_Subst.subst subst1 t)
in ((pat_e), (uu____17232), (bvs), (guard)))))
end
| (((f1, uu____17238))::formals2, ((a, imp_a))::args2) -> begin
(

let t_f1 = (FStar_Syntax_Subst.subst subst1 f1.FStar_Syntax_Syntax.sort)
in (

let uu____17296 = (

let uu____17317 = (

let uu____17318 = (FStar_Syntax_Subst.compress a)
in uu____17318.FStar_Syntax_Syntax.n)
in (match (uu____17317) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let x1 = (

let uu___381_17343 = x
in {FStar_Syntax_Syntax.ppname = uu___381_17343.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___381_17343.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_f1})
in (

let a1 = (FStar_Syntax_Syntax.bv_to_name x1)
in (

let subst2 = (FStar_Syntax_Syntax.NT (((f1), (a1))))::subst1
in ((((a1), (imp_a))), (subst2), ((FStar_List.append bvs ((x1)::[]))), (FStar_TypeChecker_Env.trivial_guard)))))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____17366) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_expected_typ env1 t_f1)
in (

let uu____17380 = (tc_tot_or_gtot_term env2 a)
in (match (uu____17380) with
| (a1, uu____17408, g) -> begin
(

let g1 = (FStar_TypeChecker_Rel.discharge_guard_no_smt env2 g)
in (

let subst2 = (FStar_Syntax_Syntax.NT (((f1), (a1))))::subst1
in ((((a1), (imp_a))), (subst2), (bvs), (g1))))
end)))
end
| uu____17432 -> begin
(fail1 "Not a simple pattern")
end))
in (match (uu____17296) with
| (a1, subst2, bvs1, g) -> begin
(

let uu____17493 = (

let uu____17516 = (FStar_TypeChecker_Env.conj_guard g guard)
in ((subst2), ((FStar_List.append args_out ((a1)::[]))), (bvs1), (uu____17516)))
in (aux uu____17493 formals2 args2))
end)))
end
| uu____17555 -> begin
(fail1 "Not a fully applued pattern")
end)
end))
in (aux (([]), ([]), ([]), (FStar_TypeChecker_Env.trivial_guard)) formals args));
)
end))
end))
end
| uu____17610 -> begin
(fail1 "Not a simple pattern")
end)
end)))
in (

let rec check_nested_pattern = (fun env1 p t -> ((

let uu____17658 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Patterns")))
in (match (uu____17658) with
| true -> begin
(

let uu____17659 = (FStar_Syntax_Print.pat_to_string p)
in (

let uu____17660 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checking pattern %s at type %s\n" uu____17659 uu____17660)))
end
| uu____17661 -> begin
()
end));
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____17672) -> begin
(

let uu____17679 = (

let uu____17680 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Impossible: Expected an undecorated pattern, got %s" uu____17680))
in (failwith uu____17679))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___382_17693 = x
in {FStar_Syntax_Syntax.ppname = uu___382_17693.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___382_17693.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let uu____17694 = (FStar_Syntax_Syntax.bv_to_name x1)
in (((x1)::[]), (uu____17694), ((

let uu___383_17698 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___383_17698.FStar_Syntax_Syntax.p})), (FStar_TypeChecker_Env.trivial_guard))))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___384_17701 = x
in {FStar_Syntax_Syntax.ppname = uu___384_17701.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___384_17701.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let uu____17702 = (FStar_Syntax_Syntax.bv_to_name x1)
in (((x1)::[]), (uu____17702), ((

let uu___385_17706 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___385_17706.FStar_Syntax_Syntax.p})), (FStar_TypeChecker_Env.trivial_guard))))
end
| FStar_Syntax_Syntax.Pat_constant (uu____17707) -> begin
(

let uu____17708 = (FStar_TypeChecker_PatternUtils.pat_as_exp false env1 p)
in (match (uu____17708) with
| (uu____17729, e_c, uu____17731, uu____17732) -> begin
(

let uu____17737 = (tc_tot_or_gtot_term env1 e_c)
in (match (uu____17737) with
| (e_c1, lc, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g);
(

let expected_t = (expected_pat_typ env1 p0.FStar_Syntax_Syntax.p t)
in ((

let uu____17760 = (

let uu____17761 = (FStar_TypeChecker_Rel.teq_nosmt_force env1 lc.FStar_Syntax_Syntax.res_typ expected_t)
in (not (uu____17761)))
in (match (uu____17760) with
| true -> begin
(

let uu____17762 = (

let uu____17763 = (FStar_Syntax_Print.term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____17764 = (FStar_Syntax_Print.term_to_string expected_t)
in (FStar_Util.format2 "Type of pattern (%s) does not match type of scrutinee (%s)" uu____17763 uu____17764)))
in (fail1 uu____17762))
end
| uu____17765 -> begin
()
end));
(([]), (e_c1), (p), (FStar_TypeChecker_Env.trivial_guard));
));
)
end))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, sub_pats) -> begin
(

let simple_pat = (

let simple_sub_pats = (FStar_List.map (fun uu____17814 -> (match (uu____17814) with
| (p1, b) -> begin
(match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____17839) -> begin
((p1), (b))
end
| uu____17848 -> begin
(

let uu____17849 = (

let uu____17852 = (

let uu____17853 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_var (uu____17853))
in (FStar_Syntax_Syntax.withinfo uu____17852 p1.FStar_Syntax_Syntax.p))
in ((uu____17849), (b)))
end)
end)) sub_pats)
in (

let uu___386_17856 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), (simple_sub_pats))); FStar_Syntax_Syntax.p = uu___386_17856.FStar_Syntax_Syntax.p}))
in (

let sub_pats1 = (FStar_All.pipe_right sub_pats (FStar_List.filter (fun uu____17896 -> (match (uu____17896) with
| (x, uu____17904) -> begin
(match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____17909) -> begin
false
end
| uu____17916 -> begin
true
end)
end))))
in (

let uu____17917 = (FStar_TypeChecker_PatternUtils.pat_as_exp false env1 simple_pat)
in (match (uu____17917) with
| (simple_bvs, simple_pat_e, g0, simple_pat_elab) -> begin
((match ((Prims.op_disEquality (FStar_List.length simple_bvs) (FStar_List.length sub_pats1))) with
| true -> begin
(

let uu____17951 = (

let uu____17952 = (FStar_Range.string_of_range p.FStar_Syntax_Syntax.p)
in (

let uu____17953 = (FStar_Syntax_Print.pat_to_string simple_pat)
in (

let uu____17954 = (FStar_Util.string_of_int (FStar_List.length sub_pats1))
in (

let uu____17959 = (FStar_Util.string_of_int (FStar_List.length simple_bvs))
in (FStar_Util.format4 "(%s) Impossible: pattern bvar mismatch: %s; expected %s sub pats; got %s" uu____17952 uu____17953 uu____17954 uu____17959)))))
in (failwith uu____17951))
end
| uu____17960 -> begin
()
end);
(

let uu____17961 = (

let uu____17970 = (type_of_simple_pat env1 simple_pat_e)
in (match (uu____17970) with
| (simple_pat_e1, simple_pat_t, simple_bvs1, guard) -> begin
(

let g' = (

let uu____17998 = (expected_pat_typ env1 p0.FStar_Syntax_Syntax.p t)
in (pat_typ_ok env1 simple_pat_t uu____17998))
in (

let guard1 = (FStar_TypeChecker_Env.conj_guard guard g')
in ((

let uu____18001 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("Patterns")))
in (match (uu____18001) with
| true -> begin
(

let uu____18002 = (FStar_Syntax_Print.term_to_string simple_pat_e1)
in (

let uu____18003 = (FStar_Syntax_Print.term_to_string simple_pat_t)
in (

let uu____18004 = (

let uu____18005 = (FStar_List.map (fun x -> (

let uu____18011 = (

let uu____18012 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____18013 = (

let uu____18014 = (

let uu____18015 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (Prims.strcat uu____18015 ")"))
in (Prims.strcat " : " uu____18014))
in (Prims.strcat uu____18012 uu____18013)))
in (Prims.strcat "(" uu____18011))) simple_bvs1)
in (FStar_All.pipe_right uu____18005 (FStar_String.concat " ")))
in (FStar_Util.print3 "$$$$$$$$$$$$Checked simple pattern %s at type %s with bvs=%s\n" uu____18002 uu____18003 uu____18004))))
end
| uu____18018 -> begin
()
end));
((simple_pat_e1), (simple_bvs1), (guard1));
)))
end))
in (match (uu____17961) with
| (simple_pat_e1, simple_bvs1, g1) -> begin
(

let uu____18038 = (

let uu____18059 = (

let uu____18080 = (FStar_TypeChecker_Env.conj_guard g0 g1)
in ((env1), ([]), ([]), ([]), (uu____18080)))
in (FStar_List.fold_left2 (fun uu____18137 uu____18138 x -> (match (((uu____18137), (uu____18138))) with
| ((env2, bvs, pats, subst1, g), (p1, b)) -> begin
(

let expected_t = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in (

let uu____18260 = (check_nested_pattern env2 p1 expected_t)
in (match (uu____18260) with
| (bvs_p, e_p, p2, g') -> begin
(

let env3 = (FStar_TypeChecker_Env.push_bvs env2 bvs_p)
in (

let uu____18300 = (FStar_TypeChecker_Env.conj_guard g g')
in ((env3), ((FStar_List.append bvs bvs_p)), ((FStar_List.append pats ((((p2), (b)))::[]))), ((FStar_Syntax_Syntax.NT (((x), (e_p))))::subst1), (uu____18300))))
end)))
end)) uu____18059 sub_pats1 simple_bvs1))
in (match (uu____18038) with
| (_env, bvs, checked_sub_pats, subst1, g) -> begin
(

let pat_e = (FStar_Syntax_Subst.subst subst1 simple_pat_e1)
in (

let reconstruct_nested_pat = (fun pat -> (

let rec aux = (fun simple_pats bvs1 sub_pats2 -> (match (simple_pats) with
| [] -> begin
[]
end
| ((hd1, b))::simple_pats1 -> begin
(match (hd1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(

let e1 = (FStar_Syntax_Subst.subst subst1 e)
in (

let hd2 = (

let uu___387_18492 = hd1
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (e1))); FStar_Syntax_Syntax.p = uu___387_18492.FStar_Syntax_Syntax.p})
in (

let uu____18497 = (aux simple_pats1 bvs1 sub_pats2)
in (((hd2), (b)))::uu____18497)))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(match (((bvs1), (sub_pats2))) with
| ((x')::bvs2, ((hd2, uu____18536))::sub_pats3) when (FStar_Syntax_Syntax.bv_eq x x') -> begin
(

let uu____18568 = (aux simple_pats1 bvs2 sub_pats3)
in (((hd2), (b)))::uu____18568)
end
| uu____18585 -> begin
(failwith "Impossible: simple pat variable mismatch")
end)
end
| uu____18608 -> begin
(failwith "Impossible: expected a simple pattern")
end)
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv1, simple_pats) -> begin
(

let nested_pats = (aux simple_pats simple_bvs1 checked_sub_pats)
in (

let uu___388_18646 = pat
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv1), (nested_pats))); FStar_Syntax_Syntax.p = uu___388_18646.FStar_Syntax_Syntax.p}))
end
| uu____18657 -> begin
(failwith "Impossible")
end)))
in (

let uu____18660 = (reconstruct_nested_pat simple_pat_elab)
in ((bvs), (pat_e), (uu____18660), (g)))))
end))
end));
)
end))))
end);
))
in ((

let uu____18664 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Patterns")))
in (match (uu____18664) with
| true -> begin
(

let uu____18665 = (FStar_Syntax_Print.pat_to_string p0)
in (FStar_Util.print1 "Checking pattern: %s\n" uu____18665))
end
| uu____18666 -> begin
()
end));
(

let uu____18667 = (

let uu____18678 = (

let uu___389_18679 = (

let uu____18680 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right uu____18680 FStar_Pervasives_Native.fst))
in {FStar_TypeChecker_Env.solver = uu___389_18679.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___389_18679.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___389_18679.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___389_18679.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___389_18679.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___389_18679.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___389_18679.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___389_18679.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___389_18679.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___389_18679.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___389_18679.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___389_18679.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___389_18679.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___389_18679.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___389_18679.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___389_18679.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___389_18679.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = true; FStar_TypeChecker_Env.is_iface = uu___389_18679.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___389_18679.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___389_18679.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___389_18679.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___389_18679.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___389_18679.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___389_18679.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___389_18679.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___389_18679.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___389_18679.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___389_18679.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___389_18679.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___389_18679.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___389_18679.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___389_18679.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___389_18679.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___389_18679.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___389_18679.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___389_18679.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___389_18679.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___389_18679.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___389_18679.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___389_18679.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___389_18679.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___389_18679.FStar_TypeChecker_Env.nbe})
in (

let uu____18695 = (FStar_TypeChecker_PatternUtils.elaborate_pat env p0)
in (check_nested_pattern uu____18678 uu____18695 pat_t)))
in (match (uu____18667) with
| (bvs, pat_e, pat, g) -> begin
((

let uu____18719 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Patterns")))
in (match (uu____18719) with
| true -> begin
(

let uu____18720 = (FStar_Syntax_Print.pat_to_string pat)
in (

let uu____18721 = (FStar_Syntax_Print.term_to_string pat_e)
in (FStar_Util.print2 "Done checking pattern %s as expression %s\n" uu____18720 uu____18721)))
end
| uu____18722 -> begin
()
end));
(

let uu____18723 = (FStar_TypeChecker_Env.push_bvs env bvs)
in (

let uu____18724 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env pat_e)
in ((pat), (bvs), (uu____18723), (pat_e), (uu____18724), (g))));
)
end));
)))))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list * (Prims.bool  ->  FStar_Syntax_Syntax.lcomp) * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch1 -> (

let uu____18769 = (FStar_Syntax_Subst.open_branch branch1)
in (match (uu____18769) with
| (pattern, when_clause, branch_exp) -> begin
(

let uu____18814 = branch1
in (match (uu____18814) with
| (cpat, uu____18855, cbr) -> begin
(

let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (

let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (

let uu____18877 = (

let uu____18884 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right uu____18884 FStar_TypeChecker_Env.clear_expected_typ))
in (match (uu____18877) with
| (scrutinee_env, uu____18917) -> begin
(

let uu____18922 = (tc_pat env pat_t pattern)
in (match (uu____18922) with
| (pattern1, pat_bvs1, pat_env, pat_exp, norm_pat_exp, guard_pat) -> begin
(

let uu____18972 = (match (when_clause) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_TypeChecker_Env.trivial_guard))
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____19002 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____19002) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_WhenClauseNotSupported), ("When clauses are not yet supported in --verify mode; they will be some day")) e.FStar_Syntax_Syntax.pos)
end
| uu____19019 -> begin
(

let uu____19020 = (

let uu____19027 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_Syntax_Util.t_bool)
in (tc_term uu____19027 e))
in (match (uu____19020) with
| (e1, c, g) -> begin
((FStar_Pervasives_Native.Some (e1)), (g))
end))
end))
end)
in (match (uu____18972) with
| (when_clause1, g_when) -> begin
(

let uu____19080 = (tc_term pat_env branch_exp)
in (match (uu____19080) with
| (branch_exp1, c, g_branch) -> begin
((FStar_TypeChecker_Env.def_check_guard_wf cbr.FStar_Syntax_Syntax.pos "tc_eqn.1" pat_env g_branch);
(

let when_condition = (match (when_clause1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____19134 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero FStar_Syntax_Util.t_bool w FStar_Syntax_Util.exp_true_bool)
in (FStar_All.pipe_left (fun _0_2 -> FStar_Pervasives_Native.Some (_0_2)) uu____19134))
end)
in (

let uu____19145 = (

let eqs = (

let uu____19166 = (

let uu____19167 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____19167)))
in (match (uu____19166) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____19174 -> begin
(

let e = (FStar_Syntax_Subst.compress pat_exp)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____19180) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_constant (uu____19195) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_fvar (uu____19198) -> begin
FStar_Pervasives_Native.None
end
| uu____19201 -> begin
(

let uu____19202 = (

let uu____19205 = (env.FStar_TypeChecker_Env.universe_of env pat_t)
in (FStar_Syntax_Util.mk_eq2 uu____19205 pat_t scrutinee_tm e))
in FStar_Pervasives_Native.Some (uu____19202))
end))
end))
in (

let uu____19208 = (FStar_TypeChecker_Util.strengthen_precondition FStar_Pervasives_Native.None env branch_exp1 c g_branch)
in (match (uu____19208) with
| (c1, g_branch1) -> begin
(

let uu____19233 = (match (((eqs), (when_condition))) with
| uu____19250 when (

let uu____19263 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____19263))) -> begin
((c1), (g_when))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
((c1), (g_when))
end
| (FStar_Pervasives_Native.Some (f), FStar_Pervasives_Native.None) -> begin
(

let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g = (FStar_TypeChecker_Env.guard_of_guard_formula gf)
in (

let uu____19293 = (FStar_TypeChecker_Util.weaken_precondition env c1 gf)
in (

let uu____19294 = (FStar_TypeChecker_Env.imp_guard g g_when)
in ((uu____19293), (uu____19294))))))
end
| (FStar_Pervasives_Native.Some (f), FStar_Pervasives_Native.Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (

let uu____19315 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (uu____19315))
in (

let uu____19316 = (FStar_TypeChecker_Util.weaken_precondition env c1 g_fw)
in (

let uu____19317 = (

let uu____19318 = (FStar_TypeChecker_Env.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Env.imp_guard uu____19318 g_when))
in ((uu____19316), (uu____19317))))))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Env.guard_of_guard_formula g_w)
in (

let uu____19336 = (FStar_TypeChecker_Util.weaken_precondition env c1 g_w)
in ((uu____19336), (g_when)))))
end)
in (match (uu____19233) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs1)
in (

let maybe_return_c_weak = (fun should_return1 -> (

let c_weak1 = (

let uu____19376 = (should_return1 && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c_weak))
in (match (uu____19376) with
| true -> begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env branch_exp1 c_weak)
end
| uu____19377 -> begin
c_weak
end))
in (FStar_TypeChecker_Util.close_lcomp env pat_bvs1 c_weak1)))
in (

let uu____19378 = (FStar_TypeChecker_Env.close_guard env binders g_when_weak)
in (

let uu____19379 = (FStar_TypeChecker_Env.conj_guard guard_pat g_branch1)
in ((c_weak.FStar_Syntax_Syntax.eff_name), (c_weak.FStar_Syntax_Syntax.cflags), (maybe_return_c_weak), (uu____19378), (uu____19379))))))
end))
end)))
in (match (uu____19145) with
| (effect_label, cflags, maybe_return_c, g_when1, g_branch1) -> begin
(

let branch_guard = (

let uu____19426 = (

let uu____19427 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____19427)))
in (match (uu____19426) with
| true -> begin
FStar_Syntax_Util.t_true
end
| uu____19428 -> begin
(

let rec build_branch_guard = (fun scrutinee_tm1 pat_exp1 -> (

let discriminate = (fun scrutinee_tm2 f -> (

let uu____19469 = (

let uu____19476 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env uu____19476))
in (match (uu____19469) with
| (is_induc, datacons) -> begin
(match (((not (is_induc)) || ((FStar_List.length datacons) > (Prims.parse_int "1")))) with
| true -> begin
(

let discriminator = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (

let uu____19488 = (FStar_TypeChecker_Env.try_lookup_lid env discriminator)
in (match (uu____19488) with
| FStar_Pervasives_Native.None -> begin
[]
end
| uu____19509 -> begin
(

let disc = (FStar_Syntax_Syntax.fvar discriminator (FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let disc1 = (

let uu____19524 = (

let uu____19529 = (

let uu____19530 = (FStar_Syntax_Syntax.as_arg scrutinee_tm2)
in (uu____19530)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc uu____19529))
in (uu____19524 FStar_Pervasives_Native.None scrutinee_tm2.FStar_Syntax_Syntax.pos))
in (

let uu____19557 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero FStar_Syntax_Util.t_bool disc1 FStar_Syntax_Util.exp_true_bool)
in (uu____19557)::[])))
end)))
end
| uu____19558 -> begin
[]
end)
end)))
in (

let fail1 = (fun uu____19564 -> (

let uu____19565 = (

let uu____19566 = (FStar_Range.string_of_range pat_exp1.FStar_Syntax_Syntax.pos)
in (

let uu____19567 = (FStar_Syntax_Print.term_to_string pat_exp1)
in (

let uu____19568 = (FStar_Syntax_Print.tag_of_term pat_exp1)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" uu____19566 uu____19567 uu____19568))))
in (failwith uu____19565)))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____19581) -> begin
(head_constructor t1)
end
| uu____19586 -> begin
(fail1 ())
end))
in (

let pat_exp2 = (

let uu____19590 = (FStar_Syntax_Subst.compress pat_exp1)
in (FStar_All.pipe_right uu____19590 FStar_Syntax_Util.unmeta))
in (match (pat_exp2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____19595) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____19608); FStar_Syntax_Syntax.pos = uu____19609; FStar_Syntax_Syntax.vars = uu____19610}, uu____19611) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_name (uu____19648) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (c1) -> begin
(

let uu____19650 = (

let uu____19651 = (tc_constant env pat_exp2.FStar_Syntax_Syntax.pos c1)
in (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero uu____19651 scrutinee_tm1 pat_exp2))
in (uu____19650)::[])
end
| FStar_Syntax_Syntax.Tm_uinst (uu____19652) -> begin
(

let f = (head_constructor pat_exp2)
in (

let uu____19660 = (

let uu____19661 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____19661)))
in (match (uu____19660) with
| true -> begin
[]
end
| uu____19664 -> begin
(

let uu____19665 = (head_constructor pat_exp2)
in (discriminate scrutinee_tm1 uu____19665))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____19668) -> begin
(

let f = (head_constructor pat_exp2)
in (

let uu____19670 = (

let uu____19671 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____19671)))
in (match (uu____19670) with
| true -> begin
[]
end
| uu____19674 -> begin
(

let uu____19675 = (head_constructor pat_exp2)
in (discriminate scrutinee_tm1 uu____19675))
end)))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let f = (head_constructor head1)
in (

let uu____19705 = (

let uu____19706 = (FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v)
in (not (uu____19706)))
in (match (uu____19705) with
| true -> begin
[]
end
| uu____19709 -> begin
(

let sub_term_guards = (

let uu____19713 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____19749 -> (match (uu____19749) with
| (ei, uu____19761) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (

let uu____19771 = (FStar_TypeChecker_Env.try_lookup_lid env projector)
in (match (uu____19771) with
| FStar_Pervasives_Native.None -> begin
[]
end
| uu____19792 -> begin
(

let sub_term = (

let uu____19806 = (

let uu____19811 = (

let uu____19812 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar uu____19812 (FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
in (

let uu____19813 = (

let uu____19814 = (FStar_Syntax_Syntax.as_arg scrutinee_tm1)
in (uu____19814)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____19811 uu____19813)))
in (uu____19806 FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.p))
in (build_branch_guard sub_term ei))
end)))
end))))
in (FStar_All.pipe_right uu____19713 FStar_List.flatten))
in (

let uu____19847 = (discriminate scrutinee_tm1 f)
in (FStar_List.append uu____19847 sub_term_guards)))
end)))
end
| uu____19850 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm1 pat -> (

let uu____19866 = (

let uu____19867 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____19867)))
in (match (uu____19866) with
| true -> begin
(FStar_TypeChecker_Util.fvar_const env FStar_Parser_Const.true_lid)
end
| uu____19868 -> begin
(

let t = (

let uu____19870 = (build_branch_guard scrutinee_tm1 pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l uu____19870))
in (

let uu____19879 = (FStar_Syntax_Util.type_u ())
in (match (uu____19879) with
| (k, uu____19885) -> begin
(

let uu____19886 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (uu____19886) with
| (t1, uu____19894, uu____19895) -> begin
t1
end))
end)))
end)))
in (

let branch_guard = (build_and_check_branch_guard scrutinee_tm norm_pat_exp)
in (

let branch_guard1 = (match (when_condition) with
| FStar_Pervasives_Native.None -> begin
branch_guard
end
| FStar_Pervasives_Native.Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard1))))
end))
in (

let guard = (FStar_TypeChecker_Env.conj_guard g_when1 g_branch1)
in ((

let uu____19907 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____19907) with
| true -> begin
(

let uu____19908 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") uu____19908))
end
| uu____19909 -> begin
()
end));
(

let uu____19910 = (FStar_Syntax_Subst.close_branch ((pattern1), (when_clause1), (branch_exp1)))
in (

let uu____19927 = (

let uu____19928 = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs1)
in (FStar_TypeChecker_Util.close_guard_implicits env uu____19928 guard))
in ((uu____19910), (branch_guard), (effect_label), (cflags), (maybe_return_c), (uu____19927))));
)))
end)));
)
end))
end))
end))
end))))
end))
end)))
and check_top_level_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env1 = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let uu____19971 = (check_let_bound_def true env1 lb)
in (match (uu____19971) with
| (e1, univ_vars1, c1, g1, annotated) -> begin
(

let uu____19993 = (match ((annotated && (not (env1.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____20014 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env1 e1)
in ((g1), (uu____20014), (univ_vars1), (c1)))
end
| uu____20017 -> begin
(

let g11 = (

let uu____20019 = (FStar_TypeChecker_Rel.solve_deferred_constraints env1 g1)
in (FStar_All.pipe_right uu____20019 (FStar_TypeChecker_Rel.resolve_implicits env1)))
in (

let uu____20021 = (

let uu____20034 = (

let uu____20049 = (

let uu____20058 = (

let uu____20065 = (FStar_Syntax_Syntax.lcomp_comp c1)
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (uu____20065)))
in (uu____20058)::[])
in (FStar_TypeChecker_Util.generalize env1 false uu____20049))
in (FStar_List.hd uu____20034))
in (match (uu____20021) with
| (uu____20100, univs1, e11, c11, gvs) -> begin
(

let g12 = (FStar_All.pipe_left (FStar_TypeChecker_Env.map_guard g11) (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::(FStar_TypeChecker_Env.CompressUvars)::(FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::[]) env1))
in (

let g13 = (FStar_TypeChecker_Env.abstract_guard_n gvs g12)
in (

let uu____20114 = (FStar_Syntax_Util.lcomp_of_comp c11)
in ((g13), (e11), (univs1), (uu____20114)))))
end)))
end)
in (match (uu____19993) with
| (g11, e11, univ_vars2, c11) -> begin
(

let uu____20131 = (

let uu____20140 = (FStar_TypeChecker_Env.should_verify env1)
in (match (uu____20140) with
| true -> begin
(

let uu____20149 = (FStar_TypeChecker_Util.check_top_level env1 g11 c11)
in (match (uu____20149) with
| (ok, c12) -> begin
(match (ok) with
| true -> begin
((e2), (c12))
end
| uu____20176 -> begin
((

let uu____20178 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.log_issue uu____20178 FStar_TypeChecker_Err.top_level_effect));
(

let uu____20179 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos)
in ((uu____20179), (c12)));
)
end)
end))
end
| uu____20188 -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g11);
(

let c = (

let uu____20193 = (FStar_Syntax_Syntax.lcomp_comp c11)
in (FStar_All.pipe_right uu____20193 (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::[]) env1)))
in (

let e21 = (

let uu____20199 = (FStar_Syntax_Util.is_pure_comp c)
in (match (uu____20199) with
| true -> begin
e2
end
| uu____20202 -> begin
((

let uu____20204 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.log_issue uu____20204 FStar_TypeChecker_Err.top_level_effect));
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) FStar_Pervasives_Native.None e2.FStar_Syntax_Syntax.pos);
)
end))
in ((e21), (c))));
)
end))
in (match (uu____20131) with
| (e21, c12) -> begin
((

let uu____20228 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Medium)
in (match (uu____20228) with
| true -> begin
(

let uu____20229 = (FStar_Syntax_Print.term_to_string e11)
in (FStar_Util.print1 "Let binding BEFORE tcnorm: %s\n" uu____20229))
end
| uu____20230 -> begin
()
end));
(

let e12 = (

let uu____20232 = (FStar_Options.tcnorm ())
in (match (uu____20232) with
| true -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldAttr ((FStar_Parser_Const.tcnorm_attr)::[]))::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta))::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::(FStar_TypeChecker_Env.NoFullNorm)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::[]) env1 e11)
end
| uu____20233 -> begin
e11
end))
in ((

let uu____20235 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Medium)
in (match (uu____20235) with
| true -> begin
(

let uu____20236 = (FStar_Syntax_Print.term_to_string e12)
in (FStar_Util.print1 "Let binding AFTER tcnorm: %s\n" uu____20236))
end
| uu____20237 -> begin
()
end));
(

let cres = (FStar_TypeChecker_Env.null_wp_for_eff env1 (FStar_Syntax_Util.comp_effect_name c12) FStar_Syntax_Syntax.U_zero FStar_Syntax_Syntax.t_unit)
in (

let lb1 = (FStar_Syntax_Util.close_univs_and_mk_letbinding FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbname univ_vars2 (FStar_Syntax_Util.comp_result c12) (FStar_Syntax_Util.comp_effect_name c12) e12 lb.FStar_Syntax_Syntax.lbattrs lb.FStar_Syntax_Syntax.lbpos)
in (

let uu____20242 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (e21)))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (

let uu____20253 = (FStar_Syntax_Util.lcomp_of_comp cres)
in ((uu____20242), (uu____20253), (FStar_TypeChecker_Env.trivial_guard))))));
));
)
end))
end))
end))
end
| uu____20254 -> begin
(failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env1 = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env2 = (

let uu___390_20285 = env1
in {FStar_TypeChecker_Env.solver = uu___390_20285.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___390_20285.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___390_20285.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___390_20285.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___390_20285.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___390_20285.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___390_20285.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___390_20285.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___390_20285.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___390_20285.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___390_20285.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___390_20285.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___390_20285.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___390_20285.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___390_20285.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___390_20285.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___390_20285.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___390_20285.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___390_20285.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___390_20285.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___390_20285.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___390_20285.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___390_20285.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___390_20285.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___390_20285.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___390_20285.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___390_20285.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___390_20285.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___390_20285.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___390_20285.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___390_20285.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___390_20285.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___390_20285.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___390_20285.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___390_20285.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___390_20285.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___390_20285.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___390_20285.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___390_20285.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___390_20285.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___390_20285.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___390_20285.FStar_TypeChecker_Env.nbe})
in (

let uu____20286 = (

let uu____20297 = (

let uu____20298 = (FStar_TypeChecker_Env.clear_expected_typ env2)
in (FStar_All.pipe_right uu____20298 FStar_Pervasives_Native.fst))
in (check_let_bound_def false uu____20297 lb))
in (match (uu____20286) with
| (e1, uu____20320, c1, g1, annotated) -> begin
((

let uu____20325 = ((FStar_Util.for_some (FStar_Syntax_Util.is_fvar FStar_Parser_Const.inline_let_attr) lb.FStar_Syntax_Syntax.lbattrs) && (

let uu____20329 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp c1)
in (not (uu____20329))))
in (match (uu____20325) with
| true -> begin
(

let uu____20330 = (

let uu____20335 = (

let uu____20336 = (FStar_Syntax_Print.term_to_string e1)
in (

let uu____20337 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.eff_name)
in (FStar_Util.format2 "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\"" uu____20336 uu____20337)))
in ((FStar_Errors.Fatal_ExpectedPureExpression), (uu____20335)))
in (FStar_Errors.raise_error uu____20330 e1.FStar_Syntax_Syntax.pos))
end
| uu____20338 -> begin
()
end));
(

let x = (

let uu___391_20340 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___391_20340.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___391_20340.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let uu____20341 = (

let uu____20346 = (

let uu____20347 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____20347)::[])
in (FStar_Syntax_Subst.open_term uu____20346 e2))
in (match (uu____20341) with
| (xb, e21) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x1 = (FStar_Pervasives_Native.fst xbinder)
in (

let env_x = (FStar_TypeChecker_Env.push_bv env2 x1)
in (

let uu____20391 = (tc_term env_x e21)
in (match (uu____20391) with
| (e22, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.maybe_return_e2_and_bind e1.FStar_Syntax_Syntax.pos env2 (FStar_Pervasives_Native.Some (e1)) c1 e22 ((FStar_Pervasives_Native.Some (x1)), (c2)))
in (

let e11 = (FStar_TypeChecker_Util.maybe_lift env2 e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name c1.FStar_Syntax_Syntax.res_typ)
in (

let e23 = (FStar_TypeChecker_Util.maybe_lift env2 e22 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.res_typ)
in (

let lb1 = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x1)) [] c1.FStar_Syntax_Syntax.res_typ cres.FStar_Syntax_Syntax.eff_name e11 lb.FStar_Syntax_Syntax.lbattrs lb.FStar_Syntax_Syntax.lbpos)
in (

let e3 = (

let uu____20416 = (

let uu____20423 = (

let uu____20424 = (

let uu____20437 = (FStar_Syntax_Subst.close xb e23)
in ((((false), ((lb1)::[]))), (uu____20437)))
in FStar_Syntax_Syntax.Tm_let (uu____20424))
in (FStar_Syntax_Syntax.mk uu____20423))
in (uu____20416 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
in (

let e4 = (FStar_TypeChecker_Util.maybe_monadic env2 e3 cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (

let uu____20455 = (

let uu____20456 = (env2.FStar_TypeChecker_Env.universe_of env2 c1.FStar_Syntax_Syntax.res_typ)
in (

let uu____20457 = (FStar_Syntax_Syntax.bv_to_name x1)
in (FStar_Syntax_Util.mk_eq2 uu____20456 c1.FStar_Syntax_Syntax.res_typ uu____20457 e11)))
in (FStar_All.pipe_left (fun _0_3 -> FStar_TypeChecker_Common.NonTrivial (_0_3)) uu____20455))
in (

let g21 = (

let uu____20459 = (

let uu____20460 = (FStar_TypeChecker_Env.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Env.imp_guard uu____20460 g2))
in (FStar_TypeChecker_Env.close_guard env2 xb uu____20459))
in (

let g22 = (FStar_TypeChecker_Util.close_guard_implicits env2 xb g21)
in (

let guard = (FStar_TypeChecker_Env.conj_guard g1 g22)
in (

let uu____20463 = (

let uu____20464 = (FStar_TypeChecker_Env.expected_typ env2)
in (FStar_Option.isSome uu____20464))
in (match (uu____20463) with
| true -> begin
(

let tt = (

let uu____20474 = (FStar_TypeChecker_Env.expected_typ env2)
in (FStar_All.pipe_right uu____20474 FStar_Option.get))
in ((

let uu____20480 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Exports")))
in (match (uu____20480) with
| true -> begin
(

let uu____20481 = (FStar_Syntax_Print.term_to_string tt)
in (

let uu____20482 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Got expected type from env %s\ncres.res_typ=%s\n" uu____20481 uu____20482)))
end
| uu____20483 -> begin
()
end));
((e4), (cres), (guard));
))
end
| uu____20484 -> begin
(

let uu____20485 = (check_no_escape FStar_Pervasives_Native.None env2 ((x1)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (match (uu____20485) with
| (t, g_ex) -> begin
((

let uu____20499 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("Exports")))
in (match (uu____20499) with
| true -> begin
(

let uu____20500 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (

let uu____20501 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checked %s has no escaping types; normalized to %s\n" uu____20500 uu____20501)))
end
| uu____20502 -> begin
()
end));
(

let uu____20503 = (FStar_TypeChecker_Env.conj_guard g_ex guard)
in ((e4), ((

let uu___392_20505 = cres
in {FStar_Syntax_Syntax.eff_name = uu___392_20505.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu___392_20505.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___392_20505.FStar_Syntax_Syntax.comp_thunk})), (uu____20503)));
)
end))
end))))))))))))
end)))))
end)));
)
end)))
end
| uu____20506 -> begin
(failwith "Impossible (inner let with more than one lb)")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env1 = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____20538 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____20538) with
| (lbs1, e21) -> begin
(

let uu____20557 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____20557) with
| (env0, topt) -> begin
(

let uu____20576 = (build_let_rec_env true env0 lbs1)
in (match (uu____20576) with
| (lbs2, rec_env, g_t) -> begin
(

let uu____20598 = (check_let_recs rec_env lbs2)
in (match (uu____20598) with
| (lbs3, g_lbs) -> begin
(

let g_lbs1 = (

let uu____20618 = (

let uu____20619 = (FStar_TypeChecker_Env.conj_guard g_t g_lbs)
in (FStar_All.pipe_right uu____20619 (FStar_TypeChecker_Rel.solve_deferred_constraints env1)))
in (FStar_All.pipe_right uu____20618 (FStar_TypeChecker_Rel.resolve_implicits env1)))
in (

let all_lb_names = (

let uu____20625 = (FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____20625 (fun _0_4 -> FStar_Pervasives_Native.Some (_0_4))))
in (

let lbs4 = (match ((not (env1.FStar_TypeChecker_Env.generalize))) with
| true -> begin
(FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (

let lbdef = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env1 lb.FStar_Syntax_Syntax.lbdef)
in (match ((Prims.op_Equality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
lb
end
| uu____20657 -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lbdef lb.FStar_Syntax_Syntax.lbattrs lb.FStar_Syntax_Syntax.lbpos)
end)))))
end
| uu____20658 -> begin
(

let ecs = (

let uu____20674 = (FStar_All.pipe_right lbs3 (FStar_List.map (fun lb -> (

let uu____20708 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (uu____20708))))))
in (FStar_TypeChecker_Util.generalize env1 true uu____20674))
in (FStar_List.map2 (fun uu____20742 lb -> (match (uu____20742) with
| (x, uvs, e, c, gvs) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e lb.FStar_Syntax_Syntax.lbattrs lb.FStar_Syntax_Syntax.lbpos)
end)) ecs lbs3))
end)
in (

let cres = (

let uu____20790 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____20790))
in (

let uu____20791 = (FStar_Syntax_Subst.close_let_rec lbs4 e21)
in (match (uu____20791) with
| (lbs5, e22) -> begin
((

let uu____20811 = (FStar_TypeChecker_Rel.discharge_guard env1 g_lbs1)
in (FStar_All.pipe_right uu____20811 (FStar_TypeChecker_Rel.force_trivial_guard env1)));
(

let uu____20812 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs5))), (e22)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in ((uu____20812), (cres), (FStar_TypeChecker_Env.trivial_guard)));
)
end))))))
end))
end))
end))
end))
end
| uu____20823 -> begin
(failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env1 = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let uu____20855 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (uu____20855) with
| (lbs1, e21) -> begin
(

let uu____20874 = (FStar_TypeChecker_Env.clear_expected_typ env1)
in (match (uu____20874) with
| (env0, topt) -> begin
(

let uu____20893 = (build_let_rec_env false env0 lbs1)
in (match (uu____20893) with
| (lbs2, rec_env, g_t) -> begin
(

let uu____20915 = (

let uu____20922 = (check_let_recs rec_env lbs2)
in (FStar_All.pipe_right uu____20922 (fun uu____20945 -> (match (uu____20945) with
| (lbs3, g) -> begin
(

let uu____20964 = (FStar_TypeChecker_Env.conj_guard g_t g)
in ((lbs3), (uu____20964)))
end))))
in (match (uu____20915) with
| (lbs3, g_lbs) -> begin
(

let uu____20979 = (FStar_All.pipe_right lbs3 (FStar_Util.fold_map (fun env2 lb -> (

let x = (

let uu___393_21002 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___393_21002.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___393_21002.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb1 = (

let uu___394_21004 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___394_21004.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___394_21004.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___394_21004.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___394_21004.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___394_21004.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___394_21004.FStar_Syntax_Syntax.lbpos})
in (

let env3 = (FStar_TypeChecker_Env.push_let_binding env2 lb1.FStar_Syntax_Syntax.lbname (([]), (lb1.FStar_Syntax_Syntax.lbtyp)))
in ((env3), (lb1)))))) env1))
in (match (uu____20979) with
| (env2, lbs4) -> begin
(

let bvs = (FStar_All.pipe_right lbs4 (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let uu____21031 = (tc_term env2 e21)
in (match (uu____21031) with
| (e22, cres, g2) -> begin
(

let cres1 = (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env2 e22 cres)
in (

let cres2 = (FStar_Syntax_Util.lcomp_set_flags cres1 ((FStar_Syntax_Syntax.SHOULD_NOT_INLINE)::[]))
in (

let guard = (

let uu____21050 = (

let uu____21051 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (FStar_TypeChecker_Env.close_guard env2 uu____21051 g2))
in (FStar_TypeChecker_Env.conj_guard g_lbs uu____21050))
in (

let cres3 = (FStar_TypeChecker_Util.close_lcomp env2 bvs cres2)
in (

let tres = (norm env2 cres3.FStar_Syntax_Syntax.res_typ)
in (

let cres4 = (

let uu___395_21061 = cres3
in {FStar_Syntax_Syntax.eff_name = uu___395_21061.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = uu___395_21061.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___395_21061.FStar_Syntax_Syntax.comp_thunk})
in (

let guard1 = (

let bs = (FStar_All.pipe_right lbs4 (FStar_List.map (fun lb -> (

let uu____21069 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.mk_binder uu____21069)))))
in (FStar_TypeChecker_Util.close_guard_implicits env2 bs guard))
in (

let uu____21070 = (FStar_Syntax_Subst.close_let_rec lbs4 e22)
in (match (uu____21070) with
| (lbs5, e23) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs5))), (e23)))) FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| FStar_Pervasives_Native.Some (uu____21108) -> begin
((e), (cres4), (guard1))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____21109 = (check_no_escape FStar_Pervasives_Native.None env2 bvs tres)
in (match (uu____21109) with
| (tres1, g_ex) -> begin
(

let cres5 = (

let uu___396_21123 = cres4
in {FStar_Syntax_Syntax.eff_name = uu___396_21123.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres1; FStar_Syntax_Syntax.cflags = uu___396_21123.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp_thunk = uu___396_21123.FStar_Syntax_Syntax.comp_thunk})
in (

let uu____21124 = (FStar_TypeChecker_Env.conj_guard g_ex guard1)
in ((e), (cres5), (uu____21124))))
end))
end))
end)))))))))
end)))
end))
end))
end))
end))
end))
end
| uu____21125 -> begin
(failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t * FStar_TypeChecker_Env.guard_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun lbname lbdef lbtyp -> (

let uu____21170 = (FStar_Options.ml_ish ())
in (match (uu____21170) with
| true -> begin
false
end
| uu____21171 -> begin
(

let t = (FStar_TypeChecker_Normalize.unfold_whnf env lbtyp)
in (

let uu____21173 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____21173) with
| (formals, c) -> begin
(

let uu____21204 = (FStar_Syntax_Util.abs_formals lbdef)
in (match (uu____21204) with
| (actuals, uu____21214, uu____21215) -> begin
(match ((((FStar_List.length formals) < (Prims.parse_int "1")) || ((FStar_List.length actuals) < (Prims.parse_int "1")))) with
| true -> begin
(

let uu____21232 = (

let uu____21237 = (

let uu____21238 = (FStar_Syntax_Print.term_to_string lbdef)
in (

let uu____21239 = (FStar_Syntax_Print.term_to_string lbtyp)
in (FStar_Util.format2 "Only function literals with arrow types can be defined recursively; got %s : %s" uu____21238 uu____21239)))
in ((FStar_Errors.Fatal_RecursiveFunctionLiteral), (uu____21237)))
in (FStar_Errors.raise_error uu____21232 lbtyp.FStar_Syntax_Syntax.pos))
end
| uu____21240 -> begin
(

let actuals1 = (

let uu____21242 = (FStar_TypeChecker_Env.set_expected_typ env lbtyp)
in (FStar_TypeChecker_Util.maybe_add_implicit_binders uu____21242 actuals))
in ((match ((Prims.op_disEquality (FStar_List.length formals) (FStar_List.length actuals1))) with
| true -> begin
(

let actuals_msg = (

let n1 = (FStar_List.length actuals1)
in (match ((Prims.op_Equality n1 (Prims.parse_int "1"))) with
| true -> begin
"1 argument was found"
end
| uu____21268 -> begin
(

let uu____21269 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "%s arguments were found" uu____21269))
end))
in (

let formals_msg = (

let n1 = (FStar_List.length formals)
in (match ((Prims.op_Equality n1 (Prims.parse_int "1"))) with
| true -> begin
"1 argument"
end
| uu____21288 -> begin
(

let uu____21289 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "%s arguments" uu____21289))
end))
in (

let msg = (

let uu____21297 = (FStar_Syntax_Print.term_to_string lbtyp)
in (

let uu____21298 = (FStar_Syntax_Print.lbname_to_string lbname)
in (FStar_Util.format4 "From its type %s, the definition of `let rec %s` expects a function with %s, but %s" uu____21297 uu____21298 formals_msg actuals_msg)))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_LetRecArgumentMismatch), (msg)) lbdef.FStar_Syntax_Syntax.pos))))
end
| uu____21299 -> begin
()
end);
(

let quals = (FStar_TypeChecker_Env.lookup_effect_quals env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)));
))
end)
end))
end)))
end)))
in (

let uu____21305 = (FStar_List.fold_left (fun uu____21338 lb -> (match (uu____21338) with
| (lbs1, env1, g_acc) -> begin
(

let uu____21363 = (FStar_TypeChecker_Util.extract_let_rec_annotation env1 lb)
in (match (uu____21363) with
| (univ_vars1, t, check_t) -> begin
(

let env2 = (FStar_TypeChecker_Env.push_univ_vars env1 univ_vars1)
in (

let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (

let uu____21383 = (match ((not (check_t))) with
| true -> begin
((g_acc), (t))
end
| uu____21398 -> begin
(

let env01 = (FStar_TypeChecker_Env.push_univ_vars env0 univ_vars1)
in (

let uu____21400 = (

let uu____21407 = (

let uu____21408 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____21408))
in (tc_check_tot_or_gtot_term (

let uu___397_21419 = env01
in {FStar_TypeChecker_Env.solver = uu___397_21419.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___397_21419.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___397_21419.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___397_21419.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___397_21419.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___397_21419.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___397_21419.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___397_21419.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___397_21419.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___397_21419.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___397_21419.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___397_21419.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___397_21419.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___397_21419.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___397_21419.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___397_21419.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = uu___397_21419.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___397_21419.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___397_21419.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___397_21419.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___397_21419.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___397_21419.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___397_21419.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___397_21419.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___397_21419.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___397_21419.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___397_21419.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___397_21419.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___397_21419.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___397_21419.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___397_21419.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___397_21419.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___397_21419.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___397_21419.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___397_21419.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___397_21419.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___397_21419.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___397_21419.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___397_21419.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___397_21419.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___397_21419.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___397_21419.FStar_TypeChecker_Env.nbe}) t uu____21407))
in (match (uu____21400) with
| (t1, uu____21427, g) -> begin
(

let uu____21429 = (

let uu____21430 = (

let uu____21431 = (FStar_All.pipe_right g (FStar_TypeChecker_Rel.resolve_implicits env2))
in (FStar_All.pipe_right uu____21431 (FStar_TypeChecker_Rel.discharge_guard env2)))
in (FStar_TypeChecker_Env.conj_guard g_acc uu____21430))
in (

let uu____21432 = (norm env01 t1)
in ((uu____21429), (uu____21432))))
end)))
end)
in (match (uu____21383) with
| (g, t1) -> begin
(

let env3 = (

let uu____21452 = (termination_check_enabled lb.FStar_Syntax_Syntax.lbname e t1)
in (match (uu____21452) with
| true -> begin
(

let uu___398_21453 = env2
in {FStar_TypeChecker_Env.solver = uu___398_21453.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___398_21453.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___398_21453.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___398_21453.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___398_21453.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___398_21453.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___398_21453.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___398_21453.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___398_21453.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___398_21453.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___398_21453.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___398_21453.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___398_21453.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___398_21453.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t1), (univ_vars1)))::env2.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___398_21453.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___398_21453.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___398_21453.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___398_21453.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___398_21453.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___398_21453.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___398_21453.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___398_21453.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___398_21453.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___398_21453.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___398_21453.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___398_21453.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___398_21453.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___398_21453.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___398_21453.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___398_21453.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___398_21453.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___398_21453.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___398_21453.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___398_21453.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___398_21453.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___398_21453.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___398_21453.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___398_21453.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___398_21453.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___398_21453.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___398_21453.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___398_21453.FStar_TypeChecker_Env.nbe})
end
| uu____21460 -> begin
(FStar_TypeChecker_Env.push_let_binding env2 lb.FStar_Syntax_Syntax.lbname ((univ_vars1), (t1)))
end))
in (

let lb1 = (

let uu___399_21466 = lb
in {FStar_Syntax_Syntax.lbname = uu___399_21466.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars1; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu___399_21466.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu___399_21466.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___399_21466.FStar_Syntax_Syntax.lbpos})
in (((lb1)::lbs1), (env3), (g))))
end))))
end))
end)) (([]), (env), (FStar_TypeChecker_Env.trivial_guard)) lbs)
in (match (uu____21305) with
| (lbs1, env1, g) -> begin
(((FStar_List.rev lbs1)), (env1), (g))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let uu____21492 = (

let uu____21501 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____21527 = (FStar_Syntax_Util.abs_formals lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____21527) with
| (bs, t, lcomp) -> begin
(match (bs) with
| [] -> begin
(

let uu____21557 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_RecursiveFunctionLiteral), ("Only function literals may be defined recursively")) uu____21557))
end
| uu____21562 -> begin
(

let lb1 = (

let uu___400_21565 = lb
in (

let uu____21566 = (FStar_Syntax_Util.abs bs t lcomp)
in {FStar_Syntax_Syntax.lbname = uu___400_21565.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___400_21565.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___400_21565.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___400_21565.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____21566; FStar_Syntax_Syntax.lbattrs = uu___400_21565.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___400_21565.FStar_Syntax_Syntax.lbpos}))
in (

let uu____21569 = (

let uu____21576 = (FStar_TypeChecker_Env.set_expected_typ env lb1.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term uu____21576 lb1.FStar_Syntax_Syntax.lbdef))
in (match (uu____21569) with
| (e, c, g) -> begin
((

let uu____21585 = (

let uu____21586 = (FStar_Syntax_Util.is_total_lcomp c)
in (not (uu____21586)))
in (match (uu____21585) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedGTotForLetRec), ("Expected let rec to be a Tot term; got effect GTot")) e.FStar_Syntax_Syntax.pos)
end
| uu____21587 -> begin
()
end));
(

let lb2 = (FStar_Syntax_Util.mk_letbinding lb1.FStar_Syntax_Syntax.lbname lb1.FStar_Syntax_Syntax.lbunivs lb1.FStar_Syntax_Syntax.lbtyp FStar_Parser_Const.effect_Tot_lid e lb1.FStar_Syntax_Syntax.lbattrs lb1.FStar_Syntax_Syntax.lbpos)
in ((lb2), (g)));
)
end)))
end)
end)))))
in (FStar_All.pipe_right uu____21501 FStar_List.unzip))
in (match (uu____21492) with
| (lbs1, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Env.conj_guard gs FStar_TypeChecker_Env.trivial_guard)
in ((lbs1), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let uu____21635 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____21635) with
| (env1, uu____21653) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let uu____21661 = (check_lbtyp top_level env lb)
in (match (uu____21661) with
| (topt, wf_annot, univ_vars1, univ_opening, env11) -> begin
((match (((not (top_level)) && (Prims.op_disEquality univ_vars1 []))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UniversePolymorphicInnerLetBound), ("Inner let-bound definitions cannot be universe polymorphic")) e1.FStar_Syntax_Syntax.pos)
end
| uu____21702 -> begin
()
end);
(

let e11 = (FStar_Syntax_Subst.subst univ_opening e1)
in (

let uu____21705 = (tc_maybe_toplevel_term (

let uu___401_21714 = env11
in {FStar_TypeChecker_Env.solver = uu___401_21714.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___401_21714.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___401_21714.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___401_21714.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___401_21714.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___401_21714.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___401_21714.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___401_21714.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___401_21714.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___401_21714.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___401_21714.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___401_21714.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___401_21714.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___401_21714.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___401_21714.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = uu___401_21714.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___401_21714.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___401_21714.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___401_21714.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___401_21714.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___401_21714.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___401_21714.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___401_21714.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___401_21714.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___401_21714.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___401_21714.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___401_21714.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___401_21714.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___401_21714.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___401_21714.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___401_21714.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___401_21714.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___401_21714.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___401_21714.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___401_21714.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___401_21714.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___401_21714.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___401_21714.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___401_21714.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___401_21714.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___401_21714.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___401_21714.FStar_TypeChecker_Env.nbe}) e11)
in (match (uu____21705) with
| (e12, c1, g1) -> begin
(

let uu____21728 = (

let uu____21733 = (FStar_TypeChecker_Env.set_range env11 e12.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (FStar_Pervasives_Native.Some ((fun uu____21738 -> (FStar_Util.return_all FStar_TypeChecker_Err.ill_kinded_type)))) uu____21733 e12 c1 wf_annot))
in (match (uu____21728) with
| (c11, guard_f) -> begin
(

let g11 = (FStar_TypeChecker_Env.conj_guard g1 guard_f)
in ((

let uu____21753 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____21753) with
| true -> begin
(

let uu____21754 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____21755 = (FStar_Syntax_Print.lcomp_to_string c11)
in (

let uu____21756 = (FStar_TypeChecker_Rel.guard_to_string env g11)
in (FStar_Util.print3 "checked let-bound def %s : %s guard is %s\n" uu____21754 uu____21755 uu____21756))))
end
| uu____21757 -> begin
()
end));
((e12), (univ_vars1), (c11), (g11), ((FStar_Option.isSome topt)));
))
end))
end)));
)
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.subst_elt Prims.list * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____21790 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____21790) with
| (univ_opening, univ_vars1) -> begin
(

let uu____21823 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars1)
in ((FStar_Pervasives_Native.None), (FStar_TypeChecker_Env.trivial_guard), (univ_vars1), (univ_opening), (uu____21823)))
end))
end
| uu____21828 -> begin
(

let uu____21829 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____21829) with
| (univ_opening, univ_vars1) -> begin
(

let t1 = (FStar_Syntax_Subst.subst univ_opening t)
in (

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars1)
in (match ((top_level && (not (env.FStar_TypeChecker_Env.generalize)))) with
| true -> begin
(

let uu____21878 = (FStar_TypeChecker_Env.set_expected_typ env1 t1)
in ((FStar_Pervasives_Native.Some (t1)), (FStar_TypeChecker_Env.trivial_guard), (univ_vars1), (univ_opening), (uu____21878)))
end
| uu____21883 -> begin
(

let uu____21884 = (FStar_Syntax_Util.type_u ())
in (match (uu____21884) with
| (k, uu____21904) -> begin
(

let uu____21905 = (tc_check_tot_or_gtot_term env1 t1 k)
in (match (uu____21905) with
| (t2, uu____21927, g) -> begin
((

let uu____21930 = (FStar_TypeChecker_Env.debug env FStar_Options.Medium)
in (match (uu____21930) with
| true -> begin
(

let uu____21931 = (

let uu____21932 = (FStar_Syntax_Util.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range uu____21932))
in (

let uu____21933 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" uu____21931 uu____21933)))
end
| uu____21934 -> begin
()
end));
(

let t3 = (norm env1 t2)
in (

let uu____21936 = (FStar_TypeChecker_Env.set_expected_typ env1 t3)
in ((FStar_Pervasives_Native.Some (t3)), (g), (univ_vars1), (univ_opening), (uu____21936))));
)
end))
end))
end)))
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env uu____21942 -> (match (uu____21942) with
| (x, imp) -> begin
(

let uu____21969 = (FStar_Syntax_Util.type_u ())
in (match (uu____21969) with
| (tu, u) -> begin
((

let uu____21991 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____21991) with
| true -> begin
(

let uu____21992 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____21993 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____21994 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binder %s:%s at type %s\n" uu____21992 uu____21993 uu____21994))))
end
| uu____21995 -> begin
()
end));
(

let uu____21996 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (uu____21996) with
| (t, uu____22018, g) -> begin
(

let uu____22020 = (match (imp) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (tau)) -> begin
(

let uu____22036 = (tc_tactic env tau)
in (match (uu____22036) with
| (tau1, uu____22050, g1) -> begin
((FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (tau1))), (g1))
end))
end
| uu____22054 -> begin
((imp), (FStar_TypeChecker_Env.trivial_guard))
end)
in (match (uu____22020) with
| (imp1, g') -> begin
(

let x1 = (((

let uu___402_22089 = x
in {FStar_Syntax_Syntax.ppname = uu___402_22089.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___402_22089.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp1))
in ((

let uu____22091 = (FStar_TypeChecker_Env.debug env FStar_Options.High)
in (match (uu____22091) with
| true -> begin
(

let uu____22092 = (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst x1))
in (

let uu____22095 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" uu____22092 uu____22095)))
end
| uu____22096 -> begin
()
end));
(

let uu____22097 = (push_binding env x1)
in ((x1), (uu____22097), (g), (u)));
))
end))
end));
)
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universes) = (fun env bs -> ((

let uu____22109 = (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
in (match (uu____22109) with
| true -> begin
(

let uu____22110 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Checking binders %s\n" uu____22110))
end
| uu____22111 -> begin
()
end));
(

let rec aux = (fun env1 bs1 -> (match (bs1) with
| [] -> begin
(([]), (env1), (FStar_TypeChecker_Env.trivial_guard), ([]))
end
| (b)::bs2 -> begin
(

let uu____22219 = (tc_binder env1 b)
in (match (uu____22219) with
| (b1, env', g, u) -> begin
(

let uu____22268 = (aux env' bs2)
in (match (uu____22268) with
| (bs3, env'1, g', us) -> begin
(

let uu____22329 = (

let uu____22330 = (FStar_TypeChecker_Env.close_guard_univs ((u)::[]) ((b1)::[]) g')
in (FStar_TypeChecker_Env.conj_guard g uu____22330))
in (((b1)::bs3), (env'1), (uu____22329), ((u)::us)))
end))
end))
end))
in (aux env bs));
))
and tc_smt_pats : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list Prims.list  ->  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env1 args -> (FStar_List.fold_right (fun uu____22437 uu____22438 -> (match (((uu____22437), (uu____22438))) with
| ((t, imp), (args1, g)) -> begin
(

let uu____22529 = (tc_term env1 t)
in (match (uu____22529) with
| (t1, uu____22549, g') -> begin
(

let uu____22551 = (FStar_TypeChecker_Env.conj_guard g g')
in (((((t1), (imp)))::args1), (uu____22551)))
end))
end)) args (([]), (FStar_TypeChecker_Env.trivial_guard))))
in (FStar_List.fold_right (fun p uu____22605 -> (match (uu____22605) with
| (pats1, g) -> begin
(

let uu____22632 = (tc_args env p)
in (match (uu____22632) with
| (args, g') -> begin
(

let uu____22645 = (FStar_TypeChecker_Env.conj_guard g g')
in (((args)::pats1), (uu____22645)))
end))
end)) pats (([]), (FStar_TypeChecker_Env.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let uu____22658 = (tc_maybe_toplevel_term env e)
in (match (uu____22658) with
| (e1, c, g) -> begin
(

let uu____22674 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
in (match (uu____22674) with
| true -> begin
((e1), (c), (g))
end
| uu____22681 -> begin
(

let g1 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c1 = (FStar_Syntax_Syntax.lcomp_comp c)
in (

let c2 = (norm_c env c1)
in (

let uu____22685 = (

let uu____22690 = (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c2))
in (match (uu____22690) with
| true -> begin
(

let uu____22695 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c2))
in ((uu____22695), (false)))
end
| uu____22696 -> begin
(

let uu____22697 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((uu____22697), (true)))
end))
in (match (uu____22685) with
| (target_comp, allow_ghost) -> begin
(

let uu____22706 = (FStar_TypeChecker_Rel.sub_comp env c2 target_comp)
in (match (uu____22706) with
| FStar_Pervasives_Native.Some (g') -> begin
(

let uu____22716 = (FStar_Syntax_Util.lcomp_of_comp target_comp)
in (

let uu____22717 = (FStar_TypeChecker_Env.conj_guard g1 g')
in ((e1), (uu____22716), (uu____22717))))
end
| uu____22718 -> begin
(match (allow_ghost) with
| true -> begin
(

let uu____22727 = (FStar_TypeChecker_Err.expected_ghost_expression e1 c2)
in (FStar_Errors.raise_error uu____22727 e1.FStar_Syntax_Syntax.pos))
end
| uu____22738 -> begin
(

let uu____22739 = (FStar_TypeChecker_Err.expected_pure_expression e1 c2)
in (FStar_Errors.raise_error uu____22739 e1.FStar_Syntax_Syntax.pos))
end)
end))
end)))))
end))
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env1 e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let uu____22762 = (tc_tot_or_gtot_term env t)
in (match (uu____22762) with
| (t1, c, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
((t1), (c));
)
end)))


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> ((

let uu____22794 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck")))
in (match (uu____22794) with
| true -> begin
(

let uu____22795 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" uu____22795))
end
| uu____22796 -> begin
()
end));
(

let env1 = (

let uu___403_22798 = env
in {FStar_TypeChecker_Env.solver = uu___403_22798.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___403_22798.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___403_22798.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___403_22798.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___403_22798.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___403_22798.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___403_22798.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___403_22798.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___403_22798.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___403_22798.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___403_22798.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___403_22798.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___403_22798.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___403_22798.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___403_22798.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___403_22798.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___403_22798.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___403_22798.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___403_22798.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___403_22798.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___403_22798.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___403_22798.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___403_22798.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___403_22798.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___403_22798.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___403_22798.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___403_22798.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___403_22798.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___403_22798.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___403_22798.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___403_22798.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___403_22798.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___403_22798.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___403_22798.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___403_22798.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___403_22798.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___403_22798.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___403_22798.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___403_22798.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___403_22798.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___403_22798.FStar_TypeChecker_Env.nbe})
in (

let uu____22805 = (FStar_All.try_with (fun uu___405_22819 -> (match (()) with
| () -> begin
(tc_tot_or_gtot_term env1 e)
end)) (fun uu___404_22831 -> (match (uu___404_22831) with
| FStar_Errors.Error (e1, msg, uu____22840) -> begin
(

let uu____22841 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error ((e1), (msg)) uu____22841))
end)))
in (match (uu____22805) with
| (t, c, g) -> begin
(

let uu____22857 = (FStar_Syntax_Util.is_total_lcomp c)
in (match (uu____22857) with
| true -> begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end
| uu____22864 -> begin
(

let uu____22865 = (

let uu____22870 = (

let uu____22871 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" uu____22871))
in ((FStar_Errors.Fatal_UnexpectedImplictArgument), (uu____22870)))
in (

let uu____22872 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error uu____22865 uu____22872)))
end))
end)));
))


let level_of_type_fail : 'Auu____22887 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string  ->  'Auu____22887 = (fun env e t -> (

let uu____22903 = (

let uu____22908 = (

let uu____22909 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" uu____22909 t))
in ((FStar_Errors.Fatal_UnexpectedTermType), (uu____22908)))
in (

let uu____22910 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____22903 uu____22910))))


let level_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe = (fun env e t -> (

let rec aux = (fun retry t1 -> (

let uu____22945 = (

let uu____22946 = (FStar_Syntax_Util.unrefine t1)
in uu____22946.FStar_Syntax_Syntax.n)
in (match (uu____22945) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| uu____22950 -> begin
(match (retry) with
| true -> begin
(

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) env t1)
in (aux false t2))
end
| uu____22952 -> begin
(

let uu____22953 = (FStar_Syntax_Util.type_u ())
in (match (uu____22953) with
| (t_u, u) -> begin
(

let env1 = (

let uu___406_22961 = env
in {FStar_TypeChecker_Env.solver = uu___406_22961.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___406_22961.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___406_22961.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___406_22961.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___406_22961.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___406_22961.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___406_22961.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___406_22961.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___406_22961.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___406_22961.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___406_22961.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___406_22961.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___406_22961.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___406_22961.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___406_22961.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___406_22961.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___406_22961.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___406_22961.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___406_22961.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___406_22961.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___406_22961.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___406_22961.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___406_22961.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___406_22961.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___406_22961.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___406_22961.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___406_22961.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___406_22961.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___406_22961.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___406_22961.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___406_22961.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___406_22961.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___406_22961.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___406_22961.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___406_22961.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___406_22961.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___406_22961.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___406_22961.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___406_22961.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___406_22961.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___406_22961.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___406_22961.FStar_TypeChecker_Env.nbe})
in (

let g = (FStar_TypeChecker_Rel.teq env1 t1 t_u)
in ((match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____22965 = (FStar_Syntax_Print.term_to_string t1)
in (level_of_type_fail env1 e uu____22965))
end
| uu____22966 -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g)
end);
u;
)))
end))
end)
end)))
in (aux true t)))


let rec universe_of_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun env e -> (

let uu____22983 = (

let uu____22984 = (FStar_Syntax_Subst.compress e)
in uu____22984.FStar_Syntax_Syntax.n)
in (match (uu____22983) with
| FStar_Syntax_Syntax.Tm_bvar (uu____22989) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____22994) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_let (uu____23019) -> begin
(

let e1 = (FStar_TypeChecker_Normalize.normalize [] env e)
in (universe_of_aux env e1))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, uu____23035) -> begin
(level_of_type_fail env e "arrow type")
end
| FStar_Syntax_Syntax.Tm_uvar (u, s) -> begin
(FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ)
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____23081) -> begin
(universe_of_aux env t)
end
| FStar_Syntax_Syntax.Tm_name (n1) -> begin
n1.FStar_Syntax_Syntax.sort
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____23088 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____23088) with
| ((uu____23099, t), uu____23101) -> begin
t
end))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____23107 = (FStar_Syntax_Util.unfold_lazy i)
in (universe_of_aux env uu____23107))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____23110, (FStar_Util.Inl (t), uu____23112), uu____23113) -> begin
t
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____23160, (FStar_Util.Inr (c), uu____23162), uu____23163) -> begin
(FStar_Syntax_Util.comp_result c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____23211) -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Syntax_Syntax.Tm_constant (sc) -> begin
(tc_constant env e.FStar_Syntax_Syntax.pos sc)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____23220; FStar_Syntax_Syntax.vars = uu____23221}, us) -> begin
(

let uu____23227 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____23227) with
| ((us', t), uu____23240) -> begin
((match ((Prims.op_disEquality (FStar_List.length us) (FStar_List.length us'))) with
| true -> begin
(

let uu____23246 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedNumberOfUniverse), ("Unexpected number of universe instantiations")) uu____23246))
end
| uu____23247 -> begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Syntax_Unionfind.univ_change u'' u)
end
| uu____23262 -> begin
(failwith "Impossible")
end)) us' us)
end);
t;
)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____23263) -> begin
(failwith "Impossible: Tm_uinst\'s head must be an fvar")
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____23273) -> begin
(universe_of_aux env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____23300 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____23300) with
| (bs1, c1) -> begin
(

let us = (FStar_List.map (fun uu____23322 -> (match (uu____23322) with
| (b, uu____23330) -> begin
(

let uu____23335 = (universe_of_aux env b.FStar_Syntax_Syntax.sort)
in (level_of_type env b.FStar_Syntax_Syntax.sort uu____23335))
end)) bs1)
in (

let u_res = (

let res = (FStar_Syntax_Util.comp_result c1)
in (

let uu____23342 = (universe_of_aux env res)
in (level_of_type env res uu____23342)))
in (

let u_c = (

let uu____23346 = (FStar_TypeChecker_Env.effect_repr env c1 u_res)
in (match (uu____23346) with
| FStar_Pervasives_Native.None -> begin
u_res
end
| FStar_Pervasives_Native.Some (trepr) -> begin
(

let uu____23350 = (universe_of_aux env trepr)
in (level_of_type env trepr uu____23350))
end))
in (

let u = (FStar_TypeChecker_Normalize.normalize_universe env (FStar_Syntax_Syntax.U_max ((u_c)::us)))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))))
end))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let rec type_of_head = (fun retry hd2 args1 -> (

let hd3 = (FStar_Syntax_Subst.compress hd2)
in (match (hd3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_bvar (uu____23465) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_delayed (uu____23482) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_fvar (uu____23521) -> begin
(

let uu____23522 = (universe_of_aux env hd3)
in ((uu____23522), (args1)))
end
| FStar_Syntax_Syntax.Tm_name (uu____23537) -> begin
(

let uu____23538 = (universe_of_aux env hd3)
in ((uu____23538), (args1)))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____23553) -> begin
(

let uu____23566 = (universe_of_aux env hd3)
in ((uu____23566), (args1)))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____23581) -> begin
(

let uu____23588 = (universe_of_aux env hd3)
in ((uu____23588), (args1)))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____23603) -> begin
(

let uu____23630 = (universe_of_aux env hd3)
in ((uu____23630), (args1)))
end
| FStar_Syntax_Syntax.Tm_refine (uu____23645) -> begin
(

let uu____23652 = (universe_of_aux env hd3)
in ((uu____23652), (args1)))
end
| FStar_Syntax_Syntax.Tm_constant (uu____23667) -> begin
(

let uu____23668 = (universe_of_aux env hd3)
in ((uu____23668), (args1)))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____23683) -> begin
(

let uu____23698 = (universe_of_aux env hd3)
in ((uu____23698), (args1)))
end
| FStar_Syntax_Syntax.Tm_meta (uu____23713) -> begin
(

let uu____23720 = (universe_of_aux env hd3)
in ((uu____23720), (args1)))
end
| FStar_Syntax_Syntax.Tm_type (uu____23735) -> begin
(

let uu____23736 = (universe_of_aux env hd3)
in ((uu____23736), (args1)))
end
| FStar_Syntax_Syntax.Tm_match (uu____23751, (hd4)::uu____23753) -> begin
(

let uu____23818 = (FStar_Syntax_Subst.open_branch hd4)
in (match (uu____23818) with
| (uu____23835, uu____23836, hd5) -> begin
(

let uu____23854 = (FStar_Syntax_Util.head_and_args hd5)
in (match (uu____23854) with
| (hd6, args2) -> begin
(type_of_head retry hd6 args2)
end))
end))
end
| uu____23913 when retry -> begin
(

let e1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::[]) env e)
in (

let uu____23915 = (FStar_Syntax_Util.head_and_args e1)
in (match (uu____23915) with
| (hd4, args2) -> begin
(type_of_head false hd4 args2)
end)))
end
| uu____23974 -> begin
(

let uu____23975 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____23975) with
| (env1, uu____23999) -> begin
(

let env2 = (

let uu___407_24005 = env1
in {FStar_TypeChecker_Env.solver = uu___407_24005.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___407_24005.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___407_24005.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___407_24005.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___407_24005.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___407_24005.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___407_24005.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___407_24005.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___407_24005.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___407_24005.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___407_24005.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___407_24005.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___407_24005.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___407_24005.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___407_24005.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___407_24005.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___407_24005.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___407_24005.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___407_24005.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___407_24005.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___407_24005.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___407_24005.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___407_24005.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___407_24005.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___407_24005.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___407_24005.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___407_24005.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___407_24005.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___407_24005.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___407_24005.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___407_24005.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___407_24005.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___407_24005.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___407_24005.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___407_24005.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___407_24005.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___407_24005.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___407_24005.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___407_24005.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___407_24005.FStar_TypeChecker_Env.nbe})
in ((

let uu____24007 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("UniverseOf")))
in (match (uu____24007) with
| true -> begin
(

let uu____24008 = (

let uu____24009 = (FStar_TypeChecker_Env.get_range env2)
in (FStar_Range.string_of_range uu____24009))
in (

let uu____24010 = (FStar_Syntax_Print.term_to_string hd3)
in (FStar_Util.print2 "%s: About to type-check %s\n" uu____24008 uu____24010)))
end
| uu____24011 -> begin
()
end));
(

let uu____24012 = (tc_term env2 hd3)
in (match (uu____24012) with
| (uu____24035, {FStar_Syntax_Syntax.eff_name = uu____24036; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = uu____24038; FStar_Syntax_Syntax.comp_thunk = uu____24039}, g) -> begin
((

let uu____24053 = (FStar_TypeChecker_Rel.solve_deferred_constraints env2 g)
in (FStar_All.pipe_right uu____24053 (fun a1 -> ())));
((t), (args1));
)
end));
))
end))
end)))
in (

let uu____24066 = (type_of_head true hd1 args)
in (match (uu____24066) with
| (t, args1) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) env t)
in (

let uu____24112 = (FStar_Syntax_Util.arrow_formals_comp t1)
in (match (uu____24112) with
| (bs, res) -> begin
(

let res1 = (FStar_Syntax_Util.comp_result res)
in (match ((Prims.op_Equality (FStar_List.length bs) (FStar_List.length args1))) with
| true -> begin
(

let subst1 = (FStar_Syntax_Util.subst_of_list bs args1)
in (FStar_Syntax_Subst.subst subst1 res1))
end
| uu____24165 -> begin
(

let uu____24166 = (FStar_Syntax_Print.term_to_string res1)
in (level_of_type_fail env e uu____24166))
end))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_match (uu____24169, (hd1)::uu____24171) -> begin
(

let uu____24236 = (FStar_Syntax_Subst.open_branch hd1)
in (match (uu____24236) with
| (uu____24239, uu____24240, hd2) -> begin
(universe_of_aux env hd2)
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____24258, []) -> begin
(level_of_type_fail env e "empty match cases")
end)))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> (

let uu____24305 = (universe_of_aux env e)
in (level_of_type env e uu____24305)))


let tc_tparams : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let uu____24330 = (tc_binders env tps)
in (match (uu____24330) with
| (tps1, env1, g, us) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env1 g);
((tps1), (env1), (us));
)
end)))


let rec type_of_well_typed_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option = (fun env t -> (

let mk_tm_type = (fun u -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____24387) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_bvar (uu____24412) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____24417 = (FStar_Syntax_Util.unfold_lazy i)
in (type_of_well_typed_term env uu____24417))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____24419 = (FStar_TypeChecker_Env.try_lookup_and_inst_lid env [] fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.bind_opt uu____24419 (fun uu____24433 -> (match (uu____24433) with
| (t2, uu____24441) -> begin
FStar_Pervasives_Native.Some (t2)
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____24443; FStar_Syntax_Syntax.vars = uu____24444}, us) -> begin
(

let uu____24450 = (FStar_TypeChecker_Env.try_lookup_and_inst_lid env us fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.bind_opt uu____24450 (fun uu____24464 -> (match (uu____24464) with
| (t2, uu____24472) -> begin
FStar_Pervasives_Native.Some (t2)
end))))
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____24473)) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_constant (sc) -> begin
(

let uu____24475 = (tc_constant env t1.FStar_Syntax_Syntax.pos sc)
in FStar_Pervasives_Native.Some (uu____24475))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____24477 = (mk_tm_type (FStar_Syntax_Syntax.U_succ (u)))
in FStar_Pervasives_Native.Some (uu____24477))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.residual_effect = eff; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (tbody); FStar_Syntax_Syntax.residual_flags = uu____24482})) -> begin
(

let mk_comp = (

let uu____24526 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid)
in (match (uu____24526) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.mk_Total')
end
| uu____24553 -> begin
(

let uu____24554 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid)
in (match (uu____24554) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.mk_GTotal')
end
| uu____24581 -> begin
FStar_Pervasives_Native.None
end))
end))
in (FStar_Util.bind_opt mk_comp (fun f -> (

let uu____24621 = (universe_of_well_typed_term env tbody)
in (FStar_Util.bind_opt uu____24621 (fun u -> (

let uu____24629 = (

let uu____24632 = (

let uu____24639 = (

let uu____24640 = (

let uu____24655 = (f tbody (FStar_Pervasives_Native.Some (u)))
in ((bs), (uu____24655)))
in FStar_Syntax_Syntax.Tm_arrow (uu____24640))
in (FStar_Syntax_Syntax.mk uu____24639))
in (uu____24632 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos))
in FStar_Pervasives_Native.Some (uu____24629))))))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____24695 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____24695) with
| (bs1, c1) -> begin
(

let rec aux = (fun env1 us bs2 -> (match (bs2) with
| [] -> begin
(

let uu____24754 = (universe_of_well_typed_term env1 (FStar_Syntax_Util.comp_result c1))
in (FStar_Util.bind_opt uu____24754 (fun uc -> (

let uu____24762 = (mk_tm_type (FStar_Syntax_Syntax.U_max ((uc)::us)))
in FStar_Pervasives_Native.Some (uu____24762)))))
end
| ((x, imp))::bs3 -> begin
(

let uu____24788 = (universe_of_well_typed_term env1 x.FStar_Syntax_Syntax.sort)
in (FStar_Util.bind_opt uu____24788 (fun u_x -> (

let env2 = (FStar_TypeChecker_Env.push_bv env1 x)
in (aux env2 ((u_x)::us) bs3)))))
end))
in (aux env [] bs1))
end))
end
| FStar_Syntax_Syntax.Tm_abs (uu____24797) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____24817) -> begin
(

let uu____24822 = (universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort)
in (FStar_Util.bind_opt uu____24822 (fun u_x -> (

let uu____24830 = (mk_tm_type u_x)
in FStar_Pervasives_Native.Some (uu____24830)))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____24835; FStar_Syntax_Syntax.vars = uu____24836}, (a)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____24915 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____24915) with
| (unary_op1, uu____24935) -> begin
(

let head1 = (

let uu____24963 = (FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op1), ((a)::[])))) FStar_Pervasives_Native.None uu____24963))
in (

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (type_of_well_typed_term env t2)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____25011; FStar_Syntax_Syntax.vars = uu____25012}, (a1)::(a2)::(hd1)::rest) -> begin
(

let rest1 = (hd1)::rest
in (

let uu____25108 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____25108) with
| (unary_op1, uu____25128) -> begin
(

let head1 = (

let uu____25156 = (FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op1), ((a1)::(a2)::[])))) FStar_Pervasives_Native.None uu____25156))
in (

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head1), (rest1)))) FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)
in (type_of_well_typed_term env t2)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of); FStar_Syntax_Syntax.pos = uu____25212; FStar_Syntax_Syntax.vars = uu____25213}, (uu____25214)::[]) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.t_range)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of); FStar_Syntax_Syntax.pos = uu____25253; FStar_Syntax_Syntax.vars = uu____25254}, ((t2, uu____25256))::(uu____25257)::[]) -> begin
(type_of_well_typed_term env t2)
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let t_hd = (type_of_well_typed_term env hd1)
in (

let rec aux = (fun t_hd1 -> (

let uu____25353 = (

let uu____25354 = (FStar_TypeChecker_Normalize.unfold_whnf env t_hd1)
in uu____25354.FStar_Syntax_Syntax.n)
in (match (uu____25353) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_bs = (FStar_List.length bs)
in (

let bs_t_opt = (match ((n_args < n_bs)) with
| true -> begin
(

let uu____25436 = (FStar_Util.first_N n_args bs)
in (match (uu____25436) with
| (bs1, rest) -> begin
(

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) FStar_Pervasives_Native.None t_hd1.FStar_Syntax_Syntax.pos)
in (

let uu____25528 = (

let uu____25533 = (FStar_Syntax_Syntax.mk_Total t2)
in (FStar_Syntax_Subst.open_comp bs1 uu____25533))
in (match (uu____25528) with
| (bs2, c1) -> begin
FStar_Pervasives_Native.Some (((bs2), ((FStar_Syntax_Util.comp_result c1))))
end)))
end))
end
| uu____25570 -> begin
(match ((Prims.op_Equality n_args n_bs)) with
| true -> begin
(

let uu____25593 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____25593) with
| (bs1, c1) -> begin
(

let uu____25614 = (FStar_Syntax_Util.is_tot_or_gtot_comp c1)
in (match (uu____25614) with
| true -> begin
FStar_Pervasives_Native.Some (((bs1), ((FStar_Syntax_Util.comp_result c1))))
end
| uu____25649 -> begin
FStar_Pervasives_Native.None
end))
end))
end
| uu____25662 -> begin
FStar_Pervasives_Native.None
end)
end)
in (FStar_Util.bind_opt bs_t_opt (fun uu____25692 -> (match (uu____25692) with
| (bs1, t2) -> begin
(

let subst1 = (FStar_List.map2 (fun b a -> FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst b)), ((FStar_Pervasives_Native.fst a))))) bs1 args)
in (

let uu____25768 = (FStar_Syntax_Subst.subst subst1 t2)
in FStar_Pervasives_Native.Some (uu____25768)))
end))))))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____25770) -> begin
(aux x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____25776, uu____25777) -> begin
(aux t2)
end
| uu____25818 -> begin
FStar_Pervasives_Native.None
end)))
in (FStar_Util.bind_opt t_hd aux)))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____25819, (FStar_Util.Inl (t2), uu____25821), uu____25822) -> begin
FStar_Pervasives_Native.Some (t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____25869, (FStar_Util.Inr (c), uu____25871), uu____25872) -> begin
FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_uvar (u, s) -> begin
(

let uu____25937 = (FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ)
in FStar_Pervasives_Native.Some (uu____25937))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.t_term)
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____25945) -> begin
(type_of_well_typed_term env t2)
end
| FStar_Syntax_Syntax.Tm_match (uu____25950) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_let (uu____25973) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Tm_uinst (uu____25986) -> begin
FStar_Pervasives_Native.None
end))))
and universe_of_well_typed_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun env t -> (

let uu____25997 = (type_of_well_typed_term env t)
in (match (uu____25997) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type (u); FStar_Syntax_Syntax.pos = uu____26003; FStar_Syntax_Syntax.vars = uu____26004}) -> begin
FStar_Pervasives_Native.Some (u)
end
| uu____26007 -> begin
FStar_Pervasives_Native.None
end)))


let check_type_of_well_typed_term' : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun must_total env t k -> (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let env2 = (

let uu___408_26032 = env1
in {FStar_TypeChecker_Env.solver = uu___408_26032.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___408_26032.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___408_26032.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___408_26032.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___408_26032.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___408_26032.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___408_26032.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___408_26032.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___408_26032.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___408_26032.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___408_26032.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___408_26032.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___408_26032.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___408_26032.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___408_26032.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___408_26032.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___408_26032.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___408_26032.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___408_26032.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___408_26032.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___408_26032.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___408_26032.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___408_26032.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___408_26032.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___408_26032.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___408_26032.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___408_26032.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___408_26032.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___408_26032.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___408_26032.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___408_26032.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___408_26032.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___408_26032.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___408_26032.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___408_26032.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___408_26032.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___408_26032.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___408_26032.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___408_26032.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___408_26032.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___408_26032.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___408_26032.FStar_TypeChecker_Env.nbe})
in (

let slow_check = (fun uu____26038 -> (match (must_total) with
| true -> begin
(

let uu____26039 = (env2.FStar_TypeChecker_Env.type_of env2 t)
in (match (uu____26039) with
| (uu____26046, uu____26047, g) -> begin
g
end))
end
| uu____26049 -> begin
(

let uu____26050 = (env2.FStar_TypeChecker_Env.tc_term env2 t)
in (match (uu____26050) with
| (uu____26057, uu____26058, g) -> begin
g
end))
end))
in (

let uu____26060 = (type_of_well_typed_term env2 t)
in (match (uu____26060) with
| FStar_Pervasives_Native.None -> begin
(slow_check ())
end
| FStar_Pervasives_Native.Some (k') -> begin
((

let uu____26065 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("FastImplicits")))
in (match (uu____26065) with
| true -> begin
(

let uu____26066 = (FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____26067 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____26068 = (FStar_Syntax_Print.term_to_string k')
in (

let uu____26069 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n" uu____26066 uu____26067 uu____26068 uu____26069)))))
end
| uu____26070 -> begin
()
end));
(

let g = (FStar_TypeChecker_Rel.subtype_nosmt env2 k' k)
in ((

let uu____26075 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("FastImplicits")))
in (match (uu____26075) with
| true -> begin
(

let uu____26076 = (FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____26077 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____26078 = (FStar_Syntax_Print.term_to_string k')
in (

let uu____26079 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n" uu____26076 (match ((FStar_Option.isSome g)) with
| true -> begin
"succeeded with guard"
end
| uu____26080 -> begin
"failed"
end) uu____26077 uu____26078 uu____26079)))))
end
| uu____26081 -> begin
()
end));
(match (g) with
| FStar_Pervasives_Native.None -> begin
(slow_check ())
end
| FStar_Pervasives_Native.Some (g1) -> begin
g1
end);
));
)
end))))))


let check_type_of_well_typed_term : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun must_total env t k -> (

let env1 = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let env2 = (

let uu___409_26105 = env1
in {FStar_TypeChecker_Env.solver = uu___409_26105.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___409_26105.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___409_26105.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___409_26105.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___409_26105.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___409_26105.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___409_26105.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___409_26105.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___409_26105.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___409_26105.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___409_26105.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___409_26105.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___409_26105.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___409_26105.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___409_26105.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___409_26105.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___409_26105.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___409_26105.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___409_26105.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___409_26105.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___409_26105.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___409_26105.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___409_26105.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___409_26105.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___409_26105.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___409_26105.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___409_26105.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___409_26105.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___409_26105.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___409_26105.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___409_26105.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___409_26105.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___409_26105.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___409_26105.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___409_26105.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___409_26105.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___409_26105.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___409_26105.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___409_26105.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___409_26105.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___409_26105.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___409_26105.FStar_TypeChecker_Env.nbe})
in (

let slow_check = (fun uu____26111 -> (match (must_total) with
| true -> begin
(

let uu____26112 = (env2.FStar_TypeChecker_Env.type_of env2 t)
in (match (uu____26112) with
| (uu____26119, uu____26120, g) -> begin
g
end))
end
| uu____26122 -> begin
(

let uu____26123 = (env2.FStar_TypeChecker_Env.tc_term env2 t)
in (match (uu____26123) with
| (uu____26130, uu____26131, g) -> begin
g
end))
end))
in (

let uu____26133 = (

let uu____26134 = (FStar_Options.__temp_fast_implicits ())
in (FStar_All.pipe_left Prims.op_Negation uu____26134))
in (match (uu____26133) with
| true -> begin
(slow_check ())
end
| uu____26135 -> begin
(check_type_of_well_typed_term' must_total env2 t k)
end))))))




